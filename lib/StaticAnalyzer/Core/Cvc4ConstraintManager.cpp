//== MathSATConstraintManager.cpp -------------------------------*- C++ -*--==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "clang/Basic/TargetInfo.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExprEngine.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SMTConstraintManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SMTConv.h"

#include "clang/Config/config.h"

using namespace clang;
using namespace ento;

#if CLANG_ANALYZER_WITH_CVC4

#include <cvc4.h>

namespace cvc = CVC4;

namespace {


/// Configuration class for CVC4
    class Cvc4Config {
        friend class Cvc4ExprManager;

        cvc::Options Config;

    public:
        Cvc4Config() {
            // TODO: add finer-grained configurations
        }

        ~Cvc4Config() = default;
    }; // end class Cvc4Config



    /// Wrapper for CVC4 ExprManager
class Cvc4ExprManager {
public:
  cvc::ExprManager Context;

  Cvc4ExprManager() : Context(Cvc4Config().Config) { }

  virtual ~Cvc4ExprManager() = default;
}; // end class Cvc4ExprManager

/// Wrapper for MathSAT Sort
class Cvc4Sort : public SMTSort {
  friend class Cvc4Solver;

  //Todo: Never used... Staged for removal
  Cvc4ExprManager &Context;

  cvc::Type Sort;

public:
  /// Default constructor, mainly used by make_shared
  Cvc4Sort(Cvc4ExprManager &C, cvc::Type S)
      : SMTSort(), Context(C), Sort(S) {}

  ~Cvc4Sort() = default;

  bool isBitvectorSortImpl() const override {
    return Sort.isBitVector();;
  }

  bool isFloatSortImpl() const override {
    return Sort.isFloatingPoint();
  }

  bool isBooleanSortImpl() const override {
    return Sort.isBoolean();
  }

  unsigned getBitvectorSortSizeImpl() const override {
    assert(isBitvectorSortImpl() && "Cannot extract BitWidth of a non bit vector sort");
    cvc::BitVectorType bv_type = static_cast<cvc::BitVectorType>(Sort);
    return bv_type.getSize();
  }

  unsigned getFloatSortSizeImpl() const override {
    assert(isFloatSortImpl() && "Cannot extract BitWidth of a non bit vector sort");
    cvc::FloatingPointType fp_type = static_cast<cvc::FloatingPointType>(Sort);
    return fp_type.getExponentSize() + fp_type.getSignificandSize();
  }

  bool equal_to(SMTSort const &Other) const override {
    return Sort == static_cast<const Cvc4Sort &>(Other).Sort;
  }

  void print(raw_ostream &OS) const override {
    OS << Sort.toString();
  }
}; // end class Cvc4Sort

static const Cvc4Sort &toCvc4Sort(const SMTSort &S) {
  return static_cast<const Cvc4Sort &>(S);
}

class Cvc4Expr : public SMTExpr {
  friend class Cvc4Solver;

  Cvc4ExprManager &Context;

  cvc::Expr AST;

public:
        Cvc4Expr(Cvc4ExprManager &C, cvc::Expr ZA)
      : SMTExpr(), Context(C), AST(ZA) { }

  void Profile(llvm::FoldingSetNodeID &ID) const override {
    ID.AddInteger(AST.getId());
  }

  /// Comparison of AST equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override {
    assert(Context.Context.getType(AST) ==
            Context.Context.getType(static_cast<const Cvc4Expr &>(Other).AST) &&
           "AST's must have the same sort");
    return AST == static_cast<const Cvc4Expr &>(Other).AST;
  }

  void print(raw_ostream &OS) const override {
    OS << AST.toString();
  }
}; // end class Cvc4Expr

static const Cvc4Expr &toCvc4Expr(const SMTExpr &E) {
  return static_cast<const Cvc4Expr &>(E);
}

} // end anonymous namespace

typedef llvm::ImmutableSet<std::pair<SymbolRef, Cvc4Expr>>
    ConstraintCvc4Ty;
REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstraintCvc4, ConstraintCvc4Ty)

namespace {

class Cvc4Solver : public SMTSolver {
  friend class Cvc4ConstraintManager;
  // FIXME: use a proper LLVM container (e.g.: DenseMap)
  typedef std::map<const std::string, SMTExprRef> symtable_type;
  symtable_type symtable;

  Cvc4ExprManager Context;

  cvc::SmtEngine Solver;

  void setSolverOptions() {
    cvc::LogicInfo logic_info;
    //TODO: add finer-grained logic selection
    Solver.setLogic(logic_info);                    // Set the logic
    Solver.setOption("bv-sat-solver", "minisat");   // Select inner SAT solver
    Solver.setOption("produce-assignments", true);       // Produce Assignments
    Solver.setOption("produce-assertions", true);       // Produce Assertions
    Solver.setOption("output-language", "smtlib2"); // output-language
  }

public:
  Cvc4Solver() : Context(), Solver(&Context.Context) {
      setSolverOptions();
  }

  ~Cvc4Solver() {
      symtable.clear();
  }

  void addConstraint(const SMTExprRef &Exp) override {
    Solver.assertFormula(toCvc4Expr(*Exp).AST);
  }

  SMTSortRef getBoolSort() override {
    return std::make_shared<Cvc4Sort>(Context,
            Context.Context.booleanType());
  }

  SMTSortRef getBitvectorSort(unsigned BitWidth) override {
    return std::make_shared<Cvc4Sort>(
        Context, Context.Context.mkBitVectorType(BitWidth));
  }

  SMTSortRef getSort(const SMTExprRef &Exp) override {
    return std::make_shared<Cvc4Sort>(
        Context, Context.Context.getType(toCvc4Expr(*Exp).AST));
  }

  SMTSortRef getFloat16Sort() override {
    return std::make_shared<Cvc4Sort>(
        Context, Context.Context.mkFloatingPointType(5, 10));
  }

  SMTSortRef getFloat32Sort() override {
    return std::make_shared<Cvc4Sort>(
        Context, Context.Context.mkFloatingPointType(8, 23));
  }

  SMTSortRef getFloat64Sort() override {
    return std::make_shared<Cvc4Sort>(
        Context, Context.Context.mkFloatingPointType(11, 52));
  }

  SMTSortRef getFloat128Sort() override {
    return std::make_shared<Cvc4Sort>(
        Context, Context.Context.mkFloatingPointType(15, 112));
  }

  SMTExprRef newExprRef(const SMTExpr &E) const override {
    return std::make_shared<Cvc4Expr>(toCvc4Expr(E));
  }



    template <typename ...Expr>
    SMTExprRef variadicMkExpr(Cvc4ExprManager& Context, const cvc::Kind opKind, const SMTExprRef &Fst, const Expr (&... args)) {
      // Exception handling...
        cvc::Expr cnt;
        try {
            cnt = Context.Context.mkExpr(opKind, toCvc4Expr(*Fst).AST, (toCvc4Expr(*args).AST)...);
        } catch (const cvc::IllegalArgumentException& ie) {
            llvm::report_fatal_error("CVC4 threw an exception IllegalArgumentException: " + ie.toString());
        } catch (const cvc::LastExceptionBuffer& le) {
            llvm::report_fatal_error("CVC4 threw an exception LastExceptionBuffer");
        } catch (const cvc::Exception& e) {
            llvm::report_fatal_error("CVC4 threw an exception Exception: " + e.toString());
        }
        SMTExprRef res = newExprRef(Cvc4Expr(Context, cnt));

        return res;
    }

  SMTExprRef mkBVNeg(const SMTExprRef &Exp) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_NEG, Exp);
  }

  SMTExprRef mkBVNot(const SMTExprRef &Exp) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_NOT, Exp);
  }

  SMTExprRef mkNot(const SMTExprRef &Exp) override {
    return variadicMkExpr(Context, cvc::Kind::NOT, Exp);
  }

  SMTExprRef mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_PLUS, LHS, RHS);
  }

  SMTExprRef mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_SUB, LHS, RHS);
  }

  SMTExprRef mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_MULT, LHS, RHS);
  }

  SMTExprRef mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_SREM, LHS, RHS);
  }

  SMTExprRef mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
      // TODO: There is also BITVECTOR_UREM_TOTAL, but I think this is good
      return variadicMkExpr(Context, cvc::Kind::BITVECTOR_UREM, LHS, RHS);
  }

  SMTExprRef mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_SDIV, LHS, RHS);
  }

  SMTExprRef mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
      // TODO: There is also BITVECTOR_UDIV_TOTAL, but I think this is good
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_UDIV, LHS, RHS);
  }

  SMTExprRef mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_SHL, LHS, RHS);
  }

  SMTExprRef mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_ASHR, LHS, RHS);
  }

  SMTExprRef mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_LSHR, LHS, RHS);
  }

  SMTExprRef mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_XOR, LHS, RHS);
  }

  SMTExprRef mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_OR, LHS, RHS);
  }

  SMTExprRef mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_AND, LHS, RHS);
  }

  SMTExprRef mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_ULT, LHS, RHS);
  }

  SMTExprRef mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_SLT, LHS, RHS);
  }

  SMTExprRef mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_UGT, LHS, RHS);
  }

  SMTExprRef mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_SGT, LHS, RHS);
  }

  SMTExprRef mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_ULE, LHS, RHS);
  }

  SMTExprRef mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_SLE, LHS, RHS);
  }

  SMTExprRef mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_UGE, LHS, RHS);;
  }

  SMTExprRef mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_SGE, LHS, RHS);;
  }

  SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::AND, LHS, RHS);
  }

  SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::OR, LHS, RHS);
  }

  SMTExprRef mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::EQUAL, LHS, RHS);
  }

  SMTExprRef mkFPNeg(const SMTExprRef &Exp) override {
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_NEG, Exp);
  }

  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) override {
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_ISINF, Exp);
  }

  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) override {
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_ISNAN, Exp);
  }

  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) override {
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_ISN, Exp);
  }

  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) override {
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_ISZ, Exp);
  }

  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_MULT, RoundingMode, LHS, RHS);
  }

  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_DIV, RoundingMode, LHS, RHS);
  }

  SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_REM, RoundingMode, LHS, RHS);
  }

  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_PLUS, RoundingMode, LHS, RHS);
  }

  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_SUB, RoundingMode, LHS, RHS);
  }

  SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_LT, LHS, RHS);
  }

  SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_GT, LHS, RHS);
  }

  SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_LEQ, LHS, RHS);
  }

  SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_GEQ, LHS, RHS);
  }

  SMTExprRef mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_EQ, LHS, RHS);
  }

  SMTExprRef mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                   const SMTExprRef &F) override {
    return variadicMkExpr(Context, cvc::Kind::ITE, Cond, T, F);
  }

  SMTExprRef mkBVSignExt(unsigned i, const SMTExprRef &Exp) override {
    cvc::BitVectorSignExtend ext(i);
    // TODO: check this
    cvc::Expr ext2 = Context.Context.mkConst(ext);
    SMTExprRef ext2r = newExprRef(Cvc4Expr(Context, ext2));
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_SIGN_EXTEND, ext2r, Exp);
  }

  SMTExprRef mkBVZeroExt(unsigned i, const SMTExprRef &Exp) override {
    cvc::BitVectorSignExtend ext(i);
    // TODO: check this
    cvc::Expr ext2 = Context.Context.mkConst(ext);
    SMTExprRef ext2r = newExprRef(Cvc4Expr(Context, ext2));
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_ZERO_EXTEND, ext2r, Exp);
  }

  SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                         const SMTExprRef &Exp) override {
    cvc::BitVectorExtract ext(High, Low);
    // TODO: check this
    cvc::Expr ext2 = Context.Context.mkConst(ext);
    SMTExprRef ext2r = newExprRef(Cvc4Expr(Context, ext2));
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_EXTRACT, ext2r, Exp);
  }

  SMTExprRef mkBVConcat(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return variadicMkExpr(Context, cvc::Kind::BITVECTOR_CONCAT, LHS, RHS);
  }

  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To) override {
    // TODO: check this
    assert(To->isFloatSort() && "CVC4 error: To is not a floating point type");
    SMTExprRef RoundingMode = getFloatRoundingMode();
    cvc::FloatingPointType fto = static_cast<cvc::FloatingPointType>(toCvc4Sort(*To).Sort);
    unsigned ExpWidth = fto.getExponentSize();
    unsigned MantWidth = fto.getSignificandSize();

    cvc::FloatingPointToFPFloatingPoint conv_op(ExpWidth, MantWidth);
    cvc::Expr conv_op2 = Context.Context.mkConst(conv_op);
    SMTExprRef conv_op2r = newExprRef(Cvc4Expr(Context, conv_op2));

    return variadicMkExpr(Context, cvc::kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT,
                    RoundingMode, From, conv_op2r);
  }

  SMTExprRef mkFPtoSBV(const SMTExprRef &From, const SMTSortRef &To) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    cvc::FloatingPointType fpto = static_cast<cvc::FloatingPointType>(toCvc4Sort(*To).Sort);
    cvc::FloatingPointToFPSignedBitVector conv_op(fpto.getExponentSize(), fpto.getSignificandSize());
    cvc::Expr conv_op2 = Context.Context.mkConst(conv_op);
    SMTExprRef conv_op2r = newExprRef(Cvc4Expr(Context, conv_op2));

    return variadicMkExpr(Context,
            cvc::Kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR, RoundingMode, From, conv_op2r);
  }

  SMTExprRef mkFPtoUBV(const SMTExprRef &From, const SMTSortRef &To) override {
      SMTExprRef RoundingMode = getFloatRoundingMode();
      cvc::FloatingPointType fpto = static_cast<cvc::FloatingPointType>(toCvc4Sort(*To).Sort);
      cvc::FloatingPointToFPUnsignedBitVector conv_op(fpto.getExponentSize(), fpto.getSignificandSize());
      cvc::Expr conv_op2 = Context.Context.mkConst(conv_op);
      SMTExprRef conv_op2r = newExprRef(Cvc4Expr(Context, conv_op2));

      return variadicMkExpr(Context,
                            cvc::Kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR, RoundingMode, From, conv_op2r);
  }

  SMTExprRef mkSBVtoFP(const SMTExprRef &From, unsigned ToWidth) override {
    // Conversion from float to integers always truncate, so we assume
    // the round mode to be toward zero
    SMTExprRef RoundingMode = newExprRef(
        Cvc4Expr(Context, Context.Context.mkConst(CVC4::RoundingMode::roundTowardZero)));

    cvc::FloatingPointToSBV conv_op(ToWidth);
    cvc::Expr conv_op2 = Context.Context.mkConst(conv_op);
    SMTExprRef conv_op2r = newExprRef(Cvc4Expr(Context, conv_op2));

    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_TO_SBV, From, conv_op2r);
  }

  SMTExprRef mkUBVtoFP(const SMTExprRef &From, unsigned ToWidth) override {
    // Conversion from float to integers always truncate, so we assume
    // the round mode to be toward zero
    SMTExprRef RoundingMode = newExprRef(
            Cvc4Expr(Context, Context.Context.mkConst(CVC4::RoundingMode::roundTowardZero)));

    cvc::FloatingPointToUBV conv_op(ToWidth);
    cvc::Expr conv_op2 = Context.Context.mkConst(conv_op);
    SMTExprRef conv_op2r = newExprRef(Cvc4Expr(Context, conv_op2));

    return variadicMkExpr(Context, cvc::Kind::FLOATINGPOINT_TO_UBV, From, conv_op2r);
  }

  SMTExprRef mkBoolean(const bool b) override {
    return newExprRef(Cvc4Expr(Context, Context.Context.mkConst(b)));
  }

  cvc::BitVector mkPlainBitVector(const llvm::APSInt Int, unsigned BitWidth) {
      std::string Str(BitWidth, '0');
      llvm::APSInt ext_int = Int;
      if (Int.getBitWidth() < BitWidth) {
          ext_int = Int.extend(BitWidth);
      }
      for (unsigned i = 0; i < BitWidth; ++i) {
          Str[BitWidth - 1 - i] = ext_int[i] ? '1' : '0';
      }
      cvc::BitVector bit_vect(Str, 2);
      return bit_vect;
  }

  SMTExprRef mkBitvector(const llvm::APSInt Int, unsigned BitWidth) override {
     cvc::BitVector bit_vect = mkPlainBitVector(Int, BitWidth);
    return newExprRef(
        Cvc4Expr(Context, Context.Context.mkConst(bit_vect)));
  }

  SMTExprRef mkFloat(const llvm::APFloat Float) override {
    assert(false && "Cvc4ConstraintManager does not support floating point yet");
      return nullptr;
  }

  SMTExprRef mkSymbol(const char *Name, SMTSortRef Sort) override {
    std::string sname(Name);
    auto val = symtable.find(sname);
    if (val == symtable.end()) {
        SMTExprRef newval = newExprRef(
                Cvc4Expr(Context, Context.Context.mkVar(std::string(Name), toCvc4Sort(*Sort).Sort)));
        symtable[sname] = newval;
    }
    return symtable[sname];
  }

  llvm::APSInt getBitvector(const SMTExprRef &Exp, unsigned BitWidth,
                            bool isUnsigned) override {

      cvc::Expr expr = toCvc4Expr(*Exp).AST;
      assert(expr.getType().isBitVector() && "Cannot get value of a non BitVector expression");
      assert(expr.isConst() && "Cannot get value of a non const expression");

      const cvc::BitVector& bv = expr.getConst<cvc::BitVector>();

    return llvm::APSInt(llvm::APInt(BitWidth, bv.toString(2), 2));
  }

  bool getBoolean(const SMTExprRef &Exp) override {
    cvc::Expr expr = toCvc4Expr(*Exp).AST;
    assert(expr.getType().isBoolean() && "Cannot get value of a non Boolean expression");
    assert(expr.isConst() && "Cannot get value of a non const expression");
    bool res = expr.getConst<bool>();

    return res;
  }

  SMTExprRef getFloatRoundingMode() override {
    // TODO: Don't assume nearest ties to even rounding mode
    return newExprRef(Cvc4Expr(
        Context,  Context.Context.mkConst(CVC4::RoundingMode::roundNearestTiesToEven)));
  }

  SMTExprRef fromBoolean(const bool Bool) override { return mkBoolean(Bool); }

  SMTExprRef fromAPFloat(const llvm::APFloat &Float) override {
    return mkFloat(Float);
  }

  SMTExprRef fromAPSInt(const llvm::APSInt &Int) override {
    return mkBitvector(Int, Int.getBitWidth());
  }

  SMTExprRef fromInt(const char *Int, uint64_t BitWidth) override {
    return mkBitvector(llvm::APSInt(Int), BitWidth);
  }

  bool toAPFloat(const SMTSortRef &Sort, const SMTExprRef &AST,
                 llvm::APFloat &Float, bool useSemantics) {
      assert(false && "Cvc4ConstraintManager does not support floating point yet");
      return false;
  }

  bool toAPSInt(const SMTSortRef &Sort, const SMTExprRef &AST,
                llvm::APSInt &Int, bool useSemantics) {
    if (Sort->isBitvectorSort()) {
      if (useSemantics && Int.getBitWidth() != Sort->getBitvectorSortSize()) {
        assert(false && "Bitvector types don't match!");
        return false;
      }

      // FIXME: This function is also used to retrieve floating-point values,
      // which can be 16, 32, 64 or 128 bits long. Bitvectors can be anything
      // between 1 and 64 bits long, which is the reason we have this weird
      // guard. In the future, we need proper calls in the backend to retrieve
      // floating-points and its special values (NaN, +/-infinity, +/-zero),
      // then we can drop this weird condition.
      if (Sort->getBitvectorSortSize() <= 64 ||
          Sort->getBitvectorSortSize() == 128) {
        Int = getBitvector(AST, Int.getBitWidth(), Int.isUnsigned());
        return true;
      }

      assert(false && "Bitwidth not supported!");
      return false;
    }

    if (Sort->isBooleanSort()) {
      if (useSemantics && Int.getBitWidth() < 1) {
        assert(false && "Boolean type doesn't match!");
        return false;
      }

      Int = llvm::APSInt(llvm::APInt(Int.getBitWidth(), getBoolean(AST)),
                         Int.isUnsigned());
      return true;
    }

    llvm_unreachable("Unsupported sort to integer!");
  }

  bool getInterpretation(const SMTExprRef &Exp, llvm::APSInt &Int) override {
    cvc::Expr exp_value = Solver.getValue(toCvc4Expr(*Exp).AST);
    //Not required if toAPSInt takes a cvc::Expr directly
    SMTExprRef exp_value_ref = newExprRef(Cvc4Expr(Context, exp_value));
    return toAPSInt(getSort(Exp), exp_value_ref, Int, true);
  }

  bool getInterpretation(const SMTExprRef &Exp, llvm::APFloat &Float) override {
    cvc::Expr exp_value = Solver.getValue(toCvc4Expr(*Exp).AST);
    //Not required if toAPFloat takes a cvc::Expr directly
    SMTExprRef exp_value_ref = newExprRef(Cvc4Expr(Context, exp_value));
    return toAPFloat(getSort(Exp), exp_value_ref, Float, true);
  }

  Optional<bool> check() const override {
    cvc::Result r = const_cast<Cvc4Solver*>(this)->Solver.checkSat();

    if (r.isSat() == CVC4::Result::SAT)
        return true;

    if (r.isSat() == CVC4::Result::UNSAT)
        return false;

    return Optional<bool>();
  }

  void push() override { Solver.push(); }

  void pop(unsigned NumStates = 1) override {
    while (NumStates--)
      Solver.pop();
  }

  /// Reset the solver and remove all constraints.
  void reset() override {
    Solver.resetAssertions();
    //TODO: probably not required
    Solver.reset();
    setSolverOptions();
  }

  void print(raw_ostream &OS) const override {
    std::vector<cvc::Expr> assertions(const_cast<Cvc4Solver*>(this)->Solver.getAssertions());
    for (const auto &assertion : assertions) {
      OS << assertion.toString();
    }
  }
}; // end class Cvc4Solver

class Cvc4ConstraintManager
    : public SMTConstraintManager<ConstraintCvc4, Cvc4Expr> {
  SMTSolverRef Solver = CreateCvc4Solver();

public:
    Cvc4ConstraintManager(SubEngine *SE, SValBuilder &SB)
      : SMTConstraintManager(SE, SB, Solver) {}

  bool canReasonAbout(SVal X) const override {
    const TargetInfo &TI = getBasicVals().getContext().getTargetInfo();

    Optional<nonloc::SymbolVal> SymVal = X.getAs<nonloc::SymbolVal>();
    if (!SymVal)
      return true;

    const SymExpr *Sym = SymVal->getSymbol();
    QualType Ty = Sym->getType();

    // Complex types are not modeled
    if (Ty->isComplexType() || Ty->isComplexIntegerType())
      return false;

    //TODO: remove this check when support for floating point will be completed
    if (Ty->isRealFloatingType())
        return false;

    // Non-IEEE 754 floating-point types are not modeled
    if ((Ty->isSpecificBuiltinType(BuiltinType::LongDouble) &&
         (&TI.getLongDoubleFormat() == &llvm::APFloat::x87DoubleExtended() ||
          &TI.getLongDoubleFormat() == &llvm::APFloat::PPCDoubleDouble())))
      return false;

    if (isa<SymbolData>(Sym))
      return true;

    SValBuilder &SVB = getSValBuilder();

    if (const SymbolCast *SC = dyn_cast<SymbolCast>(Sym))
      return canReasonAbout(SVB.makeSymbolVal(SC->getOperand()));

    if (const BinarySymExpr *BSE = dyn_cast<BinarySymExpr>(Sym)) {
      if (const SymIntExpr *SIE = dyn_cast<SymIntExpr>(BSE))
        return canReasonAbout(SVB.makeSymbolVal(SIE->getLHS()));

      if (const IntSymExpr *ISE = dyn_cast<IntSymExpr>(BSE))
        return canReasonAbout(SVB.makeSymbolVal(ISE->getRHS()));

      if (const SymSymExpr *SSE = dyn_cast<SymSymExpr>(BSE))
        return canReasonAbout(SVB.makeSymbolVal(SSE->getLHS())) &&
               canReasonAbout(SVB.makeSymbolVal(SSE->getRHS()));
    }

    llvm_unreachable("Unsupported expression to reason about!");
  }
}; // end class Cvc4ConstraintManager

} // end anonymous namespace

#endif

SMTSolverRef clang::ento::CreateCvc4Solver() {
#if CLANG_ANALYZER_WITH_CVC4
  return llvm::make_unique<Cvc4Solver>();
#else
  llvm::report_fatal_error(
      "Clang was not compiled with CVC4 support, rebuild "
      "with -DCLANG_ANALYZER_ENABLE_CVC4_SOLVER=ON",
      false);
  return nullptr;
#endif
}

std::unique_ptr<ConstraintManager>
ento::CreateCvc4ConstraintManager(ProgramStateManager &StMgr, SubEngine *Eng) {
#if CLANG_ANALYZER_WITH_CVC4
  return llvm::make_unique<Cvc4ConstraintManager>(Eng,
                                                     StMgr.getSValBuilder());
#else
  llvm::report_fatal_error(
      "Clang was not compiled with CVC4 support, rebuild "
      "with -DCLANG_ANALYZER_ENABLE_CVC4_SOLVER=ON",
      false);
  return nullptr;
#endif
}