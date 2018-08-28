//== BoolectorConstraintManager.cpp -----------------------------*- C++ -*--==//
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

#if CLANG_ANALYZER_WITH_BOOLECTOR

// Namespace used to avoid clash with BoolectorSort
namespace btor {
#include <boolector.h>
}

#include <cstdio>
#include <iostream>

namespace {

// Function used to report errors
void BoolectorErrorHandler(const char *msg) {
  llvm::report_fatal_error("Boolector error: " + llvm::Twine(msg));
}

/// Wrapper for Boolector context
class BoolectorContext {
  void createAndConfig() {
    assert(Context == nullptr &&
           "Boolector creation failed. Context was not null");

    btor::boolector_set_abort(BoolectorErrorHandler);
    Context = btor::boolector_new();
    btor::boolector_set_opt(Context, btor::BTOR_OPT_MODEL_GEN, 1);
    btor::boolector_set_opt(Context, btor::BTOR_OPT_INCREMENTAL, 1);
    btor::boolector_set_opt(Context, btor::BTOR_OPT_AUTO_CLEANUP, 1);
  }

public:
  btor::Btor *Context;

  BoolectorContext() : Context(nullptr) { createAndConfig(); }

  virtual ~BoolectorContext() {
    btor::boolector_release_all(Context);
    btor::boolector_delete(Context);
    Context = nullptr;
  }

  void reset() {
    btor::boolector_release_all(Context);
    btor::boolector_delete(Context);
    Context = nullptr;
    createAndConfig();
  }
}; // end class BoolectorContext

/// Wrapper for Boolector Sort
class BoolectorSort : public SMTSort {
  friend class BoolectorSolver;

  BoolectorContext &Context;

  btor::BoolectorSort Sort;

  unsigned BitWidth;

public:
  /// Default constructor, mainly used by make_shared
  BoolectorSort(BoolectorContext &C, btor::BoolectorSort ZS, unsigned Width)
      : SMTSort(), Context(C), Sort(ZS), BitWidth(Width) {}

  /// Override implicit copy constructor for correct reference counting.
  BoolectorSort(const BoolectorSort &Copy)
      : SMTSort(), Context(Copy.Context), Sort(Copy.Sort),
        BitWidth(Copy.BitWidth) {}

  /// Provide move constructor
  BoolectorSort(BoolectorSort &&Move)
      : SMTSort(), Context(Move.Context), Sort(nullptr),
        BitWidth(Move.BitWidth) {
    // TODO: Weird...
    *this = std::move(Move);
  }

  /// Provide move assignment constructor
  BoolectorSort &operator=(BoolectorSort &&Move) {
    if (this != &Move) {
      Sort = Move.Sort;
      Move.Sort = nullptr;
      BitWidth = Move.BitWidth;
      Move.BitWidth = 0;
    }
    return *this;
  }

  ~BoolectorSort() {}

  bool isBitvectorSortImpl() const override {
    return btor::boolector_is_bitvec_sort(Context.Context, Sort) &&
           BitWidth != 1;
  }

  bool isFloatSortImpl() const override {
    // Boolector does not support floating point
    return false;
  }

  bool isBooleanSortImpl() const override {
    // As boolector 3.0.1 Booleans are one-sized bit-vectors
    return btor::boolector_is_bitvec_sort(Context.Context, Sort) &&
           BitWidth == 1;
  }

  unsigned getBitvectorSortSizeImpl() const override { return BitWidth; }

  unsigned getFloatSortSizeImpl() const override {
    assert(false && "Boolector error: floating-point types are not supported");
    return 0;
  }

  bool equal_to(SMTSort const &Other) const override {
    // boolector 3.0.1 API does not provide equality function for sort.
    const BoolectorSort &btor_other = static_cast<const BoolectorSort &>(Other);

    if (isBooleanSortImpl() && btor_other.isBooleanSortImpl()) {
      return true;
    }

    if (isBitvectorSortImpl() && btor_other.isBitvectorSortImpl() &&
        BitWidth == btor_other.BitWidth) {
      return true;
    }

    // TODO: add here checks for arrays and uninterpreted functions if necessary

    return false;
  }

  BoolectorSort &operator=(const BoolectorSort &Move) {
    Sort = Move.Sort;
    return *this;
  }

  void print(raw_ostream &OS) const override {
    // TODO: Boolector has only a print function that writes on C file
    // descriptor
  }
}; // end class BoolectorSort

static const BoolectorSort &toBoolectorSort(const SMTSort &S) {
  return static_cast<const BoolectorSort &>(S);
}

class BoolectorExpr : public SMTExpr {
  friend class BoolectorSolver;

  BoolectorContext &Context;

  btor::BoolectorNode *AST;

public:
  BoolectorExpr(BoolectorContext &C, btor::BoolectorNode *ZA)
      : SMTExpr(), Context(C), AST(ZA) {}

  /// Override implicit copy constructor for correct reference counting.
  BoolectorExpr(const BoolectorExpr &Copy)
      : SMTExpr(), Context(Copy.Context), AST(Copy.AST) {}

  /// Provide move constructor
  BoolectorExpr(BoolectorExpr &&Move)
      : SMTExpr(), Context(Move.Context), AST(nullptr) {
    // TODO: WEIRD!
    *this = std::move(Move);
  }

  /// Provide move assignment constructor
  BoolectorExpr &operator=(BoolectorExpr &&Move) {
    if (this != &Move) {
      AST = Move.AST;
      Move.AST = nullptr;
    }
    return *this;
  }

  ~BoolectorExpr() {}

  void Profile(llvm::FoldingSetNodeID &ID) const override {
    // FIXME: what is this? WEIRD!!
    ID.AddInteger((unsigned long long int)AST);
  }

  /// Comparison of AST equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override {
    assert(btor::boolector_is_equal_sort(
               Context.Context, AST,
               static_cast<const BoolectorExpr &>(Other).AST) &&
           "AST's must have the same sort");
    // TODO: WEIRD!!
    return AST == static_cast<const BoolectorExpr &>(Other).AST;
  }

  /// Override implicit move constructor for correct reference counting.
  BoolectorExpr &operator=(const BoolectorExpr &Move) {
    AST = Move.AST;
    return *this;
  }

  void print(raw_ostream &OS) const override {
    // TODO: Boolector has only a print function that writes on C file
    // descriptor
    return;
  }
}; // end class BoolectorExpr

static const BoolectorExpr &toBoolectorExpr(const SMTExpr &E) {
  return static_cast<const BoolectorExpr &>(E);
}
} // end anonymous namespace

typedef llvm::ImmutableSet<std::pair<SymbolRef, BoolectorExpr>>
    ConstraintBoolectorTy;
REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstraintBoolector, ConstraintBoolectorTy)

namespace {

class BoolectorSolver : public SMTSolver {
  // FIXME: use a proper LLVM container (e.g.: DenseMap)
  typedef std::map<const std::string, SMTExprRef> symtable_type;
  symtable_type symtable;
  // FIXME: use a proper LLVM container
  std::unique_ptr<std::list<SMTExprRef>> assertions =
      std::unique_ptr<std::list<SMTExprRef>>(new std::list<SMTExprRef>());

  friend class BoolectorConstraintManager;

  BoolectorContext Context;

public:
  BoolectorSolver() : SMTSolver() {}

  /// Override implicit copy constructor for correct reference counting.
  BoolectorSolver(const BoolectorSolver &Copy)
      : SMTSolver(), Context(Copy.Context) {}

  /// Provide move constructor
  BoolectorSolver(BoolectorSolver &&Move) : SMTSolver(), Context(Move.Context) {
    *this = std::move(Move);
  }

  /// Provide move assignment constructor
  BoolectorSolver &operator=(BoolectorSolver &&Move) {
    if (this != &Move) {
      this->Context = std::move(Move.Context);
    }
    return *this;
  }

  ~BoolectorSolver() {}

  void addConstraint(const SMTExprRef &Exp) const override {
    assertions->push_back(Exp);
  }

  SMTSortRef getBoolSort() override {
    return std::make_shared<BoolectorSort>(
        Context, btor::boolector_bool_sort(Context.Context), 1);
  }

  SMTSortRef getBitvectorSort(unsigned BitWidth) override {
    return std::make_shared<BoolectorSort>(
        Context, btor::boolector_bitvec_sort(Context.Context, BitWidth),
        BitWidth);
  }

  SMTSortRef getSort(const SMTExprRef &Exp) override {
    return std::make_shared<BoolectorSort>(
        Context,
        btor::boolector_get_sort(Context.Context, toBoolectorExpr(*Exp).AST),
        btor::boolector_get_width(Context.Context, toBoolectorExpr(*Exp).AST));
  }

  SMTSortRef getFloat16Sort() override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTSortRef getFloat32Sort() override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTSortRef getFloat64Sort() override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTSortRef getFloat128Sort() override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef newExprRef(const SMTExpr &E) const override {
    return std::make_shared<BoolectorExpr>(toBoolectorExpr(E));
  }

  SMTExprRef mkBVNeg(const SMTExprRef &Exp) override {
    return newExprRef(
        BoolectorExpr(Context, btor::boolector_neg(Context.Context,
                                                   toBoolectorExpr(*Exp).AST)));
  }

  SMTExprRef mkBVNot(const SMTExprRef &Exp) override {
    return newExprRef(
        BoolectorExpr(Context, btor::boolector_not(Context.Context,
                                                   toBoolectorExpr(*Exp).AST)));
  }

  SMTExprRef mkNot(const SMTExprRef &Exp) override {
    return newExprRef(
        BoolectorExpr(Context, btor::boolector_not(Context.Context,
                                                   toBoolectorExpr(*Exp).AST)));
  }

  SMTExprRef mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_add(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_sub(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_mul(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_srem(Context.Context, toBoolectorExpr(*LHS).AST,
                             toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_urem(Context.Context, toBoolectorExpr(*LHS).AST,
                             toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_sdiv(Context.Context, toBoolectorExpr(*LHS).AST,
                             toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_udiv(Context.Context, toBoolectorExpr(*LHS).AST,
                             toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_sll(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_sra(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_srl(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_xor(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_or(Context.Context, toBoolectorExpr(*LHS).AST,
                                    toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_and(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_ult(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_slt(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_ugt(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_sgt(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_ulte(Context.Context, toBoolectorExpr(*LHS).AST,
                             toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_slte(Context.Context, toBoolectorExpr(*LHS).AST,
                             toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_ugte(Context.Context, toBoolectorExpr(*LHS).AST,
                             toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_sgte(Context.Context, toBoolectorExpr(*LHS).AST,
                             toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_and(Context.Context, toBoolectorExpr(*LHS).AST,
                                     toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_or(Context.Context, toBoolectorExpr(*LHS).AST,
                                    toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_eq(Context.Context, toBoolectorExpr(*LHS).AST,
                                    toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkFPNeg(const SMTExprRef &Exp) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                   const SMTExprRef &F) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_cond(
                     Context.Context, toBoolectorExpr(*Cond).AST,
                     toBoolectorExpr(*T).AST, toBoolectorExpr(*F).AST)));
  }

  SMTExprRef mkBVSignExt(unsigned i, const SMTExprRef &Exp) override {
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_sext(Context.Context, toBoolectorExpr(*Exp).AST, i)));
  }

  SMTExprRef mkBVZeroExt(unsigned i, const SMTExprRef &Exp) override {
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_uext(Context.Context, toBoolectorExpr(*Exp).AST, i)));
  }

  SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                         const SMTExprRef &Exp) override {
    return newExprRef(BoolectorExpr(
        Context, btor::boolector_slice(Context.Context,
                                       toBoolectorExpr(*Exp).AST, High, Low)));
  }

  SMTExprRef mkBVConcat(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_concat(Context.Context, toBoolectorExpr(*LHS).AST,
                               toBoolectorExpr(*RHS).AST)));
  }

  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPtoSBV(const SMTExprRef &From, const SMTSortRef &To) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPtoUBV(const SMTExprRef &From, const SMTSortRef &To) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkSBVtoFP(const SMTExprRef &From, unsigned ToWidth) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkUBVtoFP(const SMTExprRef &From, unsigned ToWidth) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkBoolean(const bool b) override {
    return newExprRef(
        BoolectorExpr(Context, b ? btor::boolector_true(Context.Context)
                                 : btor::boolector_false(Context.Context)));
  }

  SMTExprRef mkBitvector(const llvm::APSInt Int, unsigned BitWidth) override {
    const SMTSortRef Sort = getBitvectorSort(BitWidth);
    return newExprRef(BoolectorExpr(
        Context,
        btor::boolector_constd(Context.Context, toBoolectorSort(*Sort).Sort,
                               Int.toString(10).c_str())));
  }

  SMTExprRef mkFloat(const llvm::APFloat Float) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkSymbol(const char *Name, SMTSortRef Sort) override {
    std::string sname(Name);
    auto val = symtable.find(sname);
    if (val == symtable.end()) {
      SMTExprRef newval = newExprRef(BoolectorExpr(
          Context, btor::boolector_var(Context.Context,
                                       toBoolectorSort(*Sort).Sort, Name)));
      symtable[sname] = newval;
    }

    return symtable[sname];
  }

  llvm::APSInt getBitvector(const SMTExprRef &Exp, unsigned BitWidth,
                            bool isUnsigned) override {
    assert(
        btor::boolector_is_const(Context.Context, toBoolectorExpr(*Exp).AST) &&
        "Can get value only of constant");

    const char *val = btor::boolector_bv_assignment(Context.Context,
                                                    toBoolectorExpr(*Exp).AST);

    llvm::APSInt res(llvm::APInt(BitWidth, val, 2), isUnsigned);

    btor::boolector_free_bv_assignment(Context.Context, val);

    return res;
  }

  bool getBoolean(const SMTExprRef &Exp) override {
    assert(
        btor::boolector_is_const(Context.Context, toBoolectorExpr(*Exp).AST) &&
        "Can get value only of constant");
    assert(btor::boolector_is_equal_sort(
               Context.Context, toBoolectorExpr(*Exp).AST,
               btor::boolector_true(Context.Context)) &&
           "Expression does not have Boolean type");

    const char *val =
        boolector_bv_assignment(Context.Context, toBoolectorExpr(*Exp).AST);
    bool res = parseBoolean(val);

    btor::boolector_free_bv_assignment(Context.Context, val);
    return res;
  }

  SMTExprRef getFloatRoundingMode() override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef fromBoolean(const bool Bool) override {
    btor::BoolectorNode *AST = Bool ? btor::boolector_true(Context.Context)
                                    : btor::boolector_false(Context.Context);
    return newExprRef(BoolectorExpr(Context, AST));
  }

  SMTExprRef fromAPFloat(const llvm::APFloat &Float) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef fromAPSInt(const llvm::APSInt &Int) override {
    SMTSortRef Sort = getBitvectorSort(Int.getBitWidth());
    btor::BoolectorNode *AST = btor::boolector_constd(
        Context.Context, toBoolectorSort(*Sort).Sort, Int.toString(10).c_str());
    return newExprRef(BoolectorExpr(Context, AST));
  }

  SMTExprRef fromInt(const char *Int, uint64_t BitWidth) override {
    SMTSortRef Sort = getBitvectorSort(BitWidth);
    btor::BoolectorNode *AST = btor::boolector_constd(
        Context.Context, toBoolectorSort(*Sort).Sort, Int);
    return newExprRef(BoolectorExpr(Context, AST));
  }

  bool parseInt(const char *value, llvm::APSInt &Int) {
    assert(value != nullptr &&
           "Boolector returned null boolean assignment string");
    Int = llvm::APSInt(llvm::APInt(Int.getBitWidth(), value, 2),
                       Int.isUnsigned());

    return true;
  }

  bool parseBoolean(const char *value) {
    assert(value != nullptr &&
           "Boolector returned null boolean assignment string");

    bool res;
    switch (*value) {
    case '1':
      res = true;
      break;
    case '0':
      res = false;
      break;
    default:
      llvm_unreachable("Bad boolean value");
    }

    return res;
  }

  bool toAPSInt(const SMTSortRef &Sort, const char *Value, llvm::APSInt &Int,
                bool useSemantics) {
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
        bool res = parseInt(Value, Int);
        return res;
      }

      assert(false && "Bitwidth not supported!");
      return false;
    }

    if (Sort->isBooleanSort()) {
      if (useSemantics && Int.getBitWidth() < 1) {
        assert(false && "Boolean type doesn't match!");
        return false;
      }

      Int = llvm::APSInt(llvm::APInt(Int.getBitWidth(), parseBoolean(Value)),
                         Int.isUnsigned());
      return true;
    }

    llvm_unreachable("Unsupported sort to integer!");
  }

  bool getInterpretation(const SMTExprRef &Exp, llvm::APSInt &Int) override {
    btor::BoolectorNode *ast = toBoolectorExpr(*Exp).AST;

    const char *val = btor::boolector_bv_assignment(Context.Context, ast);
    // TODO: this thanks to boolector API that does not have function for
    // getting bit width from sort
    btor::BoolectorSort sort = btor::boolector_get_sort(Context.Context, ast);
    unsigned bit_width = btor::boolector_get_width(Context.Context, ast);
    SMTSortRef Sort_w =
        std::make_shared<BoolectorSort>(Context, sort, bit_width);

    bool res = toAPSInt(Sort_w, val, Int, true);
    btor::boolector_free_bv_assignment(Context.Context, val);

    return res;
  }

  bool getInterpretation(const SMTExprRef &Exp, llvm::APFloat &Float) override {
    assert(false && "Boolector error: floating-point types are not supported");
    return false;
  }

  void setAssumptions() const {
    for (auto ite = assertions->begin(); ite != assertions->end(); ++ite) {
      btor::boolector_assume(Context.Context, toBoolectorExpr(**ite).AST);
    }
  }

  Optional<bool> check() const override {
    setAssumptions();
    int res = btor::boolector_sat(Context.Context);

    if (res == btor::BOOLECTOR_SAT)
      return true;

    if (res == btor::BOOLECTOR_UNSAT)
      return false;

    return Optional<bool>();
  }

  void push() override {
    assert(false && "Boolector push not supported since using assumptions");
    // FIXME: push should be fixed with multidimensional assumption list...
    // TODO: check 1 as level is right
    return btor::boolector_push(Context.Context, 1);
  }

  void pop(unsigned NumStates = 1) override {
    assert(false && "Boolector pop not supported since using assumptions");
    // FIXME: pop should be fixed with multidimensional assumption list...
    // TODO: check 1 as level is right
    return btor::boolector_pop(Context.Context, NumStates);
  }

  /// Reset the solver and remove all constraints.
  void reset() override {
    assertions->clear();
    btor::boolector_reset_assumptions(Context.Context);
  }

  void print(raw_ostream &OS) const override {
    // TODO: Boolector has only a print function that writes on C file
    // descriptor
    return;
  }
}; // end class BoolectorSolver

class BoolectorConstraintManager
    : public SMTConstraintManager<ConstraintBoolector, BoolectorExpr> {
  SMTSolverRef Solver = CreateBoolectorSolver();

public:
  BoolectorConstraintManager(SubEngine *SE, SValBuilder &SB)
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

    // Complex types are not modeled
    if (Ty->isFloatingType() || Ty->isRealFloatingType() ||
        Ty->isFloat16Type() || Ty->isFloat128Type())
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
}; // end class BoolectorConstraintManager

} // end anonymous namespace

#endif

SMTSolverRef clang::ento::CreateBoolectorSolver() {
#if CLANG_ANALYZER_WITH_BOOLECTOR
  return llvm::make_unique<BoolectorSolver>();
#else
  llvm::report_fatal_error(
      "Clang was not compiled with Boolector support, rebuild "
      "with -DCLANG_ANALYZER_ENABLE_BOOLECTOR_SOLVER=ON",
      false);
  return nullptr;
#endif
}

std::unique_ptr<ConstraintManager>
ento::CreateBoolectorConstraintManager(ProgramStateManager &StMgr,
                                       SubEngine *Eng) {
#if CLANG_ANALYZER_WITH_BOOLECTOR
  return llvm::make_unique<BoolectorConstraintManager>(Eng,
                                                       StMgr.getSValBuilder());
#else
  llvm::report_fatal_error(
      "Clang was not compiled with Boolector support, rebuild "
      "with -DCLANG_ANALYZER_ENABLE_BOOLECTOR_SOLVER=ON",
      false);
  return nullptr;
#endif
}
