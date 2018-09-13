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

#if CLANG_ANALYZER_WITH_MATHSAT

#include <mathsat.h>

namespace {

/// Configuration class for MathSAT
class MathSATConfig {
  friend class MathSATContext;

  msat_config Config = msat_create_config();

public:
  MathSATConfig() {
    // Enable model finding
    msat_set_option(Config, "model_generation", "true");
    msat_set_option(Config, "preprocessor.toplevel_propagation", "true");
    msat_set_option(Config, "preprocessor.simplification", "1");
    msat_set_option(Config, "dpll.branching_random_frequency", "0.01");
    msat_set_option(Config, "dpll.branching_random_invalidate_phase_cache",
                    "true");
    msat_set_option(Config, "dpll.restart_strategy", "3");
    msat_set_option(Config, "dpll.glucose_var_activity", "true");
    msat_set_option(Config, "dpll.glucose_learnt_minimization", "true");
    msat_set_option(Config, "dpll.preprocessor.mode", "1");
    msat_set_option(Config, "theory.bv.eager", "true");
    msat_set_option(Config, "theory.bv.bit_blast_mode", "2");
    msat_set_option(Config, "theory.bv.delay_propagated_eqs", "true");
    msat_set_option(Config, "theory.la.enabled", "false");
    msat_set_option(Config, "theory.fp.mode", "1");
    msat_set_option(Config, "theory.fp.bit_blast_mode", "2");
    msat_set_option(Config, "theory.fp.bv_combination_enabled", "true");
    msat_set_option(Config, "theory.arr.enable_witness", "true");
  }

  ~MathSATConfig() { msat_destroy_config(Config); }
}; // end class MathSATConfig

/// Wrapper for MathSAT context
class MathSATContext {
public:
  msat_env Context;

  MathSATContext() { Context = msat_create_env(MathSATConfig().Config); }

  virtual ~MathSATContext() { msat_destroy_env(Context); }
}; // end class MathSATContext

/// Wrapper for MathSAT Sort
class MathSATSort : public SMTSort {
  friend class MathSATSolver;

  MathSATContext &Context;

  msat_type Sort;

public:
  /// Default constructor, mainly used by make_shared
  MathSATSort(MathSATContext &C, msat_type S)
      : SMTSort(), Context(C), Sort(S) {}

  ~MathSATSort() = default;

  bool isBitvectorSortImpl() const override {
    std::size_t Width;
    return msat_is_bv_type(Context.Context, Sort, &Width);
  }

  bool isFloatSortImpl() const override {
    std::size_t ExpWidth, MantWidth;
    return msat_is_fp_type(Context.Context, Sort, &ExpWidth, &MantWidth);
  }

  bool isBooleanSortImpl() const override {
    return msat_is_bool_type(Context.Context, Sort);
  }

  unsigned getBitvectorSortSizeImpl() const override {
    std::size_t Width;
    msat_is_bv_type(Context.Context, Sort, &Width);
    return Width;
  }

  unsigned getFloatSortSizeImpl() const override {
    std::size_t ExpWidth, MantWidth;
    msat_is_fp_type(Context.Context, Sort, &ExpWidth, &MantWidth);
    return ExpWidth + MantWidth;
  }

  bool equal_to(SMTSort const &Other) const override {
    return msat_type_equals(Sort, static_cast<const MathSATSort &>(Other).Sort);
  }

  void print(raw_ostream &OS) const override {
    // TODO
  }
}; // end class MathSATSort

static const MathSATSort &toMathSATSort(const SMTSort &S) {
  return static_cast<const MathSATSort &>(S);
}

class MathSATExpr : public SMTExpr {
  friend class MathSATSolver;

  MathSATContext &Context;

  msat_term AST;

public:
  MathSATExpr(MathSATContext &C, msat_term ZA)
      : SMTExpr(), Context(C), AST(ZA) {}

  void Profile(llvm::FoldingSetNodeID &ID) const override {
    ID.AddInteger(msat_term_id(AST));
  }

  /// Comparison of AST equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override {
    assert(msat_type_equals(msat_term_get_type(AST),
                            msat_term_get_type(
                                static_cast<const MathSATExpr &>(Other).AST)) &&
           "AST's must have the same sort");
    return msat_term_id(AST) ==
           msat_term_id(static_cast<const MathSATExpr &>(Other).AST);
  }

  void print(raw_ostream &OS) const override {
    OS << msat_to_smtlib2(Context.Context, AST);
  }
}; // end class MathSATExpr

static const MathSATExpr &toMathSATExpr(const SMTExpr &E) {
  return static_cast<const MathSATExpr &>(E);
}

class MathSATModel {
  friend class MathSATSolver;

  MathSATContext &Context;

  msat_model Model;

public:
  MathSATModel(MathSATContext &C, msat_model ZM) : Context(C), Model(ZM) {}

  ~MathSATModel() = default;

  void print(raw_ostream &OS) const {
    // TODO
  }

  LLVM_DUMP_METHOD void dump() const { print(llvm::errs()); }
}; // end class MathSATModel

/// Get the corresponding IEEE floating-point type for a given bitwidth.
static const llvm::fltSemantics &getFloatSemantics(unsigned BitWidth) {
  switch (BitWidth) {
  default:
    llvm_unreachable("Unsupported floating-point semantics!");
    break;
  case 16:
    return llvm::APFloat::IEEEhalf();
  case 32:
    return llvm::APFloat::IEEEsingle();
  case 64:
    return llvm::APFloat::IEEEdouble();
  case 128:
    return llvm::APFloat::IEEEquad();
  }
}

// Determine whether two float semantics are equivalent
static bool areEquivalent(const llvm::fltSemantics &LHS,
                          const llvm::fltSemantics &RHS) {
  return (llvm::APFloat::semanticsPrecision(LHS) ==
          llvm::APFloat::semanticsPrecision(RHS)) &&
         (llvm::APFloat::semanticsMinExponent(LHS) ==
          llvm::APFloat::semanticsMinExponent(RHS)) &&
         (llvm::APFloat::semanticsMaxExponent(LHS) ==
          llvm::APFloat::semanticsMaxExponent(RHS)) &&
         (llvm::APFloat::semanticsSizeInBits(LHS) ==
          llvm::APFloat::semanticsSizeInBits(RHS));
}

} // end anonymous namespace

typedef llvm::ImmutableSet<std::pair<SymbolRef, MathSATExpr>>
    ConstraintMathSATTy;
REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstraintMathSAT, ConstraintMathSATTy)

namespace {

class MathSATSolver : public SMTSolver {
  friend class MathSATConstraintManager;

  MathSATContext Context;

public:
  MathSATSolver() = default;
  ~MathSATSolver() = default;

  void addConstraint(const SMTExprRef &Exp) const override {
    msat_assert_formula(Context.Context, toMathSATExpr(*Exp).AST);
  }

  SMTSortRef getBoolSort() override {
    return std::make_shared<MathSATSort>(Context,
                                         msat_get_bool_type(Context.Context));
  }

  SMTSortRef getBitvectorSort(unsigned BitWidth) override {
    return std::make_shared<MathSATSort>(
        Context, msat_get_bv_type(Context.Context, BitWidth));
  }

  SMTSortRef getSort(const SMTExprRef &Exp) override {
    return std::make_shared<MathSATSort>(
        Context, msat_term_get_type(toMathSATExpr(*Exp).AST));
  }

  SMTSortRef getFloat16Sort() override {
    return std::make_shared<MathSATSort>(
        Context, msat_get_fp_type(Context.Context, 5, 10));
  }

  SMTSortRef getFloat32Sort() override {
    return std::make_shared<MathSATSort>(
        Context, msat_get_fp_type(Context.Context, 8, 23));
  }

  SMTSortRef getFloat64Sort() override {
    return std::make_shared<MathSATSort>(
        Context, msat_get_fp_type(Context.Context, 11, 52));
  }

  SMTSortRef getFloat128Sort() override {
    return std::make_shared<MathSATSort>(
        Context, msat_get_fp_type(Context.Context, 15, 112));
  }

  SMTExprRef newExprRef(const SMTExpr &E) const override {
    if (MSAT_ERROR_TERM(toMathSATExpr(E).AST)) {
      llvm::errs() << "Error creating SMT\n";
      llvm::errs() << "Error text: " << msat_last_error_message(Context.Context)
                   << "\n";
      abort();
    }
    return std::make_shared<MathSATExpr>(toMathSATExpr(E));
  }

  SMTExprRef mkBVNeg(const SMTExprRef &Exp) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_neg(Context.Context, toMathSATExpr(*Exp).AST)));
  }

  SMTExprRef mkBVNot(const SMTExprRef &Exp) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_not(Context.Context, toMathSATExpr(*Exp).AST)));
  }

  SMTExprRef mkNot(const SMTExprRef &Exp) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_not(Context.Context, toMathSATExpr(*Exp).AST)));
  }

  SMTExprRef mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_plus(Context.Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_minus(Context.Context, toMathSATExpr(*LHS).AST,
                                    toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_times(Context.Context, toMathSATExpr(*LHS).AST,
                                    toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_srem(Context.Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_urem(Context.Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_sdiv(Context.Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_udiv(Context.Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_lshl(Context.Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_ashr(Context.Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_lshr(Context.Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_xor(Context.Context, toMathSATExpr(*LHS).AST,
                                  toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_or(Context.Context, toMathSATExpr(*LHS).AST,
                                 toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_and(Context.Context, toMathSATExpr(*LHS).AST,
                                  toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_ult(Context.Context, toMathSATExpr(*LHS).AST,
                                  toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_slt(Context.Context, toMathSATExpr(*LHS).AST,
                                  toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return mkNot(mkBVUle(LHS, RHS));
  }

  SMTExprRef mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return mkNot(mkBVSle(LHS, RHS));
  }

  SMTExprRef mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_uleq(Context.Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_sleq(Context.Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return mkNot(mkBVUlt(LHS, RHS));
  }

  SMTExprRef mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return mkNot(mkBVSlt(LHS, RHS));
  }

  SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_and(Context.Context, toMathSATExpr(*LHS).AST,
                               toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_or(Context.Context, toMathSATExpr(*LHS).AST,
                              toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_eq(Context.Context, toMathSATExpr(*LHS).AST,
                              toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkFPNeg(const SMTExprRef &Exp) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_neg(Context.Context, toMathSATExpr(*Exp).AST)));
  }

  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_isinf(Context.Context, toMathSATExpr(*Exp).AST)));
  }

  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_isnan(Context.Context, toMathSATExpr(*Exp).AST)));
  }

  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) override {
    return newExprRef(
        MathSATExpr(Context, msat_make_fp_isnormal(Context.Context,
                                                   toMathSATExpr(*Exp).AST)));
  }

  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) override {
    return newExprRef(
        MathSATExpr(Context, msat_make_fp_iszero(Context.Context,
                                                 toMathSATExpr(*Exp).AST)));
  }

  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_times(Context.Context, toMathSATExpr(*LHS).AST,
                                    toMathSATExpr(*RHS).AST,
                                    toMathSATExpr(*RoundingMode).AST)));
  }

  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_div(Context.Context, toMathSATExpr(*LHS).AST,
                                  toMathSATExpr(*RHS).AST,
                                  toMathSATExpr(*RoundingMode).AST)));
  }

  SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "MathSAT does not support the fp.rem operator.");
    abort();
  }

  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_plus(Context.Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST,
                                   toMathSATExpr(*RoundingMode).AST)));
  }

  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_minus(Context.Context, toMathSATExpr(*LHS).AST,
                                    toMathSATExpr(*RHS).AST,
                                    toMathSATExpr(*RoundingMode).AST)));
  }

  SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_lt(Context.Context, toMathSATExpr(*LHS).AST,
                                 toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return mkFPLt(RHS, LHS);
  }

  SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_leq(Context.Context, toMathSATExpr(*LHS).AST,
                                  toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return mkNot(mkFPLt(LHS, RHS));
  }

  SMTExprRef mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_equal(Context.Context, toMathSATExpr(*LHS).AST,
                                    toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                   const SMTExprRef &F) override {
    if (getSort(T)->isBooleanSort())
      return mkOr(mkAnd(Cond, T), mkAnd(mkNot(Cond), F));

    return newExprRef(MathSATExpr(
        Context,
        msat_make_term_ite(Context.Context, toMathSATExpr(*Cond).AST,
                           toMathSATExpr(*T).AST, toMathSATExpr(*F).AST)));
  }

  SMTExprRef mkBVSignExt(unsigned i, const SMTExprRef &Exp) override {
    return newExprRef(
        MathSATExpr(Context, msat_make_bv_sext(Context.Context, i,
                                               toMathSATExpr(*Exp).AST)));
  }

  SMTExprRef mkBVZeroExt(unsigned i, const SMTExprRef &Exp) override {
    return newExprRef(
        MathSATExpr(Context, msat_make_bv_zext(Context.Context, i,
                                               toMathSATExpr(*Exp).AST)));
  }

  SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                         const SMTExprRef &Exp) override {
    return newExprRef(
        MathSATExpr(Context, msat_make_bv_extract(Context.Context, High, Low,
                                                  toMathSATExpr(*Exp).AST)));
  }

  SMTExprRef mkBVConcat(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    return newExprRef(MathSATExpr(
        Context, msat_make_bv_concat(Context.Context, toMathSATExpr(*LHS).AST,
                                     toMathSATExpr(*RHS).AST)));
  }

  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    std::size_t ExpWidth, MantWidth;
    msat_is_fp_type(Context.Context, toMathSATSort(*To).Sort, &ExpWidth,
                    &MantWidth);
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_cast(Context.Context, ExpWidth, MantWidth,
                                   toMathSATExpr(*RoundingMode).AST,
                                   toMathSATExpr(*From).AST)));
  }

  SMTExprRef mkFPtoSBV(const SMTExprRef &From, const SMTSortRef &To) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    std::size_t ExpWidth, MantWidth;
    msat_is_fp_type(Context.Context, toMathSATSort(*To).Sort, &ExpWidth,
                    &MantWidth);
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_from_sbv(Context.Context, ExpWidth, MantWidth,
                                       toMathSATExpr(*RoundingMode).AST,
                                       toMathSATExpr(*From).AST)));
  }

  SMTExprRef mkFPtoUBV(const SMTExprRef &From, const SMTSortRef &To) override {
    SMTExprRef RoundingMode = getFloatRoundingMode();
    std::size_t ExpWidth, MantWidth;
    msat_is_fp_type(Context.Context, toMathSATSort(*To).Sort, &ExpWidth,
                    &MantWidth);
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_from_ubv(Context.Context, ExpWidth, MantWidth,
                                       toMathSATExpr(*RoundingMode).AST,
                                       toMathSATExpr(*From).AST)));
  }

  SMTExprRef mkSBVtoFP(const SMTExprRef &From, unsigned ToWidth) override {
    // Conversion from float to integers always truncate, so we assume
    // the round mode to be toward zero
    SMTExprRef RoundingMode = newExprRef(
        MathSATExpr(Context, msat_make_fp_roundingmode_zero(Context.Context)));
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_to_bv(Context.Context, ToWidth,
                                    toMathSATExpr(*RoundingMode).AST,
                                    toMathSATExpr(*From).AST)));
  }

  SMTExprRef mkUBVtoFP(const SMTExprRef &From, unsigned ToWidth) override {
    // Conversion from float to integers always truncate, so we assume
    // the round mode to be toward zero
    SMTExprRef RoundingMode = newExprRef(
        MathSATExpr(Context, msat_make_fp_roundingmode_zero(Context.Context)));
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_to_bv(Context.Context, ToWidth,
                                    toMathSATExpr(*RoundingMode).AST,
                                    toMathSATExpr(*From).AST)));
  }

  SMTExprRef mkBoolean(const bool b) override {
    return newExprRef(
        MathSATExpr(Context, b ? msat_make_true(Context.Context)
                               : msat_make_false(Context.Context)));
  }

  SMTExprRef mkBitvector(const llvm::APSInt Int, unsigned BitWidth) override {
    std::string Str = std::to_string(Int.getZExtValue());
    return newExprRef(
        MathSATExpr(Context, msat_make_bv_number(Context.Context, Str.c_str(),
                                                 BitWidth, 10)));
  }

  SMTExprRef mkFloat(const llvm::APFloat Float) override {
    SMTSortRef Sort =
        getFloatSort(llvm::APFloat::semanticsSizeInBits(Float.getSemantics()));
    std::size_t ExpWidth, MantWidth;
    msat_is_fp_type(Context.Context, toMathSATSort(*Sort).Sort, &ExpWidth,
                    &MantWidth);

    llvm::APSInt Int = llvm::APSInt(Float.bitcastToAPInt(), false);
    SMTExprRef MathSATInt = mkBitvector(Int, Int.getBitWidth());

    return newExprRef(MathSATExpr(
        Context, msat_make_fp_from_ieeebv(Context.Context, ExpWidth, MantWidth,
                                          toMathSATExpr(*MathSATInt).AST)));
  }

  SMTExprRef mkSymbol(const char *Name, SMTSortRef Sort) override {
    // XXX - does 'd' leak?
    msat_decl d =
        msat_declare_function(Context.Context, Name, toMathSATSort(*Sort).Sort);

    return newExprRef(
        MathSATExpr(Context, msat_make_constant(Context.Context, d)));
  }

  llvm::APSInt getBitvector(const SMTExprRef &Exp, unsigned BitWidth,
                            bool isUnsigned) override {
    msat_term t =
        msat_get_model_value(Context.Context, toMathSATExpr(*Exp).AST);

    // GMP rational value object.
    mpq_t val;
    mpq_init(val);

    msat_term_to_number(Context.Context, t, val);
    msat_free(msat_term_repr(t));

    mpz_t num;
    mpz_init(num);
    mpz_set(num, mpq_numref(val));
    char *buffer = (char *)malloc(sizeof(char) * mpz_sizeinbase(num, 10) + 2);
    mpz_get_str(buffer, 10, num);

    return llvm::APSInt(llvm::APInt(BitWidth, buffer, 10));
  }

  bool getBoolean(const SMTExprRef &Exp) override {
    msat_term t =
        msat_get_model_value(Context.Context, toMathSATExpr(*Exp).AST);

    bool res;
    if (msat_term_is_true(Context.Context, t))
      res = true;
    else if (msat_term_is_false(Context.Context, t))
      res = false;
    else {
      llvm::errs() << "Boolean model value is neither true or false\n";
      abort();
    }

    msat_free(msat_term_repr(t));
    return res;
  }

  SMTExprRef getFloatRoundingMode() override {
    // TODO: Don't assume nearest ties to even rounding mode
    return newExprRef(MathSATExpr(
        Context, msat_make_fp_roundingmode_nearest_even(Context.Context)));
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
    assert(Sort->isFloatSort() && "Unsupported sort to floating-point!");

    llvm::APSInt Int(Sort->getFloatSortSize(), true);
    const llvm::fltSemantics &Semantics =
        getFloatSemantics(Sort->getFloatSortSize());
    SMTSortRef BVSort = getBitvectorSort(Sort->getFloatSortSize());
    if (!toAPSInt(BVSort, AST, Int, true)) {
      return false;
    }

    if (useSemantics && !areEquivalent(Float.getSemantics(), Semantics)) {
      assert(false && "Floating-point types don't match!");
      return false;
    }

    Float = llvm::APFloat(Semantics, Int);
    return true;
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
    SMTExprRef Assign = newExprRef(
        MathSATExpr(Context, msat_get_model_value(Context.Context,
                                                  toMathSATExpr(*Exp).AST)));
    SMTSortRef Sort = getSort(Assign);
    return toAPSInt(Sort, Assign, Int, true);
  }

  bool getInterpretation(const SMTExprRef &Exp, llvm::APFloat &Float) override {
    SMTExprRef Assign = newExprRef(
        MathSATExpr(Context, msat_get_model_value(Context.Context,
                                                  toMathSATExpr(*Exp).AST)));
    SMTSortRef Sort = getSort(Assign);
    return toAPFloat(Sort, Assign, Float, true);
  }

  Optional<bool> check() const override {
    msat_result r = msat_solve(Context.Context);
    if (r == MSAT_SAT)
      return true;

    if (r == MSAT_UNSAT)
      return false;

    return Optional<bool>();
  }

  void push() override { msat_push_backtrack_point(Context.Context); }

  void pop(unsigned NumStates = 1) override {
    assert(msat_num_backtrack_points(Context.Context) >= NumStates);
    while (NumStates--)
      msat_pop_backtrack_point(Context.Context);
  }

  /// Get a model from the solver. Caller should check the model is
  /// satisfiable.
  MathSATModel getModel() {
    return MathSATModel(Context, msat_get_model(Context.Context));
  }

  /// Reset the solver and remove all constraints.
  void reset() override { msat_reset_env(Context.Context); }

  void print(raw_ostream &OS) const override {
    size_t num_of_asserted;
    msat_term *asserted_formulas =
        msat_get_asserted_formulas(Context.Context, &num_of_asserted);

    for (unsigned i = 0; i < num_of_asserted; i++)
      OS << msat_to_smtlib2(Context.Context, asserted_formulas[i]) << "\n";

    msat_free(asserted_formulas);
  }
}; // end class MathSATSolver

class MathSATConstraintManager
    : public SMTConstraintManager<ConstraintMathSAT, MathSATExpr> {
  SMTSolverRef Solver = CreateMathSATSolver();

public:
  MathSATConstraintManager(SubEngine *SE, SValBuilder &SB)
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
}; // end class MathSATConstraintManager

} // end anonymous namespace

#endif

SMTSolverRef clang::ento::CreateMathSATSolver() {
#if CLANG_ANALYZER_WITH_MATHSAT
  return llvm::make_unique<MathSATSolver>();
#else
  llvm::report_fatal_error(
      "Clang was not compiled with MathSAT support, rebuild "
      "with -DCLANG_ANALYZER_ENABLE_MATHSAT_SOLVER=ON",
      false);
  return nullptr;
#endif
}

std::unique_ptr<ConstraintManager>
ento::CreateMathSATConstraintManager(ProgramStateManager &StMgr, SubEngine *Eng) {
#if CLANG_ANALYZER_WITH_MATHSAT
  return llvm::make_unique<MathSATConstraintManager>(Eng,
                                                     StMgr.getSValBuilder());
#else
  llvm::report_fatal_error(
      "Clang was not compiled with MathSAT support, rebuild "
      "with -DCLANG_ANALYZER_ENABLE_MATHSAT_SOLVER=ON",
      false);
  return nullptr;
#endif
}