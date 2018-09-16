//== YicesConstraintManager.cpp --------------------------------*- C++ -*--==//
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

#if CLANG_ANALYZER_WITH_YICES

#include <yices.h>

#include <sstream>

namespace {

// FIXME: use something more llvm-style for stringstreams
// Error reporting functions...
static void print_terms(std::ostream &fmt) {}

template <typename Term, typename... Terms>
void print_terms(std::ostream &fmt, const Term first, const Terms &... terms) {
  char *term = nullptr;
  // FIXME: check if really different since probably are just alias for integers
  if (std::is_same<Term, term_t>::value) {
    term = yices_term_to_string((term_t)first, 160, 80, 0);
  } else if (std::is_same<Term, type_t>::value) {
    term = yices_type_to_string((type_t)first, 160, 80, 0);
  }
  fmt << first << ":" << term << "\n";
  yices_free_string(term);
  print_terms(fmt, terms...);
}
template <typename... Terms>
inline void YicesReportError(const Terms &... terms) {
  char *error_str = yices_error_string();
  std::string error(error_str);
  yices_free_string(error_str);
  std::stringstream fmt;
  print_terms(fmt, terms...);
  llvm::report_fatal_error("Yices error: " + llvm::Twine(error) +
                           llvm::Twine(" at ") + llvm::Twine(fmt.str()));
}

// Function used to report errors on terms construction (error if res == 0)
template <typename... Terms>
inline void YicesCheckTermError(term_t res, const Terms &... terms) {
  if (res != NULL_TERM && res != NULL_TYPE) {
    return;
  }
  YicesReportError(terms...);
}

// Function used to report errors on other functions(error if res == -1)
template <typename... Terms>
inline void YicesCheckError(int res, const Terms &... terms) {
  if (res >= 0) {
    return;
  }
  YicesReportError(terms...);
}

/// Configuration class for Yices
class YicesConfig {
  friend class YicesContext;

  ctx_config_t *Config = nullptr;

public:
  YicesConfig() : Config(yices_new_config()) {
    int res_code;
    res_code = yices_default_config_for_logic(Config, "QF_BV");
    res_code =
        res_code <= 0 ? res_code : yices_set_config(Config, "mode", "one-shot");
    res_code = res_code <= 0 ? res_code
                             : yices_set_config(Config, "solver-type", "dpllt");
    res_code = res_code <= 0 ? res_code
                             : yices_set_config(Config, "uf-solver", "none");
    res_code = res_code <= 0 ? res_code
                             : yices_set_config(Config, "bv-solver", "default");
    res_code = res_code <= 0 ? res_code
                             : yices_set_config(Config, "array-solver", "none");
    res_code = res_code <= 0 ? res_code
                             : yices_set_config(Config, "arith-solver", "none");
    YicesCheckError(res_code);
  }

  ~YicesConfig() { yices_free_config(Config); }
}; // end class YicesConfig

/// Wrapper for Yices context
class YicesContext {
  void ConfigContext() {
    int res_code;
    res_code = yices_context_enable_option(Context, "var-elim");
    res_code = res_code <= 0 ? res_code
                             : yices_context_enable_option(Context, "flatten");
    res_code = res_code <= 0 ? res_code
                             : yices_context_enable_option(Context, "learn-eq");

    //        : whether to eliminate term if-then-else or keep them as terms
    res_code = res_code <= 0
                   ? res_code
                   : yices_context_disable_option(Context, "keep-ite");

    res_code = res_code <= 0
                   ? res_code
                   : yices_context_disable_option(Context, "arith-elim");
    res_code = res_code <= 0
                   ? res_code
                   : yices_context_disable_option(Context, "bvarith-elim");
    res_code =
        res_code <= 0
            ? res_code
            : yices_context_disable_option(Context, "eager-arith-lemmas");
    res_code = res_code <= 0
                   ? res_code
                   : yices_context_disable_option(Context, "break-symmetries");
    res_code = res_code <= 0
                   ? res_code
                   : yices_context_disable_option(Context, "assert-ite-bounds");

    YicesCheckError(res_code);
  }

public:
  context_t *Context;

  YicesContext() {
    yices_init();
    Context = yices_new_context(YicesConfig().Config);
    ConfigContext();
  }

  virtual ~YicesContext() {
    yices_free_context(Context);
    yices_reset();
    Context = nullptr;
  }
}; // end class YicesContext

/// Wrapper for Yices Sort
class YicesSort : public SMTSort {
  friend class YicesSolver;

  YicesContext &Context;

  type_t Sort;

public:
  /// Default constructor, mainly used by make_shared
  YicesSort(YicesContext &C, type_t ZS) : SMTSort(), Context(C), Sort(ZS) {}

  /// Override implicit copy constructor for correct reference counting.
  YicesSort(const YicesSort &Copy)
      : SMTSort(), Context(Copy.Context), Sort(Copy.Sort) {}

  /// Provide move constructor
  YicesSort(YicesSort &&Move)
      : SMTSort(), Context(Move.Context), Sort(NULL_TYPE) {
    // TODO: Weird...
    *this = std::move(Move);
  }

  /// Provide move assignment constructor
  YicesSort &operator=(YicesSort &&Move) {
    if (this != &Move) {
      Sort = Move.Sort;
      Move.Sort = NULL_TYPE;
    }
    return *this;
  }

  ~YicesSort() {}

  bool isBitvectorSortImpl() const override {
    return yices_type_is_bitvector(Sort) > 0;
  }

  bool isFloatSortImpl() const override {
    // Yices does not support floating point
    return false;
  }

  bool isBooleanSortImpl() const override {
    return yices_type_is_bool(Sort) > 0;
  }

  unsigned getBitvectorSortSizeImpl() const override {
    return yices_bvtype_size(Sort);
  }

  unsigned getFloatSortSizeImpl() const override {
    assert(false && "Yices error: floating-point types are not supported");
    return 0;
  }

  bool equal_to(SMTSort const &Other) const override {
    // yices does not provide equality function for types,
    // but subtipe relations, so x == y <==> (x <= y /\ y <= x)

    type_t x = Sort;
    type_t y = static_cast<const YicesSort &>(Other).Sort;

    return yices_test_subtype(x, y) && yices_test_subtype(y, x);
  }

  YicesSort &operator=(const YicesSort &Move) {
    Sort = Move.Sort;
    return *this;
  }

  void print(raw_ostream &OS) const override {
    char *ty_str = yices_type_to_string(Sort, 160, 80, 0);
    OS << ty_str;
    yices_free_string(ty_str);
  }
}; // end class YicesSort

static const YicesSort &toYicesSort(const SMTSort &S) {
  return static_cast<const YicesSort &>(S);
}

class YicesExpr : public SMTExpr {
  friend class YicesSolver;

  YicesContext &Context;

  term_t AST;

public:
  YicesExpr(YicesContext &C, term_t ZA) : SMTExpr(), Context(C), AST(ZA) {}

  /// Override implicit copy constructor for correct reference counting.
  YicesExpr(const YicesExpr &Copy)
      : SMTExpr(), Context(Copy.Context), AST(Copy.AST) {}

  /// Provide move constructor
  YicesExpr(YicesExpr &&Move)
      : SMTExpr(), Context(Move.Context), AST(NULL_TERM) {
    // TODO: WEIRD!
    *this = std::move(Move);
  }

  /// Provide move assignment constructor
  YicesExpr &operator=(YicesExpr &&Move) {
    if (this != &Move) {
      AST = Move.AST;
      Move.AST = NULL_TERM;
    }
    return *this;
  }

  ~YicesExpr() {}

  void Profile(llvm::FoldingSetNodeID &ID) const override {
    ID.AddInteger((unsigned long long int)AST);
  }

  /// Comparison of AST equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override {
    assert(YicesSort(Context, yices_type_of_term(AST))
               .equal_to(YicesSort(
                   Context, yices_type_of_term(
                                static_cast<const YicesExpr &>(Other).AST))) &&
           "AST's must have the same sort");
    return AST == static_cast<const YicesExpr &>(Other).AST;
  }

  /// Override implicit move constructor for correct reference counting.
  YicesExpr &operator=(const YicesExpr &Move) {
    AST = Move.AST;
    return *this;
  }

  void print(raw_ostream &OS) const override {
    char *term_str = yices_term_to_string(AST, 160, 80, 0);
    OS << term_str;
    yices_free_string(term_str);
  }
}; // end class YicesExpr

static const YicesExpr &toYicesExpr(const SMTExpr &E) {
  return static_cast<const YicesExpr &>(E);
}
} // end anonymous namespace

typedef llvm::ImmutableSet<std::pair<SymbolRef, YicesExpr>> ConstraintYicesTy;
REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstraintYices, ConstraintYicesTy)

namespace {

class YicesSolver : public SMTSolver {
  std::unique_ptr<std::list<SMTExprRef>> assertions =
      std::unique_ptr<std::list<SMTExprRef>>(new std::list<SMTExprRef>());

  std::map<std::string, term_t> symtable;
  friend class YicesConstraintManager;

  YicesContext Context;

public:
  YicesSolver() : SMTSolver() {}

  /// Override implicit copy constructor for correct reference counting.
  YicesSolver(const YicesSolver &Copy) : SMTSolver(), Context(Copy.Context) {}

  /// Provide move constructor
  YicesSolver(YicesSolver &&Move) : SMTSolver(), Context(Move.Context) {
    *this = std::move(Move);
  }

  /// Provide move assignment constructor
  YicesSolver &operator=(YicesSolver &&Move) {
    if (this != &Move) {
      this->Context = std::move(Move.Context);
    }
    return *this;
  }

  ~YicesSolver() {}

  void addConstraint(const SMTExprRef &Exp) const override {
    assertions->push_back(Exp);
    int res = yices_assert_formula(Context.Context, toYicesExpr(*Exp).AST);
    YicesCheckError(res, toYicesExpr(*Exp).AST);
  }

  SMTSortRef getBoolSort() override {
    type_t res = yices_bool_type();
    YicesCheckTermError(res);
    return std::make_shared<YicesSort>(Context, res);
  }

  SMTSortRef getBitvectorSort(unsigned BitWidth) override {
    type_t res = yices_bv_type(BitWidth);
    YicesCheckTermError(res);
    return std::make_shared<YicesSort>(Context, res);
  }

  SMTSortRef getSort(const SMTExprRef &Exp) override {
    type_t res = yices_type_of_term(toYicesExpr(*Exp).AST);
    YicesCheckTermError(res);
    return std::make_shared<YicesSort>(Context, res);
  }

  SMTSortRef getFloat16Sort() override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTSortRef getFloat32Sort() override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTSortRef getFloat64Sort() override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTSortRef getFloat128Sort() override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef newExprRef(const SMTExpr &E) const override {
    return std::make_shared<YicesExpr>(toYicesExpr(E));
  }

  SMTExprRef mkBVNeg(const SMTExprRef &Exp) override {
    term_t res = yices_neg(toYicesExpr(*Exp).AST);
    YicesCheckTermError(res, toYicesExpr(*Exp).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVNot(const SMTExprRef &Exp) override {
    term_t res = yices_bvnot(toYicesExpr(*Exp).AST);
    YicesCheckTermError(res, toYicesExpr(*Exp).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkNot(const SMTExprRef &Exp) override {
    term_t res = yices_not(toYicesExpr(*Exp).AST);
    YicesCheckTermError(res, toYicesExpr(*Exp).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvadd(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvsub(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvmul(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvsrem(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvrem(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvsdiv(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvdiv(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvshl(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvashr(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvlshr(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvxor2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvor2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvand2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvlt_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvslt_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvgt_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvsgt_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvle_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvsle_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvge_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvsge_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_and2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_or2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    // TODO: check since there are 2 equality: bveq_atom and eq (eq should work
    // for both)
    term_t res = yices_eq(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkFPNeg(const SMTExprRef &Exp) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                   const SMTExprRef &F) override {
    term_t res = yices_ite(toYicesExpr(*Cond).AST, toYicesExpr(*T).AST,
                           toYicesExpr(*F).AST);
    YicesCheckTermError(res, toYicesExpr(*Cond).AST, toYicesExpr(*T).AST,
                        toYicesExpr(*F).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVSignExt(unsigned i, const SMTExprRef &Exp) override {
    term_t res = yices_sign_extend(toYicesExpr(*Exp).AST, i);
    YicesCheckTermError(res, toYicesExpr(*Exp).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVZeroExt(unsigned i, const SMTExprRef &Exp) override {
    term_t res = yices_zero_extend(toYicesExpr(*Exp).AST, i);
    YicesCheckTermError(res, toYicesExpr(*Exp).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                         const SMTExprRef &Exp) override {
    // TODO: check indexes order
    term_t res = yices_bvextract(toYicesExpr(*Exp).AST, Low, High);
    YicesCheckTermError(res, toYicesExpr(*Exp).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkBVConcat(const SMTExprRef &LHS, const SMTExprRef &RHS) override {
    term_t res = yices_bvconcat2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    YicesCheckTermError(res, toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST);
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPtoSBV(const SMTExprRef &From, const SMTSortRef &To) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkFPtoUBV(const SMTExprRef &From, const SMTSortRef &To) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkSBVtoFP(const SMTExprRef &From, unsigned ToWidth) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkUBVtoFP(const SMTExprRef &From, unsigned ToWidth) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkBoolean(const bool b) override {
    return newExprRef(YicesExpr(Context, b ? yices_true() : yices_false()));
  }

  SMTExprRef mkBitvector(const llvm::APSInt Int, unsigned BitWidth) override {
    assert(BitWidth >= Int.getBitWidth() &&
           "Yices conversion error: not enough bits");
    llvm::APSInt extended = Int;
    if (Int.getBitWidth() < BitWidth) {
      // FIXME: check is legitimate to do the extension
      extended = Int.extend(BitWidth);
    }
    char *bit_str = new char[BitWidth + 1];
    bit_str[BitWidth] = 0;

    for (unsigned i = 0; i < BitWidth; ++i) {
      bit_str[BitWidth - 1 - i] = extended[i] ? '1' : '0';
    }

    term_t res = yices_parse_bvbin(bit_str);
    YicesCheckTermError(res);
    delete[] bit_str;
    return newExprRef(YicesExpr(Context, res));
  }

  SMTExprRef mkFloat(const llvm::APFloat Float) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef mkSymbol(const char *Name, SMTSortRef Sort) override {
    std::string sname(Name);
    if (symtable.find(sname) == symtable.end()) {
      term_t sym = yices_new_uninterpreted_term(toYicesSort(*Sort).Sort);
      yices_set_term_name(sym, Name);
      YicesCheckTermError(sym);
      symtable[sname] = sym;
    }
    term_t res = symtable[sname];
    return newExprRef(YicesExpr(Context, res));
  }

  llvm::APSInt getBitvector(const SMTExprRef &Exp, unsigned BitWidth,
                            bool isUnsigned) override {
    assert(yices_term_is_bitvector(toYicesExpr(*Exp).AST) &&
           "Can get value only of a bitvector");
    // TODO: check if const
    // TODO: there is a function to get its value but works only for int32 or
    // int64

    char *val = yices_term_to_string(toYicesExpr(*Exp).AST, 160, 80, 0);
    // TODO: check if val starts with 0b (as usual in yices)

    llvm::APSInt res(llvm::APInt(BitWidth, val + 2, 2), isUnsigned);

    yices_free_string(val);

    return res;
  }

  bool getBoolean(const SMTExprRef &Exp) override {
    assert(yices_term_is_bool(toYicesExpr(*Exp).AST) &&
           "Expression does not have Boolean type");
    // TODO: check if const

    int value;
    int res = yices_bool_const_value(toYicesExpr(*Exp).AST, &value);

    if (res < 0) {
      char *error_str = yices_error_string();
      std::string error(error_str);
      yices_free_string(error_str);
      llvm::report_fatal_error("Yices error: " + llvm::Twine(error));
    }

    return (bool)value;
  }

  SMTExprRef getFloatRoundingMode() override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef fromBoolean(const bool Bool) override { return mkBoolean(Bool); }

  SMTExprRef fromAPFloat(const llvm::APFloat &Float) override {
    assert(false && "Yices error: floating-point types are not supported");
    return nullptr;
  }

  SMTExprRef fromAPSInt(const llvm::APSInt &Int) override {
    return mkBitvector(Int, Int.getBitWidth());
  }

  SMTExprRef fromInt(const char *Int, uint64_t BitWidth) override {
    // TODO: consider using toAPSInt with useSemantics = false...
    // TODO: check isUnsigned
    llvm::APSInt num = llvm::APSInt(llvm::APInt(BitWidth, Int, 10), false);
    return mkBitvector(num, BitWidth);
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
        Int = llvm::APSInt(llvm::APInt(Int.getBitWidth(), Value, 2),
                           Int.isUnsigned());
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

      Int = llvm::APSInt(llvm::APInt(Int.getBitWidth(), Value, 2),
                         Int.isUnsigned());
      return true;
    }

    llvm_unreachable("Unsupported sort to integer!");
  }

  bool getInterpretation(const SMTExprRef &Exp, llvm::APSInt &Int) override {
    YicesExpr yexp = toYicesExpr(*Exp);
    model_t *model = yices_get_model(yexp.Context.Context, true);

    int elem_size = 0;
    if (yices_term_is_bool(yexp.AST)) {
      elem_size = 1;
    } else {
      elem_size = yices_term_bitsize(yexp.AST);
    }
    char *encoding = new char[elem_size + 1];
    for (int i = 0; i < elem_size + 1; ++i) {
      encoding[i] = 0;
    }

    if (yices_term_is_bool(yexp.AST)) {
      int bool_val;
      int got_res = yices_get_bool_value(model, yexp.AST, &bool_val);
      YicesCheckError(got_res, yexp.AST);
      encoding[0] = bool_val ? '1' : '0';
    } else if (yices_term_is_bitvector(yexp.AST)) {
      int *int_enc = new int[elem_size];
      int got_res = yices_get_bv_value(model, yexp.AST, int_enc);
      YicesCheckError(got_res, yexp.AST);
      for (int i = 0; i < elem_size; ++i) {
        encoding[elem_size - 1 - i] = int_enc[i] ? '1' : '0';
      }
      delete[] int_enc;
    }

    SMTSortRef Sort = getSort(Exp);

    bool success = toAPSInt(Sort, encoding, Int, true);
    delete[] encoding;
    return success;
  }

  bool getInterpretation(const SMTExprRef &Exp, llvm::APFloat &Float) override {
    assert(false && "Yices error: floating-point types are not supported");
    return false;
  }

  Optional<bool> check() const override {
    int res = yices_check_context(Context.Context, nullptr);
    if (res == STATUS_SAT)
      return true;

    if (res == STATUS_UNSAT)
      return false;

    return Optional<bool>();
  }

  void push() override { yices_push(Context.Context); }

  void pop(unsigned NumStates = 1) override {
    for (unsigned i = 0; i < NumStates; ++i) {
      yices_pop(Context.Context);
    }
  }

  /// Reset the solver and remove all constraints.
  void reset() override {
    assertions->clear();
    yices_reset_context(Context.Context);
  }

  void print(raw_ostream &OS) const override {
    // TODO: Cannot print a solver nor context to a non C file descriptor
    //            assert(false && "Yices error: unsupported context print to a
    //            non C file descriptor");
    for (auto ite = assertions->begin(); ite != assertions->end(); ++ite) {
      (*ite)->print(OS);
    }
  }
}; // end class YicesSolver

class YicesConstraintManager
    : public SMTConstraintManager<ConstraintYices, YicesExpr> {
  SMTSolverRef Solver = CreateYicesSolver();

public:
  YicesConstraintManager(SubEngine *SE, SValBuilder &SB)
      : SMTConstraintManager(SE, SB, Solver) {}

  bool canReasonAbout(SVal X) const override {
    // FIXME: fix the floating point stuff isReal...
    const TargetInfo &TI = getBasicVals().getContext().getTargetInfo();

    Optional<nonloc::SymbolVal> SymVal = X.getAs<nonloc::SymbolVal>();
    if (!SymVal)
      return true;

    const SymExpr *Sym = SymVal->getSymbol();
    QualType Ty = Sym->getType();

    // Complex types are not modeled
    if (Ty->isComplexType() || Ty->isComplexIntegerType())
      return false;

    // Float and real types are not modeled
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
}; // end class YicesConstraintManager

} // end anonymous namespace

#endif

SMTSolverRef clang::ento::CreateYicesSolver() {
#if CLANG_ANALYZER_WITH_YICES
  return llvm::make_unique<YicesSolver>();
#else
  llvm::report_llvm::report_fatal_error(
      "Clang was not compiled with Yices support, rebuild "
      "with -DCLANG_ANALYZER_ENABLE_YICES_SOLVER=ON",
      false);
  return nullptr;
#endif
}

std::unique_ptr<ConstraintManager>
ento::CreateYicesConstraintManager(ProgramStateManager &StMgr, SubEngine *Eng) {
#if CLANG_ANALYZER_WITH_YICES
  return llvm::make_unique<YicesConstraintManager>(Eng, StMgr.getSValBuilder());
#else
  llvm::report_llvm::report_fatal_error(
      "Clang was not compiled with Yices support, rebuild "
      "with -DCLANG_ANALYZER_ENABLE_YICES_SOLVER=ON",
      false);
  return nullptr;
#endif
}
