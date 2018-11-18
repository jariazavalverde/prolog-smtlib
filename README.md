# SMT-LIB to Prolog
## An SMT-LIB parser in Prolog

SMT-LIB is an international initiative aimed at facilitating research and development in SMT. Specifically, Version 2.0 defines:
- a language for writing terms and formulas in a sorted (i.e., typed) version of first-order logic;
- a language for specifying background theories and fixing a standard vocabulary of sort, function, and predicate symbols for them;
- a language for specifying logics, suitably restricted classes of formulas to be checked for satisfiability with respect to a specific background theory;
- a command language for interacting with SMT solvers via a textual interface that allows asserting and retracting formulas, querying about their satisfiability, examining their models or their unsatisfiability proofs, and so on.

## Usage

### Read SMT-LIB scripts

```
?- smtlib_read_script('../sample/figure-3.4.smt', X).
X = [
  [reserved(set-logic),symbol(QF_LIA)],
  [reserved(declare-fun),symbol(w),[],symbol(Int)],
  [reserved(declare-fun),symbol(x),[],symbol(Int)],
  [reserved(declare-fun),symbol(y),[],symbol(Int)],
  [reserved(declare-fun),symbol(z),[],symbol(Int)],
  [reserved(assert),[symbol(>),symbol(x),symbol(y)]],
  [reserved(assert),[symbol(>),symbol(y),symbol(z)]],
  [reserved(set-option),[keyword(print-success),symbol(false)]],
  [reserved(push),numeral(1)],
  [reserved(assert),[symbol(>),symbol(z),symbol(x)]],
  [reserved(check-sat)],
  [reserved(get-info),keyword(all-statistics)],
  [reserved(pop),numeral(1)],[reserved(push),numeral(1)],
  [reserved(check-sat)],
  [reserved(exit)]
].
```
