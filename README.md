# SMT-LIB to Prolog
## An SMT-LIB parser in Prolog

SMT-LIB is an international initiative aimed at facilitating research and development in SMT. Specifically, Version 2.0 defines:
- a language for writing terms and formulas in a sorted (i.e., typed) version of first-order logic;
- a language for specifying background theories and fixing a standard vocabulary of sort, function, and predicate symbols for them;
- a language for specifying logics, suitably restricted classes of formulas to be checked for satisfiability with respect to a specific background theory;
- a command language for interacting with SMT solvers via a textual interface that allows asserting and retracting formulas, querying about their satisfiability, examining their models or their unsatisfiability proofs, and so on.

## Installation

### SWI-Prolog
```pl
?- pack_install(smtlib).
```

## Usage

```pl
:- use_module(smtlib).
```

- **smtlib_read_script/2** - reads SMT-LIB script from file.
- **smtlib_parse_script/2** - parses SMT-LIB script from chars.
- **smtlib_read_expression/2** - reads SMT-LIB expression from file.
- **smtlib_parse_expression/2** - parses SMT-LIB expression from chars.

### Read SMT-LIB scripts

```pl
?- smtlib_read_script('../sample/script/figure-3.4.smt', X).
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
  [reserved(pop),numeral(1)],
  [reserved(push),numeral(1)],
  [reserved(check-sat)],
  [reserved(exit)]
].
```
