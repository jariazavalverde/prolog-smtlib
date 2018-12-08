# SMT-LIB to Prolog
## An SMT-LIB parser in Prolog

SMT-LIB is an international initiative aimed at facilitating research and development in SMT. Specifically, Version 2.0 defines:
- a language for writing terms and formulas in a sorted (i.e., typed) version of first-order logic;
- a language for specifying background theories and fixing a standard vocabulary of sort, function, and predicate symbols for them;
- a language for specifying logics, suitably restricted classes of formulas to be checked for satisfiability with respect to a specific background theory;
- a command language for interacting with SMT solvers via a textual interface that allows asserting and retracting formulas, querying about their satisfiability, examining their models or their unsatisfiability proofs, and so on.

## Installation (SWI-Prolog)

```pl
?- pack_install(smtlib).
```

## Usage

```pl
:- use_module(library(smtlib)).
```

- **smtlib_read_script/2** - parses SMT-LIB script from file.
- **smtlib_read_theory/2** - parses SMT-LIB theory declaration from file.
- **smtlib_read_logic/2** - parses SMT-LIB logic declaration from file.
- **smtlib_read_expression/2** - parses SMT-LIB expression from file.
- **smtlib_parse_script/2** - parses SMT-LIB script from chars.
- **smtlib_parse_theory/2** - parses SMT-LIB theory declaration from chars.
- **smtlib_parse_logic/2** - parses SMT-LIB logic declaration from chars.
- **smtlib_parse_expression/2** - parses SMT-LIB expression from chars.
- **smtlib_write_to_stream/2** - writes SMT-LIB expression into stream.
- **smtlib_write_to_file/2** - writes SMT-LIB expression into file.

## Examples

#### Reading SMT-LIB scripts

```pl
?- smtlib_read_script('../sample/script/figure-3.4.smt', X).
X = list([
  [reserved('set-logic'),symbol('QF_LIA')],
  [reserved('declare-fun'),symbol(w),[],symbol('Int')],
  [reserved('declare-fun'),symbol(x),[],symbol('Int')],
  [reserved('declare-fun'),symbol(y),[],symbol('Int')],
  [reserved('declare-fun'),symbol(z),[],symbol('Int')],
  [reserved(assert),[symbol(>),symbol(x),symbol(y)]],
  [reserved(assert),[symbol(>),symbol(y),symbol(z)]],
  [reserved('set-option'),[keyword('print-success'),symbol(false)]],
  [reserved(push),numeral(1)],
  [reserved(assert),[symbol(>),symbol(z),symbol(x)]],
  [reserved('check-sat')],
  [reserved('get-info'),keyword('all-statistics')],
  [reserved(pop),numeral(1)],
  [reserved(push),numeral(1)],
  [reserved('check-sat')],
  [reserved(exit)]
]).
```

#### Reading SMT-LIB theory declarations

```pl
?- smtlib_read_theory('../sample/theory/core.smt', X).
X = list([
  symbol(theory),
  symbol('Core'),
  [keyword('smt-lib-version'),decimal(2.6)],
  [keyword('smt-lib-release'),string('2017-11-24')],
  [keyword('written-by'),string(...)],
  [keyword(date),string(...)],
  [keyword('last-updated'),string(...)],
  [keyword('update-history'),string(...)],
  [keyword(sorts),[
    [symbol('Bool'),numeral(0),[]]
  ]],
  [keyword(funs),[
    [symbol(true),symbol('Bool')],
    [symbol(false),symbol('Bool')],
    [symbol(not),symbol('Bool'),symbol('Bool')],
    [symbol(=>),symbol('Bool'),symbol('Bool'),symbol('Bool'),keyword('right-assoc')],
    [symbol(and),symbol('Bool'),symbol('Bool'),symbol('Bool'),keyword('left-assoc')],
    [symbol(or),symbol('Bool'),symbol('Bool'),symbol('Bool'),keyword('left-assoc')],
    [symbol(xor),symbol('Bool'),symbol('Bool'),symbol('Bool'),keyword('left-assoc')],
    [reserved(par),[symbol('A')],[symbol(=),symbol('A'),symbol('A'),symbol('Bool'),keyword(chainable)]],
    [reserved(par),[symbol('A')],[symbol(distinct),symbol('A'),symbol('A'),symbol('Bool'),keyword(pairwise)]],
    [reserved(par),[symbol('A')],[symbol(ite),symbol('Bool'),symbol('A'),symbol('A'),symbol('A')]]
  ]],
  [keyword(definition),string(...)],
  [keyword(values),string(...)]
]).
```

#### Reading SMT-LIB logic declarations

```pl
?- smtlib_read_logic('../sample/logic/LIA.smt', X).
X = list([
  symbol(logic),
  symbol('LIA'),
  [keyword('smt-lib-version'),decimal(2.6)],
  [keyword('smt-lib-release'),string('2017-11-24')],
  [keyword('written-by'),string(...)],
  [keyword(date),string(...)],
  [keyword('update-history'),string(...)],
  [keyword(theories),[symbol('Ints')]],
  [keyword(language),string(...)],
  [keyword(extensions),string(...)]
]).

```

## License

Source code is released under the terms of the [BSD 3-Clause License](https://github.com/jariazavalverde/prolog-smtlib/blob/master/LICENSE).

## References

1. Barrett, C., Fontaine, P. & Tinelli, C. The SMT-LIB Standard: Version 2.6. Department of Computer Science, The University of Iowa (2017). [View online](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf)
