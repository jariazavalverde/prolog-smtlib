/**
  * 
  * FILENAME: smtlib.pl
  * DESCRIPTION: This module contains predicates for parsing SMT-LIB programs.
  * AUTHORS: José Antonio Riaza Valverde <riaza.valverde@gmail.com>
  * GITHUB: https://github.com/jariazavalverde/prolog-smtlib
  * UPDATED: 17.11.2018
  * 
  **/



:- module(smtlib, [
    smtlib_parse_expression/2
]).



/**
  * 
  * Barrett, Clark, Aaron Stump, and Cesare Tinelli. "The smt-lib standard: Version 2.0."
  * Proceedings of the 8th International Workshop on Satisfiability Modulo Theories (Edinburgh, England).
  * Vol. 13. 2010.
  * 
  * http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf
  * 
  **/



% smtlib_parse_expression/2
% smtlib_parse_expression(+Chars, ?Expression)
%
% This predicate succeeds when +Chars is a list of characters and
% ?Expression is the expression resulting from parsing +Chars as an
% S-Expression of SMT-LIM.
smtlib_parse_expression(Chars, Expression) :- s_expr(Expression, Chars, []).



% LEXICON
% SMT-LIB source files consist of ASCII characters.

% A comment is any character sequence not contained within a string literal
% or a quoted symbol that begins with the semicolon character ; and ends 
% with the first subsequent line-breaking character.
comment --> [X], {X \= '\n'}, !, comment.
comment --> [].

% Comments together with the space, tab and line-breaking characters are all
% considered whitespace.
whitespace --> [' '].
whitespace --> ['\t'].
whitespace --> ['\n'].
whitespace --> [';'], comment, ['\n'].

whitespaces --> whitespace, !, whitespaces.
whitespaces --> [].

lpar --> ['('], whitespaces.
rpar --> [')'], whitespaces.

% A <numeral> is the digit 0 or a non-empty sequence of digits not starting with 0.
numeral(numeral(Y)) --> digits([X|Xs]), {(Xs = [] ; X \= '0'), number_chars(Y, [X|Xs])}, whitespaces.

digits([X|Xs]) --> [X], {char_code(X, C), C >= 48, C =< 57}, !, digits(Xs).
digits([]) --> [].

% A <decimal> is a token of the form <numeral>.0*<numeral>.
decimal(decimal(D)) -->
    digits([X|Xs]),
    {(Xs = [] ; X \= '0')},
    ['.'], digits(Y),
    {append([X|Xs], ['.'|Y], Z),
    number_chars(D, Z)},
    whitespaces.

% A <hexadecimal> is a non-empty case-insensitive sequence of digits and letters
% from A to F preceded by the (case sensitive) characters #x.
hexadecimal(hexadecimal(Y)) --> ['#','x'], hexadecimal_digits(X), {X \= [], atom_chars(Y, X)}, whitespaces.

hexadecimal_digits([X|Xs]) --> [X],
    {member(X, ['0','1','2','3','4','5','6','7','8','9',a,b,c,d,e,f,'A','B','C','D','E','F'])}, !,
    hexadecimal_digits(Xs).
hexadecimal_digits([]) --> [].

% A <binary> is a non-empty sequence of the characters 0 and 1 preceded by the characters #b.
binary(binary(Y)) --> ['#','b'], binary_digits(X), {X \= [], atom_chars(Y, X)}, whitespaces.

binary_digits([X|Xs]) --> [X], {member(X, ['0','1'])}, !, binary_digits(Xs).
binary_digits([]) --> [].

% A <string> is any sequence of printable ASCII characters delimited by double quotes
% (") and possibly containing the C-style escape sequences \" and \\, both of which are
% treated as a single character—respectively " and \.  The first escape sequence allows
% as usual the double quote character to appear within a string literal, the second allows
% the backslash character to end a string literal.
string(string(Y)) --> ['"'], quoted(X), ['"'], {atom_chars(Y, X)}, whitespaces.

quoted([X|Xs]) --> [X], {X \= '\\', X \= '"'}, !, quoted(Xs).
quoted(['"'|Xs]) --> ['\\','"'], !, quoted(Xs).
quoted(['\\'|Xs]) --> ['\\','\\'], !, quoted(Xs).
quoted([]) --> [].

% The language uses a number of reserved words, sequences of (non-whitespace) characters
% that are to be treated as individual tokens. Additionally, each command name in the
% scripting language is also a reserved word.
reserved_word(X) :- member(X, [
    par, 'NUMERAL', 'DECIMAL', 'STRING', '_', '!', as, let, forall, exists,
    'set-logic', 'set-option', 'set-info', 'declare-sort', 'define-sort',
    'declare-fun', push, pop, assert, 'check-sat', 'get-assertions',
    'get-proof', 'get-unsat-core', 'get-value', 'get-assignment', exit
]).

reserved_word(reserved(Y)) -->
    symbol_chars([X|Xs]),
    {atom_chars(Y, [X|Xs]),
    reserved_word(Y)},
    whitespaces.

% A <symbol> is either a simple symbol or a quoted symbol. The former is any non-empty
% sequence of letters, digits and the characters ~ ! @ $ % ^ & * _ - + = < > . ? / that
% does not start with a digit and is not a reserved word. The latter is any sequence of
% printable ASCII characters (including space, tab, and line-breaking characters) except
% for the backslash character \, that starts and ends with | and does not otherwise contain |.
symbol(X) --> simple_symbol(X).
symbol(X) --> quoted_symbol(X).

simple_symbol(symbol(Y)) -->
    symbol_chars([X|Xs]),
    {\+member(X, ['0','1','2','3','4','5','6','7','8','9']),
    atom_chars(Y, [X|Xs]),
    \+reserved_word(Y)},
    whitespaces.

symbol_chars([X|Xs]) --> [X],
    {member(X, ['~','!','@','$','%','^','&','*','_','-','+','=','<','>','.','?','/']) ;
    (char_code(X, C), C >= 48, C =< 57) ; 
    (char_code(X, C), C >= 97, C =< 122) ; 
    (char_code(X, C), C >= 65, C =< 90)}, !,
    symbol_chars(Xs).
symbol_chars([]) --> [].

quoted_symbol(symbol(Y)) --> ['|'], quoted_symbol_chars(X), ['|'], {atom_chars(Y, X)}, whitespaces.

quoted_symbol_chars([X|Xs]) --> [X], {X \= '|', X \= '\\'}, quoted_symbol_chars(Xs).
quoted_symbol_chars([]) --> [].

% A <keyword> is a non-empty sequence of letters, digits, and the characters
% ~ ! @ $ % ^ & * _ - + = < > . ? / preceded by the character :.
keyword(keyword(Y)) --> [':'], symbol_chars(X), {X \= [], atom_chars(Y, X)}, whitespaces.



% S-EXPRESSIONS

% An S-expression is either a non-parenthesis token or a (possibly  empty) sequence of
% S-expressions enclosed in parentheses. Every syntactic category of the SMT-LIB language
% is a specialization of the category <s-expr> defined by the production rules below.
spec_constant(X) --> decimal(X), !.
spec_constant(X) --> numeral(X), !.
spec_constant(X) --> hexadecimal(X), !.
spec_constant(X) --> binary(X), !.
spec_constant(X) --> string(X), !.

s_expr(X) --> whitespaces, s_expr2(X).
s_expr2(X) --> spec_constant(X), !.
s_expr2(X) --> symbol(X), !.
s_expr2(X) --> keyword(X), !.
s_expr2(X) --> lpar, s_exprs(X), rpar.

s_exprs([X|Xs]) --> s_expr2(X), !, s_exprs(Xs).
s_exprs([]) --> [].



% IDENTIFIERS

% Indexed identifiers are defined more systematically as the application of the reserved
% word _ to a symbol and one or more indices, given by numerals.
identifier(identifier(Xs)) --> lpar, ['_'], whitespaces, numerals(Xs), {Xs \= []}, rpar.
identifier(identifier(X)) --> symbol(X).

numerals([X|Xs]) --> numeral(X), !, numerals(Xs).
numerals([]) --> [].



% ATTRIBUTES

% These are generally pairs consisting of an attribute name and an associated value,
% although attributes with no value are also allowed.

attribute_value(X) --> spec_constant(X), !.
attribute_value(X) --> symbol(X), !.
attribute_value(Xs) --> lpar, s_exprs(Xs), rpar.

attribute(attr(X,Xs)) --> keyword(X), attribute_value(Xs), !.
attribute(attr(X)) --> keyword(X).

attributes([X|Xs]) --> attribute(X), !, attributes(Xs).
attributes([]) --> [].


% SORTS

% A sort symbol can be either the distinguished symbol Bool or any <identifier>. A sort
% parameter can be any <symbol> (which in turn, is an <identifier>).

sort(sort(X, Xs)) --> lpar, identifier(X), sorts(Xs), {Xs \= []}, rpar.
sort(sort(X, [])) --> identifier(X).

sorts([X|Xs]) --> sort(X), sorts(Xs).
sorts([]) --> [].



% TERMS AND FORMULAS

% Well-sorted terms are a subset of the set of all terms. The latter are constructed out of
% constant symbols in the <spec-constant> category (numerals, rationals, strings, etc.),
% variables, function symbols, three kinds of binders--the reserved words let, forall and
% exists--and an annotation operator--the reserved word !.

qual_identifier(qualified(X)) --> identifier(X).
qual_identifier(qualified(X,Y)) --> lpar, [a,s], whitespaces, identifier(X), sort(Y), rpar.

var_binding(binding(X,Y)) --> lpar, symbol(X), term(Y), rpar.
var_bindings([X|Xs]) --> var_binding(X), !, var_bindings(Xs).
var_bindings([]) --> [].

sorted_var(var(X,Y)) --> lpar, symbol(X), sort(Y), rpar.
sorted_vars([X|Xs]) --> sorted_var(X), !, sorted_vars(Xs).
sorted_vars([]) --> [].

term(term(X)) --> spec_constant(X).
term(term(X)) --> qual_identifier(X).
term(term(X,Xs)) --> lpar, qual_identifier(X), terms(Xs), {Xs \= []}, rpar.
term(term(reserved(let), Xs, X)) --> lpar, reserved_word(reserved(let)), lpar, var_bindings(Xs), {Xs \= []}, rpar, term(X), rpar.
term(term(reserved(Y), Xs, X)) --> lpar, reserved_word(reserved(Y)), {member(Y, [forall, exists])}, lpar, sorted_vars(Xs), {Xs \= []}, rpar, term(X), rpar.
term(term(reserved('!'), Xs)) --> lpar, reserved_word(reserved('!')), attributes(Xs), {Xs \= []}, rpar.

terms([X|Xs]) --> term(X), !, terms(Xs).
terms([]) --> [].



% THEORY DECLARATIONS

% The syntax of theory declarations follows an attribute-value-based format. A theory
% declaration consists of a theory name and a list of <attribute> elements. Theory attributes
% with the following predefined keywords have a prescribed usage and semantics: :definition,
% :funs, :funs-description, :notes, :sorts, :sorts-description, and :values. Additionally, a
% theory declaration can contain any number of user-defined attributes.

sort_symbol_decl(sort_symbol_decl(X,Y,Z)) --> lpar, identifier(X), numeral(Y), attributes(Z), rpar.