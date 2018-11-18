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

% A <numeral> is the digit 0 or a non-empty sequence of digits not starting with 0.
token_numeral(numeral(Y)) --> numeral([X|Xs]), {X \= '0', number_chars(Y, [X|Xs])}.

numeral([X|Xs]) --> [X], {char_code(X, C), C >= 48, C =< 57}, !, numeral(Xs).
numeral([]) --> [].

% A <decimal> is a token of the form <numeral>.0*<numeral>.
token_decimal(decimal(D)) -->
    token_numeral(numeral(X)),
    ['.'], numeral(Y),
    {atom_chars(Z, ['.'|Y]),
    atom_concat(X, Z, W),
    atom_number(W, D)}.

% A <hexadecimal> is a non-empty case-insensitive sequence of digits and letters
% from A to F preceded by the (case sensitive) characters #x.
token_hexadecimal(hexadecimal(Y)) --> ['#','x'], hexadecimal(X), {X \= [], atom_chars(Y, X)}.

hexadecimal([X|Xs]) --> [X],
    {member(X, ['0','1','2','3','4','5','6','7','8','9',a,b,c,d,e,f,'A','B','C','D','E','F'])}, !,
    hexadecimal(Xs).
hexadecimal([]) --> [].

% A <binary> is a non-empty sequence of the characters 0 and 1 preceded by the characters #b.
token_binary(binary(Y)) --> ['#','b'], binary(X), {X \= [], atom_chars(Y, X)}.

binary([X|Xs]) --> [X], {member(X, ['0','1'])}, !, binary(Xs).
binary([]) --> [].

% A <string> is any sequence of printable ASCII characters delimited by double quotes
% (") and possibly containing the C-style escape sequences \" and \\, both of which are
% treated as a single character—respectively " and \.  The first escape sequence allows
% as usual the double quote character to appear within a string literal, the second allows
% the backslash character to end a string literal.
token_string(string(Y)) --> ['"'], quoted(X), ['"'], {atom_chars(Y, X)}.

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

token_reserved(reserved(Y)) -->
    simple_symbol([X|Xs]),
    {atom_chars(Y, [X|Xs]),
    reserved_word(Y)}.

% A <symbol> is either a simple symbol or a quoted symbol. The former is any non-empty
% sequence of letters, digits and the characters ~ ! @ $ % ^ & * _ - + = < > . ? / that
% does not start with a digit and is not a reserved word. The latter is any sequence of
% printable ASCII characters (including space, tab, and line-breaking characters) except
% for the backslash character \, that starts and ends with | and does not otherwise contain |.
token_symbol(X) --> token_simple_symbol(X).
token_symbol(X) --> token_quoted_symbol(X).

token_simple_symbol(symbol(Y)) -->
    simple_symbol([X|Xs]),
    {\+member(X, ['0','1','2','3','4','5','6','7','8','9']),
    atom_chars(Y, [X|Xs]),
    \+reserved_word(Y)}.

simple_symbol([X|Xs]) --> [X],
    {member(X, ['~','!','@','$','%','^','&','*','_','-','+','=','<','>','.','?','/']) ;
    (char_code(X, C), C >= 48, C =< 57) ; 
    (char_code(X, C), C >= 97, C =< 122) ; 
    (char_code(X, C), C >= 65, C =< 90)}, !,
    simple_symbol(Xs).
simple_symbol([]) --> [].

token_quoted_symbol(symbol(Y)) --> ['|'], quoted_symbol(X), ['|'], {atom_chars(Y, X)}.

quoted_symbol([X|Xs]) --> [X], {X \= '|', X \= '\\'}, quoted_symbol(Xs).
quoted_symbol([]) --> [].

% A <keyword> is a non-empty sequence of letters, digits, and the characters
% ~ ! @ $ % ^ & * _ - + = < > . ? / preceded by the character :.
token_keyword(keyword(Y)) --> [':'], simple_symbol(X), {atom_chars(Y, X)}.



% S-EXPRESSIONS

% An S-expression is either a non-parenthesis token or a (possibly  empty) sequence of
% S-expressions enclosed in parentheses. Every syntactic category of the SMT-LIB language
% is a specialization of the category <s-expr> defined by the production rules below.
spec_constant(X) --> token_decimal(X), !.
spec_constant(X) --> token_numeral(X), !.
spec_constant(X) --> token_hexadecimal(X), !.
spec_constant(X) --> token_binary(X), !.
spec_constant(X) --> token_string(X), !.

s_expr(X) --> whitespaces, s_expr2(X).
s_expr2(X) --> spec_constant(X), !, whitespaces.
s_expr2(X) --> token_symbol(X), !, whitespaces.
s_expr2(X) --> token_keyword(X), !, whitespaces.
s_expr2(X) --> ['('], whitespaces, s_exprs(X), [')'], whitespaces.

s_exprs([X|Xs]) --> s_expr2(X), !, s_exprs(Xs).
s_exprs([]) --> [].



% IDENTIFIERS

% Indexed identifiers are defined more systematically as the application of the reserved
% word _ to a symbol and one or more indices, given by numerals.
identifier(identifier(Xs)) --> ['('], whitespaces, ['_'], whitespaces, numerals(Xs), {Xs \= []}, [')'], whitespaces.
identifier(identifier(X)) --> token_symbol(X), whitespaces.

numerals([X|Xs]) --> numeral(X), !, whitespaces, numerals(Xs).
numerals([]) --> [].



% ATTRIBUTES

% These are generally pairs consisting of an attribute name and an associated value,
% although attributes with no value are also allowed.

attribute_value(X) --> spec_constant(X), !, whitespaces.
attribute_value(X) --> token_symbol(X), !, whitespaces.
attribute_value(Xs) --> ['('], whitespaces, s_exprs(Xs), [')'], whitespaces.

attribute(attr(X,Xs)) --> token_keyword(X), whitespaces, attribute_value(Xs), !, whitespaces.
attribute(attr(X)) --> token_keyword(X), whitespaces.

attributes([X|Xs]) --> attribute(X), !, attributes(Xs).
attributes([]) --> [].


% SORTS

% A sort symbol can be either the distinguished symbol Bool or any <identifier>. A sort
% parameter can be any <symbol> (which in turn, is an <identifier>).

sort(sort(X, Xs)) --> ['('], whitespaces, identifier(X), whitespaces, sorts(Xs), {Xs \= []}, [')'], whitespaces.
sort(sort(X, [])) --> identifier(X), whitespaces.

sorts([X|Xs]) --> sort(X), sorts(Xs).
sorts([]) --> [].



% TERMS AND FORMULAS

% Well-sorted terms are a subset of the set of all terms. The latter are constructed out of
% constant symbols in the <spec-constant> category (numerals, rationals, strings, etc.),
% variables, function symbols, three kinds of binders--the reserved words let, forall and
% exists--and an annotation operator--the reserved word !.

qual_identifier(qualified(X)) --> identifier(X).
qual_identifier(qualified(X,Y)) --> ['('], whitespaces, [a,s], whitespaces, identifier(X), sort(Y), [')'], whitespaces.

var_binding(binding(X,Y)) --> ['('], whitespaces, token_symbol(X), whitespaces, term(Y), [')'], whitespaces.
var_bindings([X|Xs]) --> var_binding(X), !, var_bindings(Xs).
var_bindings([]) --> [].

sorted_var(var(X,Y)) --> ['('], whitespaces, token_symbol(X), whitespaces, sort(Y), [')'], whitespaces.
sorted_vars([X|Xs]) --> sorted_var(X), !, sorted_vars(Xs).
sorted_vars([]) --> [].

term(term(X)) --> spec_constant(X), whitespaces.
term(term(X)) --> qual_identifier(X).
term(term(X,Xs)) --> ['('], whitespaces, qual_identifier(X), whitespaces, terms(Xs), {Xs \= []}, [')'], whitespaces.
term(term(let, Xs, X)) --> ['('], whitespaces, token_reserved(reserved(let)), whitespaces, ['('], whitespaces, var_bindings(Xs), {Xs \= []}, [')'], whitespaces, term(X), [')'], whitespaces.
term(term(Y, Xs, X)) --> ['('], whitespaces, token_reserved(reserved(Y)), {member(Y, [forall, exists])}, whitespaces, ['('], whitespaces, sorted_vars(Xs), {Xs \= []}, [')'], whitespaces, term(X), [')'], whitespaces.
term(term('!', Xs)) --> ['('], whitespaces, token_reserved(reserved('!')), whitespaces, attributes(Xs), {Xs \= []}, [')'], whitespaces.

terms([X|Xs]) --> term(X), !, terms(Xs).
terms([]) --> [].