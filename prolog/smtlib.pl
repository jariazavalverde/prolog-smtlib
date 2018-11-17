/**
  * 
  * FILENAME: smtlib.pl
  * DESCRIPTION: This module contains predicates for parsing SMTLIB programs.
  * AUTHORS: José Antonio Riaza Valverde <riaza.valverde@gmail.com>
  * GITHUB: https://github.com/jariazavalverde/smtlib2prolog
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

token_reserved(reserved(par)) --> [p,a,r].
token_reserved(reserved('NUMERAL')) --> ['N','U','M','E','R','A','L'].
token_reserved(reserved('DECIMAL')) --> ['D,','E,','C','I','M','A','L'].
token_reserved(reserved('STRING')) --> ['S','T','R','I','N','G'].
token_reserved(reserved('_')) --> ['_'].
token_reserved(reserved('!')) --> ['!'].
token_reserved(reserved(as)) --> [a,s].
token_reserved(reserved(let)) --> [l,e,t].
token_reserved(reserved(forall)) --> [f,o,r,a,l,l].
token_reserved(reserved(exists)) --> [e,x,i,s,t,s].

token_reserved(reserved('set-logic')) --> [s,e,t,'-',l,o,g,i,c].
token_reserved(reserved('set-option')) --> [s,e,t,'-',o,p,t,i,o,n].
token_reserved(reserved('set-info')) --> [s,e,t,'-',i,n,f,o].
token_reserved(reserved('declare-sort')) --> [d,e,c,l,a,r,e,'-',s,o,r,t].
token_reserved(reserved('define-sort')) --> [d,e,f,i,n,e,'-',s,o,r,t].
token_reserved(reserved('declare-fun')) --> [d,e,c,l,a,r,e,'-',f,u,n].
token_reserved(reserved('define-fun')) --> [d,e,f,i,n,e,'-',f,u,n].
token_reserved(reserved(push)) --> [p,u,s,h].
token_reserved(reserved(pop)) --> [p,o,p].
token_reserved(reserved(assert)) --> [a,s,s,e,r,t].
token_reserved(reserved('check-sat')) --> [c,h,e,c,k,'-',s,a,t].
token_reserved(reserved('get-assertions')) --> [g,e,t,'-',a,s,s,e,r,t,i,o,n,s].
token_reserved(reserved('get-proof')) --> [g,e,t,'-',p,r,o,o,f].
token_reserved(reserved('get-unsat-core')) --> [g,e,t,'-',u,n,s,a,t,'-',c,o,r,e].
token_reserved(reserved('get-value')) --> [g,e,t,'-',v,a,l,u,e].
token_reserved(reserved('get-assignment')) --> [g,e,t,'-',a,s,s,i,g,n,m,e,n,t].
token_reserved(reserved(exit)) --> [e,x,i,t].

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
    atom_chars(Y, [X|Xs])}.

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