/**
  * 
  * FILENAME: smtlib.pl
  * DESCRIPTION: This module contains predicates for parsing SMTLIB programs.
  * AUTHORS: José Antonio Riaza Valverde
  * UPDATED: 17.11.2018
  * 
  **/



% WHITESPACES

% A comment is any character sequence not contained within a string literal
% or a quoted symbol that begins with the semicolon character ; and ends 
% with the first subsequent line-breaking character. Comments together with
% the space, tab and line-breaking characters are all considered whitespace.

comment --> [X], {X \= '\n'}, !, comment.
comment --> [].

whitespace --> [' '].
whitespace --> ['\t'].
whitespace --> ['\n'].
whitespace --> [';'], comment, ['\n'].



% LEXICON

% A <numeral> is the digit 0 or a non-empty sequence of digits not starting with 0.
token_numeral(numeral(Y)) --> numeral(X), {X \= [], number_chars(Y, X)}.

numeral(['0']) --> ['0'].
numeral([X|Xs]) --> [X], {member(X, ['1','2','3','4','5','6','7','8','9'])}, !, numeral(Xs).
numeral([]) --> [].

% A <decimal> is a token of the form <numeral>.0*<numeral>.
token_decimal(decimal(X,Y)) --> numeral(X), zeros, numeral(Y).

zeros --> ['0'], !, zeros.
zeros --> [].

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