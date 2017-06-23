/********************************************************************************
*
* File: pcat.lex
* The PCAT scanner
*
********************************************************************************/

package edu.uta.pcat;

import java_cup.runtime.Symbol;

%%
%class PcatLex
%public
%line
%column
%cup
%state comment

%{

  private Symbol symbol ( int type ) {
    return new Symbol(type, yyline, yycolumn);
  }

  private Symbol symbol ( int type, Object value ) {
    return new Symbol(type, yyline, yycolumn, value);
  }

  public void lexical_error ( String message ) {
    throw new Error("*** Lexical Error: " + message + " (line: " + yyline
                    + ", position: " + yycolumn + ")");
  }
%}

DIGIT=[0-9]

%%

<YYINITIAL> {
{DIGIT}+                { return symbol(sym.INTEGER_LITERAL, new Integer(yytext())); }
{DIGIT}+\.{DIGIT}+      { return symbol(sym.REAL_LITERAL, new Float(yytext())); }
"AND"                   { return symbol(sym.AND); }
"ARRAY"                 { return symbol(sym.ARRAY); }
"BEGIN"                 { return symbol(sym.BEGIN); }
"BY"                    { return symbol(sym.BY); }
"DIV"                   { return symbol(sym.DIV); }
"DO"                    { return symbol(sym.DO); }
"ELSE"                  { return symbol(sym.ELSE); }
"ELSIF"                 { return symbol(sym.ELSIF); }
"END"                   { return symbol(sym.END); }
"EXIT"                  { return symbol(sym.EXIT); }
"FOR"                   { return symbol(sym.FOR); }
"IF"                    { return symbol(sym.IF); }
"IS"                    { return symbol(sym.IS); }
"LOOP"                  { return symbol(sym.LOOP); }
"MOD"                   { return symbol(sym.MOD); }
"NOT"                   { return symbol(sym.NOT); }
"OF"                    { return symbol(sym.OF); }
"OR"                    { return symbol(sym.OR); }
"PROCEDURE"             { return symbol(sym.PROCEDURE); }
"PROGRAM"               { return symbol(sym.PROGRAM); }
"READ"                  { return symbol(sym.READ); }
"RECORD"                { return symbol(sym.RECORD); }
"RETURN"                { return symbol(sym.RETURN); }
"THEN"                  { return symbol(sym.THEN); }
"TO"                    { return symbol(sym.TO); }
"TYPE"                  { return symbol(sym.TYPE); }
"VAR"                   { return symbol(sym.VAR); }
"WHILE"                 { return symbol(sym.WHILE); }
"WRITE"                 { return symbol(sym.WRITE); }
":="                    { return symbol(sym.ASGN); }
"+"                     { return symbol(sym.PLUS); }
"-"                     { return symbol(sym.MINUS); }
"*"                     { return symbol(sym.TIMES); }
"/"                     { return symbol(sym.SLASH); }
"<"                     { return symbol(sym.LT); }
"<="                    { return symbol(sym.LEQ); }
">"                     { return symbol(sym.GT); }
">="                    { return symbol(sym.GEQ); }
"="                     { return symbol(sym.EQ); }
"<>"                    { return symbol(sym.NEQ); }
":"                     { return symbol(sym.COLON); }
";"                     { return symbol(sym.SEMI); }
","                     { return symbol(sym.COMMA); }
"."                     { return symbol(sym.DOT); }
"("                     { return symbol(sym.LPAREN); }
")"                     { return symbol(sym.RPAREN); }
"["                     { return symbol(sym.LSQBRA); }
"]"                     { return symbol(sym.RSQBRA); }
"(*"                    { yybegin(comment); }
"{"                     { return symbol(sym.LCUBRA); }
"}"                     { return symbol(sym.RCUBRA); }
\"[^\"\t\n]*\"          { if(yytext().length() > 257) { lexical_error("Identifier is too long"); }return symbol(sym.STRING_LITERAL, yytext().substring(1,yytext().length()-1)); }
[a-zA-Z][a-zA-Z0-9_]*   { if(yytext().length() > 255) { lexical_error("Identifier is too long"); } return symbol(sym.ID, yytext()); }
[ \t\r\n\f]             { /* ignore white spaces. */ }
.                       { lexical_error("Unrecognised character" + yytext()); }
}

<comment> {
.|\n                    { /* ignore comment */ }
"*)"                    { yybegin(YYINITIAL);  }
}