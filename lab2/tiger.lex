%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "tokens.h"
#include "errormsg.h"

int charPos=1;

int commentLvl = 0;

char buf[1024];
int bufpos = 0;

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

%}
  /* You can add lex definitions here. */
digit 	[0-9]
letter	[a-zA-Z]
digits	[0-9]+

%Start COMMENT STR
%%
  /* 
  * Below is an example, which you can wipe out
  * and write reguler expressions and actions of your own.
  */ 
<INITIAL>"/*" {adjust(); commentLvl += 1; BEGIN COMMENT; }
<INITIAL>"array" {adjust(); return ARRAY;}
<INITIAL>"let" {adjust(); return LET;}
<INITIAL>"if" {adjust(); return IF;}
<INITIAL>"else" {adjust(); return ELSE;}
<INITIAL>"while" {adjust(); return WHILE;}
<INITIAL>"for" {adjust(); return FOR;}
<INITIAL>"in" {adjust(); return IN;}
<INITIAL>"end" {adjust(); return END;}
<INITIAL>"type" {adjust(); return TYPE;}
<INITIAL>"var" {adjust(); return VAR;}
<INITIAL>"of" {adjust(); return OF;}
<INITIAL>"to" {adjust(); return TO;}
<INITIAL>"do" {adjust(); return DO;}
<INITIAL>"break" {adjust(); return BREAK;}
<INITIAL>"nil" {adjust(); return NIL;}
<INITIAL>"function" {adjust(); return FUNCTION;}
<INITIAL>"then" {adjust(); return THEN;}
<INITIAL>":=" {adjust(); return ASSIGN;}
<INITIAL>"<>" {adjust();return NEQ;}
<INITIAL>"<=" {adjust();return LE;}
<INITIAL>">=" {adjust();return GE;}
<INITIAL>":" {adjust(); return COLON;}
<INITIAL>";" {adjust(); return SEMICOLON;}
<INITIAL>">" {adjust();return GT;}
<INITIAL>"<" {adjust();return LT;}
<INITIAL>"=" {adjust(); return EQ;}
<INITIAL>"," {adjust();return COMMA;}
<INITIAL>"(" {adjust();return LPAREN;}
<INITIAL>")" {adjust();return RPAREN;}
<INITIAL>"[" {adjust(); return LBRACK;}
<INITIAL>"]" {adjust(); return RBRACK;}
<INITIAL>"{" {adjust();return LBRACE;}
<INITIAL>"}" {adjust();return RBRACE;}
<INITIAL>"." {adjust(); return DOT;}
<INITIAL>"+" {adjust(); return PLUS;}
<INITIAL>"-" {adjust(); return MINUS;}
<INITIAL>"*" {adjust(); return TIMES;}
<INITIAL>"/" {adjust(); return DIVIDE;}
<INITIAL>"&" {adjust(); return AND;}
<INITIAL>"|" {adjust(); return OR;}
<INITIAL>" " {adjust(); continue;}
<INITIAL>"\t" {adjust(); continue;}
<INITIAL>"\n" {adjust(); EM_newline(); continue;}
<INITIAL>"\"" {adjust(); BEGIN STR;}
<INITIAL>{letter}({letter}|{digit}|_)* {adjust(); yylval.sval = String(yytext); return ID;}
<INITIAL>{digits} {adjust(); yylval.ival = atoi(yytext); return INT;}
<INITIAL>. {adjust(); EM_error(EM_tokPos, "illegal character");}

<COMMENT>"\n" {adjust(); EM_newline(); continue;}
<COMMENT>"*/" {adjust(); commentLvl -= 1; if(commentLvl == 0){BEGIN INITIAL;}}
<COMMENT>"/*" {adjust(); commentLvl += 1;}
<COMMENT>. {adjust();}

<STR>"\\n" {charPos += yyleng; buf[bufpos] = '\n'; bufpos += 1;}
<STR>"\\t" {charPos += yyleng; buf[bufpos] = '\t'; bufpos += 1;}
<STR>"\\\"" {charPos += yyleng; buf[bufpos] = '\"'; bufpos += 1;}
<STR>"\\\\" {charPos += yyleng; buf[bufpos] = '\\'; bufpos += 1;}
<STR>\\digitdigitdigit {charPos += yyleng; buf[bufpos] = atoi(yytext); bufpos += 1;}
<STR>\\\^[A-Z] {charPos += yyleng; buf[bufpos] = yytext[2] - 'A' + 1; bufpos += 1;}
<STR>\\\^\[ {charPos += yyleng; buf[bufpos] = 27; bufpos += 1;}
<STR>\\\^\\ {charPos += yyleng; buf[bufpos] = 28; bufpos += 1;}
<STR>\\\^\] {charPos += yyleng; buf[bufpos] = 29; bufpos += 1;}
<STR>\\\^\^ {charPos += yyleng; buf[bufpos] = 30; bufpos += 1;}
<STR>\\\^_ {charPos += yyleng; buf[bufpos] = 31; bufpos += 1;}
<STR>\\[ \t\n\f\v]+\\ {charPos+=yyleng;}
<STR>"\"" {charPos+=yyleng; BEGIN INITIAL; buf[bufpos] = '\0'; if(bufpos == 0)yylval.sval = "(null)"; else yylval.sval = buf; bufpos = 0; return STRING; }
<STR>. {charPos+=yyleng; strcpy(buf + bufpos, yytext); bufpos += yyleng;}

