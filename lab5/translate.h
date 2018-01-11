#ifndef TRANSLATE_H
#define TRANSLATE_H

#include "util.h"
#include "absyn.h"
#include "temp.h"
#include "frame.h"

/* Lab5: your code below */

typedef struct Tr_exp_ *Tr_exp;

typedef struct Tr_expList_ *Tr_expList;

typedef struct Tr_access_ *Tr_access;

typedef struct Tr_accessList_ *Tr_accessList;

struct Tr_accessList_ {
	Tr_access head;
	Tr_accessList tail;	
};

typedef struct Tr_level_ *Tr_level;

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail);

Tr_access Tr_Access(Tr_level level, F_access access);
Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);

Tr_level Tr_outermost(void);

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals);

Tr_accessList Tr_formals(Tr_level level);

Tr_access Tr_allocLocal(Tr_level level, bool escape);

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level);
Tr_exp Tr_fieldVar(Tr_exp addr, int off);
Tr_exp Tr_subscriptVar(Tr_exp addr, Tr_exp off);

Tr_exp Tr_Nop();
Tr_exp Tr_Nil();
Tr_exp Tr_Int(int v);
Tr_exp Tr_String(string s);
Tr_exp Tr_Jump(Temp_label l);
Tr_exp Tr_Call(Tr_level level, Temp_label label, Tr_expList params, Tr_level cur);
Tr_exp Tr_OpArithm(A_oper oper, Tr_exp left, Tr_exp right);
Tr_exp Tr_OpCmp(A_oper oper, Tr_exp left, Tr_exp right, int isStr);
Tr_exp Tr_Assign(Tr_exp var, Tr_exp value);
Tr_exp Tr_Seq(Tr_exp seq, Tr_exp e);
Tr_exp Tr_IfThen(Tr_exp test, Tr_exp then);
Tr_exp Tr_IfThenElse(Tr_exp test, Tr_exp then, Tr_exp elsee);
Tr_exp Tr_While(Tr_exp test, Tr_exp body, Temp_label done);
Tr_exp Tr_For(Tr_access access, Tr_level level, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done);
Tr_exp Tr_Record(int num, Tr_expList fields);
Tr_exp Tr_Array(Tr_exp size, Tr_exp init);

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals);
F_fragList Tr_getResult(void);
#endif
