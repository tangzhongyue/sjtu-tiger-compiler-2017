#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "env.h"

/*Lab4: Your implementation of lab4*/

E_enventry E_VarEntry(Ty_ty ty)
{
	E_enventry entry = checked_malloc(sizeof(*entry));
	entry->kind = E_varEntry;
	entry->u.var.ty = ty;

	return entry;
}

E_enventry E_ROVarEntry(Ty_ty ty)
{
	E_enventry entry = checked_malloc(sizeof(*entry));
	entry->kind = E_varEntry;
	entry->u.var.ty = ty;
	entry->readonly = 1;
	return entry;
}

E_enventry E_FunEntry(Ty_tyList formals, Ty_ty result)
{
	E_enventry entry = checked_malloc(sizeof(*entry));
	entry->kind = E_funEntry;
	entry->u.fun.formals = formals;
	entry->u.fun.result = result;

	return entry;
}

//sym->value
//type_id(name, S_symbol) -> type (Ty_ty)
S_table E_base_tenv(void)
{
	S_table table;
	S_symbol ty_int;
	S_symbol ty_string;

	table = S_empty();

	//basic type: string
	ty_int = S_Symbol("int");
	S_enter(table, ty_int, Ty_Int());	

	//basic type: string
	ty_string = S_Symbol("string");
	S_enter(table, ty_string, Ty_String());	

	return table;
}

S_table E_base_venv(void)
{
	S_table table;

	table = S_empty();
	S_enter(table, S_Symbol("print"), E_FunEntry(Ty_TyList(Ty_String(), NULL), Ty_Void()));
	S_enter(table, S_Symbol("flush"), E_FunEntry(NULL, Ty_Void()));
	S_enter(table, S_Symbol("getchar"), E_FunEntry(NULL, Ty_String()));
	S_enter(table, S_Symbol("ord"), E_FunEntry(Ty_TyList(Ty_String(), NULL), Ty_Int()));
	S_enter(table, S_Symbol("chr"), E_FunEntry(Ty_TyList(Ty_Int(), NULL), Ty_String()));
	S_enter(table, S_Symbol("size"), E_FunEntry(Ty_TyList(Ty_String(), NULL), Ty_Int()));
	S_enter(table, S_Symbol("substring"), E_FunEntry(Ty_TyList(Ty_String(), Ty_TyList(Ty_Int(), Ty_TyList(Ty_Int(), NULL))), Ty_String()));
	S_enter(table, S_Symbol("concat"), E_FunEntry(Ty_TyList(Ty_String(), Ty_TyList(Ty_String(), NULL)), Ty_String()));
	S_enter(table, S_Symbol("not"), E_FunEntry(Ty_TyList(Ty_Int(), NULL), Ty_Int()));
	S_enter(table, S_Symbol("exit"), E_FunEntry(Ty_TyList(Ty_Int(), NULL), Ty_Void()));
	return table;
}
