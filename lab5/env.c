#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "types.h"
#include "env.h"


E_enventry E_VarEntry(Tr_access access, Ty_ty ty)
{
    E_enventry res = checked_malloc(sizeof(*res));
    res->kind = E_varEntry;
    res->u.var.access = access;
    res->u.var.ty = ty;
    return res;
}

E_enventry E_FunEntry(Tr_level level, Temp_label label, Ty_tyList formals, Ty_ty result)
{
    E_enventry res = checked_malloc(sizeof(*res));
    res->kind = E_funEntry;
    res->u.fun.level = level;
    res->u.fun.label = label;
    res->u.fun.formals = formals;
    res->u.fun.result = result;
    return res;
}

E_enventry E_ROVarEntry(Tr_access access, Ty_ty ty)
{
    E_enventry entry = checked_malloc(sizeof(*entry));

    entry->u.var.access = access;
    entry->u.var.ty = ty;
    entry->readonly = 1;
    return entry;
}

S_table E_base_tenv(void)
{
    S_table res = S_empty();
    S_enter(res, S_Symbol("int"), Ty_Int());
    S_enter(res, S_Symbol("string"), Ty_String());
    return res;
}

S_table E_base_venv(void) /* TODO */
{
    Temp_label label = Temp_newlabel();
    Tr_level level = Tr_outermost();
    S_table res = S_empty();
    S_enter(res, S_Symbol("print"), E_FunEntry(level, label, Ty_TyList(Ty_String(), NULL), Ty_Void()));
    S_enter(res, S_Symbol("flush"), E_FunEntry(level, label, NULL, Ty_Void()));
    S_enter(res, S_Symbol("getchar"), E_FunEntry(level, label, NULL, Ty_String()));
    S_enter(res, S_Symbol("ord"), E_FunEntry(level, label, Ty_TyList(Ty_String(), NULL), Ty_Int()));
    S_enter(res, S_Symbol("chr"), E_FunEntry(level, label, Ty_TyList(Ty_Int(), NULL), Ty_String()));
    S_enter(res, S_Symbol("size"), E_FunEntry(level, label, Ty_TyList(Ty_String(), NULL), Ty_Int()));
    S_enter(res, S_Symbol("substring"), E_FunEntry(level, label, Ty_TyList(Ty_String(), Ty_TyList(Ty_Int(), Ty_TyList(Ty_Int(), NULL))), Ty_String()));
    S_enter(res, S_Symbol("concat"), E_FunEntry(level, label, Ty_TyList(Ty_String(), Ty_TyList(Ty_String(), NULL)), Ty_String()));
    S_enter(res, S_Symbol("not"), E_FunEntry(level, label, Ty_TyList(Ty_Int(), NULL), Ty_Int()));
    S_enter(res, S_Symbol("exit"), E_FunEntry(level, label, Ty_TyList(Ty_Int(), NULL), Ty_Void()));
    return res;
}
