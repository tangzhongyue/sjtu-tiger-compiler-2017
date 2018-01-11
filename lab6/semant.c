#include <stdio.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "semant.h"
#include "translate.h"

/*Lab5: Your implementation of lab5.*/

struct expty 
{
  Tr_exp exp; 
  Ty_ty ty;
};

//In Lab4, the first argument exp should always be **NULL**.
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
  struct expty e;

  e.exp = exp;
  e.ty = ty;

  return e;
}

F_fragList SEM_transProg(A_exp exp){
  Tr_level main = Tr_outermost();
    struct expty e = transExp(E_base_venv(), E_base_tenv(), exp, main, NULL);
    Tr_procEntryExit(main, e.exp, NULL);
    return Tr_getResult();
}


Ty_ty actual_ty(Ty_ty ty)
{
  if(ty->kind == Ty_name){
    return ty->u.name.ty;
  }
  else{
    return ty;
  }
}

bool checkSameType(Ty_ty arg, Ty_ty formal){
  Ty_ty ty1 = actual_ty(arg);
  Ty_ty ty2 = actual_ty(formal);
  if (ty1->kind == Ty_int || ty1->kind == Ty_string)
    return ty1->kind == ty2->kind;
  
  if (ty1->kind == Ty_nil && ty2->kind == Ty_nil)
    return FALSE;
  
  if (ty1->kind == Ty_nil)
    return ty2->kind == Ty_record || ty2->kind == Ty_array;
  
  if (ty2->kind == Ty_nil)
    return ty1->kind == Ty_record || ty1->kind == Ty_array;
  
  return ty1 == ty2;
}

struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level level, Temp_label tl)
{
  switch(a->kind) {
    case A_varExp:
      return transVar(venv, tenv, a->u.var, level, tl);
    case A_nilExp:
      return expTy(Tr_Nil(), Ty_Nil());
    case A_intExp:
      return expTy(Tr_Int(a->u.intt), Ty_Int());
    case A_stringExp:
      return expTy(Tr_String(a->u.stringg), Ty_String());
    case A_callExp: {
      A_expList args = a->u.call.args;
      E_enventry fun = S_look(venv, a->u.call.func);
      struct expty exparg;
      Tr_expList params = NULL;
      if(fun && fun->kind == E_funEntry) {
        Ty_tyList formals = fun->u.fun.formals;
        for(; args && formals; args = args->tail, formals = formals->tail){
          exparg = transExp(venv, tenv, args->head, level, NULL);
          if(!checkSameType(exparg.ty, formals->head)){
            EM_error(args->head->pos, "para type mismatch");
          }
          params = Tr_ExpList(exparg.exp, params);
        }
        if (args) {
          EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
        }
        if (formals) {
          EM_error(a->pos, "too few params in function %s", S_name(a->u.call.func));
        }
        return expTy(Tr_Call(fun->u.fun.level, fun->u.fun.label, params, level), fun->u.fun.result);
      } 
      else {
        EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
        return expTy(Tr_Nop(), Ty_Int());
      }
      }
    case A_opExp: {
      A_oper oper = a->u.op.oper;
      struct expty left =transExp(venv, tenv, a->u.op.left, level, tl);
      struct expty right =transExp(venv, tenv, a->u.op.right, level, tl);
      if(oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp){
        if (left.ty->kind != Ty_int) {
          EM_error(a->u.op.left->pos, "integer required");
        }
        if (right.ty->kind != Ty_int) {
          EM_error(a->u.op.right->pos, "integer required");
        }
        return expTy(Tr_OpArithm(oper, left.exp, right.exp),Ty_Int());
      }
      else if (oper == A_eqOp || oper == A_neqOp) {
        if (!checkSameType(left.ty, right.ty) || left.ty->kind == Ty_void) {
          EM_error(a->pos, "same type required");
        }
        return expTy(Tr_OpCmp(oper, left.exp, right.exp, left.ty->kind == Ty_string),Ty_Int());
      } 
      else {
        if (!(left.ty->kind == Ty_int && right.ty->kind == Ty_int)) {
          EM_error(a->pos, "same type required");
        }
        return expTy(Tr_OpCmp(oper, left.exp, right.exp, left.ty->kind == Ty_string), Ty_Int());
      }
    }
    case A_recordExp: {
      Ty_ty ty = S_look(tenv, a->u.record.typ);
      if(ty){
        ty = actual_ty(ty);
      }
      else{
        EM_error(a->pos,"undefined type %s", S_name(a->u.record.typ));
        ty = Ty_Int();
      }
      A_efieldList fields = a->u.record.fields;
      Ty_fieldList tfields;
      struct expty exp;
      Tr_expList expfields = NULL;
      int num = 0;
      if(ty->kind != Ty_record){
        EM_error(a->pos, "record type required");
        return expTy(Tr_Nop(), Ty_Int());
      }
      tfields = ty->u.record;
      for(; fields && tfields; fields = fields->tail, tfields = tfields->tail){
        exp = transExp(venv, tenv, fields->head->exp, level, tl);
        if (!(fields->head->name == tfields->head->name && checkSameType(tfields->head->ty, exp.ty))) {
                    EM_error(fields->head->exp->pos, "type mismatch");
        }
        ++num;
        expfields = Tr_ExpList(exp.exp, expfields);
      }
      if(tfields || fields){
        EM_error(a->pos, "type mismatch");
      }
      return expTy(Tr_Record(num, expfields), ty);
    }
    case A_seqExp: {
      struct expty exp = expTy(Tr_Nop(), Ty_Void());
      Tr_expList el = NULL;
      A_expList list;
      for (list = a->u.seq; list != NULL; list = list->tail) {
        exp = transExp(venv, tenv, list->head, level, tl);
        el = Tr_ExpList(exp.exp, el);
      }
      return expTy(Tr_Seq(el), exp.ty);
    }
    case A_assignExp: {
      struct expty var = transVar(venv, tenv, a->u.assign.var, level, tl);
      struct expty exp = transExp(venv, tenv, a->u.assign.exp, level, tl);
      if(var.ty->kind == Ty_int){
                    //a->u.assign.var->u.simple
        E_enventry x = S_look(venv, a->u.assign.var->u.simple);
        if(x && x->readonly == 1){
          EM_error(a->pos, "loop variable can't be assigned");
        }
      }
      if(!checkSameType(exp.ty, var.ty)){
        EM_error(a->pos, "unmatched assign exp");
      }
      return expTy(Tr_Assign(var.exp, exp.exp), Ty_Void());
    } 
    case A_ifExp: {
      struct expty test = transExp(venv, tenv, a->u.iff.test, level, tl);
      if(test.ty->kind != Ty_int){
        EM_error(a->u.iff.test->pos, "integer required");
      }
      struct expty then = transExp(venv, tenv, a->u.iff.then, level, tl);
      if(a->u.iff.elsee){
        struct expty elsee = transExp(venv, tenv, a->u.iff.elsee, level, tl);
        if(checkSameType(then.ty, elsee.ty)){
          return expTy(Tr_IfThenElse(test.exp, then.exp, elsee.exp), then.ty);
        }
        else{
          EM_error(a->pos, "then exp and else exp type mismatch");
        }
      }
      else{
        if(then.ty->kind != Ty_void){
          EM_error(a->pos, "if-then exp's body must produce no value");
        }
        return expTy(Tr_IfThen(test.exp, then.exp), Ty_Void());
      }
    } 
    case A_whileExp: {
      Temp_label done = Temp_newlabel();
      struct expty t = transExp(venv, tenv, a->u.whilee.test, level, tl);
      struct expty body = transExp(venv, tenv, a->u.whilee.body, level, done);
      if (t.ty->kind != Ty_int) {
        EM_error(a->u.whilee.test->pos, "integer required");
      }
      if (body.ty->kind != Ty_void) {
        EM_error(a->u.whilee.body->pos, "while body must produce no value");
      }
      return expTy(Tr_While(t.exp, body.exp, done), Ty_Void());
    }
    case A_forExp: {
      Temp_label done = Temp_newlabel();
      struct expty lo = transExp(venv, tenv, a->u.forr.lo, level, tl);
      struct expty hi = transExp(venv, tenv, a->u.forr.hi, level, tl);
      struct expty body;
      if (lo.ty->kind != Ty_int) {
        EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
      }
      if (hi.ty->kind != Ty_int) {
        EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
      }
      S_beginScope(venv);
      Tr_access access = Tr_allocLocal(level, a->u.forr.escape);
      S_enter(venv, a->u.forr.var, E_ROVarEntry(access, Ty_Int()));
      body = transExp(venv, venv, a->u.forr.body, level, done);
      if(body.ty->kind != Ty_void){
        EM_error(a->u.forr.body->pos, "while body must produce no value");
      }
      S_endScope(venv);
      return expTy(Tr_For(access, level, lo.exp, hi.exp, body.exp, done), Ty_Void());
    }
    case A_breakExp: {
      if (tl == NULL) {
        EM_error(a->pos, "break is not inside a loop");
        return expTy(Tr_Nop(), Ty_Void());
      } 
      else {
        return expTy(Tr_Jump(tl), Ty_Void());
      }
    }
    case A_letExp: {
      struct expty exp;
      Tr_exp e = Tr_Nop(), etmp;
      A_decList d;
      S_beginScope(venv);
      S_beginScope(tenv);
      for (d = a->u.let.decs; d; d = d->tail){
        etmp = transDec(venv, tenv, d->head, level, tl);
        if(etmp) e = Tr_Let(e, etmp);
      }
      exp = transExp(venv, tenv, a->u.let.body, level, tl);
      exp.exp = Tr_Let(e, exp.exp);
      S_endScope(tenv);
      S_endScope(venv);
      return exp;
    }
    case A_arrayExp: {
      Ty_ty ty = actual_ty(S_look(tenv, a->u.array.typ));
      if(!ty){
        EM_error(a->pos, "array type required");
        return expTy(Tr_Nop(), Ty_Int());
      }
      struct expty size = transExp(venv, tenv, a->u.array.size, level, tl);
      struct expty init = transExp(venv, tenv, a->u.array.init, level, tl);
      if(size.ty->kind != Ty_int){
        EM_error(a->u.array.size->pos, "integer required");
      }
      if(!checkSameType(init.ty, ty->u.array)){
        EM_error(a->u.array.init->pos, "type mismatch");
      }
      return expTy(Tr_Array(size.exp, init.exp), ty);
    }
  }
  assert(0);
}

struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level level, Temp_label tl)
{
  switch(v->kind) {
    case A_simpleVar: {
      E_enventry x = S_look(venv, v->u.simple);
      if(x && x->kind == E_varEntry)
        return expTy(Tr_simpleVar(x->u.var.access, level), actual_ty(x->u.var.ty));
      else EM_error(v->pos,"undefined variable %s",
        S_name(v->u.simple));
      return expTy(Tr_Nop(), Ty_Int());
    }
    case A_fieldVar: {
      struct expty var = transVar(venv, tenv, v->u.field.var, level, tl);
      if(var.ty->kind == Ty_record){
        Ty_fieldList field = var.ty->u.record;
        int idx = 0;
        for (; field; field = field->tail) {
          if (field->head->name == v->u.field.sym) {
            return expTy(Tr_fieldVar(var.exp, idx), field->head->ty);
            }
          ++idx;
        }
        EM_error(v->u.field.var->pos, "field %s doesn't exist", S_name(v->u.field.sym));
        return expTy(Tr_Nop(), Ty_Int());
      }
      else{
        EM_error(v->u.field.var->pos, "not a record type");
        return expTy(Tr_Nop(), Ty_Int());
      }
    }
    case A_subscriptVar: {
      struct expty var = transVar(venv, tenv, v->u.subscript.var, level, tl);
      if (!(var.ty->kind == Ty_array)) {
        EM_error(v->u.subscript.var->pos, "array type required");
        return expTy(Tr_Nop(), Ty_Int());
      } 
      else {
        struct expty exp = transExp(venv, tenv, v->u.subscript.exp, level, tl);
        if (exp.ty->kind != Ty_int) {
          EM_error(v->u.subscript.exp->pos, "integer required");
        }
      return expTy(Tr_subscriptVar(var.exp, exp.exp), var.ty->u.array);
    }
    }
  }
}

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList params)
{
  if(params){
    A_field param = params->head;
    Ty_ty paramty = S_look(tenv, param->typ);
    if (!paramty) {
      EM_error(param->pos, "undefined type %s", S_name(param->typ));
      paramty = Ty_Int();
    }
    paramty = actual_ty(paramty);
    return Ty_TyList(paramty, makeFormalTyList(tenv, params->tail));
  }
  else{
    return NULL;
  }
}

U_boolList makeFormalBoolList(A_fieldList l)
{
    if (l) {
        return U_BoolList(l->head->escape, makeFormalBoolList(l->tail));
    } else {
        return NULL;
    }
}

bool checkExistFunc(A_fundecList fList, S_symbol name)
{
  if(fList){
    if(fList->head->name == name){
      return 1;
    }
    else return checkExistFunc(fList->tail, name);
  }
  else if(!fList){
    return 0;
  }
}

bool checkSameName(A_nametyList l, S_symbol name)
{
    if (!l) {
        return 0;
    } else if (l->head->name == name) {
        return 1;
    } else {
        return checkSameName(l->tail, name);
    }
}

Ty_fieldList makeTyFieldList(S_table tenv, A_fieldList l)
{
    if (l) {
      Ty_ty ty = S_look(tenv, l->head->typ);
      if(!ty){
        EM_error(l->head->pos, "undefined type %s", S_name(l->head->typ));
        ty = Ty_Int();
      }
        return Ty_FieldList(Ty_Field(l->head->name, ty), makeTyFieldList(tenv, l->tail));
    } 
    else {
        return NULL;
    }
}

Ty_fieldList actual_tys(Ty_fieldList l)
{
    if (l) {
        return Ty_FieldList(Ty_Field(l->head->name, actual_ty(l->head->ty)), actual_tys(l->tail));
    } else {
        return NULL;
    }
}

Tr_exp     transDec(S_table venv, S_table tenv, A_dec d, Tr_level level, Temp_label tl)
{
  switch(d->kind) {
    case A_varDec: {
      struct expty init = transExp(venv, tenv, d->u.var.init, level, tl);
      Tr_access access = Tr_allocLocal(level, d->u.var.escape);
      if(d->u.var.typ){
        Ty_ty ty = S_look(tenv, d->u.var.typ);
        if(ty){
          ty = actual_ty(ty);
        }
        else{
          ty = Ty_Int();
        }
        if(checkSameType(init.ty, ty)){
          S_enter(venv, d->u.var.var, E_VarEntry(access, ty));
        }
        else{
          EM_error(d->pos, "type mismatch");
        }
      }
      else{
        if(init.ty->kind == Ty_nil){
          EM_error(d->pos, "init should not be nil without type specified");
        }
        else{
          S_enter(venv, d->u.var.var, E_VarEntry(access, init.ty));
        }
      }
      return Tr_Assign(Tr_simpleVar(access, level), init.exp);
    }
    case A_functionDec: {
      Temp_label fname;
      A_fundecList fList;
      A_fundec f;
      Ty_ty resultTy;
      A_fieldList l;
      Ty_tyList formalTys, t;
      U_boolList formalBools;
      E_enventry e;
      struct expty exp;
      Tr_accessList accesses;
      for(fList = d->u.function; fList; fList = fList->tail){
        f = fList->head;
        if(f->result){
          resultTy = S_look(tenv, f->result);
        }
        else{
          resultTy = Ty_Void();
        }
        formalTys = makeFormalTyList(tenv, f->params);
        if (checkExistFunc(fList->tail, f->name)) 
          EM_error(d->pos, "two functions have the same name");
        formalBools = makeFormalBoolList(fList->head->params);
        fname = Temp_newlabel();
        S_enter(venv, f->name, E_FunEntry(Tr_newLevel(level, fname, formalBools), fname, formalTys, resultTy));
      }
      for(fList = d->u.function; fList; fList = fList->tail){
        f = fList->head;
        S_beginScope(venv);
        e = S_look(venv, fList->head->name);
        t = e->u.fun.formals;
        resultTy = e->u.fun.result;
        accesses = Tr_formals(e->u.fun.level);
        for(l = f->params; l; l = l->tail, t = t->tail, accesses = accesses->tail)
          S_enter(venv, l->head->name, E_VarEntry(accesses->head, t->head));
        exp = transExp(venv, tenv, f->body, e->u.fun.level, NULL);
        if(!checkSameType(exp.ty, resultTy)){
          if (resultTy->kind == Ty_void) {
            EM_error(f->body->pos, "procedure returns value");
          } 
          else EM_error(f->body->pos, "type mismatch");
        }
        S_endScope(venv);
        Tr_procEntryExit(e->u.fun.level, exp.exp, Tr_formals(e->u.fun.level));
      }
      return Tr_Nop();
    }
    case A_typeDec: {
      A_nametyList l;
      for (l = d->u.type; l; l = l->tail) {
        S_enter(tenv, l->head->name, Ty_Name(l->head->name, NULL));
      }
      for (l = d->u.type; l; l = l->tail) {
        Ty_ty t = S_look(tenv, l->head->name);
        t->u.name.ty = transTy(tenv, l->head->ty);
      }
      for (l = d->u.type; l; l = l->tail) {
        Ty_ty t = S_look(tenv, l->head->name);
        if (t->kind == Ty_name && actual_ty(t) == t) {
          EM_error(d->pos, "illegal type cycle");
          break;
        }
      }
      return Tr_Nop();
    }
  }
}

Ty_ty transTy(         S_table tenv, A_ty a) {
  switch (a->kind) {
    case A_nameTy: {
      Ty_ty t = S_look(tenv, a->u.name);
      return t;
    }
    case A_recordTy: {
      A_fieldList l;
      Ty_fieldList tl = NULL, last_tl = NULL;
      Ty_ty ty;
      tl = makeTyFieldList(tenv, a->u.record);
      return Ty_Record(tl);
    }
    case A_arrayTy: {
      Ty_ty t = S_look(tenv, a->u.array);
      return Ty_Array(t);
    }
  }
}