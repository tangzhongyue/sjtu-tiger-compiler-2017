#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "helper.h"
#include "env.h"
#include "semant.h"

/*Lab4: Your implementation of lab4*/


typedef void* Tr_exp;
struct expty 
{
	Tr_exp exp; 
	Ty_ty ty;
};

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
	if(arg->kind == Ty_array){
		return arg == formal;
	}
	else if(arg->kind == Ty_record){
		return arg == formal || formal->kind == Ty_nil;
	}
	else if(arg->kind == Ty_nil){
		return arg == formal || formal->kind == Ty_record;
	}
	else{
		return arg->kind == formal->kind;
	}
}

//In Lab4, the first argument exp should always be **NULL**.
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}

void SEM_transProg(A_exp exp){
    transExp(E_base_venv(), E_base_tenv(), exp);
}

struct expty transExp(S_table venv, S_table tenv, A_exp a)
{
	switch(a->kind) {
		case A_varExp:
			return transVar(venv, tenv, a->u.var);
		case A_nilExp:
			return expTy(NULL, Ty_Nil());
		case A_intExp:
			return expTy(NULL, Ty_Int());
		case A_stringExp:
			return expTy(NULL, Ty_String());
		case A_callExp: {
			A_expList args = a->u.call.args;
			E_enventry fun = S_look(venv, a->u.call.func);
			struct expty exparg;
			if(fun && fun->kind == E_funEntry) {
				Ty_tyList formals = fun->u.fun.formals;
				for(; args && formals; args = args->tail, formals = formals->tail){
					exparg = transExp(venv, tenv, args->head);
					if(!checkSameType(exparg.ty, formals->head)){
						EM_error(args->head->pos, "para type mismatch");
					}
				}
				if (args) {
                    EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
                }
                if (formals) {
                    EM_error(a->pos, "too few params in function %s", S_name(a->u.call.func));
                }
                return expTy(NULL, fun->u.fun.result);
                } else {
                    EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
                    return expTy(NULL, Ty_Int());
                }
			}
		case A_opExp: {
			A_oper oper = a->u.op.oper;
			struct expty left =transExp(venv, tenv, a->u.op.left);
			struct expty right =transExp(venv, tenv, a->u.op.right);
			if(oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp){
				if (left.ty->kind != Ty_int) {
                    EM_error(a->u.op.left->pos, "integer required");
                }
                if (right.ty->kind != Ty_int) {
                    EM_error(a->u.op.right->pos, "integer required");
                }
				return expTy(NULL,Ty_Int());
			}
			else if (oper == A_eqOp || oper == A_neqOp) {
                if (!checkSameType(left.ty, right.ty) || left.ty->kind == Ty_void) {
                    EM_error(a->pos, "same type required");
                }
                return expTy(NULL,Ty_Int());
            } 
            else {
                if (!(left.ty->kind == Ty_int && right.ty->kind == Ty_int)) {
                    EM_error(a->pos, "same type required");
                }
                return expTy(NULL, Ty_Int());
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
			if(ty->kind != Ty_record){
				EM_error(a->pos, "record type required");
				return expTy(NULL, Ty_Int());
			}
			tfields = ty->u.record;
			for(; fields && tfields; fields = fields->tail, tfields = tfields->tail){
				exp = transExp(venv, tenv, fields->head->exp);
				if (!(fields->head->name == tfields->head->name && checkSameType(tfields->head->ty, exp.ty))) {
                    EM_error(fields->head->exp->pos, "type mismatch");
				}
			}
			if(tfields || fields){
				EM_error(a->pos, "type mismatch");
			}
			return expTy(NULL, ty);
		}
		case A_seqExp: {
			A_expList seq = a->u.seq;
			struct expty exp;
			for(; seq; seq = seq->tail){
				exp = transExp(venv, tenv, seq->head);
			}
			return exp;
		}
		case A_assignExp: {
			struct expty var = transVar(venv, tenv, a->u.assign.var);
			struct expty exp = transExp(venv, tenv, a->u.assign.exp);
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
			return expTy(NULL, Ty_Void());
		}	
		case A_ifExp: {
			struct expty test = transExp(venv, tenv, a->u.iff.test);
			if(test.ty->kind != Ty_int){
				EM_error(a->u.iff.test->pos, "integer required");
			}
			struct expty then = transExp(venv, tenv, a->u.iff.then);
			if(a->u.iff.elsee){
				struct expty elsee = transExp(venv, tenv, a->u.iff.elsee);
				if(checkSameType(then.ty, elsee.ty)){
					return expTy(NULL, then.ty);
				}
				else{
					EM_error(a->pos, "then exp and else exp type mismatch");
				}
			}
			else{
				if(then.ty->kind != Ty_void){
					EM_error(a->pos, "if-then exp's body must produce no value");
				}
				return expTy(NULL, Ty_Void());
			}
		}	
		case A_whileExp: {
			struct expty t = transExp(venv, tenv, a->u.whilee.test);
            struct expty body = transExp(venv, tenv, a->u.whilee.body);
            if (t.ty->kind != Ty_int) {
                EM_error(a->u.whilee.test->pos, "integer required");
            }
            if (body.ty->kind != Ty_void) {
                EM_error(a->u.whilee.body->pos, "while body must produce no value");
            }
			return expTy(NULL, Ty_Void());
		}
		case A_forExp: {
			struct expty lo = transExp(venv, tenv, a->u.forr.lo);
			struct expty hi = transExp(venv, tenv, a->u.forr.hi);
			struct expty body;
			if (lo.ty->kind != Ty_int) {
                    EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
            }
            if (hi.ty->kind != Ty_int) {
                    EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
            }
            S_beginScope(venv);
            S_enter(venv, a->u.forr.var, E_ROVarEntry(Ty_Int()));
            body = transExp(venv, venv, a->u.forr.body);
            if(body.ty->kind != Ty_void){
            	EM_error(a->u.forr.body->pos, "while body must produce no value");
            }
            S_endScope(venv);
            return expTy(NULL, Ty_Void());
		}
		case A_breakExp:
			return expTy(NULL, Ty_Void());
		case A_letExp: {
			struct expty exp;
			A_decList d;
			S_beginScope(venv);
			S_beginScope(tenv);
			for (d = a->u.let.decs; d; d = d->tail)
				transDec(venv, tenv, d->head);
			exp = transExp(venv, tenv, a->u.let.body);
			S_endScope(tenv);
			S_endScope(venv);
			return exp;
		}
		case A_arrayExp: {
			Ty_ty ty = S_look(tenv, a->u.array.typ);
			if(!ty){
				EM_error(a->pos, "array type required");
				return expTy(NULL, Ty_Int());
			}
			struct expty size = transExp(venv, tenv, a->u.array.size);
			struct expty init = transExp(venv, tenv, a->u.array.init);
			if(size.ty->kind != Ty_int){
				EM_error(a->u.array.size->pos, "integer required");
			}
			if(!checkSameType(init.ty, ty->u.array)){
				EM_error(a->u.array.init->pos, "type mismatch");
			}
			return expTy(NULL, ty);
		}
	}
	assert(0);
}

struct expty transVar(S_table venv, S_table tenv, A_var v)
{
	switch(v->kind) {
		case A_simpleVar: {
			E_enventry x = S_look(venv, v->u.simple);
			if(x && x->kind == E_varEntry)
				return expTy(NULL, actual_ty(x->u.var.ty));
			else EM_error(v->pos,"undefined variable %s",
				S_name(v->u.simple));
			return expTy(NULL, Ty_Int());
		}
		case A_fieldVar: {
			struct expty var = transVar(venv, tenv, v->u.field.var);
			if(var.ty->kind == Ty_record){
				Ty_fieldList field = var.ty->u.record;
				for (; field; field = field->tail) {
                    if (field->head->name == v->u.field.sym) {
                        return expTy(NULL, field->head->ty);
                    }
                }
                EM_error(v->u.field.var->pos, "field %s doesn't exist", S_name(v->u.field.sym));
				return expTy(NULL, Ty_Int());
			}
			else{
				EM_error(v->u.field.var->pos, "not a record type");
				return expTy(NULL, Ty_Int());
			}
		}
		case A_subscriptVar: {
			struct expty var = transVar(venv, tenv, v->u.subscript.var);
                if (!(var.ty->kind == Ty_array)) {
                    EM_error(v->u.subscript.var->pos, "array type required");
                    return expTy(NULL, Ty_Int());
                } 
                else {
                    struct expty exp = transExp(venv, tenv, v->u.subscript.exp);
                    if (exp.ty->kind != Ty_int) {
                    	EM_error(v->u.subscript.exp->pos, "integer required");
                    }
                return expTy(NULL, var.ty->u.array);
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

void		 transDec(S_table venv, S_table tenv, A_dec d)
{
	switch(d->kind) {
		case A_varDec: {
			struct expty init = transExp(venv, tenv, d->u.var.init);
			if(d->u.var.typ){
				Ty_ty ty = S_look(venv, d->u.var.typ);
				if(ty){
					ty = actual_ty(ty);
				}
				else{
					EM_error(d->pos, "undefined type %s", S_name(d->u.var.typ));
					ty = Ty_Int();
				}
				if(checkSameType(init.ty, ty)){
					S_enter(venv, d->u.var.var, E_VarEntry(ty));
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
					S_enter(venv, d->u.var.var, E_VarEntry(init.ty));
				}
			}
			break;
		}
		case A_functionDec: {
			A_fundecList fList;
			A_fundec f;
            Ty_ty resultTy;
            A_fieldList l;
            Ty_tyList formalTys, t;
			E_enventry e;
			struct expty exp;
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
				S_enter(venv, f->name, E_FunEntry(formalTys, resultTy));
			}
			for(fList = d->u.function; fList; fList = fList->tail){
				f = fList->head;
				S_beginScope(venv);
				e = S_look(venv, fList->head->name);
				t = e->u.fun.formals;
				resultTy = e->u.fun.result;
				for(l = f->params; l; l = l->tail, t = t->tail)
					S_enter(venv, l->head->name, E_VarEntry(t->head));
				exp = transExp(venv, tenv, f->body);
				if(!checkSameType(exp.ty, resultTy)){
					if (resultTy->kind == Ty_void) {
                        EM_error(f->body->pos, "procedure returns value");
                    } 
                    else EM_error(f->body->pos, "type mismatch");
				}
				S_endScope(venv);
			}
		}
		case A_typeDec: {
			A_nametyList l;
			for(l = d->u.type; l; l = l->tail){
				if(checkSameName(l->tail, l->head->name)) {
                    EM_error(d->pos, "two types have the same name");
                }
				S_enter(tenv, l->head->name, Ty_Name(l->head->name, NULL));
			}
			int total = 0;
            for (l = d->u.type; l; l = l->tail) {
                switch(l->head->ty->kind) {
                    case A_nameTy:{
                        Ty_ty ty = S_look(tenv, l->head->name);
                        ty->u.name.sym = l->head->ty->u.name;
                        ++total;
                        break;
                    }
                    case A_recordTy:{
						Ty_ty ty = S_look(tenv, l->head->name);
                        ty->kind = Ty_record;
                        ty->u.record = makeTyFieldList(tenv, l->head->ty->u.record);
                        break;
                    }
                    case A_arrayTy:{
						Ty_ty ty = S_look(tenv, l->head->name);                    
                        ty->kind = Ty_array;
                        ty->u.array = S_look(tenv, l->head->ty->u.array);
                        break;
                    }
                }
			}
			int count = 0;
			while (total > 0) {
                count = 0;
                for (l = d->u.type; l; l = l->tail) {
                    if (l->head->ty->kind == A_nameTy) {
                        Ty_ty ty = S_look(tenv, l->head->name);
                        if(!ty){
							EM_error(d->pos, "undefined type %s", S_name(l->head->name));
     						ty = Ty_Int();
						}
                        if (!ty->u.name.ty) {
                            Ty_ty ty2 = S_look(tenv, ty->u.name.sym);
                            if(!ty){
								EM_error(d->pos, "undefined type %s", S_name(l->head->name));
     							ty = Ty_Int();
							}
                            if (ty2->kind == Ty_name) {
                                if (ty2->u.name.ty) {
                                    ty->u.name.ty = ty2->u.name.ty;
                                } 
                                else {
                                    ++count;
                                }
                            } 
                            else {
                                ty->u.name.ty = ty2;
                            }
                        }
                    }
                }
                if (count == total) {
                    EM_error(d->pos, "illegal type cycle");
                    break;
                }
                total = count;
			}	
			for (l = d->u.type; l; l = l->tail) {
                switch(l->head->ty->kind) {
                    case A_recordTy: {
                        Ty_ty ty = S_look(tenv, l->head->name);
                        if(!ty){
							EM_error(d->pos, "undefined type %s", S_name(l->head->name));
     						ty = Ty_Int();
						}
                        ty->u.record = actual_tys(ty->u.record);
                        break;
                    }
                    case A_arrayTy: {
                        Ty_ty ty = S_look(tenv, l->head->name);
                        if(!ty){
							EM_error(d->pos, "undefined type %s", S_name(l->head->name));
     						ty = Ty_Int();
						}
                        ty->u.array = actual_ty(ty->u.array);
                        break;
                    }
                }
            }
		}
	}
}

