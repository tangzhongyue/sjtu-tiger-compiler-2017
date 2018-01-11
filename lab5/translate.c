#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"

//LAB5: you can modify anything you want.

struct Tr_access_ {
	Tr_level level;
	F_access access;
};

struct Tr_level_ {
	F_frame frame;
	Tr_level parent;
    Tr_accessList formals;
};

typedef struct patchList_ *patchList;
struct patchList_ 
{
	Temp_label *head; 
	patchList tail;
};

struct Cx 
{
	patchList trues; 
	patchList falses; 
	T_stm stm;
};

struct Tr_exp_ {
	enum {Tr_ex, Tr_nx, Tr_cx} kind;
	union {T_exp ex; T_stm nx; struct Cx cx; } u;
};

struct Tr_expList_ {
	Tr_exp head;
	Tr_expList tail;	
};

static patchList PatchList(Temp_label *head, patchList tail)
{
	patchList list;

	list = (patchList)checked_malloc(sizeof(struct patchList_));
	list->head = head;
	list->tail = tail;
	return list;
}

void doPatch(patchList tList, Temp_label label)
{
	for(; tList; tList = tList->tail)
		*(tList->head) = label;
}

patchList joinPatch(patchList first, patchList second)
{
	if(!first) return second;
	for(; first->tail; first = first->tail);
	first->tail = second;
	return first;
}

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail)
{
	Tr_expList tr_expList = checked_malloc(sizeof(*tr_expList));
    tr_expList->head = head;
    tr_expList->tail = tail;
    return tr_expList;
}

Tr_access Tr_Access(Tr_level level, F_access access)
{
    Tr_access tr_access = checked_malloc(sizeof(*tr_access ));
    tr_access ->level = level;
    tr_access ->access = access;
    return tr_access ;
}

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail)
{
    Tr_accessList tr_accessList = checked_malloc(sizeof(*tr_accessList));
    tr_accessList->head = head;
    tr_accessList->tail = tail;
    return tr_accessList;
}

static Tr_level tr_outermost = NULL;
static F_fragList fragList;

Tr_accessList makeTrAccessList(Tr_level level, F_accessList formals)
{
    if (formals) {
        return Tr_AccessList(Tr_Access(level, formals->head), makeTrAccessList(level, formals->tail));
    } else {
        return NULL;
    }
}

Tr_level Tr_outermost(void)
{
	if(tr_outermost){
		return tr_outermost;
	}
	else{
		tr_outermost = checked_malloc(sizeof(*tr_outermost));
        tr_outermost->parent = NULL;
        tr_outermost->frame = F_newFrame(Temp_newlabel(), U_BoolList(1, NULL));
        tr_outermost->formals = makeTrAccessList(tr_outermost, F_formals(tr_outermost->frame)->tail);
        return tr_outermost;
	}
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals)
{
    Tr_level newlevel = checked_malloc(sizeof(*newlevel));
    newlevel->parent = parent;
    newlevel->frame = F_newFrame(name, U_BoolList(1, formals));
    newlevel->formals = makeTrAccessList(newlevel, F_formals(newlevel->frame)->tail); 
    return newlevel;
}

Tr_accessList Tr_formals(Tr_level level)
{
	return level->formals;
}

Tr_access Tr_allocLocal(Tr_level level, bool escape)
{
	return Tr_Access(level, F_allocLocal(level->frame, escape));
}

static Tr_exp Tr_Ex(T_exp ex)
{
	Tr_exp trex = checked_malloc(sizeof(*ex));
    trex->kind = Tr_ex;
    trex->u.ex = ex;
    return trex;
}

static Tr_exp Tr_Nx(T_stm nx)
{
	Tr_exp trnx = checked_malloc(sizeof(*nx));
    trnx->kind = Tr_nx;
    trnx->u.nx = nx;
    return trnx;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm)
{
	Tr_exp cx = checked_malloc(sizeof(*cx));
    cx->kind = Tr_cx;
    cx->u.cx.trues = trues;
    cx->u.cx.falses = falses;
    cx->u.cx.stm = stm;
    return cx;
}

static T_exp unEx(Tr_exp e)
{
	switch(e->kind) {
        case Tr_ex:
            return e->u.ex;
        case Tr_cx:
            {
                Temp_temp r = Temp_newtemp();
                Temp_label t = Temp_newlabel(), f = Temp_newlabel();
                doPatch(e->u.cx.trues, t);
                doPatch(e->u.cx.falses, f);
                return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
                           T_Eseq(e->u.cx.stm,
                               T_Eseq(T_Label(f),
                                   T_Eseq(T_Move(T_Temp(r), T_Const(0)),
                                       T_Eseq(T_Label(t), 
                                                T_Temp(r))))));
            }
        case Tr_nx:
            return T_Eseq(e->u.nx, T_Const(0));
    }
    assert(0); /* can't get here */
}

static T_stm unNx(Tr_exp e)
{
	switch(e->kind) {
        case Tr_ex:
            return T_Exp(e->u.ex);
        case Tr_cx:
			{
                Temp_label l = Temp_newlabel();
                doPatch(e->u.cx.trues, l);
                doPatch(e->u.cx.falses, l);
                return T_Seq(e->u.cx.stm, T_Label(l));
            }
        case Tr_nx:
            return e->u.nx;;
    }
    assert(0); /* can't get here */
}

static struct Cx unCx(Tr_exp e)
{
	switch(e->kind) {
        case Tr_ex:
        {
        	struct Cx cx;
            cx.stm = T_Cjump(T_ne, unEx(e), T_Const(0), NULL, NULL);
            cx.trues = PatchList(&(cx.stm->u.CJUMP.true), NULL);
            cx.falses = PatchList(&(cx.stm->u.CJUMP.false), NULL);
            return cx;
        }
        case Tr_cx:
            return e->u.cx;
        case Tr_nx:
            ;
    }
    assert(0); /* can't get here */
}

T_exp traceStaticLink(Tr_level level, Tr_level targetLevel)
{
    T_exp result = T_Temp(F_FP());
    Tr_level tmp = level;
    while (tmp && tmp != targetLevel) {
        result = F_Exp(F_formals(tmp->frame)->head, result);
        tmp = tmp->parent;
    }
    return result;
}

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level)
{
    T_exp fp = traceStaticLink(level, access->level);
    return Tr_Ex(F_Exp(access->access, fp));
}

Tr_exp Tr_fieldVar(Tr_exp addr, int off)
{
    return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(addr), T_Const(off * F_wordSize))));
}

Tr_exp Tr_subscriptVar(Tr_exp addr, Tr_exp off)
{
    return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(addr), T_Binop(T_mul, unEx(off), T_Const(F_wordSize)))));
}

Tr_exp Tr_Nop()
{
    return Tr_Ex(T_Const(0));
}

Tr_exp Tr_Nil()
{
    return Tr_Ex(T_Const(0));
}

Tr_exp Tr_Int(int v)
{
    return Tr_Ex(T_Const(v));
}

Tr_exp Tr_OpArithm(A_oper oper, Tr_exp left, Tr_exp right)
{
    T_binOp op;
    switch (oper) {
        case A_plusOp:
            op = T_plus;
            break;
        case A_minusOp:
            op = T_minus;
            break;
        case A_timesOp:
            op = T_mul;
            break;
        case A_divideOp:
            op = T_div;
            break;
    }
    return Tr_Ex(T_Binop(op, unEx(left), unEx(right)));
}

Tr_exp Tr_OpCmp(A_oper oper, Tr_exp left, Tr_exp right, int isStr)
{
    T_exp l;
    T_exp r;
    T_relOp op;
    struct Cx tmp;
    if (isStr) {
        l = F_externalCall("StrCmp", T_ExpList(unEx(left), T_ExpList(unEx(right), NULL)));
        r = T_Const(0);
    } else {
        l = unEx(left);
        r = unEx(right);
    }
    switch (oper) {
        case A_eqOp:
            op = T_eq;
            break;
        case A_neqOp:
            op = T_ne;
            break;
        case A_ltOp:
            op = T_lt;
            break;
        case A_gtOp:
            op = T_gt;
            break;
        case A_leOp:
            op = T_le;
            break;
        case A_geOp:
            op = T_ge;
            break;
    }
    tmp.stm = T_Cjump(op, l, r, NULL, NULL);
    tmp.trues = PatchList(&(tmp.stm->u.CJUMP.true), NULL);
    tmp.falses = PatchList(&(tmp.stm->u.CJUMP.false), NULL);
    return Tr_Cx(tmp.trues, tmp.falses, tmp.stm);
}

Tr_exp Tr_IfThen(Tr_exp test, Tr_exp then)
{
    Temp_label t = Temp_newlabel();
    Temp_label f = Temp_newlabel();
    struct Cx cx = unCx(test);
    doPatch(cx.trues, t);
    doPatch(cx.falses, f);
    return Tr_Nx(T_Seq(cx.stm, T_Seq(T_Label(t), T_Seq(unNx(then), T_Label(f)))));
}

Tr_exp Tr_IfThenElse(Tr_exp test, Tr_exp then, Tr_exp elsee)
{
    Temp_label t = Temp_newlabel();
    Temp_label f = Temp_newlabel();
    Temp_temp r = Temp_newtemp();
    Temp_label join = Temp_newlabel();
    struct Cx cx = unCx(test);
    doPatch(cx.trues, t);
    doPatch(cx.falses, f);
    return Tr_Ex(T_Eseq(cx.stm, 
        T_Eseq(T_Label(t), 
            T_Eseq(T_Move(T_Temp(r), unEx(then)), 
                T_Eseq(T_Jump(T_Name(join), Temp_LabelList(join, NULL)),
                    T_Eseq(T_Label(f),
                        T_Eseq(T_Move(T_Temp(r), unEx(elsee)),
                            T_Eseq(T_Jump(T_Name(join), Temp_LabelList(join, NULL)),
                                T_Eseq(T_Label(join), T_Temp(r))))))))));
}

Tr_exp Tr_String(string s)
{
    Temp_label lab = Temp_newlabel();
    F_frag strfrag = F_StringFrag(lab, s);
    fragList = F_FragList(strfrag, fragList);
    return Tr_Ex(T_Name(lab));
}

T_stm assign_field(Temp_temp r, int num, Tr_expList fields)
{
    if (fields) {
        return T_Seq(T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(F_wordSize * num))), unEx(fields->head)),
                assign_field(r, num - 1, fields->tail));
    } else {
        return T_Exp(T_Const(0));
    }
}

Tr_exp Tr_Record(int num, Tr_expList fields)
{
    Temp_temp r = Temp_newtemp();
    return Tr_Ex(T_Eseq(T_Seq(T_Move(T_Temp(r), F_externalCall("Malloc", T_ExpList(T_Const(F_wordSize * num), NULL))),
                                assign_field(r, num, fields)), T_Temp(r)));
}

Tr_exp Tr_Array(Tr_exp size, Tr_exp init)
{
    Temp_temp r = Temp_newtemp();
    Temp_temp i = Temp_newtemp();
    Temp_temp limit = Temp_newtemp();
    Temp_temp v = Temp_newtemp();
    Temp_label t = Temp_newlabel();
    Temp_label b = Temp_newlabel();
    Temp_label done = Temp_newlabel();
    return Tr_Ex(T_Eseq(T_Seq(T_Move(T_Temp(limit), unEx(size)),
                T_Seq(T_Move(T_Temp(v), unEx(init)),
                        T_Seq(T_Move(T_Temp(r), F_externalCall("Malloc", T_ExpList(T_Binop(T_mul, T_Temp(limit), T_Const(F_wordSize)), NULL))),
                            T_Seq(T_Move(T_Temp(i), T_Const(0)),
                                T_Seq(T_Label(t),
                                    T_Seq(T_Cjump(T_lt, T_Temp(i), T_Temp(limit), b, done),
                                        T_Seq(T_Label(b),
                                            T_Seq(T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Binop(T_mul, T_Temp(i), T_Const(F_wordSize)))), T_Temp(v)),
                                                T_Seq(T_Move(T_Temp(i), T_Binop(T_plus, T_Temp(i), T_Const(1))),
                                                    T_Seq(T_Jump(T_Name(t), Temp_LabelList(t, NULL)),
                                                        T_Label(done)
                                                            )))))))))), T_Temp(r)));
}

Tr_exp Tr_Jump(Temp_label l)
{
    return Tr_Nx(T_Jump(T_Name(l), Temp_LabelList(l, NULL)));
}

Tr_exp Tr_While(Tr_exp test, Tr_exp body, Temp_label done)
{
    Temp_label t = Temp_newlabel();
    Temp_label b = Temp_newlabel();
    struct Cx cx = unCx(test);
    doPatch(cx.trues, b);
    doPatch(cx.falses, done);
    return Tr_Nx(T_Seq(T_Label(t),
                T_Seq(cx.stm,
                    T_Seq(T_Label(b),
                        T_Seq(unNx(body),
                            T_Seq(T_Jump(T_Name(t), Temp_LabelList(t, NULL)),
                                T_Label(done)))))));
}

Tr_exp Tr_For(Tr_access access, Tr_level level, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done)
{
    Tr_exp i = Tr_simpleVar(access, level);
    Temp_temp limit = Temp_newtemp();
    Temp_label b = Temp_newlabel();
    Temp_label inc = Temp_newlabel();
    return Tr_Nx(T_Seq(T_Move(unEx(i), unEx(lo)),
                T_Seq(T_Move(T_Temp(limit), unEx(hi)),
                    T_Seq(T_Cjump(T_gt, unEx(i), T_Temp(limit), done, b),
                        T_Seq(T_Label(b),
                            T_Seq(unNx(body),
                                T_Seq(T_Cjump(T_eq, unEx(i), T_Temp(limit), done, inc),
                                    T_Seq(T_Label(inc),
                                        T_Seq(T_Move(unEx(i), T_Binop(T_plus, unEx(i), T_Const(1))),
                                            T_Seq(T_Jump(T_Name(b), Temp_LabelList(b, NULL)),
                                                T_Label(done)))))))))));
}

Tr_exp Tr_Call(Tr_level level, Temp_label label, Tr_expList params, Tr_level now)
{
    T_expList p = NULL;
    Tr_expList cur = params;
    while (cur) {
        p = T_ExpList(unEx(cur->head), p);
        cur = cur->tail;
    }
    return Tr_Ex(T_Call(T_Name(label), T_ExpList(traceStaticLink(now, level->parent), p)));
}

Tr_exp Tr_Assign(Tr_exp var, Tr_exp value)
{
    return Tr_Nx(T_Move(unEx(var), unEx(value)));
}

Tr_exp Tr_Seq(Tr_exp seq, Tr_exp e)
{
    return Tr_Ex(T_Eseq(unNx(seq), unEx(e)));
}

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals)
{
    F_frag frag = F_ProcFrag(NULL, NULL);
    fragList = F_FragList(frag, fragList);
}

F_fragList Tr_getResult(void) {
    return fragList;
}