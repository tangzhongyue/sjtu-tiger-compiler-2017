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
        tr_outermost->frame = F_newFrame(Temp_namedlabel("tigermain"), U_BoolList(0, NULL));
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

T_exp traceFuncStaticLink(Tr_level level, Tr_level targetLevel)
{
    T_exp result = F_staticLink(T_Temp(F_FP()));
    Tr_level tmp = level;
    if(targetLevel->parent!=tmp){
      while (tmp && tmp != targetLevel->parent) {
        result = T_Mem(result);
        tmp = tmp->parent;
      }
    }
    return result;
}

T_exp traceVarStaticLink(Tr_level level, Tr_level targetLevel)
{
    T_exp result = F_staticLink(T_Temp(F_FP()));
    Tr_level tmp = level;
      while (tmp && tmp != targetLevel) {
        result = T_Mem(result);
        tmp = tmp->parent;
      }
    return result;
}

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level)
{
    if (access->level == level) {
        return Tr_Ex(F_Exp(access->access, T_Temp(F_FP())));
    }
    T_exp fp = traceVarStaticLink(level, access->level);
    return Tr_Ex(F_ExpWithStaticLink(access->access, fp));
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
        l = F_externalCall("stringEqual", T_ExpList(unEx(left), T_ExpList(unEx(right), NULL)));
        r = T_Const(1);
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

Tr_exp Tr_Let(Tr_exp el, Tr_exp body){
  return Tr_Ex(T_Eseq(unNx(el), unEx(body)));
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
    return Tr_Ex(T_Eseq(T_Seq(T_Move(T_Temp(r), F_externalCall("allocRecord", T_ExpList(T_Const(F_wordSize * num), NULL))),
                                assign_field(r, num - 1, fields)), T_Temp(r)));
}

Tr_exp Tr_Array(Tr_exp size, Tr_exp init)
{
    return Tr_Ex(F_externalCall("initArray", T_ExpList(unEx(size), T_ExpList(unEx(init), NULL))));
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

Tr_exp Tr_For(Tr_access i, Tr_level lv, Tr_exp explo, Tr_exp exphi, Tr_exp body, Temp_label breaklbl) {
  Temp_label test = Temp_newlabel();
  Temp_label loopstart = Temp_newlabel();
  Temp_label done = breaklbl;
  Temp_temp limit = Temp_newtemp();
  T_exp vari = unEx(Tr_simpleVar(i, lv));

  T_stm s = T_Seq(T_Move(vari, unEx(explo)),
              T_Seq(T_Label(test),
                T_Seq(T_Move(T_Temp(limit), unEx(exphi)),
                  T_Seq(T_Cjump(T_le, vari, T_Temp(limit), loopstart, done),
                    T_Seq(T_Label(loopstart),
                      T_Seq(unNx(body),
                        T_Seq(T_Move(vari, T_Binop(T_plus, vari, T_Const(1))),
                          T_Seq(T_Jump(T_Name(test), Temp_LabelList(test, NULL)),
                            T_Label(done)))))))));
  return Tr_Nx(s);
}

Tr_exp Tr_Call(Tr_level level, Temp_label label, Tr_expList params, Tr_level now)
{
    T_expList p = NULL, q;
    Tr_expList cur = params;
    if(cur){
      q = p = T_ExpList(unEx(cur->head), NULL);
      cur = cur->tail;
    }
    while (cur) {
        q->tail = T_ExpList(unEx(cur->head), NULL);
        cur = cur->tail;
        q = q->tail;
    }
    if (level == tr_outermost) {
        return Tr_Ex(F_externalCall(Temp_labelstring(label), p));
    }
    return Tr_Ex(T_Call(T_Name(label), T_ExpList(traceFuncStaticLink(now, level), p)));
}

Tr_exp Tr_Assign(Tr_exp var, Tr_exp value)
{
    return Tr_Nx(T_Move(unEx(var), unEx(value)));
}

Tr_exp Tr_Seq(Tr_expList el)
{
  Tr_expList rel = NULL;
  for (; el; el = el->tail) {
    rel = Tr_ExpList(el->head, rel);
  }

  T_exp seq = T_Const(0);
  for (; rel; rel = rel->tail) {
    seq = T_Eseq(T_Exp(seq), unEx(rel->head));
  }
  return Tr_Ex(seq);
}

void Tr_procEntryExit(Tr_level level, Tr_exp body,
                    Tr_accessList formals) {
  T_stm stm = T_Move(T_Temp(F_RV()), unEx(body));
  F_frag frag = F_ProcFrag(stm, level->frame);
  fragList = F_FragList(frag, fragList);
}

F_fragList Tr_getResult(void) {
    return fragList;
}