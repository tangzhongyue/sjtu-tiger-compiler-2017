#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"

//Lab 6: put your code here
#define MAXLINE 64
static AS_instrList iList = NULL, last = NULL;
static void emit(AS_instr inst){
	if(last)
		last = last->tail = AS_InstrList(inst, NULL);
	else last = iList = AS_InstrList(inst, NULL);
}

static Temp_temp munchExp(T_exp e);
static void munchStm(T_stm s);
Temp_tempList L(Temp_temp h, Temp_tempList t){return Temp_TempList(h, t);}

static void munchStm(T_stm s){
	char *a = checked_malloc(MAXLINE);	
	switch(s->kind) {
		case T_MOVE: {
			T_exp dst = s->u.MOVE.dst, src = s->u.MOVE.src;		
			Temp_temp ts = munchExp(src);
			Temp_temp d;
			int offset;		
			if(dst->kind == T_MEM) {
				if(dst->u.MEM->kind == T_BINOP
					&& dst->u.MEM->u.BINOP.op == T_plus){
					if(dst->u.MEM->u.BINOP.left->kind == T_CONST){
						d = munchExp(dst->u.MEM->u.BINOP.right);
						offset = dst->u.MEM->u.BINOP.left->u.CONST;
						sprintf(a, "movl `s0, %d(`s1)", offset);
						emit(AS_Oper(a, NULL, L(ts, L(d, NULL)), AS_Targets(NULL)));
					}
					else if(dst->u.MEM->u.BINOP.right->kind == T_CONST){
						d = munchExp(dst->u.MEM->u.BINOP.left);
						offset = dst->u.MEM->u.BINOP.right->u.CONST;
						sprintf(a, "movl `s0, %d(`s1)", offset);
						emit(AS_Oper(a, NULL, L(ts, L(d, NULL)), AS_Targets(NULL)));
					}
					else{
						d = munchExp(dst->u.MEM);
						sprintf(a, "movl `s0, (`s1)");
						emit(AS_Oper(a, NULL, L(ts, L(d, NULL)), AS_Targets(NULL)));
					}
					
				}
				else {
					d = munchExp(dst->u.MEM);
					sprintf(a, "movl `s0, (`s1)");
					emit(AS_Oper(a, NULL, L(ts, L(d, NULL)), AS_Targets(NULL)));
				}
			}
			else if(dst->kind == T_TEMP){
				d = dst->u.TEMP;
				sprintf(a, "movl `s0, `d0");
				emit(AS_Move(a, L(d, NULL), L(ts, NULL)));
			}
			break;
		}
		case T_JUMP: {
			sprintf(a, "jmp %s", Temp_labelstring(s->u.JUMP.exp->u.NAME));
			emit(AS_Oper(a, NULL, NULL, AS_Targets(s->u.JUMP.jumps)));
			break;
		}
		case T_CJUMP: {
			Temp_temp l = munchExp(s->u.CJUMP.left), r = munchExp(s->u.CJUMP.right);
			emit(AS_Oper("cmpl `s0, `s1", NULL, L(r, L(l, NULL)), AS_Targets(NULL)));
			switch (s->u.CJUMP.op) {
				case T_eq:{
					sprintf(a, "je %s", Temp_labelstring(s->u.CJUMP.true));
					break;
				}
				case T_ne:{
					sprintf(a, "jne %s", Temp_labelstring(s->u.CJUMP.true));
					break;
				}
				case T_lt:{
					sprintf(a, "jl %s", Temp_labelstring(s->u.CJUMP.true));
					break;
				}
				case T_gt:{
					sprintf(a, "jg %s", Temp_labelstring(s->u.CJUMP.true));
					break;
				} 
				case T_le:{
					sprintf(a, "jle %s", Temp_labelstring(s->u.CJUMP.true));
					break;
				} 
				case T_ge:{
					sprintf(a, "jge %s", Temp_labelstring(s->u.CJUMP.true));
					break;
				}
			}
			emit(AS_Oper(a, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
			break;
		}
		case T_LABEL: {
			sprintf(a, "%s", Temp_labelstring(s->u.LABEL));
			emit(AS_Label(a, s->u.LABEL));
			break;
		}
		case T_EXP: {
			munchExp(s->u.EXP);
			break;
		}
	}
}

static void munchCallerSave() {
  Temp_tempList callerSaves = F_callersaves();
  for (; callerSaves; callerSaves = callerSaves->tail) {
    emit(AS_Oper("pushl `s0", L(F_SP(), NULL), L(callerSaves->head, NULL), NULL));
  }
}

static void munchCallerRestore(Temp_tempList tl) {
  int restoreCount = 0;
  char *a = (char *)checked_malloc(MAXLINE);
  for (; tl; tl = tl->tail) {
    ++restoreCount;
  }
  sprintf(a, "addl $%d, `s0", restoreCount * F_wordSize);
  emit(AS_Oper(a, L(F_SP(), NULL), L(F_SP(), NULL), AS_Targets(NULL)));
  emit(AS_Oper("popl `d0", L(F_ECX(), NULL), L(F_SP(), NULL), AS_Targets(NULL)));
  emit(AS_Oper("popl `d0", L(F_EDX(), NULL), L(F_SP(), NULL), AS_Targets(NULL)));
}

static Temp_tempList munchArgs(int i, T_expList args) {
  if (args == NULL) {
    return NULL;
  }
  Temp_tempList old = munchArgs(i + 1, args->tail);
  Temp_temp r = munchExp(args->head);
  emit(AS_Oper("pushl `s0", L(F_SP(), NULL), L(r, NULL), NULL));
  return Temp_TempList(r, old);
}


static Temp_temp munchExp(T_exp e){
	char *a = checked_malloc(MAXLINE);	
	switch (e->kind) {
		case T_BINOP:{
			Temp_temp l, r;
			int v;
        	Temp_temp t = Temp_newtemp();
			switch (e->u.BINOP.op) {
				case T_plus:{
					if(e->u.BINOP.left->kind == T_CONST){
						v = e->u.BINOP.left->u.CONST;
        				r = munchExp(e->u.BINOP.right);
        				emit(AS_Move("movl `s0, `d0", L(t, NULL), L(r, NULL)));
						sprintf(a, "addl $%d, `d0", v);
						emit(AS_Oper(a, L(t, NULL), L(t, NULL), AS_Targets(NULL)));
						break;
					}
					else if(e->u.BINOP.right->kind == T_CONST){
						v = e->u.BINOP.right->u.CONST;
						l = munchExp(e->u.BINOP.left);
						emit(AS_Move("movl `s0, `d0", L(t, NULL), L(l, NULL)));
						sprintf(a, "addl $%d, `d0", v);
						emit(AS_Oper(a, L(t, NULL), L(t, NULL), AS_Targets(NULL)));
						break;
					}
					l = munchExp(e->u.BINOP.left);
        			r = munchExp(e->u.BINOP.right);
					emit(AS_Move("movl `s0, `d0", L(t, NULL), L(l, NULL)));
					emit(AS_Oper("addl `s0, `d0", L(t, NULL), L(r, L(t, NULL)), AS_Targets(NULL)));
					break;
				}
				case T_minus:{
					l = munchExp(e->u.BINOP.left);
        			r = munchExp(e->u.BINOP.right);
					emit(AS_Move("movl `s0, `d0", L(t, NULL), L(l, NULL)));
					emit(AS_Oper("subl `s0, `d0", L(t, NULL), L(r, L(t, NULL)), AS_Targets(NULL)));
					break;
				}
				case T_mul:{
					l = munchExp(e->u.BINOP.left);
        			r = munchExp(e->u.BINOP.right);
					emit(AS_Move("movl `s0, `d0", L(t, NULL), L(l, NULL)));
					emit(AS_Oper("imul `s0, `d0", L(t, NULL), L(r, L(t, NULL)), AS_Targets(NULL)));
					break;
				}
				case T_div:{
					l = munchExp(e->u.BINOP.left);
        			r = munchExp(e->u.BINOP.right);
          			emit(AS_Move("movl `s0, `d0", L(F_EAX(), NULL), L(l, NULL)));
          			emit(AS_Oper("movl $0, `d0", L(F_EDX(), NULL), NULL, AS_Targets(NULL)));
              		emit(AS_Oper("divl `s0", L(F_EDX(), L(F_EAX(), NULL)), L(r, L(F_EAX(), L(F_EDX(), NULL))), AS_Targets(NULL)));
          			emit(AS_Oper("movl `s0, `d0", L(t, NULL), L(F_EAX(), NULL), AS_Targets(NULL)));
          			break;
        		}
			}
			return t;
		}
		case T_MEM:{
			Temp_temp r = Temp_newtemp(), m;
			if(e->u.MEM->kind == T_BINOP && e->u.MEM->u.BINOP.op == T_plus){	
				int c;
				if(e->u.MEM->u.BINOP.left->kind == T_CONST){
					m = munchExp(e->u.MEM->u.BINOP.right);
					c = e->u.MEM->u.BINOP.left->u.CONST;
					sprintf(a, "movl %d(`s0), `d0", c);
					emit(AS_Oper(a, L(r, NULL), L(m, NULL), AS_Targets(NULL)));
				}
				else if(e->u.MEM->u.BINOP.right->kind == T_CONST){
					m = munchExp(e->u.MEM->u.BINOP.left);
					c = e->u.MEM->u.BINOP.right->u.CONST;
					sprintf(a, "movl %d(`s0), `d0", c);
					emit(AS_Oper(a, L(r, NULL), L(m, NULL), AS_Targets(NULL)));
				}
				else {
                    m = munchExp(e->u.MEM);
                    emit(AS_Oper("movl (`s0), `d0", L(r, NULL), L(m, NULL), AS_Targets(NULL)));
                }
			}
			else{
				m = munchExp(e->u.MEM);
				emit(AS_Oper("movl (`s0), `d0", L(r, NULL), L(m, NULL), AS_Targets(NULL)));
			}
			return r;
		}
		case T_TEMP:{
			return e->u.TEMP;
		}
		case T_NAME:{
			Temp_temp r = Temp_newtemp();
			sprintf(a, "movl $%s, `d0", Temp_labelstring(e->u.NAME));
			emit(AS_Oper(a, L(r, NULL), NULL, AS_Targets(NULL)));
			return r;
		}
		case T_CONST:{
			Temp_temp r = Temp_newtemp();
			sprintf(a, "movl $%d, `d0", e->u.CONST);
			emit(AS_Oper(a, L(r, NULL), NULL, AS_Targets(NULL)));
			return r;
		}
		case T_CALL:{
			munchCallerSave();
      		Temp_label fun = e->u.CALL.fun->u.NAME;
      		Temp_temp r = Temp_newtemp();
      		Temp_tempList l = munchArgs(0, e->u.CALL.args);
      		Temp_tempList calldefs = L(F_RV(), L(F_FP(), F_callersaves()));
      		sprintf(a, "call %s", Temp_labelstring(fun));
      		emit(AS_Oper(a, calldefs, l, NULL));
      		emit(AS_Move("movl `s0, `d0", L(r, NULL), L(F_RV(), NULL)));
      		munchCallerRestore(l);
      		return r;
		}
	}
	assert(0);
}

AS_instrList F_codegen(F_frame f, T_stmList stmList) {
  AS_instrList list;
  T_stmList sl;
  for (sl = stmList; sl; sl = sl->tail) {
    munchStm(sl->head);
  }
  list = iList;
  iList = last = NULL;
  return list;
}
