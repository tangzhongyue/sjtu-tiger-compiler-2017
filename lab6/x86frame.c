#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"
#define MAXLINE 64
/*Lab5: Your implementation here.*/
//varibales
struct F_access_ {
  enum {inFrame, inReg} kind;
  union {
    int offset; //inFrame
    Temp_temp reg; //inReg
  } u;
};

struct F_frame_ {
  Temp_label name;
  Temp_map temp;
  F_accessList formals;
  F_accessList locals;
};

Temp_map F_tempMap = NULL;

const int F_wordSize = 4;

static Temp_temp eax = NULL;
static Temp_temp ebx = NULL;
static Temp_temp ecx = NULL;
static Temp_temp edx = NULL;
static Temp_temp esi = NULL;
static Temp_temp edi = NULL;
static Temp_temp ebp = NULL;
static Temp_temp esp = NULL;

void F_initRegisters(void){
    ebp = Temp_newtemp();
    esp = Temp_newtemp();
    eax = Temp_newtemp();
    ebx = Temp_newtemp();
    edx = Temp_newtemp();
    ecx = Temp_newtemp();
    esi = Temp_newtemp();
    edi = Temp_newtemp();
}

Temp_temp F_SP(void)
{
    if (!esp) {
        F_initRegisters();
    }
    return esp;
}

Temp_temp F_FP(void)
{
    if (!ebp) {
        F_initRegisters();
    }
    return ebp;
}

Temp_temp F_RV(void)
{
    if (!eax) {
        F_initRegisters();
    }
    return eax;
}

Temp_temp F_EAX(void)
{
    if (!eax) {
        F_initRegisters();
    }
    return eax;
}

Temp_temp F_EBX(void)
{
    if (!ebx) {
        F_initRegisters();
    }
    return ebx;
}

Temp_temp F_ECX(void)
{
    if (!ecx) {
        F_initRegisters();
    }
    return ecx;
}

Temp_temp F_EDX(void)
{
    if (!edx) {
        F_initRegisters();
    }
    return edx;
}

Temp_temp F_ESI(void)
{
    if (!esi) {
        F_initRegisters();
    }
    return esi;
}

Temp_temp F_EDI(void)
{
    if (!edi) {
        F_initRegisters();
    }
    return edi;
}

Temp_map F_initialRegisters(F_frame f) {
  Temp_map m = Temp_empty();
  Temp_enter(m, ebp, "%ebp");
  Temp_enter(m, esp, "%esp");
  Temp_enter(m, eax, "%eax");
  Temp_enter(m, ecx, "%ecx");
  Temp_enter(m, edx, "%edx");
  Temp_enter(m, ebx, "%ebx");
  Temp_enter(m, esi, "%esi");
  Temp_enter(m, edi, "%edi");
  return m;
}

Temp_tempList F_registers(void){
    return Temp_TempList(F_EAX(),
                       Temp_TempList(F_EBX(),
                       Temp_TempList(F_ECX(),
                       Temp_TempList(F_EDX(),
                       Temp_TempList(F_ESI(),
                       Temp_TempList(F_EDI(),NULL))))));
}

static F_access InFrame(int offset)
{
  F_access inframe = checked_malloc(sizeof(*inframe));
    inframe->kind = inFrame;
    inframe->u.offset = offset;
    return inframe;
}

static F_access InReg(Temp_temp reg)
{
  F_access inreg = checked_malloc(sizeof(*inreg));
    inreg->kind = inReg;
    inreg->u.reg = reg;
    return inreg;
}

Temp_tempList F_callersaves(void) {
  if (ebp == NULL) {
    F_initRegisters();
  }
  return Temp_TempList(edx,
              Temp_TempList(ecx, NULL));
}

Temp_tempList F_calleesaves(void) {
  if (ebp == NULL) {
    F_initRegisters();
  }
  return Temp_TempList(ebx,
            Temp_TempList(esi,
              Temp_TempList(edi, NULL)));
}

F_access F_allocLocal(F_frame f, bool escape) {
  if (escape == FALSE) {
    F_access l = InReg(Temp_newtemp());
    f->locals = F_AccessList(l, f->locals);
    return l;
  }
  int offset = -16;
  F_accessList locals = f->locals;
  while (locals != NULL) {
    if (locals->head->kind == inFrame)
      offset -= 4;
    locals = locals->tail;
  }
  F_access l = InFrame(offset);
  f->locals = F_AccessList(l, f->locals);
  return l;
}

F_frame F_newFrame(Temp_label name, U_boolList formals) {
  F_frame f = checked_malloc(sizeof(*f));
  f->name = name;
  int offset = 8;
  U_boolList formalEscape = formals;
  F_accessList formal = NULL;
  while (formalEscape) {
    offset += 4;
    formal = F_AccessList(InFrame(offset), formal);
    formalEscape = formalEscape->tail;
  }
  f->formals = formal;
  f->locals = NULL;
  f->temp = Temp_empty(); 
  return f;
}

F_accessList F_AccessList(F_access head, F_accessList tail)
{
  F_accessList l = checked_malloc(sizeof(*l));
    l->head = head;
    l->tail = tail;
    return l;
}

T_exp F_Exp(F_access access, T_exp fp)
{
    if(access->kind == inFrame){
        return T_Mem(T_Binop(T_plus, fp, T_Const(access->u.offset)));
    }
    else{
        return T_Temp(access->u.reg);
    }
}

int F_accessOffset(F_access a) {
  return a->u.offset;
}

T_exp F_ExpWithStaticLink(F_access acc, T_exp staticLink) {
  if (acc->kind == inReg) {
    return T_Temp(acc->u.reg);
  }
  return T_Mem(T_Binop(T_plus, staticLink, T_Const(acc->u.offset - 8)));
}

T_exp F_staticLink(T_exp framePtr) {
  return T_Binop(T_plus, framePtr, T_Const(2 * F_wordSize));
}

F_accessList F_formals(F_frame f)
{
    return f->formals;
}

Temp_label F_name(F_frame f)
{
    return f->name;
}

T_exp F_externalCall(string s, T_expList args) 
{
    return T_Call(T_Name(Temp_namedlabel(s)), args);
}

F_frag F_StringFrag(Temp_label label, string str) 
{   
    F_frag stringfrag = checked_malloc(sizeof(*stringfrag));
    stringfrag->kind = F_stringFrag;
    stringfrag->u.stringg.label = label;
    stringfrag->u.stringg.str = str;
    return stringfrag;            
}                                                     
                                                      
F_frag F_ProcFrag(T_stm body, F_frame frame) 
{        
  F_frag procfrag = checked_malloc(sizeof(*procfrag));
    procfrag->kind = F_procFrag;
    procfrag->u.proc.body = body;
    procfrag->u.proc.frame = frame;
    return procfrag;                           
}                                                     
                                                      
F_fragList F_FragList(F_frag head, F_fragList tail) { 
  F_fragList fraglist = checked_malloc(sizeof(*fraglist)); 
    fraglist->head = head;
    fraglist->tail = tail;
    return fraglist;                              
}                                                     

static Temp_tempList L(Temp_temp h, Temp_tempList t) {
  return Temp_TempList(h, t);
}

static int frameSize(F_frame f) {
  int size = 12;
  F_accessList locals = f->locals;
  while (locals != NULL) {
    if (locals->head->kind == inFrame)
      size += 4;
    locals = locals->tail;
  }
  return size;
}

static AS_instrList pushCalleeSave(AS_instrList il) {
  Temp_tempList calleesaves = Temp_TempList(edi, Temp_TempList(esi, Temp_TempList(ebx, NULL)));
  AS_instrList ail = il;
  for (; calleesaves; calleesaves = calleesaves->tail) {
    ail = AS_InstrList(
            AS_Oper("pushl `s0", L(F_SP(), NULL), L(calleesaves->head, NULL), NULL), ail);
  }
  return ail;
}

static AS_instrList popCalleeSave(AS_instrList il) {
  Temp_tempList calleesaves = F_calleesaves();
  AS_instrList ail = NULL;
  for (; calleesaves; calleesaves = calleesaves->tail) {
    ail = AS_InstrList(
            AS_Oper("popl `s0", L(F_SP(), NULL), L(calleesaves->head, NULL), NULL), ail);
  }
  return AS_splice(ail, il);
}

AS_instrList F_procEntryExit2(F_frame frame, AS_instrList body) {
  char *add = checked_malloc(MAXLINE);
  int frame_size = frameSize(frame);
  sprintf(add, "addl $%d, `s0", frame_size);
  return AS_splice(body, 
          AS_InstrList(AS_Oper(add, L(F_SP(), NULL), L(F_SP(), NULL), AS_Targets(NULL)),
            popCalleeSave(
              AS_InstrList(AS_Oper("leave", NULL, NULL, AS_Targets(NULL)),
                AS_InstrList(AS_Oper("ret", NULL, NULL, AS_Targets(NULL)), NULL)))));
}

AS_proc F_procEntryExit3(F_frame frame, AS_instrList body) {
  char *sub = checked_malloc(MAXLINE);
  int frame_size = frameSize(frame);
  sprintf(sub, "subl $%d, `s0", frame_size);
  body = AS_InstrList(AS_Label(S_name(frame->name), frame->name),
            AS_InstrList(AS_Oper("pushl `s0", L(F_FP(), L(F_SP(), NULL)), L(F_FP(), NULL), AS_Targets(NULL)),
              AS_InstrList(AS_Move("movl `s0, `d0", L(F_FP(), NULL), L(F_SP(), NULL)),
                pushCalleeSave(
                    AS_InstrList(AS_Oper(sub, L(F_SP(), NULL), L(F_SP(), NULL), AS_Targets(NULL)),
                      body)))));
  return AS_Proc("#BEGIN FUNCTION", body, "#END FUNCTION");
}