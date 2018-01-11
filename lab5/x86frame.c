#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/
Temp_temp F_FP(void)
{
    return Temp_newtemp(); 
}

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
    F_accessList formals;
    int local_cnt;
};

const int F_wordSize = 4;

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

F_access F_allocLocal(F_frame f, bool escape)
{
    if(escape){
        return InFrame(-F_wordSize * (++f->local_cnt));
    }
    else{
        return InReg(Temp_newtemp());
    }
}

F_accessList makeFAccessList(int offs, U_boolList formals) {
    if (formals) {
        return F_AccessList(InFrame(offs), makeFAccessList(offs + F_wordSize, formals->tail));
    } else {
        return NULL;
    }
}

F_frame F_newFrame(Temp_label name, U_boolList formals)
{
    F_frame f = checked_malloc(sizeof(*f));
    f->name = name;
    f->formals = makeFAccessList(F_wordSize, formals);
    f->local_cnt = 0;
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

Temp_temp F_RV(void)
{
    return Temp_newtemp(); 
}