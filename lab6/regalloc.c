#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "regalloc.h"
#include "table.h"
#include "flowgraph.h"
#define MAXLINE 64
static Temp_tempList L(Temp_temp h, Temp_tempList t) {
  return Temp_TempList(h, t);
}

static AS_instrList reverseInstrList(AS_instrList il) {
  AS_instrList rl = NULL;
  for (; il; il = il->tail) {
    rl = AS_InstrList(il->head, rl);
  }
  return rl;
}

static Temp_tempList inst_def(AS_instr inst) {
  switch (inst->kind) {
    case I_OPER:
      return inst->u.OPER.dst;
    case I_LABEL:
      return NULL;
    case I_MOVE:
      return inst->u.MOVE.dst;
  }
}

static Temp_tempList inst_use(AS_instr inst) {
  switch (inst->kind) {
    case I_OPER:
      return inst->u.OPER.src;
    case I_LABEL:
      return NULL;
    case I_MOVE:
      return inst->u.MOVE.src;
  }
  return NULL;
}

static G_node temp2Node(Temp_temp t, G_graph g) {
  if (t == NULL) return NULL;
  G_nodeList nodes = G_nodes(g);
  for(; nodes; nodes = nodes->tail)
    if (Live_gtemp(nodes->head)==t) return nodes->head;
  return NULL;
}

static Temp_tempList T_Union(Temp_tempList ta, Temp_tempList tb){
  Temp_temp t;
  Temp_tempList tl = NULL;
  Temp_map m = Temp_empty();
  for (; ta; ta = ta->tail) {
    t = ta->head;
    if (Temp_look(m, t) == NULL) {
      Temp_enter(m, t, "union");
      tl = L(t, tl);
    }
  }
  for (; tb; tb = tb->tail) {
    t = tb->head;
    if (Temp_look(m, t) == NULL) {
      Temp_enter(m, t, "union");
      tl = L(t, tl);
    }
  }
  return tl;
}

static bool T_InTempList(Temp_temp t, Temp_tempList tl) {
  for (; tl; tl = tl->tail) {
    if (tl->head == t) {
      return TRUE;
    }
  }
  return FALSE;
}

Temp_tempList T_Intersect(Temp_tempList ta, Temp_tempList tb) {
  Temp_temp t;
  Temp_tempList tl = NULL;
  Temp_map m = Temp_empty();
  for (; ta; ta = ta->tail) {
    if(T_InTempList(ta->head, tb)){
      tl = L(ta->head, tl);
    }
  }
  return tl;
}

static bool AS_InInstrList(AS_instr i, AS_instrList il) {
  for (; il; il = il->tail) {
    if (il->head == i) {
      return TRUE;
    }
  }
  return FALSE;
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
  //your code here.
  struct RA_result ret;
  G_graph flow;
  struct Live_graph live;
  Temp_map initial;
  struct COL_result col;
  AS_instrList rewriteList;
  while (TRUE) {
    flow = FG_AssemFlowGraph(il, f);
    live = Live_liveness(flow);
    initial = F_initialRegisters(f);
    col = COL_color(live.graph, initial, F_registers(),
                    live.worklistMoves, live.moveList, live.spillCost);
    if (col.spills == NULL) {
      break;
    }
    Temp_tempList spilled = col.spills;
    rewriteList = NULL; 
    Temp_tempList tl;
    TAB_table spilledLocal = TAB_empty();
    for (tl = spilled; tl; tl = tl->tail) {
      F_access local = F_allocLocal(f, TRUE);
      TAB_enter(spilledLocal, tl->head, local);
    }
    for (; il; il = il->tail) {
      AS_instr inst = il->head;
      Temp_tempList useSpilled = T_Intersect(inst_use(inst), spilled);
      Temp_tempList defSpilled = T_Intersect(inst_def(inst), spilled);
      Temp_tempList tempSpilled = T_Union(useSpilled, defSpilled);
      if (tempSpilled == NULL) {
        rewriteList = AS_InstrList(inst, rewriteList);
      }
      else{
        for (tl = useSpilled; tl; tl = tl->tail) {
          char buf[MAXLINE];
          Temp_temp temp = tl->head;
          F_access local = (F_access)TAB_look(spilledLocal, temp);
          sprintf(buf, "movl %d(`s0), `d0 \n", F_accessOffset(local));
          rewriteList = AS_InstrList(
            AS_Oper(String(buf), L(temp, NULL), L(F_FP(), NULL), AS_Targets(NULL)), rewriteList);
        }
        rewriteList = AS_InstrList(inst, rewriteList);
        for (tl = defSpilled; tl; tl = tl->tail) {
          char buf[MAXLINE];
          Temp_temp temp = tl->head;
          F_access local = (F_access)TAB_look(spilledLocal, temp);
          sprintf(buf, "movl `s0, %d(`s1) \n", F_accessOffset(local));
          rewriteList = AS_InstrList(
            AS_Oper(String(buf), NULL, L(temp, L(F_FP(), NULL)), AS_Targets(NULL)), rewriteList);
        }
      }
    }
    il = reverseInstrList(rewriteList);
  }
  if (col.coalescedMoves != NULL) {
    rewriteList = NULL;
    for (; il; il = il->tail) {
      AS_instr inst = il->head;
      if (!AS_InInstrList(inst, col.coalescedMoves)) {
        rewriteList = AS_InstrList(inst, rewriteList);
      }
    }
    il = reverseInstrList(rewriteList);
  }
  ret.coloring = col.coloring;
  ret.il = il;
  return ret;
}
