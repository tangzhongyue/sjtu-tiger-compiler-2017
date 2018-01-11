#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "errormsg.h"
#include "table.h"
Temp_tempList FG_def(G_node n) {
	AS_instr info = G_nodeInfo(n);
	switch (info->kind) {
		case I_OPER:{
			return info->u.OPER.dst;
		}
		case I_MOVE:{
			return info->u.MOVE.dst;
		}
	}
	return NULL;
}

Temp_tempList FG_use(G_node n) {
	AS_instr info = G_nodeInfo(n);
	switch (info->kind) {
		case I_OPER:{
			return info->u.OPER.src;
		}
		case I_MOVE:{
			return info->u.MOVE.src;
		}
	}
	return NULL;
}

bool FG_isMove(G_node n) {
	AS_instr info = G_nodeInfo(n);
	return info->kind == I_MOVE;
}

G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f) {
  G_graph g = G_Graph();
  TAB_table labelnodes = G_empty();
  G_nodeList jumpnl = NULL;
  Temp_labelList jl = NULL;
  G_node n = NULL, last_n = NULL, jump_n = NULL;
  AS_instr inst = NULL;
  for (; il; il = il->tail) {
    inst = il->head;
    n = G_Node(g, inst);
    if(inst->kind == I_LABEL){
      TAB_enter(labelnodes, inst->u.LABEL.label, n);
    }
    else {
      if (inst->u.OPER.jumps != NULL) {
        jumpnl = G_NodeList(n, jumpnl);
      } 
    }
    if (last_n) {
      G_addEdge(last_n, n);
    }
    last_n = n;
  }
  for (; jumpnl; jumpnl = jumpnl->tail) {
    n = jumpnl->head;
    inst = G_nodeInfo(n);
    for (jl = inst->u.OPER.jumps->labels; jl; jl = jl->tail) {
      jump_n = TAB_look(labelnodes, jl->head);
      if (jump_n) {
        G_addEdge(n, jump_n);
      } else {
        EM_error(0, "fail to find node for label %s", Temp_labelstring(jl->head));
      }
    }
  }
  return g;
}
