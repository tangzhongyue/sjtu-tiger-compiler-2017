#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"
Temp_temp Live_gtemp(G_node n) {
  return G_nodeInfo(n);
}

static void enterLiveMap(G_table t, G_node flowNode, Temp_tempList temps) {
  G_enter(t, flowNode, temps);
}

static Temp_tempList lookupLiveMap(G_table t, G_node flownode) {
  return (Temp_tempList)G_look(t, flownode);
}

static Temp_tempList T_Union(Temp_tempList ta, Temp_tempList tb){
  Temp_temp t;
  Temp_tempList tl = NULL;
  Temp_map m = Temp_empty();
  for (; ta; ta = ta->tail) {
    t = ta->head;
    if (Temp_look(m, t) == NULL) {
      Temp_enter(m, t, "union");
      tl = Temp_TempList(t, tl);
    }
  }
  for (; tb; tb = tb->tail) {
    t = tb->head;
    if (Temp_look(m, t) == NULL) {
      Temp_enter(m, t, "union");
      tl = Temp_TempList(t, tl);
    }
  }
  return tl;
}

static Temp_tempList T_Minus(Temp_tempList ta, Temp_tempList tb){
  Temp_temp t;
  Temp_tempList tl = NULL;
  Temp_map m = Temp_empty();
  for (; tb; tb = tb->tail) {
    t = tb->head;
    Temp_enter(m, t, "minus");
  }
  for (; ta; ta = ta->tail) {
    t = ta->head;
    if (Temp_look(m, t) == NULL) {
      tl = Temp_TempList(t, tl);
    }
  }
  return tl;
}

static AS_instrList I_Union(AS_instrList ta, AS_instrList tb){
  AS_instr t;
  AS_instrList tl = NULL;
  TAB_table m = TAB_empty();
  for (; ta; ta = ta->tail) {
    t = ta->head;
    if (TAB_look(m, t) == NULL) {
      TAB_enter(m, t, "u");
      tl = AS_InstrList(t, tl);
    }
  }
  for (; tb; tb = tb->tail) {
    t = tb->head;
    if (TAB_look(m, t) == NULL) {
      TAB_enter(m, t, "u");
      tl = AS_InstrList(t, tl);
    }
  }
  return tl;
}

static bool T_Equal(Temp_tempList ta, Temp_tempList tb) {
  Temp_temp t;
  Temp_tempList tl = NULL;
  Temp_map m = Temp_empty();
  int ca = 0, cb = 0;
  for (; ta; ta = ta->tail) {
    t = ta->head;
    Temp_enter(m, t, "e");
    ++ca;
  }
  for (; tb; tb = tb->tail) {
    t = tb->head;
    if (Temp_look(m, t) == NULL) {
      return FALSE;
    }
    ++cb;
  }
  return (ca == cb);
}

static void getLiveMap(G_graph flow, G_table out) {
  G_nodeList fl, sl;
  G_node n, sn;
  G_table in = G_empty(), last_in = G_empty(), last_out = G_empty();
  Temp_tempList ci, co, li, lo;
  bool flag = TRUE;
  while (flag) {
    int i1 = 0, i2 = 0;
    for (fl = G_nodes(flow); fl; fl = fl->tail) {
      i1++;
      n = fl->head;
      li = lookupLiveMap(in, n);
      lo = lookupLiveMap(out, n);
      enterLiveMap(last_in, n, li);
      enterLiveMap(last_out, n, lo);
      ci = T_Union(FG_use(n), T_Minus(lo, FG_def(n)));
      co = NULL;
      for (sl = G_succ(n); sl; sl = sl->tail) {
        co = T_Union(co, lookupLiveMap(in, sl->head));
      }
      enterLiveMap(in, n, ci);
      enterLiveMap(out, n, co);
      if(T_Equal(li, ci) && T_Equal(lo, co)){
        i2++;
      }
    }
    if(i1 == i2) break;
  }
}

static G_node getNode(Temp_temp t, G_graph g, TAB_table tab) {
  G_node ln = (G_node)TAB_look(tab, t);
  if (ln == NULL) {
    ln = G_Node(g, t);
    TAB_enter(tab, t, ln);
  }
  return ln;
}

static void build(struct Live_graph *lg,
                          G_graph flow, G_table out) {
  G_graph g = G_Graph();
  TAB_table tab = TAB_empty();
  G_table moveList = G_empty(), spillCost = G_empty();
  G_nodeList fl;
  G_node n, ndef, nedge, move_src, move_dst, tmpn;
  Temp_tempList tdef, tout, tuse, t, tedge;
  AS_instr inst;
  AS_instrList worklistMoves = NULL;
  for (fl = G_nodes(flow); fl; fl = fl->tail) {
    n = fl->head;
    inst = G_nodeInfo(n);
    tout = lookupLiveMap(out, n);
    tdef = FG_def(n);
    tuse = FG_use(n);
    Temp_tempList defuse = T_Union(tuse, tdef);
    for (t = defuse; t; t = t->tail) {
      Temp_temp ti = t->head;
      tmpn = getNode(ti, g, tab);
      long spills = (long)G_look(spillCost, tmpn);
      ++spills;
      G_enter(spillCost, tmpn, (void *)spills);
    }
    if (FG_isMove(n)) {
      for (; defuse; defuse = defuse->tail) {
        Temp_temp t = defuse->head;
        tmpn = getNode(t, g, tab);
        AS_instrList ml = (AS_instrList)G_look(moveList, tmpn);
        ml = I_Union(ml, AS_InstrList(inst, NULL));
        G_enter(moveList, tmpn, ml);
      }
      worklistMoves = I_Union(worklistMoves, AS_InstrList(inst, NULL));
    }
    for (t = tout; t; t = t->tail) {
      ndef = getNode(t->head, g, tab);
      for (tedge = tout; tedge; tedge = tedge->tail) {
        nedge = getNode(tedge->head, g, tab);
        if (!(ndef == nedge || G_goesTo(ndef, nedge) || G_goesTo(nedge, ndef))) {
          if (!(FG_isMove(n) && nedge == move_src)) {
          G_addEdge(ndef, nedge);
          }
        }
      }
    }
  }
  lg->graph = g;
  lg->worklistMoves = worklistMoves;
  lg->moveList = moveList;
  lg->spillCost = spillCost;
}

struct Live_graph Live_liveness(G_graph flow) {
  G_table out = G_empty();
  getLiveMap(flow, out);
  struct Live_graph lg;
  build(&lg, flow, out);
  return lg;
}
