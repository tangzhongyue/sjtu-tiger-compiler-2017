#include <stdio.h>
#include <string.h>

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
#include "table.h"

struct colordata {
  G_graph nodes;
  Temp_map precolored;
  G_nodeList initial;
  G_nodeList spillWorklist;
  G_nodeList freezeWorklist;
  G_nodeList simplifyWorklist;
  G_nodeList spilledNodes;
  G_nodeList coalescedNodes;
  G_nodeList coloredNodes;
  G_nodeList selectStack;
  AS_instrList coalescedMoves;
  AS_instrList constrainedMoves;
  AS_instrList frozenMoves;
  AS_instrList worklistMoves;
  AS_instrList activeMoves;
  G_table spillCost;
  G_table moveList;
  G_table alias;
  G_table degree;
  int K;
};

static struct colordata c;

static G_nodeList G_addNode(G_node n, G_nodeList l){
  if(!(G_inNodeList(n, l))){
    return G_NodeList(n, l);
  }
  return l;
}

static G_nodeList G_Union(G_nodeList ga, G_nodeList gb){
  G_node n;
  G_nodeList nl = NULL;
  for(; ga; ga = ga->tail){
    nl = G_addNode(ga->head, nl);
  }
  for(; gb; gb = gb->tail){
    nl = G_addNode(gb->head, nl);
  }
  return nl;
}

static G_nodeList G_Minus(G_nodeList ga, G_nodeList gb) {
  G_node n;
  G_nodeList nl = ga;
  for (; gb; gb = gb->tail) {
    nl = delete(gb->head, ga);
  }
  return nl;
}

static bool AS_InInstrList(AS_instr i, AS_instrList il) {
  for (; il; il = il->tail) {
    if (il->head == i) {
      return TRUE;
    }
  }
  return FALSE;
}

static AS_instrList AS_addInstr(AS_instr t, AS_instrList tl){
  assert(t);
  if(!AS_InInstrList(t, tl)){
    return AS_InstrList(t, tl);
  }
  return tl;
}

static AS_instrList AS_deleteInstr(AS_instr t, AS_instrList tl){
  if(!tl || !t)return NULL;
  AS_instrList tmpl = tl;
  if (t==tl->head) return tl->tail;
  else return AS_InstrList(tl->head, AS_deleteInstr(t, tl->tail));
}

static AS_instrList AS_Union(AS_instrList ta, AS_instrList tb){
  AS_instr t;
  AS_instrList tl = NULL;
  for (; ta; ta = ta->tail) {
    tl = AS_addInstr(ta->head, tl);
  }
  for (; tb; tb = tb->tail) {
    tl = AS_addInstr(tb->head, tl);
  }
  return tl;
}

static AS_instrList AS_Minus(AS_instrList ta, AS_instrList tb) {
  AS_instr t;
  AS_instrList tl = NULL;
  TAB_table m = TAB_empty();
  for (; tb; tb = tb->tail) {
    t = tb->head;
    TAB_enter(m, t, "m");
  }
  for (; ta; ta = ta->tail) {
    t = ta->head;
    if (TAB_look(m, t) == NULL) {
      tl = AS_InstrList(t, tl);
    }
  }
  return tl;
}

static AS_instrList AS_Intersect(AS_instrList ta, AS_instrList tb) {
  AS_instr t;
  AS_instrList tl = NULL;
  for (; ta; ta = ta->tail) {
    if(AS_InInstrList(ta->head, tb)){
      tl = AS_InstrList(ta->head, tl);
    }
  }
  return tl;
}

static Temp_tempList AS_Def(AS_instr inst) {
  switch (inst->kind) {
    case I_OPER:
      return inst->u.OPER.dst;
    case I_LABEL:
      return NULL;
    case I_MOVE:
      return inst->u.MOVE.dst;
  }
}

static Temp_tempList AS_Use(AS_instr inst) {
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

static Temp_tempList T_Copy(Temp_tempList regs) {
  Temp_tempList tl = NULL;
  for (; regs; regs = regs->tail) {
    tl = Temp_TempList(regs->head, tl);
  }
  return tl;
}

static Temp_tempList T_Minus(Temp_tempList ta, Temp_tempList tb) {
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

static G_node temp2Node(Temp_temp t) {
  if (!t) return NULL;
  G_nodeList nodes = G_nodes(c.nodes);
  for(nodes; nodes; nodes = nodes->tail)
    if (Live_gtemp(nodes->head) == t) return nodes->head;
  return NULL;
}

static Temp_tempList nodeL2TempL(G_nodeList nl) {
  Temp_tempList tl = NULL;
  for (; nl; nl = nl->tail) {
    tl = Temp_TempList(Live_gtemp(nl->head), tl);
  }
  return tl;
}

static Temp_temp getColor(string color, Temp_map regcolors, Temp_tempList regs) {
  for (; regs; regs = regs->tail) {
    string s = Temp_look(regcolors, regs->head);
    if (s && (strcmp(s, color) == 0)) {
      return regs->head;
    }
  }
  return NULL;
}

static int Count(Temp_tempList t) {
  int cnt = 0;
  for (; t; t = t->tail) {
    ++cnt;
  }
  return cnt;
};

static G_nodeList adjacent(G_node n) {
  G_nodeList adjn = G_adj(n);
  G_nodeList adjs = NULL;
  for (; adjn; adjn = adjn->tail) {
    adjs = G_NodeList(n, adjs);
  }
  adjs = G_Minus(adjs, G_Union(c.selectStack, c.coalescedNodes));
  return adjs;
}

static void addEdge(G_node nu, G_node nv) {
  if ((nu == nv) || G_goesTo(nu, nv) || G_goesTo(nv, nu)) return;
  G_addEdge(nu, nv);
  Temp_temp u = Live_gtemp(nu), v = Live_gtemp(nv);
  int d;
  if (Temp_look(c.precolored, u) == NULL) {
    d = (int)G_look(c.degree, nu);
    d += 1;
    G_enter(c.degree, nu, (void*)d);
  }
  if (Temp_look(c.precolored, v) == NULL) {
    d = (int)G_look(c.degree, nv);
    d += 1;
    G_enter(c.degree, nv, (void*)d);
  }
}

static AS_instrList nodeMoves(G_node n) {
  return AS_Intersect(G_look(c.moveList, n), AS_Union(c.activeMoves, c.worklistMoves));
}

static bool moveRelated(G_node n) {
  return nodeMoves(n) != NULL;
}

static void makeWorkList() {
  G_nodeList nl;
  for (nl = c.initial; nl; nl = nl->tail) {
    G_node n = nl->head;
    c.initial = delete(n, c.initial);
    if (G_degree(n) >= c.K) {
      c.spillWorklist = G_addNode(n ,c.spillWorklist);
    } 
    else if (moveRelated(n)) {
      c.freezeWorklist = G_addNode(n, c.freezeWorklist);
    } 
    else {
      c.simplifyWorklist = G_addNode(n, c.simplifyWorklist);
    }
  }
}

static void removeAdj(G_node n) {
  G_nodeList adjs = G_succ(n);
  for (; adjs; adjs = adjs->tail) {
    G_node m = adjs->head;
    G_rmEdge(n, m);
  }
  adjs = G_pred(n);
  for (; adjs; adjs = adjs->tail) {
    G_rmEdge(adjs->head, n);
  }
}

static void enableMoves(G_nodeList nl) {
  for(; nl; nl = nl->tail){
    AS_instrList il = nodeMoves(nl->head);
    for (; il; il = il->tail) {
      AS_instr m = il->head;
      if (AS_InInstrList(m, c.activeMoves)) {
        c.activeMoves = AS_deleteInstr(m, c.activeMoves);
        c.worklistMoves = AS_addInstr(m, c.worklistMoves);
      }
    }
  }
}

static void decrementDegree(G_node n) {
  int d = (int)G_look(c.degree, n);
  d -= 1;
  G_enter(c.degree, n, (void*)d);
  if (d == c.K) {
    enableMoves(G_NodeList(n, adjacent(n)));
    c.spillWorklist = delete(n , c.spillWorklist);
    if (moveRelated(n)) {
      c.freezeWorklist = G_addNode(n, c.freezeWorklist);
    } 
    else {
      c.simplifyWorklist = G_addNode(n, c.simplifyWorklist);
    }
  }
}

static void addWorkList(G_node n) {
  int degree = (int)G_look(c.degree, n);
  Temp_temp t = Live_gtemp(n);
  if (Temp_look(c.precolored, t) == NULL && (!moveRelated(n)) && (degree < c.K)) {
      c.freezeWorklist = delete(n, c.freezeWorklist);
      c.simplifyWorklist = G_addNode(n, c.simplifyWorklist);
   
  }
}

static bool OK(G_node t, G_node r) {
  int degree = (int)G_look(c.degree, t);
  return degree < c.K || Temp_look(c.precolored, Live_gtemp(t)) || 
  G_goesTo(t, r) || G_goesTo(r, t);
}

static bool conservative(G_nodeList nl) {
  int k = 0;
  for (; nl; nl = nl->tail) {
    int degree = (int)G_look(c.degree, nl->head);
    if (degree >= c.K) {
      ++k;
    }
  }
  return (k < c.K);
}

static G_node getAlias(G_node n) {
  if (G_inNodeList(n, c.coalescedNodes)) {
    G_node alias = (G_node)G_look(c.alias, n);
    return getAlias(alias);
  } else {
    return n;
  }
}

static void simplify() {
  if (c.simplifyWorklist == NULL) {
    return;
  }
  G_node n = c.simplifyWorklist->head;
  c.simplifyWorklist = c.simplifyWorklist->tail;
  c.selectStack = G_NodeList(n , c.selectStack);
  G_nodeList adjs = G_adj(n);
  for (; adjs; adjs = adjs->tail) {
    G_node m = adjs->head;
    decrementDegree(m);
  }
}

static void combine(G_node u, G_node v) {
  if (G_inNodeList(v, c.freezeWorklist)) {
    c.freezeWorklist = delete(v, c.freezeWorklist);
  } else {
    c.spillWorklist = delete(v, c.spillWorklist);
  }
  c.coalescedNodes = G_NodeList(v, c.coalescedNodes);
  G_enter(c.alias, v, (void*)u);
  AS_instrList au = (AS_instrList)G_look(c.moveList, u);
  AS_instrList av = (AS_instrList)G_look(c.moveList, v);
  au = AS_Union(au, av);
  G_enter(c.moveList, u, (void*)au);
  enableMoves(G_NodeList(v, NULL));
  G_nodeList adjs = G_adj(v);
  for (; adjs; adjs = adjs->tail) {
    G_node t = adjs->head;
    t = getAlias(t);
    addEdge(t, u);
    decrementDegree(t);
  }
  int degree = (int)G_look(c.degree, u);
  if (degree >= c.K && G_inNodeList(u, c.freezeWorklist)) {
    c.freezeWorklist = delete(u, c.freezeWorklist);
    c.spillWorklist = G_addNode(u, c.spillWorklist);
  }
}

static void coalesce() {
  if (c.worklistMoves == NULL) {
    return;
  }
  AS_instr m = c.worklistMoves->head;
  Temp_temp cx = AS_Use(m)->head;
  Temp_temp cy = AS_Def(m)->head;
  G_node u, v,
  x = getAlias(temp2Node(cx)),
  y = getAlias(temp2Node(cy));
  if (Temp_look(c.precolored, cx) != NULL) {
    u = y; v = x;
  } 
  else {
    u = x; v = y;
  }
  c.worklistMoves = AS_Minus(c.worklistMoves, AS_InstrList(m, NULL));
  if (u == v) {
    c.coalescedMoves = AS_addInstr(m, c.coalescedMoves);
    addWorkList(u);
  } 
  else if (Temp_look(c.precolored, Live_gtemp(v)) || G_goesTo(u, v) || G_goesTo(v, u)) {
    c.constrainedMoves = AS_addInstr(m, c.constrainedMoves);
    addWorkList(u);
    addWorkList(v);
  } 
  else {
    bool flag = FALSE;
    if (Temp_look(c.precolored, Live_gtemp(u))) {
      flag = TRUE;
      G_nodeList adj = adjacent(v);
      for (; adj; adj = adj->tail) {
        if (!OK(adj->head, u)) {
          flag = FALSE;
          break;
        }
      }
    } 
    else {
      flag = conservative(G_Union(adjacent(u), adjacent(v)));
    }
    if (flag) {
      c.coalescedMoves = AS_addInstr(m, c.coalescedMoves);
      combine(u, v);
      addWorkList(u);
    } 
    else {
      c.activeMoves = AS_addInstr(m, c.activeMoves);
    }
  }
}

static void freezeMoves(G_node n) {
  AS_instrList il = nodeMoves(n);
  for (; il; il = il->tail) {
    AS_instr m = il->head;
    Temp_temp x = AS_Use(m)->head;
    Temp_temp y = AS_Def(m)->head;
    G_node nx = temp2Node(x);
    G_node ny = temp2Node(y);
    G_node nv;
    if (getAlias(ny) == getAlias(n)) {
      nv = getAlias(nx);
    } else {
      nv = getAlias(ny);
    }
    c.activeMoves = AS_deleteInstr(m, c.activeMoves);
    c.frozenMoves = AS_addInstr(m, c.frozenMoves);
    int degree = (int)G_look(c.degree, nv);
    if (nodeMoves(nv) == NULL && degree < c.K) {
      c.freezeWorklist = delete(nv, c.freezeWorklist);
      c.simplifyWorklist = G_addNode(nv, c.simplifyWorklist);
    }
  }
}

static void freeze() {
  if (c.freezeWorklist == NULL) {
    return;
  }
  G_node n = c.freezeWorklist->head;
  c.freezeWorklist = delete(n, c.freezeWorklist);  
  c.simplifyWorklist = G_addNode(n, c.simplifyWorklist);
  freezeMoves(n);
}

static void selectSpill() {
  if (c.spillWorklist == NULL) {
    return;
  }
  G_nodeList nl = c.spillWorklist;
  float minSpillPriority = 10000;
  G_node m = NULL;
  for (; nl; nl = nl->tail) {
    G_node t = nl->head;
    int cost = (int)G_look(c.spillCost, t);
    int degree = (int)G_look(c.degree, t);
    if(degree == 0) degree = 1;
    float priority = ((float)cost) / degree;
    if (priority < minSpillPriority) {
      minSpillPriority = priority;
      m = t;
    }
  }
  c.spillWorklist = delete(m, c.spillWorklist);
  c.simplifyWorklist = G_addNode(m, c.simplifyWorklist);
  freezeMoves(m);
}

static void assignColors(Temp_map colors, Temp_tempList regs, Temp_map precolored){
  while (c.selectStack != NULL) {
    G_node n = c.selectStack->head; 
    c.selectStack = c.selectStack->tail;
    Temp_temp t = Live_gtemp(n);
    Temp_tempList okColors = T_Copy(regs);
    G_nodeList adjs = G_adj(n);
    G_node nw;
    string color;
    for (; adjs; adjs = adjs->tail) {
      nw = adjs->head; 
      G_node nw_alias = getAlias(nw);
      Temp_temp w_alias = Live_gtemp(nw_alias);
      if ((color = Temp_look(colors, w_alias)) != NULL) {
        Temp_temp colorTemp = getColor(color, precolored, regs);
        if (colorTemp) {
          okColors = T_Minus(okColors, Temp_TempList(colorTemp, NULL));
        }
      }
    }
    if (okColors == NULL) {
      c.spilledNodes = G_addNode(n, c.spilledNodes);
    } 
    else {
      c.coloredNodes = G_addNode(n, c.coloredNodes);
      Temp_enter(colors, t, Temp_look(precolored, okColors->head));
    }
  }
  G_nodeList nl;
  for (nl = c.coalescedNodes; nl; nl = nl->tail) {
    G_node alias = getAlias(nl->head);
    string color = Temp_look(colors, Live_gtemp(alias));
    Temp_enter(colors, Live_gtemp(nl->head), color);
  }
}

struct COL_result COL_color(G_graph ig, Temp_map initial, Temp_tempList regs,
                            AS_instrList worklistMoves, G_table moveList, G_table spillCost) {
  //your code here.
  struct COL_result ret;
  c.precolored = initial;
  c.initial = NULL;
  c.simplifyWorklist = NULL;
  c.freezeWorklist = NULL;
  c.spillWorklist = NULL;
  c.spilledNodes = NULL;
  c.coalescedNodes = NULL;
  c.coloredNodes = NULL;
  c.selectStack = NULL;
  c.coalescedMoves = NULL;
  c.constrainedMoves = NULL;
  c.frozenMoves = NULL;
  c.worklistMoves = worklistMoves;
  c.activeMoves = NULL;
  c.spillCost = spillCost;
  c.moveList = moveList;
  c.degree = G_empty();
  c.alias = G_empty();
  c.nodes = ig;
  c.K = Count(regs);
  Temp_map precolored = initial;
  Temp_map colors = Temp_layerMap(Temp_empty(), initial);
  G_nodeList nodes = G_nodes(ig);
  G_nodeList nl;
  for (nl = nodes; nl; nl = nl->tail) {
    int degree = G_degree(nl->head);
    G_enter(c.degree, nl->head, (void*)degree);
    if (Temp_look(precolored, Live_gtemp(nl->head))) {
      G_enter(c.degree, nl->head, (void*)1000);
      continue;
    }
    c.initial = G_NodeList(nl->head, c.initial);
  }
  makeWorkList();
  do {
    if (c.simplifyWorklist != NULL) {
      simplify();
    } else if (c.worklistMoves != NULL) {
      coalesce();
    } else if (c.freezeWorklist != NULL) {
      freeze();
    } else if (c.spillWorklist != NULL) {
      selectSpill();
    }
  } while (c.simplifyWorklist != NULL || c.worklistMoves != NULL || c.freezeWorklist != NULL || c.spillWorklist != NULL);
  assignColors(colors, regs, precolored);
  ret.coloring = colors;
  ret.colored = NULL;
  for (; c.coloredNodes; c.coloredNodes = c.coloredNodes->tail) {
    ret.colored = Temp_TempList(Live_gtemp(c.coloredNodes->head), ret.colored);
  }
  ret.spills = NULL;
  for (; c.spilledNodes; c.spilledNodes = c.spilledNodes->tail) {
    ret.spills = Temp_TempList(Live_gtemp(c.spilledNodes->head), ret.spills);
  }
  ret.coalescedMoves = c.coalescedMoves;
  ret.coalescedNodes = nodeL2TempL(c.coalescedNodes);
  ret.alias = c.alias;
  return ret;
}
