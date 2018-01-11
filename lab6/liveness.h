#ifndef LIVENESS_H
#define LIVENESS_H

struct Live_graph {
	G_graph graph;
	AS_instrList worklistMoves;
	G_table spillCost;
	G_table moveList;
};

Temp_temp Live_gtemp(G_node n);

struct Live_graph Live_liveness(G_graph flow);

#endif
