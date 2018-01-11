/*
 * color.h - Data structures and function prototypes for coloring algorithm
 *             to determine register allocation.
 */

#ifndef COLOR_H
#define COLOR_H

struct COL_result {Temp_map coloring; Temp_tempList colored; Temp_tempList spills;
                    AS_instrList coalescedMoves; Temp_tempList coalescedNodes; G_table alias;};
struct COL_result COL_color(G_graph ig, Temp_map initial, Temp_tempList regs,
                            AS_instrList worklistMoves, G_table moveList, G_table spillCost);

#endif
