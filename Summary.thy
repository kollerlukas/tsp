theory Summary
  imports Main Misc WeightedGraph CompleteGraph MST TSP DoubleTree ChristofidesSerdyukov
begin

section \<open>Definitions\<close>

subsection \<open>Connected Graphs\<close>

text \<open>A graph is connected if any pair of vertices is contained in the same connected component.\<close>
thm is_connected_def

thm connected_bridge

subsection \<open>Weighted Graphs\<close>

text \<open>Graph with edge weights. Locale @{const w_graph_abs}}\<close>

text \<open>Weighted graph with only positive edges weights. Locale @{const pos_w_graph_abs}\<close>

subsection \<open>Complete Graphs\<close>

text \<open>A graph is complete if there exists an edges for any pair of vertices that are not equal.\<close>
thm is_complete_def

text \<open>Complete graph locale @{const compl_graph_abs}\<close>

text \<open>A locale that fixes a subgraph of a complete graph. Locale @{const restr_compl_graph_abs}\<close>

text \<open>Complete graph with triangle inequality. @{const metric_graph_abs}\<close>

thm metric_graph_abs.cost_of_path_short_cut_tri_ineq

text \<open>In a complete graph, any sequence of vertices s.t. no two consecutive vertices are equal 
(@{const distinct_adj}) is a path.\<close>
thm compl_graph_abs.path_complete_graph

subsection \<open>Acyclic Graphs\<close>

text \<open>A path is a simple if no edge is used twice.\<close>
thm is_simple_def

text \<open>A cycle is a path s.t. (i) it starts and ends at the same node, (ii) it is simple, and 
(iii) it uses at least one edge.\<close>
thm is_cycle_def

text \<open>A vertex that is contained in a cycle has a degree greater-equal to 2.\<close>
thm cycle_degree

text \<open>A graph is acyclic if no cycle is contained in the graph.\<close>
thm is_acyclic_def

subsection \<open>Trees\<close>

text \<open>A tree is a graph that is (i) connected and (ii) acyclic.\<close>
thm is_tree_def

subsection \<open>Spanning Trees\<close>

text \<open>A spanning tree is a subgraph s.t. (i) it is a tree and (ii) it contains every vertex.\<close>
thm graph_abs.is_st_def

subsection \<open>Minimum Spanning Trees\<close>

text \<open>A minimum spanning tree is a spanning tree with minimum weight.\<close>
thm w_graph_abs.is_mst_def

text \<open>A locale that a minimum spanning. Locale @{const mst}}\<close>

subsection \<open>Hamiltonian Cycles\<close>

thm graph_abs.is_hc_def

subsection \<open>Traveling-Salesman Problem\<close>

thm pos_w_graph_abs.is_tsp_def

term metric_graph_abs.is_mtsp

subsection \<open>Multi-Graphs\<close>

(* TODO: finish encoding of a multi-graph in a regular graph. *)

subsection \<open>Eulerian Tours\<close>

thm is_eulerian_def

text \<open>Locale that fixes an algorithm that computes a Eulerian tour for a given multi-graph.
  Locale @{const eulerian}\<close>

(* TODO: implement and verify an algorithm for Eulerian Tour *)

text \<open>Eulerian Tour on a Multi-Graph.\<close>
thm is_et_def

subsection \<open>Perfect Matchings\<close>

thm is_perf_match_def

subsection \<open>Minimum-Weight Perfect Matchings\<close>

thm is_min_match_def

text \<open>Locale that fixes an algorithm that computes a minimum-weight perfect matching for a given 
graph. Locale @{const min_weight_matching}\<close>

text \<open>Every complete graph with an even number of vertices has a perfect matching.\<close>
thm compl_graph_abs.perf_match_exists

section \<open>Graph Lemmas\<close>

thm graph_abs.handshake

section \<open>\textsc{DoubleTree} Approximation Algorithm for \textsc{mTSP}\<close>

subsection \<open>Definition\<close>

thm double_tree_algo.double_tree_def

subsection \<open>Feasibilty\<close>

thm double_tree_algo_feasibility.dt_is_hc

subsection \<open>Approximation\<close>

thm double_tree_algo_approx.dt_approx

section \<open>\textsc{Christofides-Serdyukov} Approximation Algorithm for \textsc{mTSP}\<close>

subsection \<open>Definition\<close>

thm christofides_serdyukov_algo.christofides_serdyukov_def

text \<open>christofides_serdyukov_algo.christofides_serdyukov\<close>

subsection \<open>Feasibilty\<close>

thm christofides_serdyukov_algo_feasibility.cs_is_hc

subsection \<open>Approximation\<close>

thm christofides_serdyukov_algo_approx.cs_approx

section \<open>Miscellaneous\<close>

text \<open>Filter a list and only keep even-index elements.\<close>
term even_elems

thm finite2_induct
 
(* TODO ... *)

end