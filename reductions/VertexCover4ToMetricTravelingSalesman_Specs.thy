theory VertexCover4ToMetricTravelingSalesman_Specs
  imports Main tsp.GraphAdjMap_Specs WeightedGraph
begin

locale VC4_To_mTSP = 
  g1: ugraph_adj_map map_empty1 update1 map_delete1 lookup1 map_invar1 set_empty1 insert1
      set_delete1 isin1 set1 set_invar1 union1 inter1 diff1 rep1 
      \<comment> \<open>Adjacency map of the graph for VC4.\<close> +
  g2: ugraph_adj_map map_empty2 update2 map_delete2 lookup2 map_invar2 set_empty2 insert2
      set_delete2 isin2 set2 set_invar2 union2 inter2 diff2 rep2 
      \<comment> \<open>Adjacency map of the graph for mTSP.\<close>
  for map_empty1 :: "'g1" and update1 :: "'v1 \<Rightarrow> 'v1set \<Rightarrow> 'g1 \<Rightarrow> 'g1" and map_delete1 lookup1 
      map_invar1 and set_empty1 :: "'v1set" and insert1 :: "'v1 \<Rightarrow> 'v1set \<Rightarrow> 'v1set" and set_delete1 
      isin1 set1 set_invar1 union1 inter1 diff1 rep1 
  and map_empty2 :: "'g2" and update2 :: "'v1 uedge \<times> 'v1 \<times> nat \<Rightarrow> 'v2set \<Rightarrow> 'g2 \<Rightarrow> 'g2" and 
      map_delete2 lookup2 map_invar2 and set_empty2 :: "'v2set" and 
      insert2 :: "'v1 uedge \<times> 'v1 \<times> nat \<Rightarrow> 'v2set \<Rightarrow> 'v2set" and set_delete2 isin2 set2 set_invar2 
      union2 inter2 diff2 rep2 +
  \<comment> \<open>Functions that fold the undirected edges of the graph for VC4. Multiple fold-functions are 
  necessary. Essentialy all fold-functions are the same, but we need to instantiate different 
  functions because we cannot quantify over types)\<close>
  fixes fold_g1_uedges1 :: "('v1 uedge \<Rightarrow> 'v2set \<Rightarrow> 'v2set) \<Rightarrow> 'g1 \<Rightarrow> 'v2set \<Rightarrow> 'v2set"
    \<comment> \<open>Function that folds the undirected edges of a graph represented by an adjacency map.\<close>
  assumes fold_g1_uedges1: "\<And>M f a. g1.ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges1 f M a = fold f es a"
  fixes fold_g1_uedges2 :: "('v1 uedge \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 'g1 \<Rightarrow> bool \<Rightarrow> bool"
  assumes fold_g1_uedges2: "\<And>M f a. g1.ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges2 f M a = fold f es a"
  fixes fold_g1_uedges3 :: "('v1 uedge \<Rightarrow> enat \<Rightarrow> enat) \<Rightarrow> 'g1 \<Rightarrow> enat \<Rightarrow> enat"
  assumes fold_g1_uedges3: "\<And>M f a. g1.ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges3 f M a = fold f es a"
  fixes fold_g1_uedges4 :: "('v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list) 
    \<Rightarrow> 'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list"
  assumes fold_g1_uedges4: "\<And>M f a. g1.ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges4 f M a = fold f es a"
  fixes fold_g1_uedges5 :: "('v1 uedge \<Rightarrow> 'v1set \<Rightarrow> 'v1set) \<Rightarrow> 'g1 \<Rightarrow> 'v1set \<Rightarrow> 'v1set"
  assumes fold_g1_uedges5: "\<And>M f a. g1.ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges5 f M a = fold f es a"

  fixes fold_v1set1 :: "('v1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list) 
    \<Rightarrow> 'v1set \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list"
    \<comment> \<open>Function that folds the vertices of a graph represented by an adjacency map.\<close>
  assumes finite_sets1: "\<And>X. finite (set1 X)"
  assumes fold_v1set1: "\<And>X f a. set_invar1 X \<Longrightarrow> \<exists>xs. distinct xs \<and> List.set xs = set1 X 
      \<and> fold_v1set1 f X a = fold f xs a"

  fixes fold_v1set2 :: "('v1 \<Rightarrow> 'v1set \<Rightarrow> 'v1set) \<Rightarrow> 'v1set \<Rightarrow> 'v1set \<Rightarrow> 'v1set"
    \<comment> \<open>Function that folds the vertices of a graph represented by an adjacency map.\<close>
  assumes fold_v1set2: "\<And>X f a. set_invar1 X \<Longrightarrow> \<exists>xs. distinct xs \<and> List.set xs = set1 X 
      \<and> fold_v1set2 f X a = fold f xs a"

  fixes fold_v2set1 :: "(('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> 'g2 \<Rightarrow> 'g2) \<Rightarrow> 'v2set \<Rightarrow> 'g2 \<Rightarrow> 'g2"
    \<comment> \<open>Function that folds the vertices of a graph represented by an adjacency map.\<close>
  assumes finite_sets2: "\<And>X. finite (set2 X)"
  assumes fold_v2set1: "\<And>X f a. set_invar2 X \<Longrightarrow> \<exists>xs. distinct xs \<and> List.set xs = set2 X 
      \<and> fold_v2set1 f X a = fold f xs a" \<comment> \<open>For locale \<open>graph_of_vertices_for_ugraph_adj_map\<close>.\<close>
begin

\<comment> \<open>Import lemmas by instantiating a sublocale for each fold-function.\<close>

sublocale fold1: ugraph_adj_map_fold_uedges map_empty1 update1 map_delete1 lookup1 map_invar1 
  set_empty1 insert1 set_delete1 isin1 set1 set_invar1 union1 inter1 diff1 rep1 fold_g1_uedges1
  using fold_g1_uedges1 by unfold_locales

sublocale fold2: ugraph_adj_map_fold_uedges map_empty1 update1 map_delete1 lookup1 map_invar1 
  set_empty1 insert1 set_delete1 isin1 set1 set_invar1 union1 inter1 diff1 rep1 fold_g1_uedges2
  using fold_g1_uedges2 by unfold_locales

sublocale fold3: ugraph_adj_map_fold_uedges map_empty1 update1 map_delete1 lookup1 map_invar1 
  set_empty1 insert1 set_delete1 isin1 set1 set_invar1 union1 inter1 diff1 rep1 fold_g1_uedges3
  using fold_g1_uedges3 by unfold_locales

sublocale fold4: ugraph_adj_map_fold_uedges map_empty1 update1 map_delete1 lookup1 map_invar1 
  set_empty1 insert1 set_delete1 isin1 set1 set_invar1 union1 inter1 diff1 rep1 fold_g1_uedges4
  using fold_g1_uedges4 by unfold_locales

sublocale fold5: ugraph_adj_map_fold_uedges map_empty1 update1 map_delete1 lookup1 map_invar1 
  set_empty1 insert1 set_delete1 isin1 set1 set_invar1 union1 inter1 diff1 rep1 fold_g1_uedges5
  using fold_g1_uedges5 by unfold_locales

sublocale graph_of_vertices_for_ugraph_adj_map map_empty2 update2 map_delete2 lookup2 map_invar2 
  set_empty2 insert2 set_delete2 isin2 set2 set_invar2 union2 inter2 diff2 rep2 fold_v2set1
  using fold_v2set1 finite_sets2 by unfold_locales

sublocale fold6: fold_set2 set_empty1 set_delete1 isin1 set1 set_invar1 insert1 union1 inter1 diff1 
  fold_v1set1
  using fold_v1set1 finite_sets1 by unfold_locales

sublocale filter1: filter_set2 set_empty1 set_delete1 isin1 set1 set_invar1 insert1 union1 inter1 diff1 
  fold_v1set2
  using fold_v1set2 finite_sets1 by unfold_locales

notation filter1.filter_set ("filter'_v1set")

notation g1.neighborhood ("\<N>\<^sub>1")
notation g2.neighborhood ("\<N>\<^sub>2")

text \<open>
(uEdge u v,u,1) --- (uEdge u v,u,5) --- (uEdge u v,v,2)
       |                                        |
(uEdge u v,u,3) --- (uEdge u v,u,6) --- (uEdge u v,v,4)
       |                                        |
(uEdge u v,u,4) --- (uEdge u v,v,6) --- (uEdge u v,v,3)
       |                                        |
(uEdge u v,u,2) --- (uEdge u v,v,5) --- (uEdge u v,v,1)
\<close>

(* fun H\<^sub>e :: "'v1 uedge \<Rightarrow> 'g2" where
  "H\<^sub>e e = (case rep1 e of uEdge u v \<Rightarrow> let e = uEdge u v in
    update2 (e,u,1) (g2.set_of_list [(e,u,3),(e,u,5)])
    (update2 (e,u,2) (g2.set_of_list [(e,u,4),(e,v,5)])
    (update2 (e,u,3) (g2.set_of_list [(e,u,1),(e,u,4),(e,u,6)])
    (update2 (e,u,4) (g2.set_of_list [(e,u,2),(e,u,3),(e,v,6)])
    (update2 (e,u,5) (g2.set_of_list [(e,u,1),(e,v,2)])
    (update2 (e,u,6) (g2.set_of_list [(e,u,3),(e,v,4)])
    (update2 (e,v,1) (g2.set_of_list [(e,v,3),(e,v,5)])
    (update2 (e,v,2) (g2.set_of_list [(e,v,4),(e,u,5)])
    (update2 (e,v,3) (g2.set_of_list [(e,v,1),(e,v,4),(e,v,6)])
    (update2 (e,v,4) (g2.set_of_list [(e,v,2),(e,v,3),(e,u,6)])
    (update2 (e,v,5) (g2.set_of_list [(e,v,1),(e,u,2)])
    (update2 (e,v,6) (g2.set_of_list [(e,v,3),(e,u,4)]) map_empty2))))))))))))" *)

fun vertices_of_He :: "'v1 uedge \<Rightarrow> 'v2set" ("V\<^sub>H\<^sub>e") where 
  "vertices_of_He e = (case rep1 e of uEdge u v \<Rightarrow>
    g2.set_of_list ([(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),
      (rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]))"

fun neighborhood_in_He :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> 'v2set" ("\<N>\<^sub>H\<^sub>e") where
  "neighborhood_in_He (e,w,i) = (case rep1 e of uEdge u v \<Rightarrow>
    if w = u \<and> i = 1 then g2.set_of_list [(rep1 e,u,3),(rep1 e,u,5)]
    else if w = u \<and> i = 2 then g2.set_of_list [(rep1 e,u,4),(rep1 e,v,5)]
    else if w = u \<and> i = 3 then g2.set_of_list [(rep1 e,u,1),(rep1 e,u,4),(rep1 e,u,6)]
    else if w = u \<and> i = 4 then g2.set_of_list [(rep1 e,u,2),(rep1 e,u,3),(rep1 e,v,6)]
    else if w = u \<and> i = 5 then g2.set_of_list [(rep1 e,u,1),(rep1 e,v,2)]
    else if w = u \<and> i = 6 then g2.set_of_list [(rep1 e,u,3),(rep1 e,v,4)]
    else if w = v \<and> i = 1 then g2.set_of_list [(rep1 e,v,3),(rep1 e,v,5)]
    else if w = v \<and> i = 2 then g2.set_of_list [(rep1 e,v,4),(rep1 e,u,5)]
    else if w = v \<and> i = 3 then g2.set_of_list [(rep1 e,v,1),(rep1 e,v,4),(rep1 e,v,6)]
    else if w = v \<and> i = 4 then g2.set_of_list [(rep1 e,v,2),(rep1 e,v,3),(rep1 e,u,6)]
    else if w = v \<and> i = 5 then g2.set_of_list [(rep1 e,v,1),(rep1 e,u,2)]
    else if w = v \<and> i = 6 then g2.set_of_list [(rep1 e,v,3),(rep1 e,u,4)]
    else g2.set_of_list [])"

fun He :: "'v1 uedge \<Rightarrow> 'g2" ("H\<^sub>e") where
  "H\<^sub>e e = graph_of_vertices \<N>\<^sub>H\<^sub>e (V\<^sub>H\<^sub>e e)"

abbreviation "hp e \<equiv> (case e of uEdge u v \<Rightarrow>
    [(rep1 e,u,1::nat),(rep1 e,u,5),(rep1 e,v,2),(rep1 e,v,4),(rep1 e,u,6),(rep1 e,u,3),
      (rep1 e,u,4),(rep1 e,v,6),(rep1 e,v,3),(rep1 e,v,1),(rep1 e,v,5),(rep1 e,u,2)])"

fun hp_u1 where 
  (* "hp_u1 e = hp e" *)
  "hp_u1 e = (case rep1 e of uEdge u v \<Rightarrow> hp (uEdge u v))"
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,u,1)\<close>.\<close>

fun hp_u2 where "hp_u2 e = rev (hp_u1 e)" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,u,2)\<close>.\<close>

fun hp_v1 where 
  "hp_v1 e = (case rep1 e of uEdge u v \<Rightarrow> hp (uEdge v u))" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,v,1)\<close>.\<close>

fun hp_v2 where "hp_v2 e = rev (hp_v1 e)" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,v,2)\<close>.\<close>

end

section \<open>Implementation of Auxiliary Functions\<close>

context VC4_To_mTSP
begin

fun neighborhood_compl :: "'v2set \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> 'v2set" ("\<N>\<^sup>C") where
  "neighborhood_compl X x = (if isin2 X x then set_delete2 x X else set_empty2)"

fun complete_graph :: "'v2set \<Rightarrow> 'g2" where
  "complete_graph X = graph_of_vertices (\<N>\<^sup>C X) X"

fun is_edge_in_He :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) uedge \<Rightarrow> bool" where
  "is_edge_in_He G (uEdge x y) = fold_g1_uedges2 (\<lambda>e b. b \<or> isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y) G False"
  \<comment> \<open>Return \<open>True\<close> if the graph \<open>G\<close> contains an edge \<open>e\<close> in s.t. \<open>(uEdge x y)\<close> is an edge in the 
  subgraph \<open>H\<^sub>e e\<close>; return \<open>False\<close> otherwise.\<close>

fun min_dist_in_He :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> enat" where
  "min_dist_in_He G x y = fold_g1_uedges3 (\<lambda>e d. min (g2.path_dist (H\<^sub>e e) x y) d) G \<infinity>"
  \<comment> \<open>This function returns the minimum distance between \<open>x\<close> and \<open>y\<close> in \<open>H\<^sub>e e\<close> for an edge \<open>e\<close> in \<open>G\<close>.\<close>

fun are_vertices_in_He :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> bool" where
  "are_vertices_in_He G x y = 
    fold_g1_uedges2 (\<lambda>e b. b \<or> (isin2 (V\<^sub>H\<^sub>e e) x \<and> isin2 (V\<^sub>H\<^sub>e e) y)) G False"
  \<comment> \<open>Return \<open>True\<close> if the graph \<open>G\<close> contains an edge \<open>e\<close> in s.t. \<open>u\<close> and \<open>y\<close> are vertices in the 
  subgraph \<open>H\<^sub>e e\<close>; return \<open>False\<close> otherwise.\<close>
  (* alternate definition:  min_dist_in_He < \<infinity> *)

fun map_edge_to_hp_start_vertex :: 
  "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat)" where
  (* "map_edge_to_hp_start_vertex G T e = (case rotate_tour (isin2 (V\<^sub>H\<^sub>e e)) T of 
    x#(e',w,i)#T \<Rightarrow> (case rep1 e' of uEdge u v \<Rightarrow>
      if (w = u \<or> w = v) \<and> (i = 1 \<or> i = 2) then (uEdge u v,w,i)
      else (uEdge u v,u,1))
    | _ \<Rightarrow> undefined)" *)
  "map_edge_to_hp_start_vertex G T e = (case rotate_tour (isin2 (V\<^sub>H\<^sub>e e)) T of 
    x#(e',w,i)#T \<Rightarrow> (case rep1 e' of uEdge u v \<Rightarrow>
      if w = v then (uEdge u v,w,1) else (uEdge u v,u,1))
    | _ \<Rightarrow> undefined)"
  \<comment> \<open>Map an edge \<open>e\<close> of the VC4-graph to a start-edge \<open>(uEdge u v,x,i)\<close> of a Hamiltonian path in 
    \<open>H\<^sub>e e\<close>.\<close>

fun map_tour_to_hp_staring_vertices :: 
  "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "map_tour_to_hp_staring_vertices G T = 
    fold_g1_uedges4 (\<lambda>e xs. xs @ [map_edge_to_hp_start_vertex G T e]) G []"

fun map_edge_to_covering_vertex :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1 uedge \<Rightarrow> 'v1" where
  "map_edge_to_covering_vertex G T e = (case map_edge_to_hp_start_vertex G T e of (e,w,i) \<Rightarrow> w)"
  \<comment> \<open>Map an edge \<open>e\<close> of the VC4-graph to a vertex \<open>x\<close> that covers \<open>e\<close> in \<open>G\<close>.\<close>

fun hp_for_neighborhood :: "'v1 \<Rightarrow> 'v1set \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where 
  "hp_for_neighborhood u N\<^sub>u = fold_v1set1 
    (\<lambda>v T. T @ (if rep1 (uEdge u v) = uEdge u v then hp_u2 (uEdge u v) else hp_v2 (uEdge u v))) N\<^sub>u []"
  \<comment> \<open>Compute a Hamiltonian Path for a subgraph \<open>{{u,v} | v. v \<in> set1 N\<^sub>u}\<close> of \<open>f G\<close>. The subgraph 
  is induced by the neighborhood \<open>N\<^sub>u\<close> of \<open>u\<close>.\<close>

fun partition_for_vertex :: "'g1 \<Rightarrow> 'v1set \<Rightarrow> 'v1 \<Rightarrow> 'v1set" ("\<P>") where 
  "partition_for_vertex G X u = 
    filter_v1set (\<lambda>v. \<not> isin1 X v \<or> rep1 (uEdge u v) = uEdge u v) (\<N>\<^sub>1 G u)"
  \<comment> \<open>Compute a partition on the set of edges of \<open>G\<close> that is induced by a vertex cover; 
  return the partition corresponding to the vertex \<open>u\<close> from a vertex cover.\<close>

fun hp_from_vc :: "'g1 \<Rightarrow> 'v1set \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_from_vc G X = fold_v1set1 (\<lambda>u T. T @ hp_for_neighborhood u (partition_for_vertex G X u)) X []"
  \<comment> \<open>Compute a Hamiltonian path on \<open>f G\<close> that is induced by the vertex cover \<open>X\<close> of the graph \<open>G\<close>..\<close>

end

section \<open>Implementation of Reduction-Functions\<close>

context VC4_To_mTSP
begin

fun vertices_of_H :: "'g1 \<Rightarrow> 'v2set" ("V\<^sub>H") where 
  "V\<^sub>H G = fold_g1_uedges1 (union2 o V\<^sub>H\<^sub>e) G set_empty2"
  \<comment> \<open>Compute the vertices of the graph \<open>H := f G\<close>.\<close>

fun f :: "'g1 \<Rightarrow> 'g2" where
  "f G = complete_graph (V\<^sub>H G)" \<comment> \<open>The graph \<open>H\<close> is the complete graph for the vertices \<open>V\<^sub>H\<close>.\<close>

fun c :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> int" where
  "c G (e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2) = 
    (if is_edge_in_He G (uEdge (e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2)) then 1
    else if are_vertices_in_He G (e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2) then 
      the_enat (min_dist_in_He G (e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2))
    else if w\<^sub>1 = w\<^sub>2 \<and> rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2 then 4
    else 5)"

fun g :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1set" where
  "g G T = fold_g1_uedges5 (insert1 o (map_edge_to_covering_vertex G T)) G set_empty1"

(*
  Algorithm: given a Hamiltonian cycle T of g2.
  0. T' := T;
  1. for each {u,v} \<in> g1.
    a. T' := rotate T' to first vertex of Vs (H\<^sub>e u v);
    b. if hd T' = (uEdge u v,u,1) then
      I. T' := (Hamiltonian path starting at (uEdge u v,u,1)) @ filter (\<notin> Vs (H\<^sub>e u v)) T';
    c. else if hd T' = (uEdge u v,u,2) then
      I. T' := (Hamiltonian path starting at (uEdge u v,u,2)) @ filter (\<notin> Vs (H\<^sub>e u v)) T';
    d. else if hd T' = (uEdge u v,v,1) then
      I. T' := (Hamiltonian path starting at (uEdge u v,v,1)) @ filter (\<notin> Vs (H\<^sub>e u v)) T';
    e. else // if hd T' = (uEdge u v,v,2) then
      I. T' := (Hamiltonian path starting at (uEdge u v,v,2)) @ filter (\<notin> Vs (H\<^sub>e u v)) T';
  2. return T';

  claim. c T' \<le> c T
*)

end

section \<open>Properties of Auxiliary Functions\<close>

(* context VC4_To_mTSP
begin

lemma hp_for_neighborhood_intro:
  assumes "set_invar1 P" 
      and "\<And>vs. distinct vs \<Longrightarrow> List.set vs = set1 P \<Longrightarrow> F (fold (\<lambda>v T. T @ hp_u2 (uEdge u v)) vs [])"
  shows "F (hp_for_neighborhood u P)" (is "F ?hp")
proof -
  obtain vs where "distinct vs" "List.set vs = set1 P" "?hp = fold (\<lambda>v T. T @ hp_u2 (uEdge u v)) vs []"
    using assms by (auto elim!: fold6.fold_setE)
  thus ?thesis
    using assms by auto
qed

end *)

context VC4_To_mTSP
begin

lemma vertices_of_He_rep_idem: "V\<^sub>H\<^sub>e (rep1 e) = V\<^sub>H\<^sub>e e"
  by (simp only: vertices_of_He.simps g1.rep_idem)

lemma invar_vertices_of_He: "set_invar2 (V\<^sub>H\<^sub>e e)"
  by (auto simp add: g2.invar_set_of_list simp del: g2.set_of_list.simps split: uedge.splits)

lemma vertices_of_He_non_empty: "\<exists>x. isin2 (V\<^sub>H\<^sub>e e) x"
  using invar_vertices_of_He by (auto simp add: g2.set_specs split: uedge.splits)

lemma isin_vertices_of_He_iff: 
  assumes "rep1 e = rep1 (uEdge u v)"
  shows "isin2 (V\<^sub>H\<^sub>e e) x \<longleftrightarrow> isin2 (g2.set_of_list ([(rep1 e,u,1::nat),(rep1 e,u,2),
    (rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),
    (rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)])) x" 
    (is "_ \<longleftrightarrow> isin2 (g2.set_of_list ?V) x")
  using assms by (rule g1.rep_cases) 
    (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)

lemma set_vertices_of_He: 
  assumes "rep1 e = rep1 (uEdge u v)" 
  shows "set2 (V\<^sub>H\<^sub>e e) = List.set [(rep1 e,u,1::nat),(rep1 e,u,2),
    (rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),
    (rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
  using assms by (rule g1.rep_cases) (auto simp add: g2.set_of_list simp del: g2.set_of_list.simps)

lemma isin_vertices_of_He_intro: 
  assumes "rep1 e = rep1 (uEdge u v)" 
    "x \<in> List.set [(rep1 e,u,1::nat),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),
      (rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
  shows "isin2 (V\<^sub>H\<^sub>e e) x" 
  using assms(1) apply (rule g1.rep_cases) 
  using assms(2) apply (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)
  done

lemma isin_vertices_of_He_elim:
  assumes "isin2 (V\<^sub>H\<^sub>e e) x"
  obtains u v where "rep1 e = rep1 (uEdge u v)" 
    "x \<in> List.set [(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6)]"
proof -
  obtain u v where [simp]: "e = uEdge u v"
    using uedge.exhaust by auto
  hence "x \<in> List.set [(rep1 e,u,1),(rep1 e,u,2),
    (rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),
    (rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
    using assms isin_vertices_of_He_iff g2.isin_set_of_list 
      by (auto simp del: vertices_of_He.simps g2.set_of_list.simps)
  then consider 
    "x \<in> List.set [(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6)]" 
    | "x \<in> List.set [(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
    by auto
  thus ?thesis
    using that
  proof cases
    assume "x \<in> List.set [(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
    moreover have "rep1 e = rep1 (uEdge v u)"
      by (auto simp: g1.is_rep)
    ultimately show ?thesis
      using that by auto
  qed auto
qed

lemma isin_vertices_of_He_intro2:
  assumes "rep1 e = uEdge u v" "w \<in> {u,v}" "i \<in> {1..6}" 
  shows "isin2 (V\<^sub>H\<^sub>e e) (uEdge u v,w,i)" (is "isin2 _ ?x")
proof (intro isin_vertices_of_He_intro)
  show "rep1 e = rep1 (uEdge u v)"
    using assms g1.rep_simps by auto 
  have "1 \<le> i" "i \<le> 6"
    using assms by auto
  hence "i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> i = 6"
    by linarith
  then consider "w = u" "i = 1" | "w = u" "i = 2" | "w = u" "i = 3" | "w = u" "i = 4" 
    | "w = u" "i = 5" | "w = u" "i = 6" | "w = v" "i = 1" | "w = v" "i = 2" | "w = v" "i = 3" 
    | "w = v" "i = 4" | "w = v" "i = 5" | "w = v" "i = 6"
    using assms by auto
  thus "?x \<in> List.set [(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6), 
    (rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
    using assms by cases auto
qed

(* lemma isin_vertices_of_He_elim2:
  assumes "isin2 (V\<^sub>H\<^sub>e e) (uEdge u v,w,i)" (is "isin2 _ ?x")
  shows "rep1 e = uEdge u v \<and> w \<in> {u,v} \<and> i \<in> {1..6}"
  using assms
proof (rule isin_vertices_of_He_elim)
  fix u' v' 
  assume "rep1 e = rep1 (uEdge u' v')" and
    x_isin: "?x \<in> List.set [(rep1 e,u',1),(rep1 e,u',2),(rep1 e,u',3),(rep1 e,u',4),(rep1 e,u',5),(rep1 e,u',6)]" 
  then consider "rep1 e = uEdge u' v'" | "rep1 e = uEdge v' u'"
    using g1.is_rep by auto
  thus ?thesis
    using x_isin by cases auto
qed *)

lemma isin_vertices_of_He_elim2:
  assumes "isin2 (V\<^sub>H\<^sub>e e) x"
  obtains u v w i where "x = (uEdge u v,w,i)" "rep1 e = uEdge u v" "w \<in> {u,v}" "i \<in> {1..6}"
  using assms
proof (rule isin_vertices_of_He_elim)
  fix u' v' 
  assume "rep1 e = rep1 (uEdge u' v')" and
    x_isin: "x \<in> List.set [(rep1 e,u',1),(rep1 e,u',2),(rep1 e,u',3),(rep1 e,u',4),(rep1 e,u',5),(rep1 e,u',6)]" 
  then consider "rep1 e = uEdge u' v'" | "rep1 e = uEdge v' u'"
    using g1.is_rep by auto
  thus ?thesis
    using that x_isin by cases auto
qed

lemma isin_vertices_of_He_unique:
  assumes "isin2 (V\<^sub>H\<^sub>e e\<^sub>1) x"
  shows "isin2 (V\<^sub>H\<^sub>e e\<^sub>2) x \<longleftrightarrow> rep1 e\<^sub>1 = rep1 e\<^sub>2"
proof
  assume "isin2 (V\<^sub>H\<^sub>e e\<^sub>2) x"
  then obtain u\<^sub>1 v\<^sub>1 w\<^sub>1 i\<^sub>1 u\<^sub>2 v\<^sub>2 w\<^sub>2 i\<^sub>2 where "x = (uEdge u\<^sub>1 v\<^sub>1,w\<^sub>1,i\<^sub>1)" "rep1 e\<^sub>1 = uEdge u\<^sub>1 v\<^sub>1" 
    and "x = (uEdge u\<^sub>2 v\<^sub>2,w\<^sub>2,i\<^sub>2)" "rep1 e\<^sub>2 = uEdge u\<^sub>2 v\<^sub>2"
    using assms by (auto elim!: isin_vertices_of_He_elim2 simp del: vertices_of_He.simps)
  thus "rep1 e\<^sub>1 = rep1 e\<^sub>2"
    by auto
next
  assume "rep1 e\<^sub>1 = rep1 e\<^sub>2"
  moreover obtain u\<^sub>1 v\<^sub>1 w\<^sub>1 i\<^sub>1 where "x = (uEdge u\<^sub>1 v\<^sub>1,w\<^sub>1,i\<^sub>1)" and "rep1 e\<^sub>1 = uEdge u\<^sub>1 v\<^sub>1" "w\<^sub>1 \<in> {u\<^sub>1,v\<^sub>1}" "i\<^sub>1 \<in> {1..6}"
    using assms by (auto elim!: isin_vertices_of_He_elim2 simp del: vertices_of_He.simps)
  moreover have "rep1 e\<^sub>2 = uEdge u\<^sub>1 v\<^sub>1"
    using calculation by auto
  ultimately show "isin2 (V\<^sub>H\<^sub>e e\<^sub>2) x"
    by (auto intro!: isin_vertices_of_He_intro2 simp del: vertices_of_He.simps)
qed

lemma He_rep_idem: "H\<^sub>e (rep1 e) = H\<^sub>e e"
  by (simp only: He.simps vertices_of_He_rep_idem)

lemma neighborhood_He: "isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> \<N>\<^sub>2 (H\<^sub>e e) x = \<N>\<^sub>H\<^sub>e x"
  using invar_vertices_of_He by (auto simp add: graph_of_vertices_neighborhood 
      simp del: graph_of_vertices.simps vertices_of_He.simps)

lemma neighborhood_in_He_def2:
  "\<N>\<^sub>H\<^sub>e (rep1 (uEdge u v),u,i) = 
    (if i = 1 then 
      g2.set_of_list [(rep1 (uEdge u v),u,3),(rep1 (uEdge u v),u,5)]
    else if i = 2 then 
      g2.set_of_list [(rep1 (uEdge u v),u,4),(rep1 (uEdge u v),v,5)]
    else if i = 3 then 
      g2.set_of_list [(rep1 (uEdge u v),u,1),(rep1 (uEdge u v),u,4),(rep1 (uEdge u v),u,6)]
    else if i = 4 then 
      g2.set_of_list [(rep1 (uEdge u v),u,2),(rep1 (uEdge u v),u,3),(rep1 (uEdge u v),v,6)]
    else if i = 5 then 
      g2.set_of_list [(rep1 (uEdge u v),u,1),(rep1 (uEdge u v),v,2)]
    else if i = 6 then 
      g2.set_of_list [(rep1 (uEdge u v),u,3),(rep1 (uEdge u v),v,4)]
    else 
      g2.set_of_list [])"
proof -
  consider "rep1 (uEdge u v) = uEdge u v" 
    | "u \<noteq> v" "rep1 (uEdge u v) = uEdge v u" "rep1 (uEdge v u) = uEdge v u"
    using g1.is_rep by auto 
  thus ?thesis
    by cases (auto simp del: g2.set_of_list.simps)
qed

lemma isin_vertices_of_He_neighborhood_elim:
  assumes "isin2 (V\<^sub>H\<^sub>e e) x"
  obtains 
    u v where "x = (rep1 e,u,1)" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,3),(rep1 e,u,5)]"
    | u v where "x = (rep1 e,u,2)" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,4),(rep1 e,v,5)]"
    | u v where "x = (rep1 e,u,3)" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,u,4),(rep1 e,u,6)]"
    | u v where "x = (rep1 e,u,4)" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,2),(rep1 e,u,3),(rep1 e,v,6)]"
    | u v where "x = (rep1 e,u,5)" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,v,2)]"
    | u v where "x = (rep1 e,u,6)" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,3),(rep1 e,v,4)]"
proof -
  obtain u v where rep1_e_uv [simp]: "rep1 e = rep1 (uEdge u v)" and
    "x \<in> List.set [(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6)]"
    using assms by (elim isin_vertices_of_He_elim)
  then consider "x = (rep1 e,u,1)" | "x = (rep1 e,u,2)" | "x = (rep1 e,u,3)" 
    | "x = (rep1 e,u,4)" | "x = (rep1 e,u,5)" | "x = (rep1 e,u,6)"
    by auto
  thus ?thesis
    using that neighborhood_in_He_def2 by cases auto
qed

lemma neighborhood_in_He_non_empty:
  assumes "isin2 (V\<^sub>H\<^sub>e e) x"
  shows "\<exists>y. isin2 (\<N>\<^sub>H\<^sub>e x) y"
  using assms by (rule isin_vertices_of_He_neighborhood_elim) 
    (auto simp: g2.set_of_list g2.set_specs)

lemma neighborhood_in_He_subset_of_vertices_of_He:
  assumes "isin2 (V\<^sub>H\<^sub>e e) x" "isin2 (\<N>\<^sub>H\<^sub>e x) y"
  shows "isin2 (V\<^sub>H\<^sub>e e) y"
  using assms(1) apply (rule isin_vertices_of_He_neighborhood_elim)
  using assms(2) by (auto intro!: isin_vertices_of_He_intro simp add: g2.isin_set_of_list 
      simp del: g2.set_of_list.simps vertices_of_He.simps)

lemma isin_vertices_of_He_edge: "isin2 (V\<^sub>H\<^sub>e e) (e',w,i) \<Longrightarrow> rep1 e = e'"
  by (auto elim!: isin_vertices_of_He_elim simp del: vertices_of_He.simps)

lemma set_invar_neighborhood_in_He: "set_invar2 (\<N>\<^sub>H\<^sub>e x)"
proof -
  obtain e w i where [simp]: "x = (e,w,i)"
    by (cases x)
  obtain u v where [simp]: "e = uEdge u v"
    by (cases e)
  consider "rep1 e = uEdge u v" | "rep1 e = uEdge v u"
    using g1.is_rep by auto
  thus ?thesis
    using g2.invar_set_of_list by cases (auto simp del: g2.set_of_list.simps)
qed

lemma vertices_of_He: "g2.vertices (H\<^sub>e e) = set2 (V\<^sub>H\<^sub>e e)"
  using invar_vertices_of_He set_invar_neighborhood_in_He neighborhood_in_He_non_empty
proof (simp only: He.simps; intro vertices_graph_of_vertices)
  show "\<And>x. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> \<exists>y. isin2 (\<N>\<^sub>H\<^sub>e x) y"
    by (rule neighborhood_in_He_non_empty)
  show "\<And>x y. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> isin2 (\<N>\<^sub>H\<^sub>e x) y \<Longrightarrow> isin2 (V\<^sub>H\<^sub>e e) y"
    by (rule neighborhood_in_He_subset_of_vertices_of_He)
qed auto

lemma vertices_of_He_disjoint:
  assumes "rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2" 
  shows "set2 (V\<^sub>H\<^sub>e e\<^sub>1) \<inter> set2 (V\<^sub>H\<^sub>e e\<^sub>2) = {}"
proof (rule ccontr)
  assume "set2 (V\<^sub>H\<^sub>e e\<^sub>1) \<inter> set2 (V\<^sub>H\<^sub>e e\<^sub>2) \<noteq> {}"
  then obtain x where "x \<in> set2 (V\<^sub>H\<^sub>e e\<^sub>1)" "x \<in> set2 (V\<^sub>H\<^sub>e e\<^sub>2)"
    using vertices_of_He by auto
  hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>1) x" "isin2 (V\<^sub>H\<^sub>e e\<^sub>2) x"
    using invar_vertices_of_He g2.set_specs by auto
  then obtain u\<^sub>1 v\<^sub>1 u\<^sub>2 v\<^sub>2 where "rep1 e\<^sub>1 = rep1 (uEdge u\<^sub>1 v\<^sub>1)" "rep1 e\<^sub>2 = rep1 (uEdge u\<^sub>2 v\<^sub>2)"
    and "x \<in> set [(rep1 e\<^sub>1,u\<^sub>1,1),(rep1 e\<^sub>1,u\<^sub>1,2),(rep1 e\<^sub>1,u\<^sub>1,3),(rep1 e\<^sub>1,u\<^sub>1,4),(rep1 e\<^sub>1,u\<^sub>1,5),(rep1 e\<^sub>1,u\<^sub>1,6)]"
    and "x \<in> set [(rep1 e\<^sub>2,u\<^sub>2,1),(rep1 e\<^sub>2,u\<^sub>2,2),(rep1 e\<^sub>2,u\<^sub>2,3),(rep1 e\<^sub>2,u\<^sub>2,4),(rep1 e\<^sub>2,u\<^sub>2,5),(rep1 e\<^sub>2,u\<^sub>2,6)]"
    by (auto elim!: isin_vertices_of_He_elim simp del: vertices_of_He.simps)
  thus "False"
    using assms by auto
qed

(* lemma
  assumes "rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2" 
  shows "g2.vertices (H\<^sub>e e\<^sub>1) \<inter> g2.vertices (H\<^sub>e e\<^sub>2) = {}"
  using assms vertices_of_He_disjoint 
  by (auto simp add: vertices_of_He simp del: He.simps vertices_of_He.simps) *)

lemma neighborhood_in_He_irreflexive: 
  assumes "isin2 (V\<^sub>H\<^sub>e e) x"
  shows "\<not> isin2 (\<N>\<^sub>H\<^sub>e x) x"
  using assms by (rule isin_vertices_of_He_neighborhood_elim)
    (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)

lemma neighborhood_in_He_sym: 
  assumes "isin2 (V\<^sub>H\<^sub>e e) x" "isin2 (\<N>\<^sub>H\<^sub>e x) y"
  shows "isin2 (\<N>\<^sub>H\<^sub>e y) x"
  using assms(1)
proof (rule isin_vertices_of_He_neighborhood_elim)
  fix u v
  assume "x = (rep1 e,u,1)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,3),(rep1 e,u,5)]" 
  thus ?thesis
    using assms neighborhood_in_He_def2 
      by (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,2)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,4),(rep1 e,v,5)]" 
  thus ?thesis
    using assms neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,3)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,u,4),(rep1 e,u,6)]" 
  thus ?thesis
    using assms neighborhood_in_He_def2 
      by (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,4)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,2),(rep1 e,u,3),(rep1 e,v,6)]" 
  thus ?thesis
    using assms neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,5)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,v,2)]" 
  thus ?thesis
    using assms neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,6)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,3),(rep1 e,v,4)]" 
  thus ?thesis
    using assms neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
qed (* TODO: clean up! *)

lemma invar_He: "g2.ugraph_adj_map_invar (H\<^sub>e e)"
  using invar_vertices_of_He set_invar_neighborhood_in_He
proof (simp only: He.simps; intro invar_graph_of_vertices)
  show "\<And>x. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> \<exists>y. isin2 (\<N>\<^sub>H\<^sub>e x) y"
    by (rule neighborhood_in_He_non_empty)
  show "\<And>x y. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> isin2 (\<N>\<^sub>H\<^sub>e x) y \<Longrightarrow> isin2 (V\<^sub>H\<^sub>e e) y"
    by (rule neighborhood_in_He_subset_of_vertices_of_He)
  show "\<And>x. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> \<not> isin2 (\<N>\<^sub>H\<^sub>e x) x"
    by (rule neighborhood_in_He_irreflexive)
  show "\<And>x y. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> isin2 (\<N>\<^sub>H\<^sub>e x) y \<Longrightarrow> isin2 (\<N>\<^sub>H\<^sub>e y) x"
    by (rule neighborhood_in_He_sym)
qed auto        

lemma neighborhood_compl_sym: 
  assumes "set_invar2 X" "isin2 (\<N>\<^sup>C X x) y"
  shows "isin2 (\<N>\<^sup>C X y) x"
  using assms g2.set_specs empty_iff by (auto split: if_splits)

lemma map_invar_complete_graph: "set_invar2 X \<Longrightarrow> map_invar2 (complete_graph X)"
  using map_invar_graph_of_vertices by auto

lemma complete_graph_neighborhood: "set_invar2 X \<Longrightarrow> \<N>\<^sub>2 (complete_graph X) = \<N>\<^sup>C X"
  using graph_of_vertices_neighborhood by auto

lemma vertices_complete_graph: 
  assumes "set_invar2 X"
      and "\<And>x. isin2 X x \<Longrightarrow> \<exists>y. isin2 (set_delete2 x X) y" 
        \<comment> \<open>The set \<open>X\<close> contains at least two vertices.\<close>
  shows "g2.vertices (complete_graph X) = set2 X" (is "g2.vertices ?G\<^sub>X = set2 X")
  using assms g2.set_specs
  by (simp only: complete_graph.simps; intro vertices_graph_of_vertices) (auto split: if_splits)

lemma invar_complete_graph:
  assumes "set_invar2 X"
    and "\<And>x. isin2 X x \<Longrightarrow> \<exists>y. isin2 (set_delete2 x X) y" 
      \<comment> \<open>The set \<open>X\<close> contains at least two vertices.\<close>
  shows "g2.ugraph_adj_map_invar (complete_graph X)"
  using assms g2.set_specs
proof (simp only: complete_graph.simps; intro invar_graph_of_vertices)
  show "\<And>x y. isin2 (\<N>\<^sup>C X x) y \<Longrightarrow> isin2 X y"
  proof -
    fix x y
    assume "isin2 (\<N>\<^sup>C X x) y"
    moreover hence "\<N>\<^sup>C X x = set_delete2 x X"
      using assms g2.set_specs by auto
    ultimately show "isin2 X y"
      using assms g2.set_specs by auto
  qed
  show "\<And>x y. isin2 (\<N>\<^sup>C X x) y \<Longrightarrow> isin2 (\<N>\<^sup>C X y) x"
    using assms neighborhood_compl_sym by auto
qed auto

lemma complete_graph_is_complete_Adj: 
  assumes "set_invar2 X"
    and "\<And>x. isin2 X x \<Longrightarrow> \<exists>y. isin2 (set_delete2 x X) y" 
      \<comment> \<open>The set \<open>X\<close> contains at least two vertices.\<close>
  shows "g2.is_complete_Adj (complete_graph X)" (is "g2.is_complete_Adj ?E")
proof (intro g2.is_complete_AdjI)
  let ?f="\<lambda>v. set_delete2 v X"
  fix u v
  assume "u \<in> g2.vertices ?E" "v \<in> g2.vertices ?E" "u \<noteq> v"
  hence "isin2 X u" and "isin2 (?f u) v"
    using assms g2.set_specs by (auto simp: vertices_complete_graph[OF assms,symmetric])
  thus "isin2 (\<N>\<^sub>2 (complete_graph X) u) v"
    using assms complete_graph_neighborhood by (auto simp: g2.neighborhood_def)
qed

lemma complete_graph_is_complete: 
  assumes "set_invar2 X"
    and "\<And>x. isin2 X x \<Longrightarrow> \<exists>y. isin2 (set_delete2 x X) y" 
      \<comment> \<open>The set \<open>X\<close> contains at least two vertices.\<close>
  shows "is_complete (set_of_uedge ` g2.uedges (complete_graph X))" (is "is_complete ?E")
  using assms by (intro g2.is_complete_equiv complete_graph_is_complete_Adj)

lemma are_vertices_in_He_elim:
  assumes "g1.ugraph_adj_map_invar G" and "are_vertices_in_He G x y"
  obtains e where "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)" "y \<in> g2.vertices (H\<^sub>e e)"
proof -
  let ?f="\<lambda>e b. b \<or> (isin2 (V\<^sub>H\<^sub>e e) x \<and> isin2 (V\<^sub>H\<^sub>e e) y)"
  have "fold_g1_uedges2 ?f G False \<noteq> False"
    using assms by auto
  then obtain e where "e \<in> g1.uedges G" "?f e False \<noteq> False"
    using assms by (elim fold2.fold_neq_obtain_edge)
  thus ?thesis
    using that vertices_of_He g2.set_specs invar_vertices_of_He by auto
qed

lemma are_vertices_in_He_intro:
  assumes "g1.ugraph_adj_map_invar G" 
      and "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)" "y \<in> g2.vertices (H\<^sub>e e)"
  shows "are_vertices_in_He G x y"
  using assms(1)
proof (rule fold2.fold_uedgesE)
  let ?f="\<lambda>e b. b \<or> (isin2 (V\<^sub>H\<^sub>e e) x \<and> isin2 (V\<^sub>H\<^sub>e e) y)"
  fix es 
  assume "distinct es" "map rep1 es = es" and set_es: "List.set es = g1.uedges G" 
    and [simp]: "fold_g1_uedges2 ?f G False = fold ?f es False"
  hence "e \<in> List.set es"
    using assms by auto
  then obtain es\<^sub>1 es\<^sub>2 where [simp]: "es = es\<^sub>1 @ e#es\<^sub>2"
    by (meson split_list)
  hence "fold ?f es False = fold ?f es\<^sub>2 True"
    using assms vertices_of_He g2.set_specs invar_vertices_of_He by auto
  thus "are_vertices_in_He G x y"
    by (induction es\<^sub>2) (auto simp del: vertices_of_He.simps) 
qed

lemma are_vertices_in_He:
  assumes "g1.ugraph_adj_map_invar G"
  shows "are_vertices_in_He G x y 
    \<longleftrightarrow> (\<exists>e. e \<in> g1.uedges G \<and> x \<in> g2.vertices (H\<^sub>e e) \<and> y \<in> g2.vertices (H\<^sub>e e))"
  using assms are_vertices_in_He_intro are_vertices_in_He_elim by metis

(* lemma not_vertices_in_He:
  assumes "g1.ugraph_adj_map_invar G" "rep1 e\<^sub>x \<noteq> rep1 e\<^sub>y" 
      and "x \<in> g2.vertices (H\<^sub>e e\<^sub>x)" "y \<in> g2.vertices (H\<^sub>e e\<^sub>y)"
  shows "\<not> are_vertices_in_He G x y"
proof (rule ccontr; simp only: not_not)
  assume "are_vertices_in_He G x y"
  then obtain e where "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)" "y \<in> g2.vertices (H\<^sub>e e)"
    using assms by (elim are_vertices_in_He_elim)
  hence "isin2 (V\<^sub>H\<^sub>e e) x" "isin2 (V\<^sub>H\<^sub>e e) y"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  moreover have "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x" "isin2 (V\<^sub>H\<^sub>e e\<^sub>y) y"
    using assms invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately have "rep1 e = rep1 e\<^sub>x" "rep1 e = rep1 e\<^sub>y"
    using assms isin_vertices_of_He_unique by blast+
  thus "False"
    using assms by auto
qed *)

lemma vertices_in_He_rep_iff:
  assumes "g1.ugraph_adj_map_invar G" "e\<^sub>x \<in> g1.uedges G" "e\<^sub>y \<in> g1.uedges G" 
      and "x \<in> g2.vertices (H\<^sub>e e\<^sub>x)" "y \<in> g2.vertices (H\<^sub>e e\<^sub>y)"
  shows "are_vertices_in_He G x y \<longleftrightarrow> rep1 e\<^sub>x = rep1 e\<^sub>y"
proof
  assume "are_vertices_in_He G x y"
  then obtain e where "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)" "y \<in> g2.vertices (H\<^sub>e e)"
    using assms by (elim are_vertices_in_He_elim)
  hence "isin2 (V\<^sub>H\<^sub>e e) x" "isin2 (V\<^sub>H\<^sub>e e) y"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  moreover have "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x" "isin2 (V\<^sub>H\<^sub>e e\<^sub>y) y"
    using assms invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately have "rep1 e = rep1 e\<^sub>x" "rep1 e = rep1 e\<^sub>y"
    using assms isin_vertices_of_He_unique by blast+
  thus "rep1 e\<^sub>x = rep1 e\<^sub>y"
    by auto
next
  assume "rep1 e\<^sub>x = rep1 e\<^sub>y"
  moreover hence "y \<in> g2.vertices (H\<^sub>e e\<^sub>x)"
    using assms He_rep_idem by metis
  thus "are_vertices_in_He G x y"
    using assms by (intro are_vertices_in_He_intro)
qed
  
lemma are_vertices_in_He_sym:
  assumes "g1.ugraph_adj_map_invar G" "are_vertices_in_He G x y"
  shows "are_vertices_in_He G y x"
  using assms are_vertices_in_He by auto

(* lemma vertices_in_He_path_dist: 
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" 
      and "x \<in> g2.vertices (H\<^sub>e e)" "y \<in> g2.vertices (H\<^sub>e e)"
  shows "g2.path_dist (H\<^sub>e e) x y < \<infinity>"
  using invar_He
  apply (intro g2.path_dist_less_inf)
  apply simp
  sorry (* TODO: How to prove? *) *)

lemma min_dist_in_He_leq_path_dist:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
  shows "min_dist_in_He G x y \<le> g2.path_dist (H\<^sub>e e) x y"
  using assms(1)
proof (rule fold3.fold_uedgesE)
  let ?f="\<lambda>e d. min (g2.path_dist (H\<^sub>e e) x y) d"
  fix es
  assume "distinct es" "map rep1 es = es" and set_es: "List.set es = g1.uedges G" and
    [simp]: "fold_g1_uedges3 ?f G \<infinity> = fold ?f es \<infinity>"
  moreover hence "e \<in> set es"
    using assms by auto
  moreover hence "\<And>d. fold ?f es d \<le> ?f e d"
    by (intro fold_enat_min_leq_member)
  ultimately show ?thesis
    by auto
qed

lemma are_vertices_in_He_min_dist: 
  assumes "g1.ugraph_adj_map_invar G" "are_vertices_in_He G x y"
  shows "min_dist_in_He G x y < \<infinity>"
  using assms
proof (rule are_vertices_in_He_elim)
  fix e 
  assume e_isin_G: "e \<in> g1.uedges G" and "x \<in> g2.vertices (H\<^sub>e e)" "y \<in> g2.vertices (H\<^sub>e e)"
  hence d\<^sub>x\<^sub>y_le_inf: "g2.path_dist (H\<^sub>e e) x y < \<infinity>" (is "?d\<^sub>x\<^sub>y < \<infinity>")
    using assms sorry (* vertices_in_He_path_dist by auto *)
  moreover have "min_dist_in_He G x y \<le> g2.path_dist (H\<^sub>e e) x y"
    using assms e_isin_G by (intro min_dist_in_He_leq_path_dist)
  ultimately show ?thesis
    using order_le_less_trans by blast
qed

lemma min_dist_in_He_geq1:
  assumes "g1.ugraph_adj_map_invar G"
  shows "min_dist_in_He G x y \<ge> enat 1"
  sorry

lemma min_dist_in_He_sym:
  assumes "g1.ugraph_adj_map_invar G"
  shows "min_dist_in_He G x y = min_dist_in_He G y x"
  sorry

lemma is_edge_in_He_intro:
  assumes "g1.ugraph_adj_map_invar G" and "e \<in> g1.uedges G" "rep2 e' \<in> g2.uedges (H\<^sub>e e)"
  shows "is_edge_in_He G e'"
  using invar_He assms(3)
proof (rule g2.rep_isin_uedges_elim)
  fix x y
  assume [simp]: "e' = uEdge x y" and y_isin_Nx: "isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y"
  let ?f="\<lambda>e b. b \<or> isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y"
  obtain es where "distinct es" "map rep1 es = es" and set_es: "List.set es = g1.uedges G" and
   [simp]: "fold_g1_uedges2 ?f G False = fold ?f es False"
    using assms by (elim fold2.fold_uedgesE)
  hence "e \<in> List.set es"
    using assms by auto
  then obtain es\<^sub>1 es\<^sub>2 where "es = es\<^sub>1 @ e#es\<^sub>2"
    by (meson split_list)
  hence "fold ?f es False = fold ?f es\<^sub>2 True"
    using assms y_isin_Nx by auto
  also have "... = True"
    by (induction es\<^sub>2) auto
  finally show ?thesis
    by (simp del: He.simps)
qed

lemma is_edge_in_He_intro2:
  assumes "g1.ugraph_adj_map_invar G" and "rep1 e = uEdge u v" "rep1 e \<in> g1.uedges G" 
    "w\<^sub>1 \<in> {u,v}" "w\<^sub>2 \<in> {u,v}" "i\<^sub>1 \<in> {1::nat..6}" "i\<^sub>2 \<in> {1::nat..6}" "isin2 (\<N>\<^sub>H\<^sub>e (rep1 e,w\<^sub>1,i\<^sub>1)) (rep1 e,w\<^sub>2,i\<^sub>2)"
  shows "is_edge_in_He G (uEdge (rep1 e,w\<^sub>1,i\<^sub>1) (rep1 e,w\<^sub>2,i\<^sub>2))"
  using assms(1,3)
proof (rule is_edge_in_He_intro)
  have "isin2 (V\<^sub>H\<^sub>e e) (uEdge u v,w\<^sub>1,i\<^sub>1)"
    using assms by (intro isin_vertices_of_He_intro2) auto
  hence "isin2 (\<N>\<^sub>2 (H\<^sub>e (rep1 e)) (rep1 e,w\<^sub>1,i\<^sub>1)) (rep1 e,w\<^sub>2,i\<^sub>2)"
    using assms by (subst He_rep_idem; subst neighborhood_He) auto 
  thus "rep2 (uEdge (rep1 e,w\<^sub>1,i\<^sub>1) (rep1 e,w\<^sub>2,i\<^sub>2)) \<in> g2.uedges (H\<^sub>e (rep1 e))"
    unfolding g2.uedges_def2 by blast
  find_theorems "H\<^sub>e (rep1 ?e)"
qed

lemma is_edge_in_He_elim:
  assumes "g1.ugraph_adj_map_invar G" "is_edge_in_He G e'"
  obtains e where "e \<in> g1.uedges G" "rep2 e' \<in> g2.uedges (H\<^sub>e e)"
proof (cases e')
  case (uEdge x y)
  let ?f="\<lambda>e b. b \<or> isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y"
  have "fold_g1_uedges2 ?f G False \<noteq> False"
    using assms by (auto simp add: uEdge simp del: He.simps)
  then obtain e where "e \<in> g1.uedges G" "?f e False \<noteq> False"
    using assms by (elim fold2.fold_neq_obtain_edge)
  moreover hence "isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y"
    by auto
  moreover hence "rep2 e' \<in> g2.uedges (H\<^sub>e e)"
    unfolding g2.uedges_def2 uEdge by blast
  ultimately show ?thesis
    using that by auto
qed

lemma is_edge_in_He: 
  assumes "g1.ugraph_adj_map_invar G"
  shows "is_edge_in_He G e' \<longleftrightarrow> (\<exists>e. e \<in> g1.uedges G \<and> rep2 e' \<in> g2.uedges (H\<^sub>e e))"
  using assms is_edge_in_He_intro is_edge_in_He_elim by metis

lemma is_edge_in_He_sym: 
  assumes "g1.ugraph_adj_map_invar G" "is_edge_in_He G (uEdge x y)"
  shows "is_edge_in_He G (uEdge y x)"
proof -
  obtain e where "e \<in> g1.uedges G" "rep2 (uEdge x y) \<in> g2.uedges (H\<^sub>e e)"
    using assms by (elim is_edge_in_He_elim)
  moreover hence "rep2 (uEdge y x) \<in> g2.uedges (H\<^sub>e e)"
    using g2.is_rep by auto
  ultimately show ?thesis
    using assms by (intro is_edge_in_He_intro)
qed

lemma vertices_in_He_of_edge_in_He:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "rep2 (uEdge x y) \<in> g2.uedges (H\<^sub>e e)"
  shows "x \<in> g2.vertices (H\<^sub>e e)" "y \<in> g2.vertices (H\<^sub>e e)"
  using assms
proof -
  have y_isin_Nx: "isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y"
    using assms g2.rep_isin_uedges_elim[of "H\<^sub>e e", OF invar_He] by blast
  moreover thus "x \<in> g2.vertices (H\<^sub>e e)"
    by (auto intro!: g2.vertices_memberI1)
  ultimately show "y \<in> g2.vertices (H\<^sub>e e)"
    by (auto intro!: g2.vertices_memberI2)
qed

lemma edge_in_He_are_vertices:
  assumes "g1.ugraph_adj_map_invar G" "is_edge_in_He G (uEdge x y)"
  shows "are_vertices_in_He G x y"
  using assms 
proof -
  obtain e where "e \<in> g1.uedges G" "rep2 (uEdge x y) \<in> g2.uedges (H\<^sub>e e)"
    using assms is_edge_in_He by blast
  moreover hence "x \<in> g2.vertices (H\<^sub>e e)" "y \<in> g2.vertices (H\<^sub>e e)"
    using assms vertices_in_He_of_edge_in_He by blast+
  ultimately show ?thesis
    using assms by (intro are_vertices_in_He_intro)
qed

lemma invar_vertices_of_H:
  assumes "g1.ugraph_adj_map_invar G"
  shows "set_invar2 (V\<^sub>H G)"
  using assms
proof (rule fold1.fold_uedgesE)
  let ?f="union2 \<circ> V\<^sub>H\<^sub>e"
  fix es
  assume "distinct es" "map rep1 es = es" "List.set es = g1.uedges G" 
    "fold_g1_uedges1 ?f G set_empty2 = fold ?f es set_empty2"
  then show ?thesis
    using invar_vertices_of_He 
      by (auto intro!: g2.invar_fold_union simp: fold_map[symmetric] g2.set_specs)
qed

lemma set_vertices_of_H:
  assumes "g1.ugraph_adj_map_invar G"
  shows "set2 (V\<^sub>H G) = \<Union> ((set2 o V\<^sub>H\<^sub>e) ` g1.uedges G)"
  using assms
proof (rule fold1.fold_uedgesE)
  let ?f="union2 \<circ> V\<^sub>H\<^sub>e"
  fix es
  assume "distinct es" "map rep1 es = es" "List.set es = g1.uedges G" 
    "fold_g1_uedges1 ?f G set_empty2 = fold ?f es set_empty2"
  moreover have "set2 (fold ?f es set_empty2) = \<Union> (List.set (map (set2 o vertices_of_He) es))" 
    apply (subst fold_map[symmetric])
    apply (subst map_map)
    apply (intro g2.fold_union_empty)
    using invar_vertices_of_He g2.fold_union_empty by (auto simp: g2.set_specs)
  ultimately show ?thesis
    by auto
qed

lemma isin_vertices_of_H_obtain_edge:
  assumes "g1.ugraph_adj_map_invar G" "isin2 (V\<^sub>H G) x"
  obtains e where "e \<in> g1.uedges G" "isin2 (V\<^sub>H\<^sub>e e) x"
proof -
  have "set2 (V\<^sub>H G) = \<Union> ((set2 o V\<^sub>H\<^sub>e) ` g1.uedges G)"
    using assms by (intro set_vertices_of_H)
  then obtain e where "e \<in> g1.uedges G" "isin2 (V\<^sub>H\<^sub>e e) x"
    using assms invar_vertices_of_H invar_vertices_of_He g2.set_specs by auto
  thus ?thesis
    using that by auto
qed

lemma fst_of_vertex_is_edge:
  assumes "g1.ugraph_adj_map_invar G" and "isin2 (V\<^sub>H G) (e,w,i)" (is "isin2 (V\<^sub>H G) ?x")
  shows "isin2 (V\<^sub>H\<^sub>e e) (e,w,i) \<and> e \<in> g1.uedges G"
  using assms
proof (rule isin_vertices_of_H_obtain_edge)
  fix e'
  assume "e' \<in> g1.uedges G" "isin2 (V\<^sub>H\<^sub>e e') ?x"
  moreover hence "e = rep1 e'"
    by (elim isin_vertices_of_He_elim2) (auto simp add: g1.rep_idem)
  moreover have "rep1 e' \<in> g1.uedges G"
    using calculation by (intro g1.rep_of_edge_is_edge)
  ultimately show "isin2 (V\<^sub>H\<^sub>e e) ?x \<and> e \<in> g1.uedges G"
    using vertices_of_He_rep_idem by auto
qed

lemma obtain_other_vertex_of_H:
  assumes "g1.ugraph_adj_map_invar G" "isin2 (V\<^sub>H G) x"
  obtains y where "isin2 (V\<^sub>H G) y" "x \<noteq> y"
  using assms
proof (rule isin_vertices_of_H_obtain_edge)
  fix e
  assume isin_e: "e \<in> g1.uedges G" and isin_x: "isin2 (V\<^sub>H\<^sub>e e) x"
  then obtain u v where [simp]: "rep1 e = rep1 (uEdge u v)"
    by (elim isin_vertices_of_He_elim) thm isin_vertices_of_He_intro
  consider "x = (rep1 e,u,1::nat)" | "x \<noteq> (rep1 e,u,1::nat)"
    by auto
  then obtain y where "isin2 (V\<^sub>H\<^sub>e e) y" and x_neq_y: "x \<noteq> y"
  proof cases
    let ?y="(rep1 e,u,2::nat)"
    assume "x = (rep1 e,u,1::nat)"
    moreover have "isin2 (V\<^sub>H\<^sub>e e) ?y"
      by (intro isin_vertices_of_He_intro) auto
    ultimately show ?thesis
      using that isin_x by auto
  next
    let ?y="(rep1 e,u,1::nat)"
    assume "x \<noteq> (rep1 e,u,1::nat)"
    moreover have "isin2 (V\<^sub>H\<^sub>e e) ?y"
      by (intro isin_vertices_of_He_intro) auto
    ultimately show ?thesis
      using that isin_x by auto
  qed
  hence "y \<in> set2 (V\<^sub>H\<^sub>e e)"
    using assms invar_vertices_of_He g2.set_specs by blast
  hence "y \<in> \<Union> ((set2 o V\<^sub>H\<^sub>e) ` g1.uedges G)"
    using isin_e by fastforce
  hence "isin2 (V\<^sub>H G) y"
    using assms invar_vertices_of_H set_vertices_of_H g2.set_specs by auto
  thus ?thesis
    using that x_neq_y by auto
qed

lemma at_least_two_vertices_in_H:
  assumes "g1.ugraph_adj_map_invar G" "isin2 (V\<^sub>H G) x"
  shows "\<exists>y. isin2 (set_delete2 x (V\<^sub>H G)) y"
  using assms
proof (rule obtain_other_vertex_of_H)
  fix y
  assume "isin2 (V\<^sub>H G) y" "x \<noteq> y"
  hence "isin2 (set_delete2 x (V\<^sub>H G)) y"
    using assms invar_vertices_of_H g2.set_specs by auto
  thus ?thesis
    by blast
qed
                                       
lemma c_geq1:
  assumes "g1.ugraph_adj_map_invar G"
  shows "c G x y \<ge> 1"
proof -
  obtain e\<^sub>x w\<^sub>x i\<^sub>x where [simp]: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)"
    by (cases x)
  obtain e\<^sub>y w\<^sub>y i\<^sub>y where [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
    by (cases y)
  consider 
    "is_edge_in_He G (uEdge x y)" 
    | "\<not> is_edge_in_He G (uEdge x y)" "are_vertices_in_He G x y" 
    | "\<not> is_edge_in_He G (uEdge x y)" "\<not> are_vertices_in_He G x y" "w\<^sub>x = w\<^sub>y" "rep1 e\<^sub>x \<noteq> rep1 e\<^sub>y" 
    | "\<not> is_edge_in_He G (uEdge x y)" "\<not> are_vertices_in_He G x y" "w\<^sub>x \<noteq> w\<^sub>y \<or> rep1 e\<^sub>x = rep1 e\<^sub>y"
    by auto
  thus ?thesis
  proof cases
    assume "\<not> is_edge_in_He G (uEdge x y)" "are_vertices_in_He G x y"
    moreover hence "min_dist_in_He G x y \<ge> enat 1" and "min_dist_in_He G x y < \<infinity>"
      using assms min_dist_in_He_geq1 are_vertices_in_He_min_dist by auto
    moreover then obtain k where "min_dist_in_He G x y = enat k"
      by (elim less_infinityE)
    ultimately show ?thesis
      by auto
  qed auto
qed

lemma cost_path_geq_len:
  assumes "g1.ugraph_adj_map_invar G"
  shows "cost_of_path (c G) P \<ge> int (length P) - 1"
  using assms  
proof (induction P rule: list012.induct)
  case (3 u v P)
  thus ?case 
    using c_geq1[of G u v] by auto
qed auto

lemma c_sym: 
  assumes "g1.ugraph_adj_map_invar G"
  shows "c G x y = c G y x"
proof -
  obtain e\<^sub>x w\<^sub>x i\<^sub>x where [simp]: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)"
    by (cases x)
  obtain e\<^sub>y w\<^sub>y i\<^sub>y where [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
    by (cases y)
  consider 
    "is_edge_in_He G (uEdge x y)" 
    | "\<not> is_edge_in_He G (uEdge x y)" "are_vertices_in_He G x y" 
    | "\<not> is_edge_in_He G (uEdge x y)" "\<not> are_vertices_in_He G x y" "w\<^sub>x = w\<^sub>y" "rep1 e\<^sub>x \<noteq> rep1 e\<^sub>y" 
    | "\<not> is_edge_in_He G (uEdge x y)" "\<not> are_vertices_in_He G x y" "w\<^sub>x \<noteq> w\<^sub>y \<or> rep1 e\<^sub>x = rep1 e\<^sub>y"
    by auto
  thus ?thesis
  proof cases
    assume "is_edge_in_He G (uEdge x y)"
    moreover hence "is_edge_in_He G (uEdge y x)"
      using assms is_edge_in_He_sym are_vertices_in_He_sym by blast
    ultimately show ?thesis
      by auto
  next
    assume "\<not> is_edge_in_He G (uEdge x y)" "are_vertices_in_He G x y" 
    moreover hence "\<not> is_edge_in_He G (uEdge y x)" "are_vertices_in_He G y x" 
      using assms calculation is_edge_in_He_sym are_vertices_in_He_sym by blast+
    ultimately show ?thesis
      using assms min_dist_in_He_sym by auto
  next
    assume "\<not> is_edge_in_He G (uEdge x y)" "\<not> are_vertices_in_He G x y" "w\<^sub>x = w\<^sub>y" "rep1 e\<^sub>x \<noteq> rep1 e\<^sub>y"
    moreover hence "\<not> is_edge_in_He G (uEdge y x)" "\<not> are_vertices_in_He G y x" 
      using assms calculation is_edge_in_He_sym are_vertices_in_He_sym by blast+
    ultimately show ?thesis
      by auto
  next
    assume "\<not> is_edge_in_He G (uEdge x y)" "\<not> are_vertices_in_He G x y" 
      "w\<^sub>x \<noteq> w\<^sub>y \<or> rep1 e\<^sub>x = rep1 e\<^sub>y"
    moreover hence "\<not> is_edge_in_He G (uEdge y x)" "\<not> are_vertices_in_He G y x" 
      using assms calculation is_edge_in_He_sym are_vertices_in_He_sym by blast+
    ultimately show ?thesis
      by auto
  qed
qed

lemma hp_u1_non_nil: "hp_u1 e \<noteq> []"
  by (auto split: uedge.splits)

lemma hd_hp_u1: "rep1 e = uEdge u v \<Longrightarrow> hd (hp_u1 e) = (rep1 e,u,1)"
  using g1.rep_simps by (auto split: uedge.splits)

lemma hp_u1_rep_idem: "hp_u1 (rep1 e) = hp_u1 e"
  using g1.rep_idem by auto

lemma path_hp_u1: 
  assumes "rep1 e = uEdge u v"
  shows "g2.path_betw (H\<^sub>e e) (rep1 e,u,1) (hp_u1 e) (rep1 e,u,2)" 
    (is "g2.path_betw (H\<^sub>e ?e) ?u\<^sub>1 _ ?u\<^sub>2")    
proof -
  have "rep1 e = rep1 (uEdge u v)"
    using assms g1.rep_simps by metis
  moreover hence "?u\<^sub>2 \<in> g2.vertices (H\<^sub>e ?e)"
    using assms vertices_of_He set_vertices_of_He[OF \<open>rep1 e = rep1 (uEdge u v)\<close>] by (auto simp del: He.simps)
  ultimately show "g2.path_betw (H\<^sub>e e) ?u\<^sub>1 (hp_u1 e) ?u\<^sub>2"
    using assms by (fastforce intro!: g2.path_betw.intros isin_vertices_of_He_intro2 
        simp add: neighborhood_He g2.isin_set_of_list simp del: He.simps g2.set_of_list.simps)
qed

(* lemma cost_of_hp_u1_uedge: 
  assumes "g1.ugraph_adj_map_invar G" 
    and "rep1 (uEdge u v) = uEdge u v" "rep1 (uEdge u v) \<in> g1.uedges G" (is "rep1 ?e \<in> _")
  shows "cost_of_path (c G) (hp_u1 (uEdge u v)) = 11"
proof -
  have neighborhoods_u: 
    "isin2 (\<N>\<^sub>H\<^sub>e (rep1 ?e,u,1)) (rep1 ?e,u,5)"
    "isin2 (\<N>\<^sub>H\<^sub>e (rep1 ?e,u,5)) (rep1 ?e,v,2)"
    "isin2 (\<N>\<^sub>H\<^sub>e (rep1 ?e,u,6)) (rep1 ?e,u,3)"
    "isin2 (\<N>\<^sub>H\<^sub>e (rep1 ?e,u,3)) (rep1 ?e,u,4)"
    "isin2 (\<N>\<^sub>H\<^sub>e (rep1 ?e,u,4)) (rep1 ?e,v,6)"
    unfolding neighborhood_in_He_def2 using g2.isin_set_of_list by (simp del: g2.set_of_list.simps)+
  have neighborhoods_v: 
    "isin2 (\<N>\<^sub>H\<^sub>e (rep1 ?e,v,2)) (rep1 ?e,v,4)"
    "isin2 (\<N>\<^sub>H\<^sub>e (rep1 ?e,v,4)) (rep1 ?e,u,6)"
    "isin2 (\<N>\<^sub>H\<^sub>e (rep1 ?e,v,6)) (rep1 ?e,v,3)"
    "isin2 (\<N>\<^sub>H\<^sub>e (rep1 ?e,v,3)) (rep1 ?e,v,1)"
    "isin2 (\<N>\<^sub>H\<^sub>e (rep1 ?e,v,1)) (rep1 ?e,v,5)" 
    "isin2 (\<N>\<^sub>H\<^sub>e (rep1 ?e,v,5)) (rep1 ?e,u,2)"
    apply (subst g1.is_rep(1))
    unfolding neighborhood_in_He_def2 using g2.isin_set_of_list
    apply (simp add: g1.is_rep(1) del: g2.set_of_list.simps)    
    apply (subst g1.is_rep(1))
    unfolding neighborhood_in_He_def2 using g2.isin_set_of_list
    apply (simp add: g1.is_rep(1) del: g2.set_of_list.simps)
    apply (subst g1.is_rep(1))
    unfolding neighborhood_in_He_def2 using g2.isin_set_of_list
    apply (simp add: g1.is_rep(1) del: g2.set_of_list.simps)
    apply (subst g1.is_rep(1))
    unfolding neighborhood_in_He_def2 using g2.isin_set_of_list
    apply (simp add: g1.is_rep(1) del: g2.set_of_list.simps)
    apply (subst g1.is_rep(1))
    unfolding neighborhood_in_He_def2 using g2.isin_set_of_list
    apply (simp add: g1.is_rep(1) del: g2.set_of_list.simps)
    apply (subst g1.is_rep(1))
    unfolding neighborhood_in_He_def2 using g2.isin_set_of_list
    apply (simp add: g1.is_rep(1) del: g2.set_of_list.simps)
    done
  have "is_edge_in_He G (uEdge (rep1 ?e,u,1) (rep1 ?e,u,5))"
    "is_edge_in_He G (uEdge (rep1 ?e,u,5) (rep1 ?e,v,2))"
    "is_edge_in_He G (uEdge (rep1 ?e,v,2) (rep1 ?e,v,4))"
    "is_edge_in_He G (uEdge (rep1 ?e,v,4) (rep1 ?e,u,6))"
    "is_edge_in_He G (uEdge (rep1 ?e,u,6) (rep1 ?e,u,3))"
    "is_edge_in_He G (uEdge (rep1 ?e,u,3) (rep1 ?e,u,4))"
    "is_edge_in_He G (uEdge (rep1 ?e,u,4) (rep1 ?e,v,6))"
    "is_edge_in_He G (uEdge (rep1 ?e,v,6) (rep1 ?e,v,3))"
    "is_edge_in_He G (uEdge (rep1 ?e,v,3) (rep1 ?e,v,1))"
    "is_edge_in_He G (uEdge (rep1 ?e,v,1) (rep1 ?e,v,5))" 
    "is_edge_in_He G (uEdge (rep1 ?e,v,5) (rep1 ?e,u,2))"
    apply goal_cases                       
    using assms neighborhoods_u apply (intro is_edge_in_He_intro2) apply auto[8]
    using assms neighborhoods_u apply (intro is_edge_in_He_intro2) apply auto[8]
    using assms neighborhoods_v apply (intro is_edge_in_He_intro2) apply auto[8]
    using assms neighborhoods_v apply (intro is_edge_in_He_intro2) apply auto[8]
    using assms neighborhoods_u apply (intro is_edge_in_He_intro2) apply auto[8]
    using assms neighborhoods_u apply (intro is_edge_in_He_intro2) apply auto[8]
    using assms neighborhoods_u apply (intro is_edge_in_He_intro2) apply auto[8]
    using assms neighborhoods_v apply (intro is_edge_in_He_intro2) apply auto[8]
    using assms neighborhoods_v apply (intro is_edge_in_He_intro2) apply auto[8]
    using assms neighborhoods_v apply (intro is_edge_in_He_intro2) apply auto[8]
    using assms neighborhoods_v apply (intro is_edge_in_He_intro2) apply auto[8]
    done
    thus ?thesis
      by auto
qed (* TODO: clean up! *) *)

lemma cost_of_hp_u1: 
  assumes "g1.ugraph_adj_map_invar G" "rep1 e \<in> g1.uedges G"
  shows "cost_of_path (c G) (hp_u1 e) = 11"
  using assms
proof (rule g1.uedge_not_refl_elim; simp only: g1.rep_idem)
  fix u v
  assume "rep1 e = uEdge u v" "u \<noteq> v"
  moreover hence "is_edge_in_He G (uEdge (rep1 e,u,1) (rep1 e,u,5))"
    "is_edge_in_He G (uEdge (rep1 e,u,5) (rep1 e,v,2))"
    "is_edge_in_He G (uEdge (rep1 e,v,2) (rep1 e,v,4))"
    "is_edge_in_He G (uEdge (rep1 e,v,4) (rep1 e,u,6))"
    "is_edge_in_He G (uEdge (rep1 e,u,6) (rep1 e,u,3))"
    "is_edge_in_He G (uEdge (rep1 e,u,3) (rep1 e,u,4))"
    "is_edge_in_He G (uEdge (rep1 e,u,4) (rep1 e,v,6))"
    "is_edge_in_He G (uEdge (rep1 e,v,6) (rep1 e,v,3))"
    "is_edge_in_He G (uEdge (rep1 e,v,3) (rep1 e,v,1))"
    "is_edge_in_He G (uEdge (rep1 e,v,1) (rep1 e,v,5))" 
    "is_edge_in_He G (uEdge (rep1 e,v,5) (rep1 e,u,2))"
    using assms g1.rep_simps by (fastforce intro!: is_edge_in_He_intro 
        simp add: g2.uedges_def2 neighborhood_He g2.isin_set_of_list 
        simp del: He.simps g2.set_of_list.simps)+
  ultimately show ?thesis
    using assms g1.rep_simps by auto
qed

lemma vertices_hp_u1: "g2.vertices (H\<^sub>e e) = List.set (hp_u1 e)"
  apply (cases e; rule g1.rep_cases)
  apply simp
proof -
  fix u v
  assume "e = uEdge u v" "rep1 (uEdge u v) = uEdge u v"
  thus ?thesis
    using g1.rep_simps apply (subst vertices_of_He)
    apply (subst set_vertices_of_He)
    apply blast
    apply fastforce
    done
next
  fix u v
  assume "e = uEdge u v" "rep1 (uEdge u v) = uEdge v u"
  thus ?thesis
    using g1.rep_simps apply (subst vertices_of_He)
    apply (subst set_vertices_of_He)
    apply blast
    apply fastforce
    done
qed (* TODO: clean up! *)

(* lemma hp_u1_inj: "inj hp_u1"
proof
  fix e\<^sub>1 e\<^sub>2
  assume "hp_u1 e\<^sub>1 = hp_u1 e\<^sub>2"
  thus "e\<^sub>1 = e\<^sub>2"
    by (cases e\<^sub>1; cases e\<^sub>2) simp
qed *)

(* lemma hp_u1_disjoint:
  assumes "g1.ugraph_adj_map_invar G" "rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
  shows "List.set (hp_u1 e\<^sub>1) \<inter> List.set (hp_u1 e\<^sub>2) = {}"
proof -
  have "g2.vertices (H\<^sub>e e\<^sub>1) \<inter> g2.vertices (H\<^sub>e e\<^sub>2) = {}"
    using assms by (auto intro!: vertices_of_He_disjoint 
      simp add: vertices_of_He simp del: He.simps vertices_of_He.simps)
  thus ?thesis
    using assms vertices_hp_u1 by auto
qed *)

lemma distinct_hp_u1:
  assumes "g1.ugraph_adj_map_invar G" "rep1 e \<in> g1.uedges G"
  shows "distinct (hp_u1 e)"
  using assms
proof (rule g1.uedge_not_refl_elim; simp only: g1.rep_idem)
  fix u v
  assume "rep1 e = uEdge u v" "u \<noteq> v"
  thus ?thesis
    by auto
qed

lemma hp_u2_non_nil: "hp_u2 e \<noteq> []"
  by (auto split: uedge.splits)

lemma hd_hp_u2: "rep1 e = uEdge u v \<Longrightarrow> hd (hp_u2 e) = (rep1 e,u,2)"
  using g1.rep_simps by (auto split: uedge.splits)

lemma hp_u2_rep_idem: "hp_u2 (rep1 e) = hp_u2 e"
  using g1.rep_idem by auto

lemma path_hp_u2: 
  assumes "rep1 e = uEdge u v"
  shows "g2.path_betw (H\<^sub>e e) (rep1 e,u,2) (hp_u2 e) (rep1 e,u,1)" 
  using assms path_hp_u1 by (simp del: He.simps hp_u1.simps) (intro g2.rev_path[OF _ invar_He])

lemma cost_of_hp_u2: 
  assumes "g1.ugraph_adj_map_invar G" "rep1 e \<in> g1.uedges G"
  shows "cost_of_path (c G) (hp_u2 e) = 11"
  using assms c_sym cost_of_hp_u1 by (auto simp add: cost_of_path_rev)

lemma vertices_hp_u2: "g2.vertices (H\<^sub>e e) = List.set (hp_u2 e)"
  using vertices_hp_u1 by auto

(* lemma hp_u2_inj: "inj hp_u2"
proof
  fix e\<^sub>1 e\<^sub>2
  assume "hp_u2 e\<^sub>1 = hp_u2 e\<^sub>2"
  thus "e\<^sub>1 = e\<^sub>2"
    by (cases e\<^sub>1; cases e\<^sub>2) simp
qed *)

(* lemma hp_u2_disjoint:
  assumes "g1.ugraph_adj_map_invar G" "rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
  shows "List.set (hp_u2 e\<^sub>1) \<inter> List.set (hp_u2 e\<^sub>2) = {}"
  using assms vertices_hp_u1 vertices_hp_u2 hp_u1_disjoint by blast

lemma hp_v2_disjoint:
  assumes "g1.ugraph_adj_map_invar G" "rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
  shows "List.set (hp_u2 e\<^sub>1) \<inter> List.set (hp_v2 e\<^sub>2) = {}"
  sorry *)

lemma distinct_hp_u2:
  assumes "g1.ugraph_adj_map_invar G" "rep1 e \<in> g1.uedges G"
  shows "distinct (hp_u2 e)"
  using assms
proof (rule g1.uedge_not_refl_elim; simp only: g1.rep_idem)
  fix u v
  assume "rep1 e = uEdge u v" "u \<noteq> v"
  thus ?thesis
    by auto
qed

(* lemma path_hp_v1: 
  assumes "rep1 e = uEdge u v"
  shows "g2.path_betw (H\<^sub>e e) (uEdge u v,v,1) (hp_v1 e) (uEdge u v,v,2)" 
    (is "g2.path_betw (H\<^sub>e e) ?v\<^sub>1 _ ?v\<^sub>2")
proof -
  have "rep1 e = rep1 (uEdge u v)"
    using assms g1.rep_idem by metis
  moreover hence "?v\<^sub>2 \<in> g2.vertices (H\<^sub>e e)"
    using assms vertices_of_He by (auto simp add: set_vertices_of_He simp del: vertices_of_He.simps)
  ultimately show "g2.path_betw (H\<^sub>e e) ?v\<^sub>1 (hp_v1 e) ?v\<^sub>2"
    using assms g1.rep_simps by (fastforce intro!: g2.path_betw.intros isin_vertices_of_He_intro2 
        simp add: neighborhood_He g2.isin_set_of_list simp del: He.simps g2.set_of_list.simps)
qed

lemma cost_of_hp_v1: 
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "rep1 e = uEdge u v"
  shows "cost_of_path (c G) (hp_v1 e) = 11"
proof -
  have "is_edge_in_He G (uEdge (rep1 e,v,1) (rep1 e,v,5))"
    "is_edge_in_He G (uEdge (rep1 e,v,5) (rep1 e,u,2))"
    "is_edge_in_He G (uEdge (rep1 e,u,2) (rep1 e,u,4))"
    "is_edge_in_He G (uEdge (rep1 e,u,4) (rep1 e,v,6))"
    "is_edge_in_He G (uEdge (rep1 e,v,6) (rep1 e,v,3))"
    "is_edge_in_He G (uEdge (rep1 e,v,3) (rep1 e,v,4))"
    "is_edge_in_He G (uEdge (rep1 e,v,4) (rep1 e,u,6))"
    "is_edge_in_He G (uEdge (rep1 e,u,6) (rep1 e,u,3))"
    "is_edge_in_He G (uEdge (rep1 e,u,3) (rep1 e,u,1))"
    "is_edge_in_He G (uEdge (rep1 e,u,1) (rep1 e,u,5))" 
    "is_edge_in_He G (uEdge (rep1 e,u,5) (rep1 e,v,2))"
    using assms g1.rep_simps by (fastforce intro!: is_edge_in_He_intro 
        simp add: g2.uedges_def2 neighborhood_He g2.isin_set_of_list 
        simp del: He.simps g2.set_of_list.simps)+
  thus ?thesis
    using assms g1.rep_simps by auto
qed

lemma vertices_hp_v1:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
  shows "g2.vertices (H\<^sub>e e) = List.set (hp_v1 e)"
  using assms
proof (rule g1.uedge_not_refl)
  fix u v 
  assume "rep1 e = uEdge u v" "u \<noteq> v"
  moreover hence "rep1 e = rep1 (uEdge u v)" and "rep1 (uEdge u v) = uEdge u v"
    using g1.rep_simps by blast+
  ultimately show ?thesis
    apply (subst vertices_of_He)
    apply (subst set_vertices_of_He)
    apply fastforce
    sorry
qed

lemma path_hc_v2: 
  assumes "rep1 e = uEdge u v"
  shows "g2.path_betw (H\<^sub>e e) (uEdge u v,v,2) (hp_v2 e) (uEdge u v,v,1)" 
  using assms path_hp_v1 by (simp del: He.simps hp_v1.simps) (intro g2.rev_path[OF _ invar_He])

lemma cost_of_hp_v2: 
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "rep1 e = uEdge u v"
  shows "cost_of_path (c G) (hp_v2 e) = 11"
  sorry

lemma vertices_hp_v2:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
  shows "g2.vertices (H\<^sub>e e) = List.set (hp_v2 e)"
  using assms vertices_hp_v1 by auto *)

lemma hp_v1_rep_idem: "hp_v1 (rep1 e) = hp_v1 e"
  using g1.rep_idem by auto

lemma vertices_hp_v1: "g2.vertices (H\<^sub>e e) = List.set (hp_v1 e)"
  apply (cases e; rule g1.rep_cases)
  apply simp
proof -
  fix u v
  assume "e = uEdge u v" "rep1 (uEdge u v) = uEdge u v"
  thus ?thesis
    using g1.rep_simps apply (subst vertices_of_He)
    apply (subst set_vertices_of_He)
    apply blast
    apply fastforce
    done
next
  fix u v
  assume "e = uEdge u v" "rep1 (uEdge u v) = uEdge v u"
  thus ?thesis
    using g1.rep_simps apply (subst vertices_of_He)
    apply (subst set_vertices_of_He)
    apply blast
    apply fastforce
    done
qed (* TODO: clean up! *)

lemma cost_of_hp_v1: 
  assumes "g1.ugraph_adj_map_invar G" "rep1 e \<in> g1.uedges G"
  shows "cost_of_path (c G) (hp_v1 e) = 11"
  using assms
proof (rule g1.uedge_not_refl_elim; simp only: g1.rep_idem)
  fix u v
  assume "rep1 e = uEdge u v" "u \<noteq> v"
  moreover hence "is_edge_in_He G (uEdge (rep1 e,v,1) (rep1 e,v,5))"
    "is_edge_in_He G (uEdge (rep1 e,v,5) (rep1 e,u,2))"
    "is_edge_in_He G (uEdge (rep1 e,u,2) (rep1 e,u,4))"
    "is_edge_in_He G (uEdge (rep1 e,u,4) (rep1 e,v,6))"
    "is_edge_in_He G (uEdge (rep1 e,v,6) (rep1 e,v,3))"
    "is_edge_in_He G (uEdge (rep1 e,v,3) (rep1 e,v,4))"
    "is_edge_in_He G (uEdge (rep1 e,v,4) (rep1 e,u,6))"
    "is_edge_in_He G (uEdge (rep1 e,u,6) (rep1 e,u,3))"
    "is_edge_in_He G (uEdge (rep1 e,u,3) (rep1 e,u,1))"
    "is_edge_in_He G (uEdge (rep1 e,u,1) (rep1 e,u,5))" 
    "is_edge_in_He G (uEdge (rep1 e,u,5) (rep1 e,v,2))"
    using assms g1.rep_simps by (fastforce intro!: is_edge_in_He_intro 
        simp add: g2.uedges_def2 neighborhood_He g2.isin_set_of_list 
        simp del: He.simps g2.set_of_list.simps)+
  ultimately show ?thesis
    using assms g1.rep_simps by auto
qed

lemma hp_v2_non_nil: "hp_v2 e \<noteq> []"
  by (auto split: uedge.splits)

lemma hd_hp_v2: "rep1 e = uEdge u v \<Longrightarrow> hd (hp_v2 e) = (rep1 e,v,2)"
  using g1.rep_simps by (auto split: uedge.splits)

lemma hp_v2_rep_idem: "hp_v2 (rep1 e) = hp_v2 e"
  using g1.rep_idem by auto

lemma vertices_hp_v2: "g2.vertices (H\<^sub>e e) = List.set (hp_v2 e)"
  using vertices_hp_v1 by auto

lemma distinct_hp_v2:
  assumes "g1.ugraph_adj_map_invar G" "rep1 e \<in> g1.uedges G"
  shows "distinct (hp_v2 e)"
  using assms
proof (rule g1.uedge_not_refl_elim; simp only: g1.rep_idem)
  fix u v
  assume "rep1 e = uEdge u v" "u \<noteq> v"
  thus ?thesis
    by auto
qed

lemma cost_of_hp_v2: 
  assumes "g1.ugraph_adj_map_invar G" "rep1 e \<in> g1.uedges G"
  shows "cost_of_path (c G) (hp_v2 e) = 11"
  using assms c_sym cost_of_hp_v1 by (auto simp add: cost_of_path_rev)

lemma u1_u2_no_edge_in_He: 
  assumes "g1.ugraph_adj_map_invar G"
  shows "\<not> is_edge_in_He G (uEdge (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,1) (e\<^sub>2,u\<^sub>2,2))" 
    (is "\<not> is_edge_in_He G (uEdge ?x ?y)")
proof (rule ccontr; simp only: not_not)
  assume "is_edge_in_He G (uEdge ?x ?y)"
  then obtain e' where "e' \<in> g1.uedges G" and "rep2 (uEdge ?x ?y) \<in> g2.uedges (H\<^sub>e e')"
    using assms by (elim is_edge_in_He_elim)
  hence "isin2 (\<N>\<^sub>2 (H\<^sub>e e') ?x) ?y"
    using invar_He g2.rep_isin_uedges_elim2 by blast
  moreover hence "?x \<in> g2.vertices (H\<^sub>e e')"
    by (intro g2.vertices_memberI1)
  moreover hence "isin2 (V\<^sub>H\<^sub>e e') ?x"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately have "isin2 (\<N>\<^sub>H\<^sub>e ?x) ?y"
    using neighborhood_He by auto
  hence "isin2 (g2.set_of_list [(rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,3),(rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,5)]) ?y"
    using neighborhood_in_He_def2 by auto
  hence "?y \<in> set [(rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,3),(rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,5)]"
    using g2.isin_set_of_list by blast
  thus "False"
    by auto
qed

lemma min_dist_u1_v2_leq4: 
  assumes "g1.ugraph_adj_map_invar G" "rep1 (uEdge u v) \<in> g1.uedges G" "w \<in> {u,v}"
  shows "min_dist_in_He G (rep1 (uEdge u v),u,1) (rep1 (uEdge u v),w,2) \<le> enat 4" 
    (is "min_dist_in_He G ?x ?y \<le> enat 4")
proof -
  have x_vert: "isin2 (V\<^sub>H\<^sub>e (rep1 (uEdge u v))) ?x" (is "isin2 (V\<^sub>H\<^sub>e ?e) ?x") 
    and "isin2 (V\<^sub>H\<^sub>e (rep1 (uEdge u v))) ?y" 
    using assms isin_vertices_of_He_intro by (auto simp add: g1.rep_idem)
  hence "?x \<in> g2.vertices (H\<^sub>e (rep1 (uEdge u v)))"
    and y_vert: "?y \<in> g2.vertices (H\<^sub>e (rep1 (uEdge u v)))" 
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)

  consider "w = u" | "w = v"
    using assms by auto
  then obtain P where path: "g2.path_betw (H\<^sub>e ?e) ?x P ?y" and len_P: "length P \<le> 4"
  proof cases
    assume [simp]: "w = u"
    have "isin2 (\<N>\<^sub>H\<^sub>e ?x) (?e,u,3)" "isin2 (\<N>\<^sub>H\<^sub>e (?e,u,3)) (?e,u,4)" "isin2 (\<N>\<^sub>H\<^sub>e (?e,u,4)) ?y"
      using g2.isin_set_of_list neighborhood_in_He_def2 by (fastforce simp del: g2.set_of_list.simps)+
    moreover hence "isin2 (V\<^sub>H\<^sub>e ?e) ?x" "isin2 (V\<^sub>H\<^sub>e ?e) (?e,u,3)" "isin2 (V\<^sub>H\<^sub>e ?e) (?e,u,4)"
      using x_vert neighborhood_in_He_subset_of_vertices_of_He by blast+
    ultimately have "isin2 (\<N>\<^sub>2 (H\<^sub>e ?e) ?x) (?e,u,3)" 
      "isin2 (\<N>\<^sub>2 (H\<^sub>e ?e) (?e,u,3)) (?e,u,4)" 
      "isin2 (\<N>\<^sub>2 (H\<^sub>e ?e) (?e,u,4)) ?y"
      using neighborhood_He by auto
    hence path: "g2.path_betw (H\<^sub>e ?e) ?x [?x,(?e,u,3),(?e,u,4),?y] ?y"
      using y_vert by (auto intro!: g2.path_betw.intros)
    thus ?thesis
      using that by auto
  next
    assume [simp]: "w = v"
    have "isin2 (\<N>\<^sub>H\<^sub>e ?x) (?e,u,5)" "isin2 (\<N>\<^sub>H\<^sub>e (?e,u,5)) ?y"
      using g2.isin_set_of_list neighborhood_in_He_def2 by (fastforce simp del: g2.set_of_list.simps)+
    moreover hence "isin2 (V\<^sub>H\<^sub>e ?e) ?x" "isin2 (V\<^sub>H\<^sub>e ?e) (?e,u,5)"
      using x_vert neighborhood_in_He_subset_of_vertices_of_He by blast+
    ultimately have "isin2 (\<N>\<^sub>2 (H\<^sub>e ?e) ?x) (?e,u,5)" "isin2 (\<N>\<^sub>2 (H\<^sub>e ?e) (?e,u,5)) ?y"
      using neighborhood_He by auto
    hence path: "g2.path_betw (H\<^sub>e ?e) ?x [?x,(?e,u,5),?y] ?y"
      using y_vert by (auto intro!: g2.path_betw.intros)
    thus ?thesis
      using that by auto
  qed
  have "min_dist_in_He G ?x ?y \<le> g2.path_dist (H\<^sub>e ?e) ?x ?y" 
    using assms min_dist_in_He_leq_path_dist by auto
  also have "... \<le> enat (length (tl P))"
    using path invar_He g2.path_dist_less by blast 
  also have "... \<le> enat 4"
    using len_P by auto
  finally show ?thesis .
qed

lemma min_dist_u1_u2_geq4: 
  assumes "g1.ugraph_adj_map_invar G" "rep1 (uEdge u v) \<in> g1.uedges G"
  shows "min_dist_in_He G (rep1 (uEdge u v),u,1) (rep1 (uEdge u v),u,2) \<ge> enat 4" 
    (is "min_dist_in_He G ?x ?y \<ge> enat 4")
proof (rule ccontr)
  let ?e="rep1 (uEdge u v)"
  assume "\<not> min_dist_in_He G ?x ?y \<ge> enat 4"
  hence "min_dist_in_He G ?x ?y < enat 4"
    by auto

  show "False"
    sorry
qed (* TODO: How do I prove this?! *)

(* lemma cost_u1_u2_eq4:
  assumes "g1.ugraph_adj_map_invar G"
    and "rep1 (uEdge u v) \<in> g1.uedges G" "rep1 (uEdge u w) \<in> g1.uedges G"
  shows "c G (rep1 (uEdge u v),u,1) (rep1 (uEdge u w),u,2) = 4" (is "c G ?x ?y = 4")
proof cases
  assume are_vert: "are_vertices_in_He G ?x ?y"
  moreover hence x_vert: "isin2 (V\<^sub>H\<^sub>e (rep1 (uEdge u v))) ?x" 
    and "isin2 (V\<^sub>H\<^sub>e (rep1 (uEdge u w))) ?y" 
    using assms isin_vertices_of_He_intro by (auto simp add: g1.rep_idem)
  moreover hence "?x \<in> g2.vertices (H\<^sub>e (rep1 (uEdge u v)))" (is "_ \<in> g2.vertices (H\<^sub>e ?e)") 
    and y_vert: "?y \<in> g2.vertices (H\<^sub>e (rep1 (uEdge u w)))" 
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately have "rep1 (uEdge u v) = rep1 (uEdge u w)"
    using assms vertices_in_He_rep_iff g1.rep_idem[symmetric] by auto
  hence [simp]: "w = v"
    using g1.rep_eq_iff by auto
    
  have "\<not> is_edge_in_He G (uEdge ?x ?y)"
    using assms by (intro u1_u2_no_edge_in_He)
  moreover have "min_dist_in_He G ?x ?y \<le> enat 4"
    using assms by (subst \<open>w = v\<close>; intro min_dist_u1_v2_leq4) auto
  moreover have "min_dist_in_He G ?x ?y \<ge> enat 4"
    using assms by (subst \<open>w = v\<close>; intro min_dist_u1_u2_geq4)
  moreover hence "the_enat (min_dist_in_He G ?x ?y) = 4"
    using calculation by (cases "min_dist_in_He G ?x ?y") auto
  ultimately show ?thesis
    using are_vert by auto
next
  assume no_vert: "\<not> are_vertices_in_He G ?x ?y"
  moreover have "isin2 (V\<^sub>H\<^sub>e (rep1 (uEdge u v))) ?x" (is "isin2 (V\<^sub>H\<^sub>e ?e\<^sub>x) _")
    using assms g1.rep_idem by (intro isin_vertices_of_He_intro) auto
  moreover hence "?x \<in> g2.vertices (H\<^sub>e ?e\<^sub>x)"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  moreover have "isin2 (V\<^sub>H\<^sub>e (rep1 (uEdge u w))) ?y" (is "isin2 (V\<^sub>H\<^sub>e ?e\<^sub>y) _")
    using assms g1.rep_idem by (intro isin_vertices_of_He_intro) auto
  moreover hence "?y \<in> g2.vertices (H\<^sub>e ?e\<^sub>y)"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately have "rep1 ?e\<^sub>x \<noteq> rep1 ?e\<^sub>y"
    using assms vertices_in_He_rep_iff g1.rep_idem by auto
  moreover have "\<not> is_edge_in_He G (uEdge ?x ?y)"
    using assms no_vert edge_in_He_are_vertices by auto
  ultimately show ?thesis
    using no_vert by auto
qed *)

(* lemma cost_leq4:
  assumes "g1.ugraph_adj_map_invar G"
    and "rep1 (uEdge u v) \<in> g1.uedges G" "rep1 (uEdge u w) \<in> g1.uedges G" "i\<^sub>v \<in> {1,2}" "i\<^sub>w \<in> {1,2}"
  shows "c G (rep1 (uEdge u v),u,i\<^sub>v) (rep1 (uEdge u w),u,i\<^sub>w) \<le> 4" (is "c G ?x ?y \<le> 4")
proof cases
  assume "are_vertices_in_He G ?x ?y"
  thus ?thesis
    sorry
next
  assume no_vert: "\<not> are_vertices_in_He G ?x ?y"
  moreover have "isin2 (V\<^sub>H\<^sub>e (rep1 (uEdge u v))) ?x" (is "isin2 (V\<^sub>H\<^sub>e ?e\<^sub>x) _")
    using assms g1.rep_idem by (intro isin_vertices_of_He_intro) auto
  moreover hence "?x \<in> g2.vertices (H\<^sub>e ?e\<^sub>x)"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  moreover have "isin2 (V\<^sub>H\<^sub>e (rep1 (uEdge u w))) ?y" (is "isin2 (V\<^sub>H\<^sub>e ?e\<^sub>y) _")
    using assms g1.rep_idem by (intro isin_vertices_of_He_intro) auto
  moreover hence "?y \<in> g2.vertices (H\<^sub>e ?e\<^sub>y)"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately have "rep1 ?e\<^sub>x \<noteq> rep1 ?e\<^sub>y"
    using assms vertices_in_He_rep_iff g1.rep_idem by auto
  moreover have "\<not> is_edge_in_He G (uEdge ?x ?y)"
    using assms no_vert edge_in_He_are_vertices by auto
  ultimately show "c G ?x ?y \<le> 4"
    using no_vert by auto
qed *)

lemma cost_x_y_geq4:
  assumes "g1.ugraph_adj_map_invar G" "\<not> are_vertices_in_He G x y"
  shows "c G x y \<ge> 4"
proof (cases x; cases y)
  fix e\<^sub>x w\<^sub>x i\<^sub>x e\<^sub>y w\<^sub>y i\<^sub>y
  assume [simp]: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)" and [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
  have "\<not> is_edge_in_He G (uEdge x y)"
    using assms edge_in_He_are_vertices by blast
  thus ?thesis
    using assms by auto
qed

lemma cost_x_y_leq5:
  assumes "g1.ugraph_adj_map_invar G" "\<not> are_vertices_in_He G x y"
  shows "c G x y \<le> 5"
proof (cases x; cases y)
  fix e\<^sub>x w\<^sub>x i\<^sub>x e\<^sub>y w\<^sub>y i\<^sub>y
  assume [simp]: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)" and [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
  have "\<not> is_edge_in_He G (uEdge x y)"
    using assms edge_in_He_are_vertices by blast
  thus ?thesis
    using assms by auto
qed

lemma cost_u1_u2_leq5:
  assumes "g1.ugraph_adj_map_invar G"     
  shows "c G (e\<^sub>1,w\<^sub>1,1) (e\<^sub>2,w\<^sub>2,2) \<le> 5" (is "c G ?x ?y \<le> 5")
proof cases 
  assume "are_vertices_in_He G ?x ?y"
  then obtain e where "e \<in> g1.uedges G" "?x \<in> g2.vertices (H\<^sub>e e)" "?y \<in> g2.vertices (H\<^sub>e e)"
    using assms by (elim are_vertices_in_He_elim)
  hence "isin2 (V\<^sub>H\<^sub>e e) ?x" and "isin2 (V\<^sub>H\<^sub>e e) ?y"
    using invar_vertices_of_He by (auto simp add: vertices_of_He[symmetric] g2.set_specs 
        simp del: vertices_of_He.simps)
  hence "e\<^sub>1 = rep1 e" and "e\<^sub>2 = rep1 e"
    by (auto intro!: isin_vertices_of_He_edge[symmetric])
  hence [simp]: "e\<^sub>2 = e\<^sub>1"
    by auto

  obtain u v where "?y = (uEdge u v,w\<^sub>2,2)" and "rep1 e = uEdge u v" and isin_w2: "w\<^sub>2 \<in> {u,v}"
    using \<open>isin2 (V\<^sub>H\<^sub>e e) ?y\<close> by (elim isin_vertices_of_He_elim2) auto
  then consider "w\<^sub>1 = u" | "w\<^sub>1 = v"
    using \<open>isin2 (V\<^sub>H\<^sub>e e) ?x\<close> by (elim isin_vertices_of_He_elim2) auto
  thus ?thesis
  proof cases
    assume [simp]: "w\<^sub>1 = u"
    hence [simp]: "e\<^sub>1 = rep1 (uEdge u v)"
      using \<open>e\<^sub>1 = rep1 e\<close> g1.rep_simps(1)[OF \<open>rep1 e = uEdge u v\<close>] by auto
    have "\<not> is_edge_in_He G (uEdge ?x ?y)"
      using assms u1_u2_no_edge_in_He by simp
    moreover have "rep1 (uEdge u v) \<in> g1.uedges G"
      using \<open>e \<in> g1.uedges G\<close> 
      by (auto intro!: g1.rep_of_edge_is_edge simp add: \<open>rep1 e = uEdge u v\<close>[symmetric])
    moreover hence "min_dist_in_He G ?x ?y \<le> enat 4"
      using assms isin_w2 min_dist_u1_v2_leq4 by auto
    moreover hence "the_enat (min_dist_in_He G ?x ?y) \<le> 4"
      by (cases "min_dist_in_He G ?x ?y") auto
    ultimately show ?thesis
      by simp
  next
    assume [simp]: "w\<^sub>1 = v"
    hence [simp]: "e\<^sub>1 = rep1 (uEdge v u)"
      using \<open>e\<^sub>1 = rep1 e\<close> g1.rep_simps(2)[OF \<open>rep1 e = uEdge u v\<close>] by auto
    have "\<not> is_edge_in_He G (uEdge ?x ?y)"
      using assms u1_u2_no_edge_in_He by simp
    moreover have "rep1 (uEdge v u) \<in> g1.uedges G"
      using \<open>e \<in> g1.uedges G\<close> g1.rep_simps
      by (auto intro!: g1.rep_of_edge_is_edge simp add: \<open>rep1 e = uEdge u v\<close>[symmetric])
    moreover hence "min_dist_in_He G ?x ?y \<le> enat 4"
      using assms isin_w2 min_dist_u1_v2_leq4 by auto
    moreover hence "the_enat (min_dist_in_He G ?x ?y) \<le> 4"
      by (cases "min_dist_in_He G ?x ?y") auto
    ultimately show ?thesis
      by simp
  qed
next
  assume "\<not> are_vertices_in_He G ?x ?y"
  thus ?thesis
    using assms cost_x_y_leq5 by auto
qed

lemma hd_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 N\<^sub>u" and "\<exists>v. isin1 N\<^sub>u v" \<comment> \<open>The neighborhood is non-empty.\<close>
      and "\<And>v. isin1 N\<^sub>u v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  obtains v where "isin1 N\<^sub>u v" "rep1 (uEdge u v) \<in> g1.uedges G" "hd (hp_for_neighborhood u N\<^sub>u) = (rep1 (uEdge u v),u,2)"
  using assms(2)
proof (rule fold6.fold_setE)
  let ?f="\<lambda>v. if rep1 (uEdge u v) = uEdge u v then hp_u2 (uEdge u v) else hp_v2 (uEdge u v)"
  fix vs
  assume "distinct vs" "List.set vs = set1 N\<^sub>u" "fold_v1set1 (\<lambda>v T. T @ ?f v) N\<^sub>u [] = fold (\<lambda>v T. T @ ?f v) vs []"
  moreover hence "vs \<noteq> []" "\<exists>v \<in> set vs. ?f v \<noteq> []"
    using assms by (auto split: uedge.splits simp add: g1.set_specs)
  moreover then obtain v where "v \<in> set vs" "hd (concat (map ?f vs)) = hd (?f v)"
    by (elim hd_concat_map_elim)
  moreover have "hd (?f v) = (rep1 (uEdge u v),u,2)"
  proof -
    have "rep1 (uEdge u v) \<in> g1.uedges G"
      using assms \<open>List.set vs = set1 N\<^sub>u\<close> \<open>v \<in> set vs\<close> by (auto simp add: g1.set_specs)
    then consider "rep1 (uEdge u v) = uEdge u v" "u \<noteq> v" | "rep1 (uEdge u v) = uEdge v u" "u \<noteq> v"
      using assms g1.uedge_not_refl g1.is_rep by blast 
    thus ?thesis
      by cases auto
  qed
  ultimately show ?thesis
    using assms that by (auto simp add: g1.set_specs fold_concat_map)
qed

lemma last_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 N\<^sub>u" and "\<exists>v. isin1 N\<^sub>u v" \<comment> \<open>The neighborhood is non-empty.\<close>
      and "\<And>v. isin1 N\<^sub>u v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  obtains v where "isin1 N\<^sub>u v" "rep1 (uEdge u v) \<in> g1.uedges G" "last (hp_for_neighborhood u N\<^sub>u) = (rep1 (uEdge u v),u,1)"
  using assms(2)
proof (rule fold6.fold_setE)
  let ?f="\<lambda>v. if rep1 (uEdge u v) = uEdge u v then hp_u2 (uEdge u v) else hp_v2 (uEdge u v)"
  fix vs
  assume "distinct vs" "List.set vs = set1 N\<^sub>u" "fold_v1set1 (\<lambda>v T. T @ ?f v) N\<^sub>u [] = fold (\<lambda>v T. T @ ?f v) vs []"
  moreover hence "vs \<noteq> []" "\<exists>v \<in> set vs. ?f v \<noteq> []"
    using assms by (auto split: uedge.splits simp add: g1.set_specs)
  moreover then obtain v where "v \<in> set vs" "last (concat (map ?f vs)) = last (?f v)"
    by (elim last_concat_map_elim)
  moreover have "last (?f v) = (rep1 (uEdge u v),u,1)"
  proof -
    have "rep1 (uEdge u v) \<in> g1.uedges G"
      using assms \<open>List.set vs = set1 N\<^sub>u\<close> \<open>v \<in> set vs\<close> by (auto simp add: g1.set_specs)
    then consider "rep1 (uEdge u v) = uEdge u v" "u \<noteq> v" | "rep1 (uEdge u v) = uEdge v u" "u \<noteq> v"
      using assms g1.uedge_not_refl g1.is_rep by blast 
    thus ?thesis
      by cases auto
  qed
  ultimately show ?thesis
    using assms that by (auto simp add: g1.set_specs fold_concat_map)
qed

end

section \<open>Properties of Reduction-Functions\<close>

context VC4_To_mTSP
begin

lemma vertices_f:
  assumes "g1.ugraph_adj_map_invar G"
  shows "g2.vertices (f G) = set2 (V\<^sub>H G)"
  using assms invar_vertices_of_H at_least_two_vertices_in_H
  by (simp only: f.simps; intro vertices_complete_graph)

lemma vertices_f_non_empty:
  assumes "g1.ugraph_adj_map_invar G" 
      and "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
  shows "\<exists>v. v \<in> g2.vertices (f G)"
proof -
  obtain e v where "e \<in> g1.uedges G" "isin2 (V\<^sub>H\<^sub>e e) v"
    using assms vertices_of_He_non_empty by blast
  hence "v \<in> \<Union> ((set2 o V\<^sub>H\<^sub>e) ` g1.uedges G)"
    using invar_vertices_of_He by (auto simp add: g2.set_specs)
  thus "\<exists>v. v \<in> g2.vertices (f G)"
    using assms(1) vertices_f set_vertices_of_H by blast
qed

lemma obtain_vertex_of_He:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" and "e \<in> g1.uedges G"
  obtains x where "x \<in> List.set T" "isin2 (V\<^sub>H\<^sub>e e) x"
proof (cases e)
  case (uEdge u v)
  have "List.set (tl T) = g2.vertices (f G)"
    using assms g2.is_hc_AdjE by auto
  also have "... = \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` g1.uedges G)"
    using assms vertices_f set_vertices_of_H by auto
  finally have "set2 (V\<^sub>H\<^sub>e e) \<subseteq> List.set T"
    using assms set_tl_subset by fastforce
  moreover have "isin2 (V\<^sub>H\<^sub>e e) (rep1 e,u,1)"
    using assms uEdge by (intro isin_vertices_of_He_intro) auto
  moreover hence "(rep1 e,u,1) \<in> set2 (V\<^sub>H\<^sub>e e)"
    using invar_vertices_of_He by (auto simp add: g2.set_specs)
  ultimately obtain x where "x \<in> List.set T" "x \<in> set2 (V\<^sub>H\<^sub>e e)"
    by (auto simp del: vertices_of_He.simps) 
  moreover hence "isin2 (V\<^sub>H\<^sub>e e) x"
    using invar_vertices_of_He by (auto simp add: g2.set_specs)
  ultimately show ?thesis
    using that by auto
qed

lemma rotate_tour_all_vertices_of_He:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" and "e \<in> g1.uedges G"
      and "cost_of_path (\<lambda>x y. if \<not> isin2 (V\<^sub>H\<^sub>e e) x \<and> isin2 (V\<^sub>H\<^sub>e e) y then (1::nat) else 0) T = 0"
      and "x \<in> set T"
  shows "isin2 (V\<^sub>H\<^sub>e e) x"
proof -
  obtain u where "g2.path_betw (f G) u T u"
    using assms by (elim g2.is_hc_AdjE)
  hence "T \<noteq> []" "hd T = last T"
    using assms by (auto simp add: g2.path_non_empty g2.hd_path_betw g2.last_path_betw)
  then consider "\<And>z. z \<in> set T \<Longrightarrow> \<not> isin2 (V\<^sub>H\<^sub>e e) z" | "\<And>z. z \<in> set T \<Longrightarrow> isin2 (V\<^sub>H\<^sub>e e) z"
    using assms by (elim rotate_tour_cost_0_all_eq) auto
  moreover obtain y where "y \<in> set T" "isin2 (V\<^sub>H\<^sub>e e) y"
    using assms by (elim obtain_vertex_of_He)
  ultimately show ?thesis
    using assms by blast
qed

(* lemma map_edge_to_hp_start_vertex_is_vertex:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" and "e \<in> g1.uedges G"
  shows "map_edge_to_hp_start_vertex G T e \<in> List.set T"
proof -
  have "hd T = last T"
    using assms g2.is_hc_AdjE sorry
  hence "set T = set (rotate_tour (isin2 (V\<^sub>H\<^sub>e e)) T)"
    by (intro set_rotate_tour)
  show ?thesis
    sorry
qed *)

lemma map_edge_to_hp_start_vertex_cases:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" 
      and "e \<in> g1.uedges G" "rep1 e = rep1 (uEdge u v)"
  obtains "map_edge_to_hp_start_vertex G T e = (rep1 e,u,1)" | "map_edge_to_hp_start_vertex G T e = (rep1 e,v,1)"
proof -
  let ?f="isin2 (V\<^sub>H\<^sub>e e)"

  obtain x where "g2.path_betw (f G) x T x"
    using assms by (elim g2.is_hc_AdjE)
  hence "hd T = last T"                   
    using assms by (auto simp add: g2.path_non_empty g2.hd_path_betw g2.last_path_betw)

  have "isin2 (V\<^sub>H\<^sub>e e) (rep1 e,u,1)" "isin2 (V\<^sub>H\<^sub>e e) (rep1 e,u,2)"
    using assms(4) by (auto intro!: isin_vertices_of_He_intro simp del: vertices_of_He.simps)
  hence "(rep1 e,u,1) \<in> set2 (V\<^sub>H\<^sub>e e)" "(rep1 e,u,2) \<in> set2 (V\<^sub>H\<^sub>e e)"
    using invar_vertices_of_He by (auto simp add: g2.set_specs)
  hence "(rep1 e,u,1) \<in> g2.vertices (f G)" "(rep1 e,u,2) \<in> g2.vertices (f G)"
    using assms(1,3) vertices_f set_vertices_of_H by auto
  moreover have "g2.vertices (f G) = List.set (tl T)"
    using assms by (elim g2.is_hc_AdjE)
  ultimately have "(rep1 e,u,1) \<in> List.set (tl T)" "(rep1 e,u,2) \<in> List.set (tl T)"
    by auto
  hence "length T \<ge> 2"
    by (induction T rule: list012.induct) auto
  hence "length (rotate_tour (isin2 (V\<^sub>H\<^sub>e e)) T) \<ge> 2"
    by (simp add: length_rotate_tour del: rotate_tour.simps)
  then obtain x y xs where rotT: "rotate_tour (isin2 (V\<^sub>H\<^sub>e e)) T = x#y#xs"
    by (elim list_len_geq2_elim)
  hence "y \<in> set (rotate_tour (isin2 (V\<^sub>H\<^sub>e e)) T)"
    by auto
  hence "y \<in> set T"
    using set_rotate_tour[OF \<open>hd T = last T\<close>] by auto

  let ?c="\<lambda>x y. if \<not> isin2 (V\<^sub>H\<^sub>e e) x \<and> isin2 (V\<^sub>H\<^sub>e e) y then (1::nat) else 0"
  consider "cost_of_path ?c T = 0" | "cost_of_path ?c T > 0"
    by auto
  hence "?f y"
  proof cases
    assume "cost_of_path ?c T = 0"
    then show ?thesis
      using assms \<open>y \<in> set T\<close> by (intro rotate_tour_all_vertices_of_He)
  next
    assume "cost_of_path ?c T > 0"
    then show ?thesis 
      using rotT by (intro not_hd_snd_rotate_tour(2)[of ?f])
  qed
  moreover obtain e' w i where [simp]: "y = (e',w,i)"
    by (cases y)
  ultimately have "rep1 e = e'"
    by (auto elim: isin_vertices_of_He_elim simp del: vertices_of_He.simps)
  hence [simp]: "rep1 e = rep1 e'"
    by (auto simp add: g1.rep_idem)
  then consider "rep1 e' = uEdge u v" | "rep1 e' = uEdge v u"
    using assms g1.is_rep by auto
  hence "map_edge_to_hp_start_vertex G T e \<in> {(rep1 e,u,1),(rep1 e,v,1)}"
    by cases (auto simp add: rotT simp del: rotate_tour.simps vertices_of_He.simps)
  thus ?thesis
    using that assms by blast
qed

lemma map_edge_to_covering_vertex_cases:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" 
      and "e \<in> g1.uedges G" "rep1 e = rep1 (uEdge u v)"
  shows "map_edge_to_covering_vertex G T e \<in> {u,v}"
  using assms by (rule map_edge_to_hp_start_vertex_cases) auto

lemma map_edge_to_hp_start_vertex_cases2:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" and "e \<in> g1.uedges G"
  shows "map_edge_to_hp_start_vertex G T e = (rep1 e,map_edge_to_covering_vertex G T e,1)"
  using assms(1,3)
proof (rule g1.uedge_not_refl_elim)
  let ?x="map_edge_to_hp_start_vertex G T e"
  fix u v
  assume [symmetric]: "rep1 e = uEdge u v"
  hence "rep1 e = rep1 (uEdge u v)"
    by (simp add: g1.rep_idem)
  then consider "?x = (rep1 e,u,1)" | "?x = (rep1 e,v,1)"
    using assms by (elim map_edge_to_hp_start_vertex_cases)
  thus ?thesis
    by cases auto
qed

lemma invar_g:
  assumes "g1.ugraph_adj_map_invar G"
  shows "set_invar1 (g G T)"
  using assms
proof (rule fold5.fold_uedgesE)
  let ?f="insert1 o (map_edge_to_covering_vertex G T)"
  fix es 
  assume "distinct es" "map rep1 es = es" and [simp]: "List.set es = g1.uedges G" and
    "fold_g1_uedges5 ?f G set_empty1 = fold ?f es set_empty1"
  hence [simp]: "g G T = g1.insert_all (map (map_edge_to_covering_vertex G T) es) set_empty1"
    by (auto simp: fold_map)
  thus "set_invar1 (g G T)"
    using g1.set_specs by (auto intro!: g1.invar_insert_all simp del: g.simps g1.insert_all.simps)
qed

lemma set_g:
  assumes "g1.ugraph_adj_map_invar G"
  shows "set1 (g G T) = {map_edge_to_covering_vertex G T e | e. e \<in> g1.uedges G}"
  using assms
proof (rule fold5.fold_uedgesE)
  let ?f="insert1 o (map_edge_to_covering_vertex G T)"
  fix es 
  assume "distinct es" "map rep1 es = es" and [simp]: "List.set es = g1.uedges G" and
    "fold_g1_uedges5 ?f G set_empty1 = fold ?f es set_empty1"
  hence [simp]: "g G T = g1.insert_all (map (map_edge_to_covering_vertex G T) es) set_empty1"
    by (auto simp: fold_map)
  thus "set1 (g G T) = {map_edge_to_covering_vertex G T e | e. e \<in> g1.uedges G}"
    using g1.set_specs g1.set_insert_all by auto
qed

lemma invar_partition_for_vertex: "g1.ugraph_adj_map_invar G \<Longrightarrow> set_invar1 (\<P> G X u)"
  using filter1.invar_filter_set by auto

lemma uedge_of_partition_for_vertex:
  assumes "g1.ugraph_adj_map_invar G" "isin1 (\<P> G X u) v"
  shows "rep1 (uEdge u v) \<in> g1.uedges G"
proof (rule filter1.filter_set_elim)
  let ?f="\<lambda>v. \<not> isin1 X v \<or> rep1 (uEdge u v) = uEdge u v"
  show "set_invar1 (\<N>\<^sub>1 G u)"
    using assms by auto
  then obtain xs where "distinct xs" and set_xs_filter: "List.set xs = set1 (\<N>\<^sub>1 G u)"
    "set1 (filter_v1set ?f (\<N>\<^sub>1 G u)) = List.set (filter ?f xs)"
    using assms by (elim filter1.filter_set_elim)
  moreover hence "v \<in> set xs" "isin1 (\<N>\<^sub>1 G u) v"
    using assms invar_partition_for_vertex by (auto simp add: g1.set_specs)
  thus "rep1 (uEdge u v) \<in> g1.uedges G"
    using g1.isin_uedges by auto
qed

lemma isin_partition_for_vertex:
  assumes "g1.ugraph_adj_map_invar G" 
  shows "isin1 (\<P> G X u) v \<longleftrightarrow> (isin1 (\<N>\<^sub>1 G u) v \<and> (\<not> isin1 X v \<or> rep1 (uEdge u v) = uEdge u v))"
proof (rule filter1.filter_set_elim)
  let ?f="\<lambda>v. \<not> isin1 X v \<or> rep1 (uEdge u v) = uEdge u v"
  show "set_invar1 (\<N>\<^sub>1 G u)"
    using assms by auto
  then obtain xs where "distinct xs" and set_xs_filter: "List.set xs = set1 (\<N>\<^sub>1 G u)"
    "set1 (filter_v1set ?f (\<N>\<^sub>1 G u)) = List.set (filter ?f xs)"
    using assms by (elim filter1.filter_set_elim)
  moreover hence "v \<in> List.set (filter ?f xs) \<longleftrightarrow> v \<in> List.set xs \<and> ?f v"
    by auto
  ultimately show ?thesis
    using assms invar_partition_for_vertex by (auto simp add: g1.set_specs)
qed

lemma isin_partition_for_vertex_intro:
  assumes "g1.ugraph_adj_map_invar G" "isin1 (\<N>\<^sub>1 G u) v" "\<not> isin1 X v \<or> rep1 (uEdge u v) = uEdge u v"
  shows "isin1 (\<P> G X u) v"
  using assms isin_partition_for_vertex by auto

(* lemma partition_for_vertex_disjoint:
  assumes "g1.ugraph_adj_map_invar G" "isin1 X u\<^sub>1" "isin1 X u\<^sub>2" "u\<^sub>1 \<noteq> u\<^sub>2"
  shows "{rep1 (uEdge u\<^sub>1 v) |v. isin1 (\<P> G X u\<^sub>1) v} \<inter> {rep1 (uEdge u\<^sub>2 v) |v. isin1 (\<P> G X u\<^sub>2) v} = {}" 
    (is "?E\<^sub>1 \<inter> ?E\<^sub>2 = _")
proof (rule ccontr)
  let ?f\<^sub>1="\<lambda>v. \<not> isin1 X v \<or> rep1 (uEdge u\<^sub>1 v) = uEdge u\<^sub>1 v"
  let ?f\<^sub>2="\<lambda>v. \<not> isin1 X v \<or> rep1 (uEdge u\<^sub>2 v) = uEdge u\<^sub>2 v"
  assume "?E\<^sub>1 \<inter> ?E\<^sub>2 \<noteq> {}"
  then obtain v\<^sub>1 v\<^sub>2 where "isin1 (\<P> G X u\<^sub>1) v\<^sub>1" "isin1 (\<P> G X u\<^sub>2) v\<^sub>2" "rep1 (uEdge u\<^sub>1 v\<^sub>1) = rep1 (uEdge u\<^sub>2 v\<^sub>2)"
    using assms by auto
  hence "?f\<^sub>1 u\<^sub>2" "?f\<^sub>2 u\<^sub>1" 
    using assms isin_partition_for_vertex g1.rep_eq_iff by auto
  thus "False"
    using assms by (auto simp add: g1.is_rep)
qed

lemma partition_by_vertex_cover:                     
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X"
  shows "\<Union> {{rep1 (uEdge u v) |v. isin1 (\<P> G X u) v} |u. isin1 X u} = g1.uedges G" (is "?P = _")
proof
  show "?P \<subseteq> g1.uedges G"
    using assms uedge_of_partition_for_vertex by auto
next
  show "g1.uedges G \<subseteq> ?P"
  proof
    fix e
    assume "e \<in> g1.uedges G"
    moreover then obtain u v where [simp]: "e = uEdge u v" and v_isin_Nu: "isin1 (\<N>\<^sub>1 G u) v"
      using assms by (elim g1.isin_uedges_elim)
    ultimately have rep_uv: "rep1 (uEdge u v) = uEdge u v"
      by (auto simp add: g1.rep_of_edge)
    then consider "isin1 X u" | "isin1 X v" "\<not> isin1 X u"
      using assms v_isin_Nu g1.is_vc_AdjE by auto
    thus "e \<in> ?P"
    proof cases
      assume "isin1 X u"
      moreover hence "uEdge u v \<in> {rep1 (uEdge u v) |v. isin1 (\<P> G X u) v}"
        using assms v_isin_Nu rep_uv 
          by (force intro!: isin_partition_for_vertex_intro simp del: partition_for_vertex.simps)
      ultimately show ?thesis
        by auto
    next
      assume "isin1 X v" "\<not> isin1 X u"
      moreover have "rep1 (uEdge v u) = uEdge u v"
        using rep_uv g1.rep_simps by auto
      moreover have "isin1 (\<N>\<^sub>1 G v) u"
        using assms v_isin_Nu by auto
      ultimately have "uEdge u v \<in> {rep1 (uEdge v u) |u. isin1 (\<P> G X v) u}"
        using assms by (force intro!: isin_partition_for_vertex_intro simp del: partition_for_vertex.simps)
      thus ?thesis
        using \<open>isin1 X v\<close> by auto
    qed
  qed
qed *)

lemma partition_for_vertex_disjoint:
  assumes "g1.ugraph_adj_map_invar G" "isin1 X u\<^sub>1" "isin1 X u\<^sub>2" "u\<^sub>1 \<noteq> u\<^sub>2"
  shows "(\<lambda>v. rep1 (uEdge u\<^sub>1 v)) ` set1 (\<P> G X u\<^sub>1) \<inter> (\<lambda>v. rep1 (uEdge u\<^sub>2 v)) ` set1 (\<P> G X u\<^sub>2) = {}" 
    (is "?E\<^sub>1 \<inter> ?E\<^sub>2 = _")
proof (rule ccontr)
  let ?f\<^sub>1="\<lambda>v. \<not> isin1 X v \<or> rep1 (uEdge u\<^sub>1 v) = uEdge u\<^sub>1 v"
  let ?f\<^sub>2="\<lambda>v. \<not> isin1 X v \<or> rep1 (uEdge u\<^sub>2 v) = uEdge u\<^sub>2 v"
  assume "?E\<^sub>1 \<inter> ?E\<^sub>2 \<noteq> {}"
  then obtain v\<^sub>1 v\<^sub>2 where "isin1 (\<P> G X u\<^sub>1) v\<^sub>1" "isin1 (\<P> G X u\<^sub>2) v\<^sub>2" "rep1 (uEdge u\<^sub>1 v\<^sub>1) = rep1 (uEdge u\<^sub>2 v\<^sub>2)"
    using assms invar_partition_for_vertex by (auto simp add: g1.set_specs)
  hence "?f\<^sub>1 u\<^sub>2" "?f\<^sub>2 u\<^sub>1" 
    using assms isin_partition_for_vertex g1.rep_eq_iff by auto
  thus "False"
    using assms by (auto simp add: g1.is_rep)
qed

lemma partition_for_vertex_disjoint_set_compr:
  assumes "g1.ugraph_adj_map_invar G" "isin1 X u\<^sub>1" "isin1 X u\<^sub>2" "u\<^sub>1 \<noteq> u\<^sub>2"
  shows "{rep1 (uEdge u\<^sub>1 v) |v. isin1 (\<P> G X u\<^sub>1) v} \<inter> {rep1 (uEdge u\<^sub>2 v) |v. isin1 (\<P> G X u\<^sub>2) v} = {}" 
proof -
  have "{rep1 (uEdge u\<^sub>1 v) |v. isin1 (\<P> G X u\<^sub>1) v} = (\<lambda>v. rep1 (uEdge u\<^sub>1 v)) ` set1 (\<P> G X u\<^sub>1)"
    and "{rep1 (uEdge u\<^sub>2 v) |v. isin1 (\<P> G X u\<^sub>2) v} = (\<lambda>v. rep1 (uEdge u\<^sub>2 v)) ` set1 (\<P> G X u\<^sub>2)"
    using assms(1) invar_partition_for_vertex by (auto simp add: g1.set_specs)
  thus ?thesis
    using assms partition_for_vertex_disjoint by auto
qed

lemma partition_by_vertex_cover:                     
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X"
  shows "(\<Union>u\<in>set1 X. {rep1 (uEdge u v) | v. isin1 (\<P> G X u) v}) = g1.uedges G" (is "?P = _")
proof
  show "?P \<subseteq> g1.uedges G"
    using assms uedge_of_partition_for_vertex by auto
next
  show "g1.uedges G \<subseteq> ?P"
  proof
    fix e
    assume "e \<in> g1.uedges G"
    moreover then obtain u v where [simp]: "e = uEdge u v" and v_isin_Nu: "isin1 (\<N>\<^sub>1 G u) v"
      using assms by (elim g1.isin_uedges_elim)
    ultimately have rep_uv: "rep1 (uEdge u v) = uEdge u v"
      by (auto simp add: g1.rep_of_edge)
    then consider "isin1 X u" | "isin1 X v" "\<not> isin1 X u"
      using assms v_isin_Nu g1.is_vc_AdjE by auto
    thus "e \<in> ?P"
    proof cases
      assume "isin1 X u"
      moreover hence "uEdge u v \<in> {rep1 (uEdge u v) |v. isin1 (\<P> G X u) v}"
        using assms v_isin_Nu rep_uv 
          by (force intro!: isin_partition_for_vertex_intro simp del: partition_for_vertex.simps)
      ultimately show ?thesis
        using assms by (auto simp add: g1.set_specs)
    next
      assume "isin1 X v" "\<not> isin1 X u"
      moreover have "rep1 (uEdge v u) = uEdge u v"
        using rep_uv g1.rep_simps by auto
      moreover have "isin1 (\<N>\<^sub>1 G v) u"
        using assms v_isin_Nu by auto
      ultimately have "uEdge u v \<in> {rep1 (uEdge v u) |u. isin1 (\<P> G X v) u}"
        using assms by (force intro!: isin_partition_for_vertex_intro simp del: partition_for_vertex.simps)
      thus ?thesis
        using assms \<open>isin1 X v\<close> by (auto simp add: g1.set_specs)
    qed
  qed
qed

end

section \<open>Feasibility of the Reduction-Functions\<close>

context VC4_To_mTSP
begin

lemma f_is_complete: 
  assumes "g1.ugraph_adj_map_invar G"
  shows "g2.is_complete_Adj (f G)"
  \<comment> \<open>The graph \<open>f G\<close> is complete.\<close>
  using assms invar_vertices_of_H at_least_two_vertices_in_H
  by (simp del: complete_graph.simps; intro complete_graph_is_complete_Adj) auto

lemma c_geq_0: "c G x y \<ge> 0"
  by (cases x; cases y) simp

lemma c_tri_inequality:
  assumes "g1.ugraph_adj_map_invar G" 
      and "x \<in> g2.vertices (f G)" "y \<in> g2.vertices (f G)" "z \<in> g2.vertices (f G)"
  shows "c G x z \<le> c G x y + c G y z"
  \<comment> \<open>The cost function \<open>c\<close> for the graph \<open>f G\<close> satisfies the triangle-inequality.\<close>
  sorry (* TODO *)

lemma g_is_vc:
  assumes "g1.ugraph_adj_map_invar G" and "g2.is_hc_Adj (f G) T"
  shows "g1.is_vc_Adj G (g G T)"
  \<comment> \<open>The function \<open>g\<close> always computes a vertex cover of the graph \<open>G\<close> (feasible solution).\<close>
proof (intro g1.is_vc_AdjI) 
  show "\<And>u v. isin1 (\<N>\<^sub>1 G u) v \<Longrightarrow> isin1 (g G T) u \<or> isin1 (g G T) v"
  proof -
    fix u v
    assume "isin1 (\<N>\<^sub>1 G u) v"
    hence rep_e_isin: "rep1 (uEdge u v) \<in> g1.uedges G"
      unfolding g1.uedges_def2 by auto
    moreover hence "map_edge_to_covering_vertex G T (rep1 (uEdge u v)) \<in> {u,v}" 
      using assms g1.rep_idem map_edge_to_covering_vertex_cases
        by (auto simp del: map_edge_to_covering_vertex.simps)
    ultimately consider 
      e where "e \<in> g1.uedges G" "map_edge_to_covering_vertex G T e = u" 
      | e where "e \<in> g1.uedges G" "map_edge_to_covering_vertex G T e = v"
      using assms set_g g1.set_specs by auto
    thus "isin1 (g G T) u \<or> isin1 (g G T) v"
      using assms invar_g set_g g1.set_specs by cases auto
  qed
  
  show "\<And>v. isin1 (g G T) v \<Longrightarrow> v \<in> g1.vertices G"
  proof -
    fix v
    assume "isin1 (g G T) v"
    then obtain e where e_isin_G: "e \<in> g1.uedges G" and "v = map_edge_to_covering_vertex G T e"
      using assms invar_g set_g by (auto simp add: g1.set_specs simp del: g.simps)
    moreover then obtain x y where "e = rep1 (uEdge x y)" and y_isin_Nx: "isin1 (\<N>\<^sub>1 G x) y"
      unfolding g1.uedges_def2 by auto
    moreover hence "map_edge_to_covering_vertex G T e \<in> {x,y}"
      using assms e_isin_G map_edge_to_covering_vertex_cases by (auto simp add: g1.rep_idem)
    ultimately consider "v = x" | "v = y"
      by auto
    thus "v \<in> g1.vertices G"
    proof cases
      assume "v = x"
      thus ?thesis
        using y_isin_Nx by (auto intro!: g1.vertices_memberI1)
    next
      assume "v = y"
      thus ?thesis
        using y_isin_Nx by (auto intro!: g1.vertices_memberI2)
    qed
  qed
qed

end

section \<open>Constructing a Hamiltonian Cycle From a Vertex Cover\<close>

context VC4_To_mTSP
begin

(* lemma hp_for_neighborhood_empty: "set_invar1 P \<Longrightarrow> \<nexists>v. isin1 P v \<Longrightarrow> hp_for_neighborhood u P = []"
  by (rule fold6.fold_setE) (auto simp add: g1.set_specs) *)

lemma hp_for_neighborhood_empty: "set_invar1 P \<Longrightarrow> set1 P = {} \<Longrightarrow> hp_for_neighborhood u P = []"
  by (rule fold6.fold_setE) auto

lemma distinct_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 P" 
      and "\<And>v. isin1 P v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  shows "distinct (hp_for_neighborhood u P)"
  using assms(2)
proof (rule fold6.fold_setE)
  let ?f="\<lambda>v. if rep1 (uEdge u v) = uEdge u v then hp_u2 (uEdge u v) else hp_v2 (uEdge u v)"
  fix vs 
  assume distinct_vs: "distinct vs" and set_vs_fold: "List.set vs = set1 P" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) P [] = fold (\<lambda>v T. T @ ?f v) vs []"
  moreover hence "\<And>v. v \<in> List.set vs \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G"
    using assms by (auto simp add: g1.set_specs)
  moreover have "\<And>x. x \<in> set vs \<Longrightarrow> distinct (?f x)" 
  proof -
    fix x
    assume "x \<in> set vs"
    hence isin_rep_ux: "rep1 (uEdge u x) \<in> g1.uedges G"
      using assms set_vs_fold by (auto simp add: g1.set_specs)
    consider "rep1 (uEdge u x) = uEdge u x" | "rep1 (uEdge u x) = uEdge x u"
      using g1.is_rep by auto
    thus "distinct (?f x)"
      using distinct_hp_u2[OF assms(1) isin_rep_ux] distinct_hp_v2[OF assms(1) isin_rep_ux] by cases auto
  qed
  moreover have "\<And>x y. x \<in> set vs \<Longrightarrow> y \<in> set vs \<Longrightarrow> x \<noteq> y \<Longrightarrow> set (?f x) \<inter> set (?f y) = {}"
  proof -
    fix x y
    assume "x \<in> set vs" "y \<in> set vs" "x \<noteq> y"
    hence rep_neq: "rep1 (uEdge u x) \<noteq> rep1 (uEdge u y)" 
      and "rep1 (uEdge u x) \<in> g1.uedges G" "rep1 (uEdge u y) \<in> g1.uedges G"
      using assms set_vs_fold by (auto simp add: g1.rep_eq_iff g1.set_specs)
    moreover hence neq: "u \<noteq> x" "u \<noteq> y"
      using assms g1.uedge_not_refl by auto
    ultimately have vert_disj: "g2.vertices (H\<^sub>e (uEdge u x)) \<inter> g2.vertices (H\<^sub>e (uEdge u y)) = {}"
      using assms by (auto intro!: vertices_of_He_disjoint 
          simp add: vertices_of_He simp del: He.simps vertices_of_He.simps)

    consider "rep1 (uEdge u x) = uEdge u x" "rep1 (uEdge u y) = uEdge u y" 
      | "rep1 (uEdge u x) = uEdge x u" "rep1 (uEdge u y) = uEdge u y" 
      | "rep1 (uEdge u x) = uEdge u x" "rep1 (uEdge u y) = uEdge y u" 
      | "rep1 (uEdge u x) = uEdge x u" "rep1 (uEdge u y) = uEdge y u" 
      using g1.is_rep by auto
    thus "set (?f x) \<inter> set (?f y) = {}"
      using assms neq vert_disj by cases (auto simp add: vertices_hp_u2 vertices_hp_v2 simp del: He.simps)
  qed
  ultimately have "distinct (concat (map ?f vs))"
    using assms(1) by (intro distinct_concat_map) 
  thus ?thesis
    using set_vs_fold by (auto simp: fold_concat_map)
qed

lemma set_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 P" 
      and "\<And>v. isin1 P v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  shows "List.set (hp_for_neighborhood u P) = \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u v | v. isin1 P v})"
  using assms(2)
proof (rule fold6.fold_setE)
  let ?f="\<lambda>v. if rep1 (uEdge u v) = uEdge u v then hp_u2 (uEdge u v) else hp_v2 (uEdge u v)"
  fix vs 
  assume distinct_vs: "distinct vs" and set_vs_fold: "List.set vs = set1 P" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) P [] = fold (\<lambda>v T. T @ ?f v) vs []"
  have hp_vert: "\<And>x. x \<in> set vs \<Longrightarrow> set (?f x) = g2.vertices (H\<^sub>e (uEdge u x))"
  proof -
    fix x
    assume "x \<in> set vs"
    hence "rep1 (uEdge u x) \<in> g1.uedges G"
      using assms set_vs_fold by (auto simp add: g1.set_specs)
    then consider "rep1 (uEdge u x) = uEdge u x" "u \<noteq> x" | "rep1 (uEdge u x) = uEdge x u" "u \<noteq> x"
      using assms g1.uedge_not_refl g1.is_rep by blast
    thus "set (?f x) = g2.vertices (H\<^sub>e (uEdge u x))"
    proof cases
      assume "rep1 (uEdge u x) = uEdge u x"
      thus ?thesis 
        by (auto simp add: vertices_hp_u2 simp del: He.simps)
    next
      assume "rep1 (uEdge u x) = uEdge x u" "u \<noteq> x"
      thus ?thesis 
        by (auto simp add: vertices_hp_v2 simp del: He.simps)
    qed
  qed
  have "List.set (concat (map ?f vs)) = \<Union> ((\<lambda>x. set (?f x)) ` (List.set vs))"
    apply (subst set_concat)
    apply (subst set_map) 
    apply blast
    done
  also have "... = \<Union> ((\<lambda>v. g2.vertices (H\<^sub>e (uEdge u v))) ` (List.set vs))"
    using hp_vert by auto
  also have "... = \<Union> ((set2 o V\<^sub>H\<^sub>e) ` {uEdge u v | v. v \<in> set vs})"
    by (auto simp add: vertices_of_He vertices_of_He_rep_idem simp del: He.simps vertices_of_He.simps)
  finally show ?thesis
    using assms set_vs_fold by (auto simp add: fold_concat_map g1.set_specs)
qed

lemma path_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 P" 
      and "\<exists>v. isin1 P v" \<comment> \<open>The neighborhood is non-empty.\<close>
      and "\<And>v. isin1 P v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  obtains v w where "g2.path_betw (f G) (rep1 (uEdge u v),u,2) (hp_for_neighborhood u P) (rep1 (uEdge u w),u,1)" 
  using assms(2)
proof (rule fold6.fold_setE)
  let ?hp="hp_for_neighborhood u P"
  let ?f="\<lambda>v. if rep1 (uEdge u v) = uEdge u v then hp_u2 (uEdge u v) else hp_v2 (uEdge u v)"
  fix vs 
  assume distinct_vs: "distinct vs" and set_vs_fold: "List.set vs = set1 P" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) P [] = fold (\<lambda>v T. T @ ?f v) vs []"
  hence vs_nonnil: "vs \<noteq> []" and uv_edge: "\<And>v. v \<in> List.set vs \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G"
    using assms by (auto simp add: g1.set_specs)

  have "List.set ?hp = \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u v | v. isin1 P v})"
    using assms(1,2,4) by (rule set_hp_for_neighborhood)
  also have "... = \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {rep1 (uEdge u v) | v. isin1 P v})"
    by (auto simp add: set_hp_for_neighborhood vertices_of_He_rep_idem simp del: vertices_of_He.simps)
  finally have set_subset_f: "List.set ?hp \<subseteq> g2.vertices (f G)"
    using assms set_vertices_of_H vertices_f by (auto simp del: f.simps vertices_of_He.simps)

  \<comment> \<open>path\<close>
  have "?hp \<noteq> []"
  proof -
    have "rep1 (uEdge u (hd vs)) \<in> g1.uedges G"
      using assms set_vs_fold hd_in_set[OF vs_nonnil] by (auto simp add: g1.set_specs)
    then consider "rep1 (uEdge u (hd vs)) = uEdge u (hd vs)" "u \<noteq> (hd vs)" 
      | "rep1 (uEdge u (hd vs)) = uEdge (hd vs) u" "u \<noteq> (hd vs)"
      using assms g1.uedge_not_refl g1.is_rep by blast 
    thus ?thesis
    proof cases
      case 1
      then show ?thesis 
        using hp_u2_non_nil
        sorry
    next
      case 2
      then show ?thesis 
        using hp_v2_non_nil
        sorry
    qed
  qed
  moreover hence "g2.path_betw (f G) (hd ?hp) ?hp (last ?hp)"
    using assms f_is_complete distinct_distinct_adj[OF distinct_hp_for_neighborhood] set_subset_f 
    by (auto intro!: g2.path_betw_in_complete_graph simp del: f.simps hp_for_neighborhood.simps)
  moreover obtain v where isin_v: "isin1 P v" and "hd ?hp = (rep1 (uEdge u v),u,2)"
    using assms by (elim hd_hp_for_neighborhood)
  moreover obtain w where isin_w: "isin1 P w" and "last ?hp = (rep1 (uEdge u w),u,1)"
    using assms by (elim last_hp_for_neighborhood)
  ultimately have "g2.path_betw (f G) (rep1 (uEdge u v),u,2) ?hp (rep1 (uEdge u w),u,1)"
    by auto
  thus ?thesis
    using that by auto
qed

abbreviation "card1 X \<equiv> int (card (set1 X))"
abbreviation "card1_sub1 X \<equiv> max ((card1 X) - 1) (0::int)"

lemma cost_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 P" "set1 P \<noteq> {}"
      and "\<And>v. isin1 P v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  shows "cost_of_path (c G) (hp_for_neighborhood u P) \<le> card1 P * 11 + (card1 P - 1) * 4"
using assms(2)
proof (rule fold6.fold_setE)
  let ?hp="hp_for_neighborhood u P"
  let ?f="\<lambda>v. if rep1 (uEdge u v) = uEdge u v then hp_u2 (uEdge u v) else hp_v2 (uEdge u v)"
  fix vs 
  assume distinct_vs: "distinct vs" and set_vs_fold: "List.set vs = set1 P" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) P [] = fold (\<lambda>v T. T @ ?f v) vs []"
  hence "length vs > 0"
    using assms by auto
  hence len_vs: "length vs \<ge> 1"
    by linarith

  have uv_edge: "\<And>v. v \<in> List.set vs \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G"
    using assms set_vs_fold by (auto simp add: g1.set_specs)
  hence cost_hp_eq11: "\<And>v. v \<in> set vs \<Longrightarrow> cost_of_path (c G) (?f v) = 11"
  proof -
    fix v
    assume "v \<in> set vs"
    hence rep_uv: "rep1 (uEdge u v) \<in> g1.uedges G"
      using assms set_vs_fold by (auto simp add: g1.set_specs)
    then consider "rep1 (uEdge u v) = uEdge u v" "u \<noteq> v" | "rep1 (uEdge u v) = uEdge v u" "u \<noteq> v"
      using assms g1.uedge_not_refl g1.is_rep by blast 
    thus "cost_of_path (c G) (?f v) = 11"
    using cost_of_hp_u2[OF assms(1) rep_uv] cost_of_hp_v2[OF assms(1) rep_uv] by cases auto
  qed

  have "\<And>v w. v \<in> set vs \<Longrightarrow> w \<in> set vs \<Longrightarrow> v \<noteq> w \<Longrightarrow> ?f v \<noteq> [] \<Longrightarrow> ?f w \<noteq> [] \<Longrightarrow> c G (last (?f v)) (hd (?f w)) \<le> 4"
  proof -
    fix v w
    assume "v \<in> set vs" "w \<in> set vs" "v \<noteq> w" "?f v \<noteq> []" "?f w \<noteq> []"
    moreover hence "last (?f v) = (rep1 (uEdge u v),u,1)" (is "?x = _")
    proof -
      have "rep1 (uEdge u v) \<in> g1.uedges G"
        using assms set_vs_fold \<open>v \<in> set vs\<close> by (auto simp add: g1.set_specs)
      then consider "rep1 (uEdge u v) = uEdge u v" "u \<noteq> v" | "rep1 (uEdge u v) = uEdge v u" "u \<noteq> v"
        using assms g1.uedge_not_refl g1.is_rep by blast 
      thus ?thesis
        by cases auto
    qed
    moreover hence "hd (?f w) = (rep1 (uEdge u w),u,2)" (is "?y = _")
    proof -
      have "rep1 (uEdge u w) \<in> g1.uedges G"
        using assms set_vs_fold \<open>w \<in> set vs\<close> by (auto simp add: g1.set_specs)
      then consider "rep1 (uEdge u w) = uEdge u w" "u \<noteq> w" | "rep1 (uEdge u w) = uEdge w u" "u \<noteq> w"
        using assms g1.uedge_not_refl g1.is_rep by blast 
      thus ?thesis
        by cases auto
    qed
    moreover have edges: "rep1 (uEdge u v) \<in> g1.uedges G" "rep1 (uEdge u w) \<in> g1.uedges G"
      using assms calculation set_vs_fold by (auto simp add: g1.set_specs)
    moreover have vert_x: "?x \<in> g2.vertices (H\<^sub>e (rep1 (uEdge u v)))"
    proof -
      have "rep1 (uEdge u v) \<in> g1.uedges G"
        using assms set_vs_fold \<open>v \<in> set vs\<close> by (auto simp add: g1.set_specs)
      then consider "rep1 (uEdge u v) = uEdge u v" "u \<noteq> v" | "rep1 (uEdge u v) = uEdge v u" "u \<noteq> v"
        using assms g1.uedge_not_refl g1.is_rep by blast 
      thus ?thesis
      proof cases
        case 1
        then show ?thesis 
          using vertices_hp_u2 by (auto simp del: He.simps)
      next
        case 2
        then show ?thesis    
          using vertices_hp_v2 g1.rep_simps by (auto simp del: He.simps)
      qed
    qed
    moreover have vert_y: "?y \<in> g2.vertices (H\<^sub>e (rep1 (uEdge u w)))"
    proof -
      have "rep1 (uEdge u w) \<in> g1.uedges G"
        using assms set_vs_fold \<open>w \<in> set vs\<close> by (auto simp add: g1.set_specs)
      then consider "rep1 (uEdge u w) = uEdge u w" "u \<noteq> w" | "rep1 (uEdge u w) = uEdge w u" "u \<noteq> w"
        using assms g1.uedge_not_refl g1.is_rep by blast 
      thus ?thesis
      proof cases
        case 1
        then show ?thesis 
          using vertices_hp_u2 by (auto simp del: He.simps)
      next
        case 2
        then show ?thesis    
          using vertices_hp_v2 g1.rep_simps by (auto simp del: He.simps)
      qed
    qed
    moreover have "rep1 (uEdge u v) \<noteq> rep1 (uEdge u w)"
      using \<open>v \<noteq> w\<close> by (auto simp add: g1.rep_eq_iff)
    moreover hence "\<not> are_vertices_in_He G ?x ?y"
      using vertices_in_He_rep_iff[OF assms(1) edges vert_x vert_y] by (simp add: g1.rep_idem)
    moreover hence "\<not> is_edge_in_He G (uEdge ?x ?y)"
      using assms edge_in_He_are_vertices by blast 
    ultimately show "c G ?x ?y \<le> 4"
      by (simp add: g1.rep_idem)
  qed
  hence "cost_of_path (c G) (concat (map ?f vs)) \<le> (\<Sum>v\<leftarrow>vs. cost_of_path (c G) (?f v)) + (length (tl vs)) * 4"
    using assms(1) distinct_vs set_vs_fold uv_edge by (intro cost_concat_map) (auto simp del: cost_of_path.simps c.simps hp_u2.simps)
  also have "... = length vs * 11 + (length (tl vs)) * 4"
    using cost_hp_eq11 by (auto simp add: sum_list_const)
  also have "... = card1 P * 11 + (card1 P - 1) * 4"
    using set_vs_fold distinct_vs len_vs by (auto simp add: distinct_card[symmetric])
  finally show ?thesis
    using set_vs_fold by (auto simp add: fold_concat_map)
qed

lemma hd_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" and "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
      and "g1.is_vc_Adj G X" "set_invar1 X" 
  obtains u v where "isin1 X u" "rep1 (uEdge u v) \<in> g1.uedges G" 
    "hd (hp_from_vc G X) = (rep1 (uEdge u v),u,2)"
  using assms(4)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_vs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"

  have "\<exists>u v. u \<in> set1 X \<and> isin1 (\<P> G X u) v"
    using assms partition_by_vertex_cover by blast
  hence "\<exists>u x. u \<in> set1 X \<and> x \<in> \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v})"
    using invar_vertices_of_He vertices_of_He_non_empty g2.set_specs by fastforce
  hence "\<exists>u x. u \<in> set xs \<and> x \<in> \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v})"
    using set_vs_fold by auto
  hence "\<exists>u x. u \<in> set xs \<and> x \<in> List.set (?f u)"
    using assms(1) invar_partition_for_vertex uedge_of_partition_for_vertex 
    by (auto simp add: set_hp_for_neighborhood simp del: hp_for_neighborhood.simps)
  hence v_with_non_empty_hp: "\<exists>v \<in> set xs. ?f v \<noteq> []" "xs \<noteq> []"
    by force+
  then obtain u where "u \<in> set xs" "?f u \<noteq> []" "hd (concat (map ?f xs)) = hd (?f u)"
    by (elim hd_concat_map_elim)
  moreover hence "\<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v}) \<noteq> {}"
    apply (subst set_hp_for_neighborhood[symmetric])
    using assms(1) invar_partition_for_vertex uedge_of_partition_for_vertex by auto
  moreover hence "\<exists>v. isin1 (\<P> G X u) v"
    by blast
  moreover then obtain v where "isin1 (\<P> G X u) v" "rep1 (uEdge u v) \<in> g1.uedges G" 
    "hd (hp_for_neighborhood u (\<P> G X u)) = (rep1 (uEdge u v),u,2)"
    using assms(1) apply (elim hd_hp_for_neighborhood[of G "\<P> G X u"])
    using assms(1) invar_partition_for_vertex by (auto intro!: uedge_of_partition_for_vertex)
  ultimately show ?thesis
    using assms that set_vs_fold by (auto simp add: g1.set_specs fold_concat_map)
qed

lemma last_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" and "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
      and "g1.is_vc_Adj G X" "set_invar1 X"
  obtains u v where "isin1 X u" "rep1 (uEdge u v) \<in> g1.uedges G" 
    "last (hp_from_vc G X) = (rep1 (uEdge u v),u,1)"
  using assms(4)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_vs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"

  have "\<exists>u v. u \<in> set1 X \<and> isin1 (\<P> G X u) v"
    using assms partition_by_vertex_cover by blast
  hence "\<exists>u x. u \<in> set1 X \<and> x \<in> \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v})"
    using invar_vertices_of_He vertices_of_He_non_empty g2.set_specs by fastforce
  hence "\<exists>u x. u \<in> set xs \<and> x \<in> \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v})"
    using set_vs_fold by auto
  hence "\<exists>u x. u \<in> set xs \<and> x \<in> List.set (?f u)"
    using assms(1) invar_partition_for_vertex uedge_of_partition_for_vertex 
    by (auto simp add: set_hp_for_neighborhood simp del: hp_for_neighborhood.simps)
  hence v_with_non_empty_hp: "\<exists>v \<in> set xs. ?f v \<noteq> []" "xs \<noteq> []"
    by force+ (* TODO: unify with hd_hp_from_vc *)
  then obtain u where "u \<in> set xs" "?f u \<noteq> []" "last (concat (map ?f xs)) = last (?f u)"
    by (elim last_concat_map_elim)
  moreover hence "\<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v}) \<noteq> {}"
    apply (subst set_hp_for_neighborhood[symmetric])
    using assms(1) invar_partition_for_vertex uedge_of_partition_for_vertex by auto
  moreover hence "\<exists>v. isin1 (\<P> G X u) v"
    by blast
  moreover then obtain v where "isin1 (\<P> G X u) v" "rep1 (uEdge u v) \<in> g1.uedges G" 
    "last (hp_for_neighborhood u (\<P> G X u)) = (rep1 (uEdge u v),u,1)"
    using assms(1) apply (elim last_hp_for_neighborhood[of G "\<P> G X u"])
    using assms(1) invar_partition_for_vertex by (auto intro!: uedge_of_partition_for_vertex)
  ultimately show ?thesis
    using assms that set_vs_fold by (auto simp add: g1.set_specs fold_concat_map)
qed

lemma hp_for_neighborhood_disjoint:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 P\<^sub>1" "set_invar1 P\<^sub>2" 
      and "\<And>v. isin1 P\<^sub>1 v \<Longrightarrow> rep1 (uEdge u\<^sub>1 v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
      and "\<And>v. isin1 P\<^sub>2 v \<Longrightarrow> rep1 (uEdge u\<^sub>2 v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
      and "{rep1 (uEdge u\<^sub>1 v) |v. isin1 P\<^sub>1 v} \<inter> {rep1 (uEdge u\<^sub>2 v) |v. isin1 P\<^sub>2 v} = {}" \<comment> \<open>Set of edges are disjoint.\<close>
  shows "List.set (hp_for_neighborhood u\<^sub>1 P\<^sub>1) \<inter> List.set (hp_for_neighborhood u\<^sub>2 P\<^sub>2) = {}"
proof - 
  have "\<And>v\<^sub>1 v\<^sub>2. isin1 P\<^sub>1 v\<^sub>1 \<Longrightarrow> isin1 P\<^sub>2 v\<^sub>2 \<Longrightarrow> set2 (V\<^sub>H\<^sub>e (uEdge u\<^sub>1 v\<^sub>1)) \<inter> set2 (V\<^sub>H\<^sub>e (uEdge u\<^sub>2 v\<^sub>2)) = {}"
    using assms g1.rep_eq_iff by (auto simp add: g1.set_specs intro!: vertices_of_He_disjoint 
        simp del: vertices_of_He.simps)
  thus ?thesis
    using assms by (auto simp add: set_hp_for_neighborhood simp del: vertices_of_He.simps hp_for_neighborhood.simps)
qed

lemma distinct_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X"
  shows "distinct (hp_from_vc G X)"
  using assms(3)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_vs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"
  moreover have "distinct (concat (map ?f xs))"
    apply (intro distinct_concat_map)
    using assms(1) distinct_xs invar_partition_for_vertex uedge_of_partition_for_vertex 
      distinct_hp_for_neighborhood apply auto[2]
    apply (intro hp_for_neighborhood_disjoint)
    using assms(1) invar_partition_for_vertex uedge_of_partition_for_vertex apply auto[5]
    using assms(1) apply (intro partition_for_vertex_disjoint_set_compr)
    using assms(1,3) set_vs_fold by (auto simp add: g1.set_specs) (* TODO: clean up *)
  ultimately show ?thesis
    by (simp add: fold_concat_map)
qed

lemma set_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X"
  shows "List.set (hp_from_vc G X) = g2.vertices (f G)"
  using assms(3)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_vs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"

  have "\<And>u. u \<in> set1 X \<Longrightarrow> List.set (?f u) = \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u v | v. isin1 (\<P> G X u) v})"
    using assms invar_partition_for_vertex uedge_of_partition_for_vertex
    by (intro set_hp_for_neighborhood) (auto simp add: g1.set_specs simp del: partition_for_vertex.simps)
  hence "List.set (hp_from_vc G X) = \<Union> ((\<lambda>u. \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u v | v. isin1 (\<P> G X u) v})) ` (set1 X))"
    using set_vs_fold by (auto simp add: fold_concat_map)
  also have "... = \<Union> ((\<lambda>u. \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {rep1 (uEdge u v) | v. isin1 (\<P> G X u) v})) ` (set1 X))"
    using vertices_of_He_rep_idem by fastforce
  also have "... = \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` ((\<Union>u\<in>set1 X. {rep1 (uEdge u v) | v. isin1 (\<P> G X u) v})))"
    by auto
  also have "... = \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` g1.uedges G)"
    apply (subst partition_by_vertex_cover)
    using assms by auto
  also have "... = set2 (V\<^sub>H G)"
    apply (subst set_vertices_of_H)
    using assms by auto
  also have "... = g2.vertices (f G)"
    apply (subst vertices_f)
    using assms by auto
  finally show ?thesis
    by (auto simp add: fold_concat_map)
qed

lemma path_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" and "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
      and "g1.is_vc_Adj G X" "set_invar1 X" 
  obtains u\<^sub>1 v\<^sub>1 u\<^sub>2 v\<^sub>2 where "isin1 X u\<^sub>1" "isin1 X u\<^sub>2" 
      "rep1 (uEdge u\<^sub>1 v\<^sub>1) \<in> g1.uedges G" "rep1 (uEdge u\<^sub>2 v\<^sub>2) \<in> g1.uedges G" 
    "g2.path_betw (f G) (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2) (hp_from_vc G X) (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)" 
proof -   
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  obtain u\<^sub>1 v\<^sub>1 where uv1_isin: "isin1 X u\<^sub>1" "rep1 (uEdge u\<^sub>1 v\<^sub>1) \<in> g1.uedges G" 
    and "hd (hp_from_vc G X) = (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2)"
    using assms by (elim hd_hp_from_vc)    
  moreover obtain u\<^sub>2 v\<^sub>2 where uv2_isin: "isin1 X u\<^sub>2" "rep1 (uEdge u\<^sub>2 v\<^sub>2) \<in> g1.uedges G" 
    and "last (hp_from_vc G X) = (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)"
    using assms by (elim last_hp_from_vc)
  moreover have "List.set (hp_from_vc G X) = g2.vertices (f G)"
    using assms by (intro set_hp_from_vc)
  moreover hence "hp_from_vc G X \<noteq> []"
    using assms vertices_f_non_empty by (fastforce simp del: hp_from_vc.simps)
  ultimately have "g2.path_betw (f G) (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2) (hp_from_vc G X) (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)"
    apply (simp only: hp_from_vc.simps)
    apply (intro g2.path_betw_in_complete_graph)
    using assms f_is_complete distinct_distinct_adj[OF distinct_hp_from_vc] by auto
  thus ?thesis
    using that uv1_isin uv2_isin by auto
qed

lemma cost_hd_hp_last_hp_leq5:
  assumes "g1.ugraph_adj_map_invar G" 
      and "hp_for_neighborhood u\<^sub>1 (\<P> G X u\<^sub>1) \<noteq> []" "hp_for_neighborhood u\<^sub>2 (\<P> G X u\<^sub>2) \<noteq> []"
  shows "c G (last (hp_for_neighborhood u\<^sub>1 (\<P> G X u\<^sub>1))) (hd (hp_for_neighborhood u\<^sub>2 (\<P> G X u\<^sub>2))) \<le> 5"
  using assms(1)
proof (rule last_hp_for_neighborhood)
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  show "set_invar1 (\<P> G X u\<^sub>1)" "\<And>v. isin1 (\<P> G X u\<^sub>1) v \<Longrightarrow> rep1 (uEdge u\<^sub>1 v) \<in> g1.uedges G"
    using assms invar_partition_for_vertex uedge_of_partition_for_vertex by auto
  hence "\<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u\<^sub>1 v |v. isin1 (\<P> G X u\<^sub>1) v}) \<noteq> {}"
    using assms by (subst set_hp_for_neighborhood[symmetric]) auto
  thus "\<exists>v. isin1 (\<P> G X u\<^sub>1) v"
    by blast
  fix v\<^sub>1 
  assume "isin1 (\<P> G X u\<^sub>1) v\<^sub>1" and "last (?f u\<^sub>1) = (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,1)"
  show "c G (last (?f u\<^sub>1)) (hd (?f u\<^sub>2)) \<le> 5"
    using assms(1)
  proof (rule hd_hp_for_neighborhood)
    show "set_invar1 (\<P> G X u\<^sub>2)" "\<And>v. isin1 (\<P> G X u\<^sub>2) v \<Longrightarrow> rep1 (uEdge u\<^sub>2 v) \<in> g1.uedges G"
      using assms invar_partition_for_vertex uedge_of_partition_for_vertex by auto
    hence "\<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u\<^sub>2 v |v. isin1 (\<P> G X u\<^sub>2) v}) \<noteq> {}"
      using assms by (subst set_hp_for_neighborhood[symmetric]) auto
    thus "\<exists>v. isin1 (\<P> G X u\<^sub>2) v"
      by blast
    fix v\<^sub>2 
    assume "isin1 (\<P> G X u\<^sub>2) v\<^sub>2" and "hd (?f u\<^sub>2) = (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,2)"
    thus "c G (last (?f u\<^sub>1)) (hd (?f u\<^sub>2)) \<le> 5"
      apply (subst \<open>last (?f u\<^sub>1) = (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,1)\<close>)
      apply (subst \<open>hd (?f u\<^sub>2) = (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,2)\<close>)
      apply (intro cost_u1_u2_leq5)
      using assms(1) by simp
  qed
qed

lemma rep1_uedge_inj:
  assumes "g1.ugraph_adj_map_invar G"
  shows "inj_on (\<lambda>v. rep1 (uEdge u v)) (set1 (\<P> G X u))"
proof
  let ?f="\<lambda>v. rep1 (uEdge u v)"
  fix v w
  assume "v \<in> set1 (\<P> G X u)" "w \<in> set1 (\<P> G X u)" "?f v = ?f w"
  moreover hence "?f v \<in> g1.uedges G" "?f w \<in> g1.uedges G"
    using assms(1) invar_partition_for_vertex by (auto intro!: uedge_of_partition_for_vertex 
        simp add: g1.set_specs)
  moreover hence "u \<noteq> v" "u \<noteq> w"
    using assms(1) by (auto simp add: g1.uedge_not_refl)
  ultimately show "v = w"
    by (auto simp add: g1.rep_eq_iff)
qed

lemma sum_card1_partition:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X"
  shows "(\<Sum>x \<in> set1 X. card1 (\<P> G X x)) = card (g1.uedges G)"
proof -
  let ?f="\<lambda>u v. rep1 (uEdge u v)"
  have "(\<Sum>x \<in> set1 X. card1 (\<P> G X x)) = (\<Sum>u \<in> set1 X. card ((?f u) ` set1 (\<P> G X u)))"
    using assms(1) rep1_uedge_inj by (auto simp add: card_image)
  also have "... = (card (\<Union> ((\<lambda>u. (?f u) ` set1 (\<P> G X u)) ` (set1 X))))"
    using assms fold6.finite_sets 
    by (subst finite_sum_card[OF _ _ partition_for_vertex_disjoint]) (auto simp add: g1.set_specs)
  also have "... = card (\<Union>u\<in>set1 X. {rep1 (uEdge u v) | v. isin1 (\<P> G X u) v})"
    using assms invar_partition_for_vertex by (auto simp add: Setcompr_eq_image g1.set_specs 
        simp del: partition_for_vertex.simps)
  also have "... = card (g1.uedges G)"
    using assms by (subst partition_by_vertex_cover) auto
  finally show ?thesis .
qed

lemma cost_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
      and "g1.is_vc_Adj G X" "set_invar1 X"
  shows "cost_of_path (c G) (hp_from_vc G X) \<le> 15 * int (card (g1.uedges G)) + card1 X - 5"
  using assms(4)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_xs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"

  \<comment> \<open>Remove all vertices from vertex cover, that have an empty partition.\<close>
  let ?xs'="filter (\<lambda>x. set1 (\<P> G X x) \<noteq> {}) xs"

  obtain u v where "rep1 (uEdge u v) \<in> g1.uedges G" "isin1 (\<N>\<^sub>1 G u) v"
    using assms by (auto simp add: g1.uedges_def2)
  moreover hence "isin1 (\<N>\<^sub>1 G v) u"
    using assms by auto
  moreover hence "isin1 X u \<or> isin1 X v"
    using assms by (auto simp add: g1.is_vc_AdjE)
  moreover have "rep1 (uEdge u v) = uEdge u v \<or> rep1 (uEdge v u) = uEdge v u"
    using g1.is_rep by auto
  ultimately have "isin1 X u \<and> isin1 (\<P> G X u) v \<or> isin1 X v \<and> isin1 (\<P> G X v) u"
    using assms isin_partition_for_vertex_intro invar_partition_for_vertex g1.set_specs by blast
  hence "\<exists>x \<in> set xs. set1 (\<P> G X x) \<noteq> {}"
    using assms invar_partition_for_vertex set_xs_fold g1.set_specs by blast
  hence "?xs' \<noteq> []"
    by (induction xs) auto
  hence len_tl_xs: "length (tl ?xs') = int (length ?xs') - 1"
    by (induction xs) auto
  have "set xs = set ?xs' \<union> (set xs - set ?xs')"
    by auto

  have "\<And>x. x \<in> set ?xs' \<Longrightarrow> cost_of_path (c G) (?f x) \<le> card1 (\<P> G X x) * 11 + (card1 (\<P> G X x) - 1) * 4"
    using assms invar_partition_for_vertex uedge_of_partition_for_vertex cost_hp_for_neighborhood by auto
  hence "(\<Sum>x\<leftarrow>?xs'. cost_of_path (c G) (?f x)) \<le> (\<Sum>x\<leftarrow>?xs'. card1 (\<P> G X x) * 11 + (card1 (\<P> G X x) - 1) * 4)"
    by (intro sum_list_mono)
  also have "... = (\<Sum>x \<in> set ?xs'. card1 (\<P> G X x) * 11 + (card1 (\<P> G X x) - 1) * 4)"
    using distinct_xs by (auto simp add: sum_list_distinct_conv_sum_set)
  also have "... = (\<Sum>x \<in> set ?xs'. card1 (\<P> G X x) * 11) + (\<Sum>x \<in> set ?xs'. (card1 (\<P> G X x) - 1) * 4)"
    by (intro sum.distrib)
  also have "... = 11 * (\<Sum>x \<in> set ?xs'. card1 (\<P> G X x)) + 4 * (\<Sum>x \<in> set ?xs'. card1 (\<P> G X x) + (- 1))"
    by (auto simp add: sum_distrib_left mult.commute)
  also have "... = 15 * (\<Sum>x \<in> set ?xs'. card1 (\<P> G X x)) - 4 * card (set ?xs')"
    by (subst sum.distrib) auto
  also have "... = 15 * (\<Sum>x \<in> set ?xs'. card1 (\<P> G X x)) - 4 * int (length ?xs')"
    using distinct_xs distinct_card by (subst distinct_card) auto
  also have "... = 15 * (\<Sum>x \<in> set xs. card1 (\<P> G X x)) - 4 * int (length ?xs')"
    apply (subst \<open>set xs = set ?xs' \<union> (set xs - set ?xs')\<close>)
    apply (subst sum_Un)
    apply auto
    done
  also have "... = 15 * (\<Sum>x \<in> set1 X. card1 (\<P> G X x)) - 4 * int (length ?xs')"
    apply (subst set_xs_fold)
    apply auto
    done
  also have "... = 15 * int (card (g1.uedges G)) - 4 * int (length ?xs')"
    using assms apply (subst sum_card1_partition)
    apply auto
    done
  finally have sum_cost_hp_neighb: 
    "(\<Sum>x\<leftarrow>?xs'. cost_of_path (c G) (?f x)) \<le> 15 * int (card (g1.uedges G)) - 4 * int (length ?xs')"
    by auto

  have "\<And>x y. ?f x \<noteq> [] \<Longrightarrow> ?f y \<noteq> [] \<Longrightarrow> c G (last (?f x)) (hd (?f y)) \<le> 5"
    using assms set_xs_fold by (intro cost_hd_hp_last_hp_leq5) (auto simp add: g1.set_specs)
  hence "cost_of_path (c G) (concat (map ?f ?xs')) \<le> (\<Sum>x\<leftarrow>?xs'. cost_of_path (c G) (?f x)) + (length (tl ?xs')) * 5"
    using distinct_xs by (intro cost_concat_map) auto
  also have "... \<le> 15 * int (card (g1.uedges G)) - 4 * int (length ?xs') + (length (tl ?xs')) * 5"
    using sum_cost_hp_neighb by auto
  also have "... = 15 * int (card (g1.uedges G)) - 4 * int (length ?xs') + (int (length ?xs') - 1) * 5"
    using len_tl_xs by auto
  also have "... \<le> 15 * int (card (g1.uedges G)) + int (length ?xs') - 5"
    by auto
  finally have "cost_of_path (c G) (concat (map ?f ?xs')) \<le> 15 * int (card (g1.uedges G)) + int (length ?xs') - 5"
    by auto
  moreover have "cost_of_path (c G) (concat (map ?f xs)) = cost_of_path (c G) (concat (map ?f ?xs'))"
    using assms invar_partition_for_vertex hp_for_neighborhood_empty 
    by (subst concat_map_filter_empty) auto
  moreover have "int (length ?xs') \<le> int (length xs)"
    by auto
  ultimately have "cost_of_path (c G) (concat (map ?f xs)) \<le> 15 * int (card (g1.uedges G)) + int (length xs) - 5"
    by linarith
  moreover have "length xs = card1 X"
    using assms distinct_xs set_xs_fold by (auto simp add: distinct_card[symmetric] g1.set_specs)
  ultimately show ?thesis
    using assms distinct_xs set_xs_fold 
    by (auto simp add: distinct_card[symmetric] fold_concat_map g1.set_specs)
qed

end

section \<open>Constructing a Vertex Cover From a Hamiltonian Cycle\<close>

context VC4_To_mTSP
begin

(* fun hp_starting_at :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_starting_at (e,x,i) = (case rep1 e of uEdge u v \<Rightarrow>
    if x = u \<and> i = 1 then hp_u1 (rep1 e)
    else if x = u \<and> i = 2 then hp_u2 (rep1 e)
    else if x = v \<and> i = 1 then hp_v1 (rep1 e)
    else if x = v \<and> i = 2 then hp_v2 (rep1 e)
    else hp_u1 (rep1 e))" *)

fun hp_starting_at :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_starting_at (e,x,i) = (case rep1 e of uEdge u v \<Rightarrow>
    if x = v then hp_v1 (rep1 e) else hp_u1 (rep1 e))"

lemma hp_starting_at_non_nil: "hp_starting_at x \<noteq> []"
  by (cases x) (auto split: uedge.splits)

lemma hd_hp_starting_at: 
  assumes "rep1 e = uEdge u v" "x \<in> {u,v}"
  shows "hd (hp_starting_at (e,x,i)) = (rep1 e,x,1)"
  using assms g1.rep_simps by auto

lemma last_hp_starting_at: 
  assumes "rep1 e = uEdge u v" "x \<in> {u,v}"
  shows "last (hp_starting_at (e,x,i)) = (rep1 e,x,2)"
  using assms g1.rep_simps by auto

lemma cost_hd_hp_starting_at_leq: 
  assumes "g1.ugraph_adj_map_invar G" and "isin2 (V\<^sub>H G) x" "isin2 (V\<^sub>H G) y"
      and "\<not> are_vertices_in_He G x y"
  shows "c G x (hd (hp_starting_at y)) \<le> c G x y" (is "c G x ?hd\<^sub>y \<le> _")
proof (cases x; cases y)
  fix e\<^sub>x w\<^sub>x i\<^sub>x e\<^sub>y w\<^sub>y i\<^sub>y
  assume [simp]: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)" and [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
  hence vert_x: "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x" "e\<^sub>x \<in> g1.uedges G" 
    and vert_y: "isin2 (V\<^sub>H\<^sub>e e\<^sub>y) y" "e\<^sub>y \<in> g1.uedges G"
    using assms fst_of_vertex_is_edge by auto
  moreover then obtain u\<^sub>y v\<^sub>y where edge_y: "rep1 e\<^sub>y = uEdge u\<^sub>y v\<^sub>y" "w\<^sub>y \<in> {u\<^sub>y,v\<^sub>y}"
    by (elim isin_vertices_of_He_elim2) auto
  ultimately have rep_neq: "rep1 e\<^sub>x \<noteq> rep1 e\<^sub>y"
    using assms invar_vertices_of_He vertices_of_He vertices_in_He_rep_iff by (auto simp add: g2.set_specs)

  have hd_y: "?hd\<^sub>y = (rep1 e\<^sub>y,w\<^sub>y,1)"
    using vert_y isin_vertices_of_He_edge hd_hp_starting_at[OF edge_y] by auto
  moreover hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>y) ?hd\<^sub>y"
    using edge_y by (auto intro!: isin_vertices_of_He_intro2 simp del: vertices_of_He.simps)
  ultimately have x_hd_y_no_vert: "\<not> are_vertices_in_He G x ?hd\<^sub>y"
    using assms rep_neq vert_x vert_y invar_vertices_of_He vertices_of_He vertices_in_He_rep_iff 
    by (auto simp add: g2.set_specs)

  show ?thesis
  proof cases
    assume [simp]: "w\<^sub>x = w\<^sub>y"
    hence "c G x y = 4"
      using assms rep_neq edge_in_He_are_vertices by auto
    moreover have "c G x ?hd\<^sub>y = 4"
      using assms rep_neq hd_y x_hd_y_no_vert edge_in_He_are_vertices by (auto simp add: g1.rep_idem)
    ultimately show ?thesis
      by auto
  next
    assume "w\<^sub>x \<noteq> w\<^sub>y"
    hence "c G x y = 5"
      using assms rep_neq edge_in_He_are_vertices by auto
    moreover have "c G x ?hd\<^sub>y \<le> 5"
      using assms rep_neq hd_y x_hd_y_no_vert edge_in_He_are_vertices by (auto simp add: g1.rep_idem)
    ultimately show ?thesis
      by auto
  qed
qed

lemma cost_hp_starting_at: 
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
  shows "cost_of_path (c G) (hp_starting_at (e,x,i)) = 11"
  using assms
proof (rule g1.uedge_not_refl_elim)
  fix u v
  assume [simp]: "rep1 e = uEdge u v" and "u \<noteq> v"
  hence edge_uv: "uEdge u v \<in> g1.uedges G"
    using assms g1.rep_of_edge_is_edge by fastforce
  thus ?thesis
    using assms edge_uv g1.rep_of_edge_is_edge cost_of_hp_v1 cost_of_hp_u1 by auto
qed

lemma cost_hp_starting_at2: 
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" "e \<in> g1.uedges G"
  shows "cost_of_path (c G) (hp_starting_at (map_edge_to_hp_start_vertex G T e)) = 11"
  using assms
proof -
  have "map_edge_to_hp_start_vertex G T e = (rep1 e,map_edge_to_covering_vertex G T e,1)"
    using assms by (intro map_edge_to_hp_start_vertex_cases2)
  moreover have "rep1 e \<in> g1.uedges G"
    using assms by (simp add: g1.rep_of_edge)
  ultimately show ?thesis
    using assms cost_hp_starting_at by metis
qed

fun tour_of_hp_starting_vertices :: "('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "tour_of_hp_starting_vertices [] = []"
| "tour_of_hp_starting_vertices X' = concat (map hp_starting_at X') @ [hd X']"
  \<comment> \<open>Given a list of vertices \<open>X'\<close>, where each vertex marks the start of a Hamiltonian path, we 
  return a full tour.\<close>

lemma tour_of_hp_starting_vertices_def2:
  "X' \<noteq> [] \<Longrightarrow> tour_of_hp_starting_vertices X' = concat (map hp_starting_at X') @ [hd X']"
  by (induction X') auto

lemma cost_concat_map_geq:
  assumes "distinct_adj es" 
      and "\<And>y. y \<in> set es \<Longrightarrow> f\<^sub>1 y \<noteq> []"
      and "\<And>x y. x \<in> set es \<Longrightarrow> y \<in> set es \<Longrightarrow> x \<noteq> y \<Longrightarrow> f\<^sub>2 x = f\<^sub>2 y \<Longrightarrow> c G (last (f\<^sub>1 x)) (hd (f\<^sub>1 y)) = 4"
      and "\<And>x y. x \<in> set es \<Longrightarrow> y \<in> set es \<Longrightarrow> x \<noteq> y \<Longrightarrow> f\<^sub>2 x \<noteq> f\<^sub>2 y \<Longrightarrow> c G (last (f\<^sub>1 x)) (hd (f\<^sub>1 y)) = 5"
 obtains k where "cost_of_path (\<lambda>x y. if f\<^sub>2 x \<noteq> f\<^sub>2 y then (1::nat) else 0) es = k"
   and "cost_of_path (c G) (concat (map f\<^sub>1 es)) = (\<Sum>e\<leftarrow>es. cost_of_path (c G) (f\<^sub>1 e)) + (length (tl es)) * 4 + k"
  using assms
proof (induction es arbitrary: thesis rule: list012.induct)
  case 1
  thus ?case by auto
next
  case (2 e)
  thus ?case by auto
next
  let ?c="\<lambda>x y. if f\<^sub>2 x \<noteq> f\<^sub>2 y then (1::nat) else 0"
  let ?sum="\<lambda>xs. \<Sum>x\<leftarrow>(xs). cost_of_path (c G) (f\<^sub>1 x)"
  case (3 e\<^sub>1 e\<^sub>2 es)
  then obtain k where cost1_leq: "cost_of_path ?c (e\<^sub>2#es) = k"
    and cost2_geq: "cost_of_path (c G) (concat (map f\<^sub>1 (e\<^sub>2#es))) = ?sum (e\<^sub>2#es) + (length (tl (e\<^sub>2#es))) * 4 + k"
    by auto

  consider "f\<^sub>2 e\<^sub>1 = f\<^sub>2 (hd (e\<^sub>2#es))" "c G (last (f\<^sub>1 e\<^sub>1)) (hd (concat (map f\<^sub>1 (e\<^sub>2#es)))) = 4" 
    | "f\<^sub>2 e\<^sub>1 \<noteq> f\<^sub>2 (hd (e\<^sub>2#es))" "c G (last (f\<^sub>1 e\<^sub>1)) (hd (concat (map f\<^sub>1 (e\<^sub>2#es)))) = 5"
    using "3.prems" by (induction es) auto
  thus ?case
  proof cases
    assume "f\<^sub>2 e\<^sub>1 = f\<^sub>2 (hd (e\<^sub>2#es))" and cost: "c G (last (f\<^sub>1 e\<^sub>1)) (hd (concat (map f\<^sub>1 (e\<^sub>2#es)))) = 4"
    moreover hence "cost_of_path ?c (e\<^sub>1#e\<^sub>2#es) = k"
      using cost1_leq by auto
    moreover have "cost_of_path (c G) (concat (map f\<^sub>1 (e\<^sub>1#e\<^sub>2#es))) = ?sum (e\<^sub>1#e\<^sub>2#es) + (length (tl (e\<^sub>1#e\<^sub>2#es))) * 4 + k"
      using cost cost2_geq 3 by (auto simp add: cost_of_path_append)
    ultimately show ?thesis
      using 3 by auto
  next
    assume "f\<^sub>2 e\<^sub>1 \<noteq> f\<^sub>2 (hd (e\<^sub>2#es))" and cost: "c G (last (f\<^sub>1 e\<^sub>1)) (hd (concat (map f\<^sub>1 (e\<^sub>2#es)))) = 5"
    hence "cost_of_path ?c (e\<^sub>1#e\<^sub>2#es) = k + 1"
      using cost1_leq by auto
    moreover have "cost_of_path (c G) (concat (map f\<^sub>1 (e\<^sub>1#e\<^sub>2#es))) = ?sum (e\<^sub>1#e\<^sub>2#es) + (length (tl (e\<^sub>1#e\<^sub>2#es))) * 4 + (k + 1)"
      using cost cost2_geq 3 by (auto simp add: cost_of_path_append)
    ultimately show ?thesis
      using 3(2)[of "k+1"] by auto
  qed
qed

lemma hd_hp_starting_at_elim:
fixes f\<^sub>1 f\<^sub>2 G T
  defines "f\<^sub>1 \<equiv> hp_starting_at o (map_edge_to_hp_start_vertex G T)"
  defines "f\<^sub>2 \<equiv> map_edge_to_covering_vertex G T"
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" and "e \<in> g1.uedges G"
  obtains u v where "rep1 e = uEdge u v" "f\<^sub>2 e \<in> {u,v}" "hd (f\<^sub>1 e) = (rep1 e,f\<^sub>2 e,1)"
proof -
  obtain u v where rep_e[symmetric]: "rep1 e = uEdge u v" and "u \<noteq> v"
    using assms by (elim g1.uedge_not_refl_elim)
  hence "f\<^sub>2 e \<in> {u,v}"
    unfolding f\<^sub>2_def using assms by (intro map_edge_to_covering_vertex_cases) (auto simp add: g1.rep_idem)

  have "map_edge_to_hp_start_vertex G T e = (rep1 e,f\<^sub>2 e,1)" 
    unfolding f\<^sub>2_def using assms by (intro map_edge_to_hp_start_vertex_cases2)
  hence "hd (f\<^sub>1 e) = hd (hp_starting_at (e,f\<^sub>2 e,1))"
    unfolding f\<^sub>1_def using assms by (auto simp add: g1.rep_of_edge)
  also have "... = (rep1 e,f\<^sub>2 e,1)"
    using rep_e \<open>u \<noteq> v\<close> \<open>f\<^sub>2 e \<in> {u,v}\<close> by (intro hd_hp_starting_at) auto
  finally have "hd (f\<^sub>1 e) = (rep1 e,f\<^sub>2 e,1)"
    by auto
  thus ?thesis
    using that rep_e[symmetric] \<open>f\<^sub>2 e \<in> {u,v}\<close> by auto
qed

lemma last_hp_starting_at_elim:
fixes f\<^sub>1 f\<^sub>2 G T
  defines "f\<^sub>1 \<equiv> hp_starting_at o (map_edge_to_hp_start_vertex G T)"
  defines "f\<^sub>2 \<equiv> map_edge_to_covering_vertex G T"
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" and "e \<in> g1.uedges G"
  obtains u v where "rep1 e = uEdge u v" "f\<^sub>2 e \<in> {u,v}""last (f\<^sub>1 e) = (rep1 e,f\<^sub>2 e,2)"
proof -
  obtain u v where rep_e[symmetric]: "rep1 e = uEdge u v" and "u \<noteq> v"
    using assms by (elim g1.uedge_not_refl_elim)
  hence "f\<^sub>2 e \<in> {u,v}"
    unfolding f\<^sub>2_def using assms by (intro map_edge_to_covering_vertex_cases) (auto simp add: g1.rep_idem)

  have "map_edge_to_hp_start_vertex G T e = (rep1 e,f\<^sub>2 e,1)" 
    unfolding f\<^sub>2_def using assms by (intro map_edge_to_hp_start_vertex_cases2)
  hence "last (f\<^sub>1 e) = last (hp_starting_at (e,f\<^sub>2 e,1))"
    unfolding f\<^sub>1_def using assms by (auto simp add: g1.rep_of_edge)
  also have "... = (rep1 e,f\<^sub>2 e,2)"
    using rep_e \<open>u \<noteq> v\<close> \<open>f\<^sub>2 e \<in> {u,v}\<close> by (intro last_hp_starting_at) auto
  finally have "last (f\<^sub>1 e) = (rep1 e,f\<^sub>2 e,2)"
    by auto
  thus ?thesis
    using that rep_e[symmetric] \<open>f\<^sub>2 e \<in> {u,v}\<close> by auto
qed

(* lemma hp_start_vertices_not_vertices_in_He:
  fixes f\<^sub>1 f\<^sub>2 G T
  defines "f\<^sub>1 \<equiv> hp_starting_at o (map_edge_to_hp_start_vertex G T)"
  defines "f\<^sub>2 \<equiv> map_edge_to_covering_vertex G T"
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" 
      and "e\<^sub>1 \<in> g1.uedges G" "e\<^sub>2 \<in> g1.uedges G" "e\<^sub>1 \<noteq> e\<^sub>2"
  shows "last (f\<^sub>1 e\<^sub>1) = (rep1 e\<^sub>1,f\<^sub>2 e\<^sub>1,2)" "hd (f\<^sub>1 e\<^sub>2) = (rep1 e\<^sub>2,f\<^sub>2 e\<^sub>2,1)" "\<not> are_vertices_in_He G (last (f\<^sub>1 e\<^sub>1)) (hd (f\<^sub>1 e\<^sub>2))" 
proof -
  obtain u\<^sub>1 v\<^sub>1 where rep_e1: "rep1 e\<^sub>1 = uEdge u\<^sub>1 v\<^sub>1" and "f\<^sub>2 e\<^sub>1 \<in> {u\<^sub>1,v\<^sub>1}" 
    and [simp]: "last (f\<^sub>1 e\<^sub>1) = (rep1 e\<^sub>1,f\<^sub>2 e\<^sub>1,2)"
    unfolding f\<^sub>1_def f\<^sub>2_def using assms by (elim last_hp_starting_at_elim)
  hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>1) (last (f\<^sub>1 e\<^sub>1))"
    using rep_e1 by (auto intro!: isin_vertices_of_He_intro2 simp del: vertices_of_He.simps)
  hence last_isin_He1: "last (f\<^sub>1 e\<^sub>1) \<in> g2.vertices (H\<^sub>e e\<^sub>1)"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)

  obtain u\<^sub>2 v\<^sub>2 where rep_e2: "rep1 e\<^sub>2 = uEdge u\<^sub>2 v\<^sub>2" and "f\<^sub>2 e\<^sub>2 \<in> {u\<^sub>2,v\<^sub>2}" 
    and [simp]: "hd (f\<^sub>1 e\<^sub>2) = (rep1 e\<^sub>2,f\<^sub>2 e\<^sub>2,1)"
    unfolding f\<^sub>1_def f\<^sub>2_def using assms by (elim hd_hp_starting_at_elim)
  hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>2) (hd (f\<^sub>1 e\<^sub>2))"
    using rep_e2 by (auto intro!: isin_vertices_of_He_intro2 simp del: vertices_of_He.simps)
  hence hd_isin_He2: "hd (f\<^sub>1 e\<^sub>2) \<in> g2.vertices (H\<^sub>e e\<^sub>2)"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  
  have "rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
    using assms g1.rep_of_edge by auto
  hence "\<not> are_vertices_in_He G (last (f\<^sub>1 e\<^sub>1)) (hd (f\<^sub>1 e\<^sub>2))"
    using assms last_isin_He1 hd_isin_He2 vertices_in_He_rep_iff by auto
  thus "last (f\<^sub>1 e\<^sub>1) = (rep1 e\<^sub>1,f\<^sub>2 e\<^sub>1,2)" "hd (f\<^sub>1 e\<^sub>2) = (rep1 e\<^sub>2,f\<^sub>2 e\<^sub>2,1)" "\<not> are_vertices_in_He G (last (f\<^sub>1 e\<^sub>1)) (hd (f\<^sub>1 e\<^sub>2))" 
    using \<open>last (f\<^sub>1 e\<^sub>1) = (rep1 e\<^sub>1,f\<^sub>2 e\<^sub>1,2)\<close> \<open>hd (f\<^sub>1 e\<^sub>2) = (rep1 e\<^sub>2,f\<^sub>2 e\<^sub>2,1)\<close> by blast+
qed *)

lemma cost_hp_starting_at_last_hd:
  fixes f\<^sub>1 f\<^sub>2 G T
  defines "f\<^sub>1 \<equiv> hp_starting_at o (map_edge_to_hp_start_vertex G T)"
  defines "f\<^sub>2 \<equiv> map_edge_to_covering_vertex G T"
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" 
      and "e\<^sub>1 \<in> g1.uedges G" "e\<^sub>2 \<in> g1.uedges G" "e\<^sub>1 \<noteq> e\<^sub>2"
  obtains "f\<^sub>2 e\<^sub>1 = f\<^sub>2 e\<^sub>2" "c G (last (f\<^sub>1 e\<^sub>1)) (hd (f\<^sub>1 e\<^sub>2)) = 4"
  |  "f\<^sub>2 e\<^sub>1 \<noteq> f\<^sub>2 e\<^sub>2" "c G (last (f\<^sub>1 e\<^sub>1)) (hd (f\<^sub>1 e\<^sub>2)) = 5"
proof -
  let ?last="last (f\<^sub>1 e\<^sub>1)"
  let ?hd="hd (f\<^sub>1 e\<^sub>2)"
  have "rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
    using assms g1.rep_of_edge by auto
  obtain u\<^sub>1 v\<^sub>1 where rep_e1: "rep1 e\<^sub>1 = uEdge u\<^sub>1 v\<^sub>1" and "f\<^sub>2 e\<^sub>1 \<in> {u\<^sub>1,v\<^sub>1}" 
    and [simp]: "last (f\<^sub>1 e\<^sub>1) = (rep1 e\<^sub>1,f\<^sub>2 e\<^sub>1,2)"
    unfolding f\<^sub>1_def f\<^sub>2_def using assms by (elim last_hp_starting_at_elim)
  hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>1) (last (f\<^sub>1 e\<^sub>1))"
    using rep_e1 by (auto intro!: isin_vertices_of_He_intro2 simp del: vertices_of_He.simps)
  hence last_isin_He1: "last (f\<^sub>1 e\<^sub>1) \<in> g2.vertices (H\<^sub>e e\<^sub>1)"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)

  obtain u\<^sub>2 v\<^sub>2 where rep_e2: "rep1 e\<^sub>2 = uEdge u\<^sub>2 v\<^sub>2" and "f\<^sub>2 e\<^sub>2 \<in> {u\<^sub>2,v\<^sub>2}" 
    and [simp]: "hd (f\<^sub>1 e\<^sub>2) = (rep1 e\<^sub>2,f\<^sub>2 e\<^sub>2,1)"
    unfolding f\<^sub>1_def f\<^sub>2_def using assms by (elim hd_hp_starting_at_elim)
  hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>2) (hd (f\<^sub>1 e\<^sub>2))"
    using rep_e2 by (auto intro!: isin_vertices_of_He_intro2 simp del: vertices_of_He.simps)
  hence hd_isin_He2: "hd (f\<^sub>1 e\<^sub>2) \<in> g2.vertices (H\<^sub>e e\<^sub>2)"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  
  have "rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
    using assms g1.rep_of_edge by auto
  moreover hence "\<not> are_vertices_in_He G (last (f\<^sub>1 e\<^sub>1)) (hd (f\<^sub>1 e\<^sub>2))"
    using assms last_isin_He1 hd_isin_He2 vertices_in_He_rep_iff by auto
  moreover hence "\<not> is_edge_in_He G (uEdge (last (f\<^sub>1 e\<^sub>1)) (hd (f\<^sub>1 e\<^sub>2)))"
    using assms edge_in_He_are_vertices by blast
  ultimately show ?thesis
    using that by (cases "f\<^sub>2 e\<^sub>1 = f\<^sub>2 e\<^sub>2") (auto simp add: g1.rep_idem)
qed

lemma vc_non_empty:
  assumes "g1.ugraph_adj_map_invar G" "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
      and "g1.is_vc_Adj G X" "set_invar1 X"
  shows "card1 X \<ge> 1"
proof -
  obtain e where "e \<in> g1.uedges G"
    using assms by auto
  then obtain u v where "isin1 (\<N>\<^sub>1 G u) v"
    unfolding g1.uedges_def2 by auto
  hence "isin1 X u \<or> isin1 X v"
    using assms by (auto elim!: g1.is_vc_AdjE)
  then consider "{u} \<subseteq> set1 X" | "{v} \<subseteq> set1 X"
    using assms by (auto simp add: g1.set_specs)
  thus ?thesis
  proof cases
    assume "{u} \<subseteq> set1 X"
    hence "card {u} \<le> card (set1 X)"
      using finite_sets1 by (intro card_mono)
    thus ?thesis 
      by auto
  next
    assume "{v} \<subseteq> set1 X"
    hence "card {v} \<le> card (set1 X)"
      using finite_sets1 by (intro card_mono)
    thus ?thesis 
      by auto
  qed
qed

lemma len_remdups_leq_cycle_cost_adj:
  defines "neq \<equiv> \<lambda>x y. if x \<noteq> y then (1::nat) else 0"
  defines "t \<equiv> \<lambda>xs. if length (remdups xs) = 1 then 1 else 0"
  shows "length (remdups es) \<le> cost_of_path neq es + neq (last es) (hd es) + t es"
  using assms
proof (induction es rule: list012_induct)
  case Nil
  then show ?case by auto
next
  case (Singleton e\<^sub>1)
  then show ?case by auto
next
  case (CCons e\<^sub>1 e\<^sub>2 es)

  have "t (e\<^sub>2#es) \<le> t (e\<^sub>1#e\<^sub>2#es) \<or> (t (e\<^sub>2#es) = 1 \<and> t (e\<^sub>1#e\<^sub>2#es) = 0)"
    unfolding t_def by auto
  moreover have "e\<^sub>1 \<in> set (e\<^sub>2#es) \<longrightarrow> t (e\<^sub>2#es) = t (e\<^sub>1#e\<^sub>2#es)"
    unfolding t_def by auto
  ultimately consider "e\<^sub>1 \<in> set (e\<^sub>2#es)" "t (e\<^sub>2#es) = t (e\<^sub>1#e\<^sub>2#es)"
    | "e\<^sub>1 \<notin> set (e\<^sub>2#es)" "t (e\<^sub>2#es) \<le> t (e\<^sub>1#e\<^sub>2#es)" 
    | "e\<^sub>1 \<notin> set (e\<^sub>2#es)" "t (e\<^sub>2#es) = 1" "t (e\<^sub>1#e\<^sub>2#es) = 0"
    by auto
  thus ?case
  proof cases
    assume "e\<^sub>1 \<in> set (e\<^sub>2#es)" and [simp]: "t (e\<^sub>2#es) = t (e\<^sub>1#e\<^sub>2#es)"
    have "length (remdups (e\<^sub>1#e\<^sub>2#es)) = length (remdups (e\<^sub>2#es))"
      using \<open>e\<^sub>1 \<in> set (e\<^sub>2#es)\<close> by auto
    also have "... \<le> cost_of_path neq (e\<^sub>2#es) + neq (last (e\<^sub>2#es)) e\<^sub>2 + t (e\<^sub>2#es)"
      using CCons by auto
    also have "... \<le> neq e\<^sub>1 e\<^sub>2 + cost_of_path neq (e\<^sub>2#es) + neq (last (e\<^sub>2#es)) e\<^sub>1 + t (e\<^sub>2#es)"
      using \<open>e\<^sub>1 \<in> set (e\<^sub>2#es)\<close> by (auto simp add: neq_def)
    also have "... = cost_of_path neq (e\<^sub>1#e\<^sub>2#es) + neq (last (e\<^sub>1#e\<^sub>2#es)) (hd (e\<^sub>1#e\<^sub>2#es)) + t (e\<^sub>2#es)"
      by auto
    finally show ?thesis
      by auto
  next
    assume "e\<^sub>1 \<notin> set (e\<^sub>2#es)" and t_leq: "t (e\<^sub>2#es) \<le> t (e\<^sub>1#e\<^sub>2#es)" 
    hence "neq e\<^sub>1 e\<^sub>2 = 1" "neq (last (e\<^sub>2#es)) e\<^sub>2 \<le> neq (last (e\<^sub>2#es)) e\<^sub>1"
      by (auto simp add: neq_def)
    
    have "length (remdups (e\<^sub>1#e\<^sub>2#es)) = 1 + length (remdups (e\<^sub>2#es))"
      using \<open>e\<^sub>1 \<notin> set (e\<^sub>2#es)\<close> by auto
    also have "... \<le> 1 + cost_of_path neq (e\<^sub>2#es) + neq (last (e\<^sub>2#es)) e\<^sub>2 + t (e\<^sub>2#es)"
      using CCons by auto
    also have "... \<le> neq e\<^sub>1 e\<^sub>2 + cost_of_path neq (e\<^sub>2#es) + neq (last (e\<^sub>2#es)) e\<^sub>1 + t (e\<^sub>2#es)"
      using \<open>e\<^sub>1 \<notin> set (e\<^sub>2#es)\<close> by (auto simp add: neq_def)
    also have "... \<le> cost_of_path neq (e\<^sub>1#e\<^sub>2#es) + neq (last (e\<^sub>1#e\<^sub>2#es)) (hd (e\<^sub>1#e\<^sub>2#es)) + t (e\<^sub>1#e\<^sub>2#es)"
      using t_leq by auto
    finally show ?thesis
      by auto
  next
    assume "e\<^sub>1 \<notin> set (e\<^sub>2#es)" and [simp]: "t (e\<^sub>2#es) = 1" "t (e\<^sub>1#e\<^sub>2#es) = 0"
    hence "length (remdups (e\<^sub>2#es)) = 1"
      unfolding t_def by presburger
    hence "\<And>x y. x \<in> set (e\<^sub>2#es) \<Longrightarrow> y \<in> set (e\<^sub>2#es) \<Longrightarrow> x = y"
      by (metis length_pos_if_in_set less_numeral_extra(3) list.size(3) list_hd_singleton set_ConsD set_remdups)
    hence [simp]: "neq e\<^sub>1 e\<^sub>2 = 1" and neq_last: "neq (last (e\<^sub>2#es)) e\<^sub>2 = 0" "neq (last (e\<^sub>2#es)) e\<^sub>1 = 1"
      using \<open>e\<^sub>1 \<notin> set (e\<^sub>2#es)\<close> by (auto simp add: neq_def)

    have "length (remdups (e\<^sub>1#e\<^sub>2#es)) = 1 + length (remdups (e\<^sub>2#es))"
      using \<open>e\<^sub>1 \<notin> set (e\<^sub>2#es)\<close> by auto
    also have "... \<le> 1 + cost_of_path neq (e\<^sub>2#es) + neq (last (e\<^sub>2#es)) e\<^sub>2 + t (e\<^sub>2#es)"
      using CCons by auto
    also have "... = cost_of_path neq (e\<^sub>1#e\<^sub>2#es) + neq (last (e\<^sub>1#e\<^sub>2#es)) (hd (e\<^sub>1#e\<^sub>2#es)) + t (e\<^sub>1#e\<^sub>2#es)"
      using neq_last by auto
    finally show ?thesis
      by auto
  qed
qed

lemma card_leq_cycle_cost_adj:
  defines "neq \<equiv> \<lambda>x y. if x \<noteq> y then (1::nat) else 0"
  assumes "card (set es) > 1"
  shows "card (set es) \<le> cost_of_path neq es + neq (last es) (hd es)"
proof -
  have "length (remdups es) \<le> cost_of_path neq es + neq (last es) (hd es) + (if length (remdups es) = 1 then 1 else 0)"
    using assms len_remdups_leq_cycle_cost_adj by blast
  thus ?thesis
    using assms by (auto simp add: card_set)
qed

lemma cost_of_tour_of_hp_starting_vertices:
  fixes G T                         
  defines "T' \<equiv> tour_of_hp_starting_vertices (map_tour_to_hp_staring_vertices G T)" and "X \<equiv> g G T"
  assumes "g1.ugraph_adj_map_invar G" and "card (g1.uedges G) > 1" "card1 X > 1"
      and "g2.is_hc_Adj (f G) T"
  obtains k where "card1 X \<le> k" and "15 * int (card (g1.uedges G)) + k \<le> cost_of_path (c G) T'"
  using assms(3)
proof (rule fold4.fold_uedgesE)
  let ?E="g1.uedges G"
  let ?vs="map_tour_to_hp_staring_vertices G T"
  let ?Vs="{map_edge_to_covering_vertex G T e | e. e \<in> g1.uedges G}"
  let ?f="\<lambda>e xs. xs @ [map_edge_to_hp_start_vertex G T e]"
  let ?f\<^sub>1="hp_starting_at o (map_edge_to_hp_start_vertex G T)"
  let ?f\<^sub>2="map_edge_to_covering_vertex G T"
  let ?c="\<lambda>x y. if ?f\<^sub>2 x \<noteq> ?f\<^sub>2 y then (1::nat) else 0"
  let ?neq="\<lambda>x y. if x \<noteq> y then (1::nat) else 0"
  fix es
  assume dist_es: "distinct es" and "map rep1 es = es" and 
    set_es_fold: "set es = g1.uedges G" "fold_g1_uedges4 ?f G [] = fold ?f es []"
  hence es_non_nil [simp]: "es \<noteq> []" and len_es [simp]: "length es = card ?E"
    using assms by (auto simp add: distinct_card[symmetric]) 
  then obtain e where [simp]: "hd es = e" and e_is_edge: "e \<in> ?E"
    using set_es_fold by fastforce
  moreover hence [simp]: "rep1 e = e"
    by (intro g1.rep_of_edge)
  moreover obtain u v where e_uv: "rep1 e = uEdge u v" "u \<noteq> v"
    using assms calculation by (elim g1.uedge_not_refl_elim) auto
  moreover hence "rep1 e = rep1 (uEdge u v)"
    using calculation by (auto simp add: g1.rep_idem)
  ultimately consider "map_edge_to_hp_start_vertex G T e = (rep1 e,u,1)" | "map_edge_to_hp_start_vertex G T e = (rep1 e,v,1)"
    using assms by (elim map_edge_to_hp_start_vertex_cases)
  then obtain x where [simp]: "map_edge_to_hp_start_vertex G T e = (e,x,1)" and isin_xi: "x \<in> {u,v}"
    by cases auto

  have [simp]: "?vs = map (map_edge_to_hp_start_vertex G T) es"
    using set_es_fold by (auto simp add: fold_concat_map)
  moreover have "hd ?vs = hd (?f\<^sub>1 e)"
    using e_uv(2) isin_xi by (auto simp add: hd_hp_starting_at[OF e_uv(1)] hd_map 
        simp del: hp_starting_at.simps map_tour_to_hp_staring_vertices.simps map_edge_to_hp_start_vertex.simps)
  ultimately have "T' = concat (map ?f\<^sub>1 es) @ [hd (?f\<^sub>1 (hd es))]" (is "_ = ?T @ ?hd")
    unfolding T'_def by (auto simp add: tour_of_hp_starting_vertices_def2)
  hence cost_T_eq: "cost_of_path (c G) T' = cost_of_path (c G) (concat (map ?f\<^sub>1 es)) + c G (last (concat (map ?f\<^sub>1 es))) (hd (?f\<^sub>1 e))"
    using hp_starting_at_non_nil by (auto simp add: cost_of_path_append)

  have "?f\<^sub>2 ` set es = ?Vs"
    using set_es_fold by auto
  hence [simp]: "card1 X = card (?f\<^sub>2 ` set es)"
    unfolding X_def using assms set_g by auto
  hence "card (?f\<^sub>2 ` set es) > 1"
    using assms by auto

  have "?neq (?f\<^sub>2 (last es)) (?f\<^sub>2 (hd es)) = ?c (last es) (hd es)"
    by auto
  moreover have "last (map ?f\<^sub>2 es) = ?f\<^sub>2 (last es)"
    using es_non_nil by (intro last_map)
  moreover have "hd (map ?f\<^sub>2 es) = ?f\<^sub>2 (hd es)"
    using es_non_nil by (intro hd_map)
  moreover have "cost_of_path ?neq (map ?f\<^sub>2 es) = cost_of_path ?c es"
    by (induction es rule: list012_induct) auto
  ultimately have cost_map_eq: 
    "cost_of_path ?neq (map ?f\<^sub>2 es) + ?neq (last (map ?f\<^sub>2 es)) (hd (map ?f\<^sub>2 es)) = cost_of_path ?c es + ?c (last es) (hd es)"
    by auto

  have "card (?f\<^sub>2 ` set es) = card (set (map ?f\<^sub>2 es))"
    by auto
  also have "... \<le> cost_of_path ?neq (map ?f\<^sub>2 es) + ?neq (last (map ?f\<^sub>2 es)) (hd (map ?f\<^sub>2 es))"
    using \<open>card (?f\<^sub>2 ` set es) > 1\<close> by (intro card_leq_cycle_cost_adj) auto
  also have "... = cost_of_path ?c es + ?c (last es) (hd es)"
    using cost_map_eq by auto
  finally have card_es_leq: "card (?f\<^sub>2 ` set es) \<le> cost_of_path ?c es + ?c (last es) (hd es)"
    by auto

  have "distinct_adj es"
    using dist_es by (intro distinct_distinct_adj)
  moreover have "\<And>y. y \<in> set es \<Longrightarrow> ?f\<^sub>1 y \<noteq> []"
    using hp_starting_at_non_nil by auto
  moreover have cost_last_hd_eq_4:
    "\<And>x y. x \<in> set es \<Longrightarrow> y \<in> set es \<Longrightarrow> x \<noteq> y \<Longrightarrow> ?f\<^sub>2 x = ?f\<^sub>2 y \<Longrightarrow> c G (last (?f\<^sub>1 x)) (hd (?f\<^sub>1 y)) = 4"
  proof -
    fix x y
    assume "x \<in> set es" "y \<in> set es" "x \<noteq> y" "?f\<^sub>2 x = ?f\<^sub>2 y"
    thus "c G (last (?f\<^sub>1 x)) (hd (?f\<^sub>1 y)) = 4"
      using assms set_es_fold by (elim cost_hp_starting_at_last_hd[of _ _ x y]) auto
  qed
  moreover have cost_last_hd_eq_5: 
    "\<And>x y. x \<in> set es \<Longrightarrow> y \<in> set es \<Longrightarrow> x \<noteq> y \<Longrightarrow> ?f\<^sub>2 x \<noteq> ?f\<^sub>2 y \<Longrightarrow> c G (last (?f\<^sub>1 x)) (hd (?f\<^sub>1 y)) = 5"
  proof -
    fix x y
    assume "x \<in> set es" "y \<in> set es" "x \<noteq> y" "?f\<^sub>2 x \<noteq> ?f\<^sub>2 y"
    thus "c G (last (?f\<^sub>1 x)) (hd (?f\<^sub>1 y)) = 5"
      using assms set_es_fold by (elim cost_hp_starting_at_last_hd[of _ _ x y]) auto
  qed
  ultimately obtain k where cost_es_leq: "cost_of_path ?c es = k"
    and "cost_of_path (c G) (concat (map ?f\<^sub>1 es)) = (\<Sum>e\<leftarrow>es. cost_of_path (c G) (?f\<^sub>1 e)) + (length (tl es)) * 4 + k"
    by (elim cost_concat_map_geq)
  moreover have "(\<Sum>e\<leftarrow>es. cost_of_path (c G) (?f\<^sub>1 e)) = length es * 11"
    apply (intro sum_list_const)
    apply (subst o_apply)
    apply (subst cost_hp_starting_at2)
    using assms set_es_fold by auto
  ultimately have "cost_of_path (c G) (concat (map ?f\<^sub>1 es)) = length es * 11 + (length (tl es) + 1) * 4 + k - (4::int)"
    by auto
  also have "... = length es * 11 + (length es) * 4 + k - (4::int)"
    by (auto simp del: len_es)
  finally have cost_concat_geq: "cost_of_path (c G) (concat (map ?f\<^sub>1 es)) = 15 * length es + k - (4::int)"
    by auto

  have last_concat: "last (concat (map ?f\<^sub>1 es)) = last (?f\<^sub>1 (last es))"
    using es_non_nil hp_starting_at_non_nil by (intro last_concat_map) auto

  consider "?f\<^sub>2 (last es) = ?f\<^sub>2 (hd es)" | "?f\<^sub>2 (last es) \<noteq> ?f\<^sub>2 (hd es)"
    by auto
  thus ?thesis
  proof cases
    assume "?f\<^sub>2 (last es) = ?f\<^sub>2 (hd es)" 
    hence "c G (last (?f\<^sub>1 (last es))) (hd (?f\<^sub>1 (hd es))) = 4" 
      apply (intro cost_last_hd_eq_4)
      apply simp
      using e_is_edge set_es_fold apply simp
      using assms(4) dist_es distinct_hd_last_neq by fastforce
    hence "c G (last (concat (map ?f\<^sub>1 es))) (hd (?f\<^sub>1 (hd es))) = 4" 
      using last_concat by auto
    hence "15 * int (card ?E) + k \<le> cost_of_path (c G) T'"
      using cost_concat_geq cost_T_eq by auto
    moreover have "card1 X \<le> k"
      using \<open>?f\<^sub>2 (last es) = ?f\<^sub>2 (hd es)\<close> card_es_leq cost_es_leq by auto
    ultimately show ?thesis
      using that by blast
  next
    assume "?f\<^sub>2 (last es) \<noteq> ?f\<^sub>2 (hd es)"
    hence "c G (last (?f\<^sub>1 (last es))) (hd (?f\<^sub>1 (hd es))) = 5"
      apply (intro cost_last_hd_eq_5)
      apply simp
      using e_is_edge set_es_fold apply simp
      using assms(4) dist_es distinct_hd_last_neq by fastforce
    hence "c G (last (concat (map ?f\<^sub>1 es))) (hd (?f\<^sub>1 (hd es))) = 5" 
      using last_concat by auto
    hence "15 * int (card ?E) + k + 1 \<le> cost_of_path (c G) T'"
      using cost_concat_geq cost_T_eq by auto
    moreover have "card1 X \<le> k + 1"
      using \<open>?f\<^sub>2 (last es) \<noteq> ?f\<^sub>2 (hd es)\<close> card_es_leq cost_es_leq by auto
    ultimately show ?thesis
      using that by auto
  qed
qed

lemma cost_rotate_tour_eq:
  assumes "g1.ugraph_adj_map_invar G" and "g2.is_hc_Adj (f G) T" (* "\<exists>e. e \<in> g1.uedges G" *)
  shows "cost_of_path (c G) (rotate_tour (isin2 (V\<^sub>H\<^sub>e e)) T) = cost_of_path (c G) T"
  using assms c_sym
proof (intro cost_rotate_tour)
  show "hd T = last T"
    using assms by (elim g2.is_hc_AdjE) (auto simp add: g2.hd_path_betw g2.last_path_betw)
qed auto

(* lemma cost_filter_tour_leq_aux:
  assumes "g1.ugraph_adj_map_invar G" and "\<not> isin2 (V\<^sub>H\<^sub>e e) x" "\<And>y. y \<in> set ys \<Longrightarrow> isin2 (V\<^sub>H\<^sub>e e) y"
  shows "cost_of_path (c G) (x#zs) + length ys - 1 \<le> cost_of_path (c G) (x#ys @ zs)"
  using assms
proof (induction ys)
  case Nil
  then show ?case by auto
next
  case (Cons y ys)
  have "\<not> are_vertices_in_He G x y"
  proof (rule ccontr; simp only: not_not)
    assume "are_vertices_in_He G x y"
    then obtain e' where "e' \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e')" "y \<in> g2.vertices (H\<^sub>e e')"
      using assms by (elim are_vertices_in_He_elim)
    hence "isin2 (V\<^sub>H\<^sub>e e') x" "isin2 (V\<^sub>H\<^sub>e e') y"
      using assms invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
    moreover have "isin2 (V\<^sub>H\<^sub>e e) y"
      using Cons by auto
    ultimately have "rep1 e = rep1 e'"
      using isin_vertices_of_He_unique by auto
    hence "isin2 (V\<^sub>H\<^sub>e (rep1 e)) x"
      using \<open>isin2 (V\<^sub>H\<^sub>e e') x\<close> by (simp add: vertices_of_He_rep_idem del: vertices_of_He.simps)
    thus "False"
      using assms by (simp add: vertices_of_He_rep_idem del: vertices_of_He.simps)
  qed
  hence "c G x y \<ge> 4"
    using assms by (intro cost_x_y_geq4)

  consider "zs = []" | z tlzs where "zs = z#tlzs"
    by (cases zs)
  thus ?case
  proof cases
    case 1
    hence "cost_of_path (c G) (x#zs) + length (y#ys) - 1 = int (length (y#ys)) - 1"
      by auto
    also have "... \<le> cost_of_path (c G) (y#ys)"
      using Cons cost_path_geq_len[of _ "y#ys"] by auto
    also have "... \<le> cost_of_path (c G) (x#y#ys)"
      using c_geq_0 cost_of_path_cons_leq[of "c G" ys x] by auto
    also have "... \<le> cost_of_path (c G) (x#y#ys) + cost_of_path (c G) zs"
      using c_geq_0 cost_of_path_geq_0[of "c G" zs] by auto
    also have "... \<le> cost_of_path (c G) (x#y#ys @ zs)"
      using c_geq_0 cost_of_path_append_geq_0[of "c G" "x#y#ys" zs] by auto
    finally show ?thesis 
      by auto
  next
    fix z tlzs
    assume [simp]: "zs = z#tlzs"

    have "c G (last (y#ys)) z \<ge> 1"
    using assms c_geq1 by auto
    have "c G x z \<le> 5"
      thm cost_x_y_leq5  
    (* idea. 
      case (i) \<not> are_vertices_in_He ?G ?x ?y. thm cost_x_y_leq5 
      case (ii) are_vertices_in_He ?G ?x ?y. 
        (a) obtain e where "?x \<in> g2.vertices (H\<^sub>e e)" "?y \<in> g2.vertices (H\<^sub>e e)"
        (b) obtain u v where "rep1 e = uEdge u v"
        (c) Lemma. for every vertex "?z \<in> g2.vertices (H\<^sub>e e)" there are paths 
            "path_betw (H\<^sub>e e) ?z P\<^sub>u (rep1 e,u,1)" and "path_betw (H\<^sub>e e) ?z P\<^sub>v (rep1 e,v,1)" s.t. "length P\<^sub>u + length P\<^sub>v = 5"
        (d) obtain paths P\<^sub>ux P\<^sub>uy P\<^sub>vx P\<^sub>vy with "length P\<^sub>ux + length P\<^sub>vx = 5" and "length P\<^sub>uy + length P\<^sub>vy = 5"
        (e) hence "path_betw (H\<^sub>e e) ?x (P\<^sub>ux @ rev P\<^sub>uy) ?y" and "path_betw (H\<^sub>e e) ?x (P\<^sub>vx @ rev P\<^sub>vy) ?y"
        (f) "length P\<^sub>ux + length P\<^sub>vx + length P\<^sub>uy + length P\<^sub>vy = 10"
        (g) hence "length P\<^sub>ux + P\<^sub>uy \<le> 10" or "length P\<^sub>vx + length P\<^sub>vy \<le> 5"
        (h) by thm g2.path_dist_less. "g2.path_dist ?G ?u ?v \<le> enat 5"
        (i) hence "min_dist_in_He G ?x ?y \<le> enat 5"
    *)
    sorry (* TODO: This should hold, but I don't know how to prove it. *)

    have "cost_of_path (c G) (x#z#tlzs) + int (length (y#ys)) - 1 = c G x z + cost_of_path (c G) (z#tlzs) + int (length (y#ys)) - 1"
      by auto
    also have "... \<le> 5 + cost_of_path (c G) (z#tlzs) + int (length (y#ys)) - 1"
      using \<open>c G x z \<le> 5\<close> by auto
    also have "... \<le> 4 + cost_of_path (c G) (y#ys) + 1 + cost_of_path (c G) (z#tlzs)"
      using assms cost_path_geq_len[of G "y#ys"] by auto
    also have "... \<le> c G x y + cost_of_path (c G) (y#ys) + c G (last (y#ys)) z + cost_of_path (c G) (z#tlzs)"
      using \<open>4 \<le> c G x y\<close> \<open>c G (last (y#ys)) z \<ge> 1\<close> by auto
    also have "... = c G x y + cost_of_path (c G) ((y#ys) @ (z#tlzs))"
      apply (subst cost_of_path_append)
      apply auto
      done
    also have "... = cost_of_path (c G) (x#y#ys @ z#tlzs)"
      by auto
    finally show ?thesis 
      by auto
  qed
qed

lemma cost_filter_tour_leq:
  assumes "g1.ugraph_adj_map_invar G" and "distinct T" (* "\<exists>z \<in> set T. \<not> isin2 (V\<^sub>H\<^sub>e e) z" *)
  shows "cost_of_path (c G) (filter (Not o isin2 (V\<^sub>H\<^sub>e e)) T) + card (set2 (V\<^sub>H\<^sub>e e) \<inter> set T) - 1 \<le> cost_of_path (c G) T"
  using assms
proof (induction T rule: list012_induct)
  case Nil
  then show ?case by auto
next
  case (Singleton x)
  then show ?case 
    using invar_vertices_of_He by (auto simp add: g2.set_specs)
next
  let ?f="\<lambda>x. \<not> isin2 (V\<^sub>H\<^sub>e e) x"
  case (CCons x y T)
  then show ?case 
  proof cases
    assume "isin2 (V\<^sub>H\<^sub>e e) x"
    moreover hence "card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (x#y#T)) = card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (y#T)) + 1"
      using CCons invar_vertices_of_He by (auto simp add: g2.set_specs)
    ultimately have "cost_of_path (c G) (filter ?f (x#y#T)) + card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (x#y#T)) - 1 \<le> cost_of_path (c G) (y#T) + 1"
      using CCons by auto
    also have "... \<le> cost_of_path (c G) (x#y#T)"
      using CCons c_geq1 by (auto simp add: c_geq1)
    finally show ?thesis
      by auto
  next
    assume "\<not> isin2 (V\<^sub>H\<^sub>e e) x"
    moreover hence "card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (x#y#T)) = card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (y#T))"
      using CCons invar_vertices_of_He by (auto simp add: g2.set_specs)
    ultimately have cost_simp: "cost_of_path (c G) (filter ?f (x#y#T)) + card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (x#y#T)) 
      = cost_of_path (c G) (x#filter ?f (y#T)) + card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (y#T))"
      by auto
    then consider "filter ?f (y#T) = []" | z zs where "filter ?f (y#T) = z#zs"
      by (cases "filter ?f (y#T)") auto
    thus ?thesis
    proof cases
      assume "filter ?f (y#T) = []"
      moreover hence "set2 (V\<^sub>H\<^sub>e e) \<inter> set (y#T) = set (y#T)"
        using filter_empty_conv[of ?f "y#T"] invar_vertices_of_He by (auto simp add: g2.set_specs)
      moreover hence "card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (y#T)) = length (y#T)"
        using CCons by (auto simp add: distinct_card)
      ultimately have "cost_of_path (c G) (filter ?f (x#y#T)) + card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (x#y#T)) = length (y#T)"
        using cost_simp by auto
      also have "... \<le> cost_of_path (c G) (y#T) + 1"
        using assms cost_path_geq_len[of G "y#T"] by auto
      also have "... \<le> cost_of_path (c G) (x#y#T)"
        using CCons by (auto simp add: c_geq1)
      finally show ?thesis 
        by auto
    next
      fix z zs
      assume "filter ?f (y#T) = z#zs"
      hence "cost_of_path (c G) (filter ?f (x#y#T)) + card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (x#y#T)) - 1 = c G x z + cost_of_path (c G) (filter ?f (y#T)) + card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (y#T)) - 1"
        using cost_simp by auto
      also have "... \<le> c G x z + cost_of_path (c G) (y#T)"
        using CCons by auto

      also have "... \<le> 5 + cost_of_path (c G) (z#zs) + card (set2 (V\<^sub>H\<^sub>e e) \<inter> set (y#T)) - 1"
        using \<open>c G x z \<le> 5\<close> by auto
      also have "... \<le> 4 + cost_of_path (c G) (y#ys) + 1 + cost_of_path (c G) (z#tlzs)"
        using assms cost_path_geq_len[of G "y#ys"] by auto
      also have "... \<le> c G x y + cost_of_path (c G) (y#ys) + c G (last (y#ys)) z + cost_of_path (c G) (z#tlzs)"
        using \<open>4 \<le> c G x y\<close> \<open>c G (last (y#ys)) z \<ge> 1\<close> by auto
      also have "... = c G x y + cost_of_path (c G) ((y#ys) @ (z#tlzs))"
        apply (subst cost_of_path_append)
          apply auto
        done
      also have "... = cost_of_path (c G) (x#y#ys @ z#tlzs)"
        by auto

      then show ?thesis sorry
    qed
  qed
qed (* TODO: continue here. replace "card (set2 (V\<^sub>H\<^sub>e e) \<inter> set T)" with hp \<Rightarrow> cost 11 *)

thm cost_filter_tour_leq_aux *)

lemma is_hc_rotate_tour:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" 
  shows "g2.is_hc_Adj (f G) (rotate_tour h T)" (is "g2.is_hc_Adj (f G) ?T'")
proof (intro g2.is_hc_AdjI)
  obtain u where "g2.path_betw (f G) u T u"
    using assms by (elim g2.is_hc_AdjE)
  hence hd_eq_last: "hd T = last T" and T_non_nil: "T \<noteq> []"
    using g2.path_non_empty by (auto simp add: g2.hd_path_betw g2.last_path_betw)
  hence rotT_hd_last_eq: "hd (rotate_tour h T) = last (rotate_tour h T)"
    using rotate_tour_hd_eq_last by auto

  have "g2.vertices (f G) = List.set (tl T)"
    using assms by (elim g2.is_hc_AdjE)
  thus set_tl_rotT: "g2.vertices (f G) = set (tl (rotate_tour h T))"
    using hd_eq_last set_tl_rotate_tour by auto

  have "distinct (tl T)"
    using assms by (elim g2.is_hc_AdjE)
  thus distinct_rotT: "distinct (tl (rotate_tour h T))"
    using hd_eq_last by (intro distinct_rotate_tour)
  hence dist_adj_rotT: "distinct_adj (rotate_tour h T)"
    using distinct_distinct_adj sorry

  have set_rotT: "set (rotate_tour h T) \<subseteq> g2.vertices (f G)"
    using set_tl_rotT rotT_hd_last_eq 
    sorry

  show "\<exists>u. g2.path_betw (f G) u (rotate_tour h T) u"
  proof -
    have "g2.path_betw (f G) (hd (rotate_tour h T)) (rotate_tour h T) (last (rotate_tour h T))"
      apply (intro g2.path_betw_in_complete_graph)
      using assms f_is_complete apply simp
      using T_non_nil rotate_tour_non_nil apply auto[1]
      using dist_adj_rotT apply simp
      using set_rotT by auto 
    thus ?thesis
      using rotT_hd_last_eq by fastforce
  qed
qed

lemma shorter_tour_is_hc:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) (x#y#T @ [x])" (is "g2.is_hc_Adj (f G) ?T") and "e \<in> g1.uedges G"
      and "isin2 (V\<^sub>H G) x" "\<not> isin2 (V\<^sub>H\<^sub>e e) x" "isin2 (V\<^sub>H\<^sub>e e) y" 
   shows "g2.is_hc_Adj (f G) (x#hp_starting_at y @ filter (Not o isin2 (V\<^sub>H\<^sub>e e)) T @ [x])" (is "g2.is_hc_Adj (f G) ?T'")
proof (intro g2.is_hc_AdjI)
  have hd_eq_last: "hd ?T = last ?T" and T_non_nil: "?T \<noteq> []"
    using g2.path_non_empty by (auto simp add: g2.hd_path_betw g2.last_path_betw)
  hence rotT_hd_last_eq: "hd ?T' = last ?T'"
    using rotate_tour_hd_eq_last by auto

  have "g2.vertices (f G) = List.set (tl ?T)"
    using assms by (elim g2.is_hc_AdjE)
  thus set_tl_rotT: "g2.vertices (f G) = set (tl ?T')"
    using hd_eq_last set_tl_rotate_tour sorry

  have "distinct (tl ?T)"
    using assms by (elim g2.is_hc_AdjE)
  thus distinct_rotT: "distinct (tl ?T')"
    using hd_eq_last sorry
  hence dist_adj_rotT: "distinct_adj ?T'"
    using distinct_distinct_adj sorry

  have set_rotT: "set ?T' \<subseteq> g2.vertices (f G)"
    using set_tl_rotT rotT_hd_last_eq 
    sorry

  show "\<exists>u. g2.path_betw (f G) u ?T' u"
  proof -
    have "g2.path_betw (f G) x ?T' x"
      apply (intro g2.path_betw_in_complete_graph)
      using assms f_is_complete apply simp
      using T_non_nil rotate_tour_non_nil apply auto[1]
      using dist_adj_rotT apply simp
      using set_rotT by auto 
    thus ?thesis
      using rotT_hd_last_eq by fastforce
  qed
qed

lemma shorten_tour_for_edge:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) (x#y#T @ [x])" (is "g2.is_hc_Adj (f G) ?T") and "e \<in> g1.uedges G"
      and "isin2 (V\<^sub>H G) x" "\<not> isin2 (V\<^sub>H\<^sub>e e) x" "isin2 (V\<^sub>H\<^sub>e e) y"
  shows "cost_of_path (c G) (x#hp_starting_at y @ filter (Not o isin2 (V\<^sub>H\<^sub>e e)) T @ [x]) \<le> cost_of_path (c G) ?T"
  (is "cost_of_path (c G) (x#?hp\<^sub>y @ ?T\<^sub>f) \<le> cost_of_path (c G) ?T")
proof -
  have "y \<in> set2 (V\<^sub>H\<^sub>e e)"
    using assms invar_vertices_of_H invar_vertices_of_He by (auto simp add: g2.set_specs)
  hence y_is_vert: "isin2 (V\<^sub>H G) y"
    using assms(1,3) invar_vertices_of_H set_vertices_of_H by (auto simp add: g2.set_specs)
  
  obtain e\<^sub>x where "e\<^sub>x \<in> g1.uedges G" "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x"
    using assms by (elim isin_vertices_of_H_obtain_edge)
  moreover hence "rep1 e\<^sub>x \<noteq> rep1 e"
    using assms(5) isin_vertices_of_He_unique[OF \<open>isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x\<close>] by auto
  ultimately have x_y_no_vert: "\<not> are_vertices_in_He G x y"
    using assms vertices_in_He_rep_iff invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)

  have "cost_of_path (c G) ((x#?hp\<^sub>y) @ ?T\<^sub>f) = c G x (hd ?hp\<^sub>y) + cost_of_path (c G) ?hp\<^sub>y + c G (last ?hp\<^sub>y) (hd ?T\<^sub>f) + cost_of_path (c G) ?T\<^sub>f"
    using hp_starting_at_non_nil by (auto simp add: cost_of_path_append cost_of_path_cons last_ConsR)
  also have "... \<le> c G x (hd ?hp\<^sub>y) + cost_of_path (c G) (y#T @ [x])"
    sorry
  also have "... \<le> c G x y + cost_of_path (c G) (y#T @ [x])"
    using assms y_is_vert x_y_no_vert cost_hd_hp_starting_at_leq by auto
  also have "... \<le> cost_of_path (c G) ?T"
    by auto
  finally show ?thesis 
    by auto
qed

lemma cost_of_tour_of_hp_starting_vertices_leq:
  assumes "g1.ugraph_adj_map_invar G" (* "g2.is_hc_Adj (f G) T" and "\<exists>e. e \<in> g1.uedges G" *)
  shows "cost_of_path (c G) (tour_of_hp_starting_vertices (map_tour_to_hp_staring_vertices G T)) \<le> cost_of_path (c G) T"
  \<comment> \<open>The induced tour computed by the function \<open>g\<close> has lower cost compared to the original tour \<open>T\<close>.\<close>
  using assms(1)
proof (rule fold4.fold_uedgesE)
  let ?f="map_edge_to_hp_start_vertex G T"
  fix es
  assume "distinct es" "map rep1 es = es" and set_es_fold: "set es = g1.uedges G" 
    "fold_g1_uedges4 (\<lambda>e xs. xs @ [?f e]) G [] = fold (\<lambda>e xs. xs @ [?f e]) es []"
  (* hence es_non_empty [simp]: "es \<noteq> []" and len_es [simp]: "length es = int (card (g1.uedges G))"
    using assms by (auto simp add: distinct_card[symmetric]) *)

  have "map_tour_to_hp_staring_vertices G T = map ?f es"
    using set_es_fold by (auto simp add: fold_concat_map)

  thm cost_rotate_tour_eq

  find_theorems "cost_of_path ?c ?x \<ge> 0"

  show ?thesis
    sorry
qed
(* TODO: tricky! *)

end

section \<open>Reduction Proof\<close>

context VC4_To_mTSP
begin

lemma hc_from_vc:
  assumes "g1.ugraph_adj_map_invar G" and "card (g1.uedges G) > 1" "card1 X > 1"
      and "g1.is_vc_Adj G X" "set_invar1 X"
  obtains T where "g2.is_hc_Adj (f G) T" "cost_of_path (c G) T \<le> 15 * int (card (g1.uedges G)) + card1 X"
proof -
  have edge_exists: "\<exists>e. e \<in> g1.uedges G"
    using assms(2) finite_sets1
    by (metis all_not_in_conv dual_order.irrefl obtain_subset_with_card_n order_less_imp_le subset_empty)

  have distinct: "distinct (hp_from_vc G X)" 
    using assms(1,4,5) by (rule distinct_hp_from_vc)
  moreover have set: "List.set (hp_from_vc G X) = g2.vertices (f G)"
    using assms(1,4,5) by (rule set_hp_from_vc)
  moreover obtain u\<^sub>1 v\<^sub>1 u\<^sub>2 v\<^sub>2 where uv12_isin: "isin1 X u\<^sub>1" "isin1 X u\<^sub>2" "rep1 (uEdge u\<^sub>1 v\<^sub>1) \<in> g1.uedges G" 
    "rep1 (uEdge u\<^sub>2 v\<^sub>2) \<in> g1.uedges G" and
    path: "g2.path_betw (f G) (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2) (hp_from_vc G X) (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)" 
      (is "g2.path_betw (f G) ?u\<^sub>2 _ ?u\<^sub>1")
    using assms edge_exists by (elim path_hp_from_vc)
  moreover have cost_hp: "cost_of_path (c G) (hp_from_vc G X) \<le> 15 * int (card (g1.uedges G)) + card1 X - 5"
    using assms edge_exists by (intro cost_hp_from_vc)
  moreover have "distinct_adj (?u\<^sub>1#hp_from_vc G X)" (is "distinct_adj ?T")
      and "last (hp_from_vc G X) = ?u\<^sub>1"
      and "?u\<^sub>1 \<in> List.set (hp_from_vc G X)" "List.set (hp_from_vc G X) \<subseteq> g2.vertices (f G)"
    using distinct set distinct_distinct_adj path g2.path_non_empty g2.hd_path_betw apply (intro iffD2[OF distinct_adj_Cons]) apply auto[1]
    using path apply (intro g2.last_path_betw) apply simp
    using path g2.last_path_betw g2.path_non_empty last_in_set apply metis
    using path g2.path_vertices apply simp
    done
  moreover hence "g2.path_betw (f G) ?u\<^sub>1 ?T ?u\<^sub>1" 
    using assms f_is_complete by (intro g2.path_betw_in_complete_graph) auto
  ultimately have hc: "g2.is_hc_Adj (f G) ?T"
    by (intro g2.is_hc_AdjI) auto

  have "c G ?u\<^sub>1 ?u\<^sub>2 \<le> 5"
    using assms by (intro cost_u1_u2_leq5)
  moreover have "hp_from_vc G X \<noteq> []"
    using path by (auto intro!: g2.path_non_empty)
  moreover have "hd (hp_from_vc G X) = ?u\<^sub>2"
    using path by (auto intro!: g2.hd_path_betw)
  ultimately have cost: "cost_of_path (c G) (?u\<^sub>1#hp_from_vc G X) \<le> 15 * card (g1.uedges G) + card (set1 X)" 
    using cost_hp by (auto simp add: cost_of_path_cons)
  thus ?thesis
    using that hc by auto
qed

(* lemma hc_from_vc:
  assumes "g1.ugraph_adj_map_invar G" "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
      and "g1.is_vc_Adj G X" "set_invar1 X"
  obtains T where "g2.is_hc_Adj (f G) T" "cost_of_path (c G) T \<le> 15 * int (card (g1.uedges G)) + card1 X" 
proof -
  have distinct: "distinct (hp_from_vc G X)" 
    using assms(1,3,4) by (rule distinct_hp_from_vc)
  moreover have set: "List.set (hp_from_vc G X) = g2.vertices (f G)"
    using assms(1,3,4) by (rule set_hp_from_vc)
  moreover obtain u\<^sub>1 v\<^sub>1 u\<^sub>2 v\<^sub>2 where 
    path: "g2.path_betw (f G) (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2) (hp_from_vc G X) (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)" 
      (is "g2.path_betw (f G) ?u\<^sub>2 _ ?u\<^sub>1")
    using assms by (elim path_hp_from_vc)
  moreover have cost_hp: "cost_of_path (c G) (hp_from_vc G X) \<le> 15 * int (card (g1.uedges G)) + card1 X - 5"
    using assms by (rule cost_hp_from_vc)
  moreover have "distinct_adj (?u\<^sub>1#hp_from_vc G X)" (is "distinct_adj ?T")
      and "last (hp_from_vc G X) = ?u\<^sub>1"
      and "?u\<^sub>1 \<in> List.set (hp_from_vc G X)" "List.set (hp_from_vc G X) \<subseteq> g2.vertices (f G)"
    using distinct set distinct_distinct_adj path g2.path_non_empty g2.hd_path_betw apply (intro iffD2[OF distinct_adj_Cons]) apply auto[1]
    using path apply (intro g2.last_path_betw) apply simp
    using path g2.last_path_betw g2.path_non_empty last_in_set apply metis
    using path g2.path_vertices apply simp
    done
  moreover hence "g2.path_betw (f G) ?u\<^sub>1 ?T ?u\<^sub>1" 
    using assms f_is_complete by (intro g2.path_betw_in_complete_graph) auto
  ultimately have hc: "g2.is_hc_Adj (f G) ?T"
    by (intro g2.is_hc_AdjI) auto

  have "c G ?u\<^sub>1 ?u\<^sub>2 \<le> 5"
    using assms by (intro cost_u1_u2_leq5)
  moreover have "hp_from_vc G X \<noteq> []"
    using path by (auto intro!: g2.path_non_empty)
  moreover have "hd (hp_from_vc G X) = ?u\<^sub>2"
    using path by (auto intro!: g2.hd_path_betw)
  ultimately have cost: "cost_of_path (c G) (?u\<^sub>1#hp_from_vc G X) \<le> 15 * card (g1.uedges G) + card (set1 X)" 
    using cost_hp by (auto simp add: cost_of_path_cons)

  show ?thesis
    using that hc cost by auto
qed *)

lemma cost_of_opt_mTSP:
  assumes "g1.ugraph_adj_map_invar G"
      and "card (g1.uedges G) > 1" "card1 OPT\<^sub>V\<^sub>C > 1" (* TODO:How to deal with these assumptions? *)
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C"
      and opt_mtsp: "g2.is_tsp_Adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
      and "card (g1.uedges G) > 1" "card1 OPT\<^sub>V\<^sub>C > 1"
  shows "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 15 * int (card (g1.uedges G)) + card1 OPT\<^sub>V\<^sub>C"
  \<comment> \<open>The cost of the optimal Hamiltonian cycle in the graph \<open>f G\<close> is bounded.\<close>
proof -
  let ?E="g1.uedges G"
  let ?\<tau>_G="card1 OPT\<^sub>V\<^sub>C"
  have "g1.is_vc_Adj G OPT\<^sub>V\<^sub>C"
    using assms by (elim g1.is_min_vc_AdjE)
  then obtain T where "g2.is_hc_Adj (f G) T" "cost_of_path (c G) T \<le> 15 * int (card ?E) + ?\<tau>_G"
    using assms by (elim hc_from_vc) 
  moreover hence "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> cost_of_path (c G) T"
    using assms g2.is_tsp_AdjE by blast
  ultimately show ?thesis
    by auto
qed

(* ----- 1st condition for a L-reduction ----- *)

lemma l_reduction1:
  assumes "g1.ugraph_adj_map_invar G" and "card (g1.uedges G) > 1" "card1 OPT\<^sub>V\<^sub>C > 1"
      and max_degree: "\<And>v. v \<in> g1.vertices G \<Longrightarrow> g1.degree_Adj G v \<le> enat 4"
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C"
      and opt_mtsp: "g2.is_tsp_Adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * card1 OPT\<^sub>V\<^sub>C" (is "?c' OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> ?\<alpha> * ?\<tau>_G")
  \<comment> \<open>First condition for a L-Reduction.\<close>
proof -
  have uedges_leq_max_degree_card_vc: "card (g1.uedges G) \<le> 4 * card (set1 OPT\<^sub>V\<^sub>C)"
    using assms by (auto intro!: g1.uedges_leq_max_degree_card_vc elim: g1.is_min_vc_AdjE)

  have "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 15 * int (card (g1.uedges G)) + ?\<tau>_G"
    using assms cost_of_opt_mTSP by blast
  also have "... \<le> 15 * (4 * ?\<tau>_G) + ?\<tau>_G"
    using uedges_leq_max_degree_card_vc by (auto simp add: mult_left_mono)
  also have "... = 61 * ?\<tau>_G"                         
    by auto
  finally show ?thesis .
qed

(* ----- 2nd condition for a L-reduction ----- *)

lemma card_g_leq_k:
  assumes "g1.ugraph_adj_map_invar G" and "card (g1.uedges G) > 1" "card1 (g G T) > 1"
      and "g2.is_hc_Adj (f G) T" 
  obtains k where "card1 (g G T) \<le> k" and "15 * int (card (g1.uedges G)) + k \<le> cost_of_path (c G) T"
    \<comment> \<open>The cost of the vertex cover computed by the function \<open>g\<close> is linked to the cost of the 
    given Hamiltonian cycle of the graph \<open>f G\<close>.\<close>
  using assms
proof (rule cost_of_tour_of_hp_starting_vertices)
  let ?T'="tour_of_hp_starting_vertices (map_tour_to_hp_staring_vertices G T)"
  fix k 
  assume "card1 (g G T) \<le> k" "15 * int (card (g1.uedges G)) + k \<le> cost_of_path (c G) ?T'"
  moreover have "cost_of_path (c G) ?T' \<le> cost_of_path (c G) T"
    using assms by (intro cost_of_tour_of_hp_starting_vertices_leq)
  ultimately show ?thesis
    using that by auto
qed (* needed for proof of \<open>l_reduction2\<close> *)

lemma l_reduction2:
  assumes "g1.ugraph_adj_map_invar G" and "card (g1.uedges G) > 1" "card1 OPT\<^sub>V\<^sub>C > 1" (is "?\<tau>_G > 1")
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C"
      and opt_mtsp: "g2.is_tsp_Adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P" 
      and "g2.is_hc_Adj (f G) T"
  shows "\<bar> card1 (g G T) - card1 OPT\<^sub>V\<^sub>C \<bar> \<le> 1 * \<bar> cost_of_path (c G) T - cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>" 
  \<comment> \<open>Second condition for a L-Reduction.\<close>
  using assms(1-5)
proof -
  let ?E="g1.uedges G"
  have cost_mtsp: "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 15 * int (card (g1.uedges G)) + ?\<tau>_G"
    using assms cost_of_opt_mTSP by auto

  have "g1.is_vc_Adj G (g G T)"
    using assms by (intro g_is_vc)
  hence "g1.is_vc_Adj G OPT\<^sub>V\<^sub>C" and tauG_leq: "?\<tau>_G \<le> card1 (g G T)"
    using assms by (auto elim: g1.is_min_vc_AdjE)
  then obtain k where card_leq_k: "card1 (g G T) \<le> k" and cost_T_geq: "15 * int (card ?E) + k \<le> cost_of_path (c G) T"
    using assms by (elim card_g_leq_k) auto

  have "card1 (g G T) - ?\<tau>_G \<le> k - ?\<tau>_G"
    using card_leq_k by auto
  also have "... \<le> 15 * int (card ?E) + k - (15 * int (card ?E) + ?\<tau>_G)"
    by auto
  also have "... \<le> cost_of_path (c G) T - (15 * int (card ?E) + ?\<tau>_G)"
    using cost_T_geq by auto
  also have "... \<le> cost_of_path (c G) T - cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
    using cost_mtsp by auto
  finally show ?thesis 
    using tauG_leq by auto
qed

end

end