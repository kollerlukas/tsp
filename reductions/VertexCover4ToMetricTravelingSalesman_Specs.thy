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
  assumes fold_g1_uedges1: "\<And>M f a. g1.ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges1 f M a = fold f es a"
  fixes fold_g1_uedges2 :: "('v1 uedge \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 'g1 \<Rightarrow> bool \<Rightarrow> bool"
  assumes fold_g1_uedges2: "\<And>M f a. g1.ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges2 f M a = fold f es a"
  fixes fold_g1_uedges3 :: "('v1 uedge \<Rightarrow> enat \<Rightarrow> enat) \<Rightarrow> 'g1 \<Rightarrow> enat \<Rightarrow> enat"
  assumes fold_g1_uedges3: "\<And>M f a. g1.ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges3 f M a = fold f es a"
  fixes fold_g1_uedges4 :: "('v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list) 
    \<Rightarrow> 'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list"
  assumes fold_g1_uedges4: "\<And>M f a. g1.ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges4 f M a = fold f es a"
  fixes fold_g1_uedges5 :: "('v1 uedge \<Rightarrow> 'v1set \<Rightarrow> 'v1set) \<Rightarrow> 'g1 \<Rightarrow> 'v1set \<Rightarrow> 'v1set"
  assumes fold_g1_uedges5: "\<And>M f a. g1.ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es
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

  (* fixes choose_edge :: "'g1 \<Rightarrow> 'v1 uedge option"
  assumes choose_edge: "g1.ugraph_adj_map_invar G \<Longrightarrow> g1.uedges G \<noteq> {} \<Longrightarrow> the (choose_edge G) \<in> g1.uedges G" *)
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
  "are_vertices_in_He G x y = fold_g1_uedges2 (\<lambda>e b. b \<or> (isin2 (V\<^sub>H\<^sub>e e) x \<and> isin2 (V\<^sub>H\<^sub>e e) y)) G False"
  \<comment> \<open>Return \<open>True\<close> if the graph \<open>G\<close> contains an edge \<open>e\<close> in s.t. \<open>u\<close> and \<open>y\<close> are vertices in the 
  subgraph \<open>H\<^sub>e e\<close>; return \<open>False\<close> otherwise.\<close>
  (* alternate definition:  min_dist_in_He < \<infinity> *)

fun hp_for_neighborhood :: "'v1 \<Rightarrow> 'v1set \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where 
  "hp_for_neighborhood u N\<^sub>u = fold_v1set1 
    (\<lambda>v T. T @ (if rep1 (uEdge u v) = uEdge u v then hp_u2 (uEdge u v) else hp_v2 (uEdge u v))) N\<^sub>u []"
  \<comment> \<open>Compute a Hamiltonian Path for a subgraph \<open>{{u,v} | v. v \<in> set1 N\<^sub>u}\<close> of \<open>f G\<close>. The subgraph 
  is induced by the neighborhood \<open>N\<^sub>u\<close> of \<open>u\<close>.\<close>

fun partition_for_vertex :: "'g1 \<Rightarrow> 'v1set \<Rightarrow> 'v1 \<Rightarrow> 'v1set" ("\<P>") where 
  "partition_for_vertex G X u = filter_v1set (\<lambda>v. \<not> isin1 X v \<or> rep1 (uEdge u v) = uEdge u v) (\<N>\<^sub>1 G u)"
  \<comment> \<open>Compute a partition on the set of edges of \<open>G\<close> that is induced by a vertex cover; 
  return the partition corresponding to the vertex \<open>u\<close> from a vertex cover.\<close>

fun hp_of_vc :: "'g1 \<Rightarrow> 'v1set \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_of_vc G X = fold_v1set1 (\<lambda>u T. T @ hp_for_neighborhood u (partition_for_vertex G X u)) X []"
  \<comment> \<open>Compute a Hamiltonian path on \<open>f G\<close> that is induced by the vertex cover \<open>X\<close> of the graph \<open>G\<close>.\<close>


fun hp_starting_at :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_starting_at (e,x,i) = (case rep1 e of uEdge u v \<Rightarrow> if x = v then hp_v1 (rep1 e) else hp_u1 (rep1 e))"

fun replace_hp :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "replace_hp G [] = []"
| "replace_hp G (x#T) = hp_starting_at x @ replace_hp G (filter (\<lambda>y. \<not> are_vertices_in_He G x y) T)"

fun shorten_tour :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "shorten_tour G T = (let f = \<lambda>(e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2). w\<^sub>1 \<noteq> w\<^sub>2 \<and> rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2; 
    T' = replace_hp G (tl (rotate_tour f T)) in last T'#T')"

fun vc_of_tour :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1set" where
  "vc_of_tour G [] = set_empty1"
| "vc_of_tour G ((e,u,i)#T) = insert1 u (vc_of_tour G (filter (\<lambda>y. \<not> are_vertices_in_He G (e,u,i) y) T))"

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
    else if w\<^sub>1 = w\<^sub>2 \<and> rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2 \<and> (i\<^sub>1 = 1 \<or> i\<^sub>1 = 2) \<and> (i\<^sub>2 = 1 \<or> i\<^sub>2 = 2) then 4
    else 5)"

fun g :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1set" where
  (* "g G T = fold_g1_uedges5 (insert1 o (map_edge_to_covering_vertex G T)) G set_empty1" *)
  (* "g G T = g1.set_of_list (map (\<lambda>(_,x,_). x) (hp_starting_vertices_of_tour G T))" *)
  "g G T = vc_of_tour G (tl (shorten_tour G T))"

end

section \<open>Properties of Auxiliary Functions\<close>

context VC4_To_mTSP
begin

lemma vertices_of_He_rep_idem: "V\<^sub>H\<^sub>e (rep1 e) = V\<^sub>H\<^sub>e e"
  by (simp only: vertices_of_He.simps g1.rep_idem)

lemma invar_vertices_of_He: "set_invar2 (V\<^sub>H\<^sub>e e)"
  by (auto simp add: g2.invar_set_of_list simp del: g2.set_of_list.simps split: uedge.splits)

(* lemma vertices_of_He_non_empty: "\<exists>x. isin2 (V\<^sub>H\<^sub>e e) x"
  using invar_vertices_of_He by (auto simp add: g2.set_specs split: uedge.splits)

lemma set_vertices_of_He_non_empty: "set2 (V\<^sub>H\<^sub>e e) \<noteq> {}"
  using invar_vertices_of_He vertices_of_He_non_empty by (auto simp add: g2.set_specs) *)

lemma isin_vertices_of_He_iff: 
  assumes "rep1 e = rep1 (uEdge u v)"
  shows "isin2 (V\<^sub>H\<^sub>e e) x \<longleftrightarrow> x \<in> set [(rep1 e,u,1::nat),(rep1 e,u,2),
    (rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),
    (rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]" 
  using assms by (rule g1.rep_cases) (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)

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
    using assms isin_vertices_of_He_iff by auto
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

lemma vertices_of_He_non_empty: "\<exists>x. x \<in> g2.vertices (H\<^sub>e e)"
  using vertices_of_He invar_vertices_of_He by (auto simp add: g2.set_specs split: uedge.splits)

lemma vertices_of_He_disjoint:
  assumes "rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2" 
  shows "g2.vertices (H\<^sub>e e\<^sub>1) \<inter> g2.vertices (H\<^sub>e e\<^sub>2) = {}"
proof (rule ccontr)
  assume "g2.vertices (H\<^sub>e e\<^sub>1) \<inter> g2.vertices (H\<^sub>e e\<^sub>2) \<noteq> {}"
  then obtain x where "x \<in> g2.vertices (H\<^sub>e e\<^sub>1)" "x \<in> g2.vertices (H\<^sub>e e\<^sub>2)"
    by auto
  hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>1) x" "isin2 (V\<^sub>H\<^sub>e e\<^sub>2) x"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  then obtain u\<^sub>1 v\<^sub>1 u\<^sub>2 v\<^sub>2 where "rep1 e\<^sub>1 = rep1 (uEdge u\<^sub>1 v\<^sub>1)" "rep1 e\<^sub>2 = rep1 (uEdge u\<^sub>2 v\<^sub>2)"
    and "x \<in> set [(rep1 e\<^sub>1,u\<^sub>1,1),(rep1 e\<^sub>1,u\<^sub>1,2),(rep1 e\<^sub>1,u\<^sub>1,3),(rep1 e\<^sub>1,u\<^sub>1,4),(rep1 e\<^sub>1,u\<^sub>1,5),(rep1 e\<^sub>1,u\<^sub>1,6)]"
    and "x \<in> set [(rep1 e\<^sub>2,u\<^sub>2,1),(rep1 e\<^sub>2,u\<^sub>2,2),(rep1 e\<^sub>2,u\<^sub>2,3),(rep1 e\<^sub>2,u\<^sub>2,4),(rep1 e\<^sub>2,u\<^sub>2,5),(rep1 e\<^sub>2,u\<^sub>2,6)]"
    by (auto elim!: isin_vertices_of_He_elim simp del: vertices_of_He.simps)
  thus "False"
    using assms by auto
qed

lemma card_vertices_of_He: 
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
  shows "card (g2.vertices (H\<^sub>e e)) = 12"
  using assms
proof (rule g1.uedge_not_refl_elim)
  fix u v
  assume "rep1 e = uEdge u v" "u \<noteq> v"
  moreover hence "card (set [(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),
      (rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]) = 12"
    sorry (* TODO: How to prove this? *)
  ultimately have "card (set2 (V\<^sub>H\<^sub>e e)) = 12"
    using g2.set_of_list sorry
  thus ?thesis
    using vertices_of_He by auto
qed

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
  assume "distinct es" and set_es: "List.set es = g1.uedges G" 
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


lemma are_vertices_in_He_elim2:
  assumes "g1.ugraph_adj_map_invar G" and "are_vertices_in_He G x y" 
      and "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)"
    shows "y \<in> g2.vertices (H\<^sub>e e)"
  using assms (1,2)
proof (rule are_vertices_in_He_elim)
  fix e' 
  assume "e' \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e')" and "y \<in> g2.vertices (H\<^sub>e e')"
  moreover hence "e = e'"
    using assms vertices_in_He_rep_iff g1.rep_of_edge by metis
  ultimately show "y \<in> g2.vertices (H\<^sub>e e)"
    by auto
qed

lemma are_vertices_in_He_sym:
  assumes "g1.ugraph_adj_map_invar G" "are_vertices_in_He G x y"
  shows "are_vertices_in_He G y x"
  using assms are_vertices_in_He by auto

lemma are_vertices_in_He_trans:
  assumes "g1.ugraph_adj_map_invar G" "are_vertices_in_He G x y" "are_vertices_in_He G y z"
  shows "are_vertices_in_He G x z"
proof (rule are_vertices_in_He_elim[OF assms(1,2)]; rule are_vertices_in_He_elim[OF assms(1,3)])
  fix e\<^sub>1 e\<^sub>2
  assume "e\<^sub>1 \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e\<^sub>1)" "y \<in> g2.vertices (H\<^sub>e e\<^sub>1)" 
    "e\<^sub>2 \<in> g1.uedges G" "y \<in> g2.vertices (H\<^sub>e e\<^sub>2)" "z \<in> g2.vertices (H\<^sub>e e\<^sub>2)"
  moreover hence "e\<^sub>1 = e\<^sub>2"
    using assms vertices_in_He_rep_iff by (auto simp add: g1.rep_of_edge)
  ultimately show ?thesis
    using assms by (intro are_vertices_in_He_intro) auto
qed

(* lemma vertices_in_He_path_dist: 
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" 
      and "x \<in> g2.vertices (H\<^sub>e e)" "y \<in> g2.vertices (H\<^sub>e e)"
  shows "g2.path_dist (H\<^sub>e e) x y < \<infinity>"
  using invar_He
  apply (intro g2.path_dist_less_inf)
  apply simp
  sorry (* TODO: How to prove? *) *)

lemma min_dist_in_He_def2:
  assumes "g1.ugraph_adj_map_invar G"
  shows "min_dist_in_He G x y = Min ({g2.path_dist (H\<^sub>e e) x y | e. e \<in> g1.uedges G} \<union> {\<infinity>})"
  using assms(1)
proof (rule fold3.fold_uedgesE)
  let ?f="\<lambda>e d. min (g2.path_dist (H\<^sub>e e) x y) d"
  fix es
  assume "distinct es" and set_es: "set es = g1.uedges G" and [simp]: "fold_g1_uedges3 ?f G \<infinity> = fold ?f es \<infinity>"
  moreover have "\<And>a. fold ?f es a = fold min (map (\<lambda>e. g2.path_dist (H\<^sub>e e) x y) es) a"
    by (induction es) auto
  ultimately have "min_dist_in_He G x y = fold min (map (\<lambda>e. g2.path_dist (H\<^sub>e e) x y) es) \<infinity>"
    by auto
  also have "... = Min (set (\<infinity>#(map (\<lambda>e. g2.path_dist (H\<^sub>e e) x y) es)))"
    using Min.set_eq_fold[symmetric] by fastforce
  also have "... = Min ({g2.path_dist (H\<^sub>e e) x y | e. e \<in> g1.uedges G} \<union> {\<infinity>})"
    by (auto simp add: Setcompr_eq_image set_es)
  finally show ?thesis  
    by auto
qed

lemma min_dist_in_He_leq_path_dist:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
  shows "min_dist_in_He G x y \<le> g2.path_dist (H\<^sub>e e) x y"
  using assms(1)
proof (rule fold3.fold_uedgesE)
  let ?f="\<lambda>e d. min (g2.path_dist (H\<^sub>e e) x y) d"
  fix es
  assume "distinct es" and set_es: "List.set es = g1.uedges G" and [simp]: "fold_g1_uedges3 ?f G \<infinity> = fold ?f es \<infinity>"
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
    using invar_He apply (intro g2.path_dist_less_inf)
    sorry (* vertices_in_He_path_dist by auto *)
  moreover have "min_dist_in_He G x y \<le> g2.path_dist (H\<^sub>e e) x y"
    using assms e_isin_G by (intro min_dist_in_He_leq_path_dist)
  ultimately show ?thesis
    using order_le_less_trans by blast
qed

lemma min_dist_in_He_geq1:
  assumes "g1.ugraph_adj_map_invar G" "x \<noteq> y"
  shows "min_dist_in_He G x y \<ge> enat 1"
proof (rule ccontr)
  assume "\<not> min_dist_in_He G x y \<ge> enat 1"
  hence "min_dist_in_He G x y < enat 1"
    by auto
  hence "Min ({g2.path_dist (H\<^sub>e e) x y |e. e \<in> g1.uedges G} \<union> {\<infinity>}) < enat 1" (is "Min ?D < _")
    using assms min_dist_in_He_def2 by auto
  moreover have "?D \<noteq> {}" "finite ?D"
    using assms by auto
  ultimately obtain e where "e \<in> g1.uedges G" "g2.path_dist (H\<^sub>e e) x y < enat 1"
    using Min_less_iff[of ?D "enat 1"] by auto
  moreover have "finite ({enat (length (tl P)) |P. g2.path_betw (H\<^sub>e e) x P y \<and> distinct P} \<union> {\<infinity>})" (is "finite ?P")
    using invar_He g2.finite_paths by auto
  ultimately obtain P where path: "g2.path_betw (H\<^sub>e e) x P y" and "distinct P" "enat (length (tl P)) < enat 1"
    unfolding g2.path_dist_def using Min_less_iff[of ?P "enat 1"] by auto
  moreover hence "length (tl P) = 0"
    by auto
  moreover hence "tl P = []"
    by blast
  moreover hence "P = [x]"   
    using g2.path_non_empty[OF path] g2.hd_path_betw[OF path] by (cases P) fastforce+
  ultimately have "x = y"
    using g2.last_path_betw[OF path] by auto
  thus "False"
    using assms by auto
qed

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
  obtain es where "distinct es" and set_es: "List.set es = g1.uedges G" 
    and [simp]: "fold_g1_uedges2 ?f G False = fold ?f es False"
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
  assume "distinct es" "List.set es = g1.uedges G" 
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
  assume "distinct es" "List.set es = g1.uedges G" 
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
  assumes "g1.ugraph_adj_map_invar G" "x \<noteq> y"
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

lemma vertices_hp_u1: "List.set (hp_u1 e) = g2.vertices (H\<^sub>e e)"
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

lemma vertices_hp_u2: "List.set (hp_u2 e) = g2.vertices (H\<^sub>e e)"
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

lemma vertices_hp_v1: "List.set (hp_v1 e) = g2.vertices (H\<^sub>e e)"
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

lemma vertices_hp_v2: "List.set (hp_v2 e) = g2.vertices (H\<^sub>e e)"
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

(* lemma min_dist_u1_u2_geq4: 
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
qed (* TODO: How do I prove this?! *) *)

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

lemma vertices_f_eq_vertices_of_H:
  assumes "g1.ugraph_adj_map_invar G"
  shows "g2.vertices (f G) = set2 (V\<^sub>H G)"
  using assms invar_vertices_of_H at_least_two_vertices_in_H
  by (simp only: f.simps; intro vertices_complete_graph)

lemma vertices_f: 
  "g1.ugraph_adj_map_invar G \<Longrightarrow> g2.vertices (f G) = \<Union> ((g2.vertices o H\<^sub>e) ` g1.uedges G)"
  using vertices_f_eq_vertices_of_H set_vertices_of_H vertices_of_He by simp

lemma vertices_f_non_empty:
  assumes "g1.ugraph_adj_map_invar G" "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
  shows "\<exists>v. v \<in> g2.vertices (f G)"
  using assms vertices_of_He_non_empty by (fastforce simp add: vertices_f simp del: f.simps)

lemma obtain_vertex_of_He:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" and "e \<in> g1.uedges G"
  obtains x where "x \<in> List.set T" "x \<in> g2.vertices (H\<^sub>e e)"
proof (cases e)
  case (uEdge u v)
  have "List.set (tl T) = g2.vertices (f G)"
    using assms g2.is_hc_AdjE by auto
  also have "... = \<Union> ((g2.vertices o H\<^sub>e) ` g1.uedges G)"
    using assms vertices_f set_vertices_of_H by auto
  finally have "g2.vertices (H\<^sub>e e) \<subseteq> List.set T"
    using assms set_tl_subset by fastforce
  moreover have "isin2 (V\<^sub>H\<^sub>e e) (rep1 e,u,1)"
    using assms uEdge by (intro isin_vertices_of_He_intro) auto
  moreover hence "(rep1 e,u,1) \<in> g2.vertices (H\<^sub>e e)"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately obtain x where "x \<in> List.set T" "x \<in> g2.vertices (H\<^sub>e e)"
    by (auto simp del: vertices_of_He.simps) 
  thus ?thesis
    using that by auto
qed

lemma fst_of_vertex_is_edge:
  assumes "g1.ugraph_adj_map_invar G" and "(e,w,i) \<in> g2.vertices (f G)" (is "?x \<in> g2.vertices (f G)")
  shows "(e,w,i) \<in> g2.vertices (H\<^sub>e e) \<and> e \<in> g1.uedges G"
  using assms             
proof -
  have "g2.vertices (f G) = \<Union> ((g2.vertices o H\<^sub>e) ` g1.uedges G)"  
    using assms vertices_f by auto
  then obtain e' where "e' \<in> g1.uedges G" "?x \<in> g2.vertices (H\<^sub>e e')"
    using assms by auto
  moreover hence "isin2 (V\<^sub>H\<^sub>e e') ?x"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  moreover hence "e = rep1 e'"
    by (elim isin_vertices_of_He_elim2) (auto simp add: g1.rep_idem)
  moreover have "rep1 e' \<in> g1.uedges G"
    using calculation by (intro g1.rep_of_edge_is_edge)
  ultimately show ?thesis
    using He_rep_idem by auto
qed

lemma are_vertices_in_He_refl:      
  assumes "g1.ugraph_adj_map_invar G" "x \<in> g2.vertices (f G)"
  shows "are_vertices_in_He G x x"
proof (cases x)
  fix e w i 
  assume "x = (e,w,i)"
  hence "x \<in> g2.vertices (H\<^sub>e e)" "e \<in> g1.uedges G" 
    using assms fst_of_vertex_is_edge by auto
  thus ?thesis
    using assms are_vertices_in_He by blast
qed

(* lemma rotate_tour_all_vertices_of_He:
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
qed *)

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

(* lemma map_edge_to_hp_start_vertex_cases:
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
qed *)

(*  using assms
proof (rule fold5.fold_uedgesE)
  let ?f="insert1 o (map_edge_to_covering_vertex G T)"
  fix es 
  assume "distinct es" "map rep1 es = es" and [simp]: "List.set es = g1.uedges G" and
    "fold_g1_uedges5 ?f G set_empty1 = fold ?f es set_empty1"
  hence [simp]: "g G T = g1.insert_all (map (map_edge_to_covering_vertex G T) es) set_empty1"
    by (auto simp: fold_map)
  thus "set_invar1 (g G T)"
    using g1.set_specs by (auto intro!: g1.invar_insert_all simp del: g.simps g1.insert_all.simps)
qed *)

(* lemma set_g:
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
qed *)

lemma hp_starting_at_non_nil: "hp_starting_at x \<noteq> []"
  by (cases x) (auto split: uedge.splits)

lemma set_hp_starting_at:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)"
  shows "set (hp_starting_at x) = g2.vertices (H\<^sub>e e)"
proof -
  have "isin2 (V\<^sub>H\<^sub>e e) x"
    using assms invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  then obtain u v w i where "x = (uEdge u v,w,i)" and [simp]: "rep1 e = uEdge u v"
    by (elim isin_vertices_of_He_elim2)
  moreover hence [simp]: "x = (e,w,i)"
    using assms g1.rep_of_edge by metis
  ultimately have "uEdge u v \<in> g1.uedges G"
    using assms g1.rep_of_edge_is_edge g1.rep_idem by fastforce
  hence rep_e: "rep1 (uEdge u v) = uEdge u v" and "rep1 (uEdge u v) \<in> g1.uedges G"
    using g1.rep_of_edge g1.rep_of_edge_is_edge by auto
  hence "u \<noteq> v"
    using assms by (intro g1.uedge_not_refl)
  thus ?thesis
  proof cases
    assume "w = v"
    thus ?thesis
      apply (subst He_rep_idem[symmetric])
      using vertices_hp_v1 by simp
  next
    assume "w \<noteq> v"
    thus ?thesis
      apply (subst He_rep_idem[symmetric])
      using vertices_hp_u1 by simp
  qed
qed

lemma hd_hp_starting_at: 
  assumes "rep1 e = uEdge u v" "x \<in> {u,v}"
  shows "hd (hp_starting_at (e,x,i)) = (rep1 e,x,1)"
  using assms g1.rep_simps by auto

lemma last_hp_starting_at: 
  assumes "rep1 e = uEdge u v" "x \<in> {u,v}"
  shows "last (hp_starting_at (e,x,i)) = (rep1 e,x,2)"
  using assms g1.rep_simps by auto

lemma cost_last_hp_x_hd_hp_y_leq: 
  assumes "g1.ugraph_adj_map_invar G" and "x \<in> g2.vertices (f G)" "y \<in> g2.vertices (f G)"
      and "\<not> are_vertices_in_He G x y"
  shows "c G (last (hp_starting_at x)) (hd (hp_starting_at y)) \<le> c G (last (hp_starting_at x)) y" (is "c G ?lstx ?hdy \<le> _")
proof (cases x; cases y)
  fix e\<^sub>x w\<^sub>x i\<^sub>x e\<^sub>y w\<^sub>y i\<^sub>y
  assume [simp]: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)" and [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
  hence vert_x: "x \<in> g2.vertices (H\<^sub>e e\<^sub>x)" "e\<^sub>x \<in> g1.uedges G" 
    and vert_y: "y \<in> g2.vertices (H\<^sub>e e\<^sub>y)" "e\<^sub>y \<in> g1.uedges G"
    using assms fst_of_vertex_is_edge by auto
  moreover hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x" and "isin2 (V\<^sub>H\<^sub>e e\<^sub>y) y"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  moreover then obtain u\<^sub>x v\<^sub>x u\<^sub>y v\<^sub>y where edge_y: "rep1 e\<^sub>y = uEdge u\<^sub>y v\<^sub>y" "w\<^sub>y \<in> {u\<^sub>y,v\<^sub>y}"
    and edge_x: "rep1 e\<^sub>x = uEdge u\<^sub>x v\<^sub>x" "w\<^sub>x \<in> {u\<^sub>x,v\<^sub>x}"
    by (elim isin_vertices_of_He_elim2) auto
  ultimately have rep_neq: "rep1 e\<^sub>x \<noteq> rep1 e\<^sub>y"
    using assms invar_vertices_of_He vertices_of_He vertices_in_He_rep_iff by (auto simp add: g2.set_specs)

  have last_x: "?lstx = (rep1 e\<^sub>x,w\<^sub>x,2)"
    using vert_x isin_vertices_of_He_edge last_hp_starting_at[OF edge_x] by auto
  moreover hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) ?lstx"
    using edge_x by (auto intro!: isin_vertices_of_He_intro2 simp del: vertices_of_He.simps)
  moreover have hd_y: "?hdy = (rep1 e\<^sub>y,w\<^sub>y,1)"
    using vert_y isin_vertices_of_He_edge hd_hp_starting_at[OF edge_y] by auto
  moreover hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>y) ?hdy"
    using edge_y by (auto intro!: isin_vertices_of_He_intro2 simp del: vertices_of_He.simps)
  ultimately have no_vert_lastx_hdy: "\<not> are_vertices_in_He G ?lstx ?hdy"
    and no_vert_lastx_y: "\<not> are_vertices_in_He G ?lstx y"
    using assms rep_neq vert_x vert_y invar_vertices_of_He vertices_of_He vertices_in_He_rep_iff 
    by (auto simp add: g2.set_specs)

  thus ?thesis
  proof cases
    assume "w\<^sub>x = w\<^sub>y"
    hence "c G (last (hp_starting_at x)) (hd (hp_starting_at y)) = 4"
      and "c G (last (hp_starting_at x)) y \<ge> 4"
      using assms rep_neq last_x hd_y no_vert_lastx_hdy no_vert_lastx_y edge_in_He_are_vertices 
      by (auto simp add: g1.rep_idem)
    thus ?thesis
      by auto
  next
    assume "w\<^sub>x \<noteq> w\<^sub>y"
    hence "c G (last (hp_starting_at x)) (hd (hp_starting_at y)) = 5"
      and "c G (last (hp_starting_at x)) y = 5"
      using assms rep_neq last_x hd_y no_vert_lastx_hdy no_vert_lastx_y edge_in_He_are_vertices 
      by (auto simp add: g1.rep_idem)
    thus ?thesis
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
  assumes "g1.ugraph_adj_map_invar G" "x \<in> g2.vertices (f G)"
  shows "cost_of_path (c G) (hp_starting_at x) = 11"
proof -
  obtain e w i where "x = (e,w,i)" "e \<in> g1.uedges G"
    using assms fst_of_vertex_is_edge by (cases x) auto
  thus ?thesis
    using assms cost_hp_starting_at by auto
qed

lemma replace_hp_non_nil: "T \<noteq> [] \<Longrightarrow> replace_hp G T \<noteq> []"
  using hp_starting_at_non_nil by (cases T) auto

lemma replace_hp_Cons_non_nil: "replace_hp G (x#T) \<noteq> []"
  using hp_starting_at_non_nil by auto

lemma concat_order_for_replace_hp_and_vc_of_tour:
  assumes "g1.ugraph_adj_map_invar G" "set es \<subseteq> g1.uedges G" 
      and "distinct es" "\<forall>e \<in> set es. rep1 e = e" "set T = \<Union> ((g2.vertices o H\<^sub>e) ` set es)"
  obtains xs where "set xs \<subseteq> set T" "distinct xs" "length xs = length es" 
    and "set es = (\<lambda>(e,_,_). e) ` set xs" "set xs \<subseteq> g2.vertices (f G)"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
    and "replace_hp G T = concat (map hp_starting_at xs)"
  using assms
proof (induction G T arbitrary: es thesis rule: replace_hp.induct[case_names Nil Cons])
  case (Nil G)
  moreover have "\<And>e. g2.vertices (H\<^sub>e e) \<noteq> {}"
    using vertices_of_He_non_empty by blast
  moreover hence "es = []"
    using Nil(6) by auto
  ultimately show ?case 
    by auto 
next
  case (Cons G x T)
  let ?h="\<lambda>y. \<not> are_vertices_in_He G x y"
  obtain e\<^sub>x where vert_x: "x \<in> g2.vertices (H\<^sub>e e\<^sub>x)"
    and ex_in_es: "e\<^sub>x \<in> set es" and ex_is_edge: "e\<^sub>x \<in> g1.uedges G"
    using Cons(4,7) by (fastforce simp del: He.simps f.simps)
  hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x" and "rep1 e\<^sub>x = e\<^sub>x"
    using invar_vertices_of_He vertices_of_He g1.rep_of_edge g2.set_specs by blast+
  then obtain u i where [simp]: "x = (e\<^sub>x,u,i)"
    by (elim isin_vertices_of_He_elim2) auto
  have "x \<in> g2.vertices (f G)"
    using "Cons.prems"(2) vert_x ex_is_edge vertices_f by auto
  hence "\<forall>y. are_vertices_in_He G x y \<longleftrightarrow> y \<in> g2.vertices (H\<^sub>e e\<^sub>x)"
    using "Cons.prems"(2) ex_is_edge vert_x are_vertices_in_He_intro are_vertices_in_He_elim2 by blast
  hence "set (filter ?h T) = set (x#T) - g2.vertices (H\<^sub>e e\<^sub>x)" (is "set ?fT = _")
    using vert_x by auto
  moreover have "set (x#T) =  g2.vertices (H\<^sub>e e\<^sub>x) \<union> \<Union> ((g2.vertices o H\<^sub>e) ` set (filter ((\<noteq>) e\<^sub>x) es))"
    using "Cons.prems"(6) ex_in_es by auto
  moreover have "\<forall>e \<in> set (filter ((\<noteq>) e\<^sub>x) es). g2.vertices (H\<^sub>e e\<^sub>x) \<inter> g2.vertices (H\<^sub>e e) = {}" (is "\<forall>_ \<in> set ?es'. _")
  proof
    fix e
    assume "e \<in> set ?es'"
    hence "rep1 e\<^sub>x \<noteq> rep1 e"
      using "Cons.prems"(5) ex_in_es by auto
    thus "g2.vertices (H\<^sub>e e\<^sub>x) \<inter> g2.vertices (H\<^sub>e e) = {}"
      using vertices_of_He_disjoint by auto
  qed
  ultimately have "set ?fT = \<Union> ((g2.vertices o H\<^sub>e) ` set ?es')"
    by auto
  moreover have "distinct ?es'"
    using "Cons.prems" by auto
  moreover have "\<forall>e \<in> set ?es'. rep1 e = e" "set ?es' \<subseteq> g1.uedges G"
    using "Cons.prems" by auto
  moreover have "length ?es' < length es"
    using ex_in_es by (simp add: length_filter_less)
  ultimately obtain xs where "set xs \<subseteq> set ?fT" "distinct xs" "length xs = length ?es'" 
    and "set ?es' = (\<lambda>(e,_,_). e) ` set xs" "set xs \<subseteq> g2.vertices (f G)"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
    and "replace_hp G ?fT = concat (map hp_starting_at xs)"
    using Cons by blast
  hence "replace_hp G (x#T) = concat (map hp_starting_at (x#xs))"
    using Cons by auto
  moreover have "set (x#xs) \<subseteq> set (x#T)"
    using \<open>set xs \<subseteq> set ?fT\<close> by auto
  moreover have "set (x#xs) \<subseteq> g2.vertices (f G)"
    using \<open>x \<in> g2.vertices (f G)\<close> \<open>set xs \<subseteq> g2.vertices (f G)\<close> by auto
  moreover have "distinct (x#xs)"
    using vert_x \<open>set ?fT = set (x#T) - g2.vertices (H\<^sub>e e\<^sub>x)\<close> \<open>distinct xs\<close> \<open>set xs \<subseteq> set ?fT\<close> by auto
  moreover have "length (x#xs) = length es"
    sorry
  moreover have "set es = (\<lambda>(e,_,_). e) ` set (x#xs)"
    sorry
  moreover have "\<And>y z. y \<in> set (x#xs) \<Longrightarrow> z \<in> set (x#xs) \<Longrightarrow> y \<noteq> z \<Longrightarrow> \<not> are_vertices_in_He G y z"
    sorry
  ultimately show ?case 
    using Cons by blast
qed

lemma filter_vertices_concat_hp:
  assumes "g1.ugraph_adj_map_invar G" and "set xs \<subseteq> g2.vertices (f G)" "\<And>y. y \<in> set xs \<Longrightarrow> \<not> are_vertices_in_He G x y"
  shows "filter (\<lambda>y. \<not> are_vertices_in_He G x y) (concat (map hp_starting_at xs)) = concat (map hp_starting_at xs)"
    (is "filter ?f _ = _")
  using assms
proof (induction xs)
  case (Cons y xs)
  hence "\<not> are_vertices_in_He G x y"
    by auto
  moreover obtain e where "e \<in> g1.uedges G" "y \<in> g2.vertices (H\<^sub>e e)"
    using Cons(2,3) vertices_f by auto
  moreover hence "\<And>z. z \<in> set (hp_starting_at y) \<Longrightarrow> are_vertices_in_He G z y"
    using assms(1) are_vertices_in_He set_hp_starting_at by blast
  ultimately have "\<And>z. z \<in> set (hp_starting_at y) \<Longrightarrow> \<not> are_vertices_in_He G x z"
    using assms are_vertices_in_He_trans by blast
  thus ?case 
    using Cons by auto
qed auto

lemma vc_of_tour_concat_hp:
  assumes "g1.ugraph_adj_map_invar G" 
    and "distinct xs" "set xs \<subseteq> g2.vertices (f G)" 
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
  shows "vc_of_tour G (concat (map hp_starting_at xs)) = g1.set_of_list (map (\<lambda>(_,u,_). u) (rev xs))"
  using assms
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then obtain e where vert_x: "x \<in> g2.vertices (H\<^sub>e e)" and edge_e: "e \<in> g1.uedges G"
    using vertices_f by auto
  hence "isin2 (V\<^sub>H\<^sub>e e) x"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  then obtain u v w i where "x = (uEdge u v,w,i)" "rep1 e = uEdge u v" "w \<in> {u,v}" "i \<in> {1..6}"
    by (elim isin_vertices_of_He_elim2)  
  moreover hence [simp]: "x = (e,w,i)"
    using edge_e by (auto simp add: g1.rep_of_edge)
  ultimately have "hd (hp_starting_at x) = (e,w,1)" 
    using hp_starting_at_non_nil hd_hp_starting_at g1.rep_simps by auto
  then obtain hp where hpx: "hp_starting_at x = (e,w,1)#hp" (is "_ = ?hdx#_")
    using hp_starting_at_non_nil by (cases "hp_starting_at x") auto

  have "\<And>y. y \<in> set (hp_starting_at x) \<Longrightarrow> are_vertices_in_He G x y"
    using assms(1) vert_x edge_e are_vertices_in_He set_hp_starting_at by blast
  moreover hence vert_hdxx: "are_vertices_in_He G ?hdx x"
    using hpx are_vertices_in_He_sym[OF Cons(2)] by (auto simp del: are_vertices_in_He.simps hp_starting_at.simps)
  ultimately have vert_hdxy: "\<And>y. y \<in> set (hp_starting_at x) \<Longrightarrow> are_vertices_in_He G ?hdx y"
    using Cons are_vertices_in_He_trans by blast

  have "\<And>y. y \<in> set xs \<Longrightarrow> x \<noteq> y"
    using Cons by auto
  hence "\<And>y. y \<in> set xs \<Longrightarrow> \<not> are_vertices_in_He G x y"
    using Cons by auto
  hence no_vert_hdxy: "\<And>y. y \<in> set xs \<Longrightarrow> \<not> are_vertices_in_He G ?hdx y"
    using Cons(2) vert_hdxx are_vertices_in_He_sym are_vertices_in_He_trans by blast

  let ?f="\<lambda>y. \<not> are_vertices_in_He G ?hdx y"

  have "vc_of_tour G (concat (map hp_starting_at (x#xs))) = vc_of_tour G (?hdx#hp @ concat (map hp_starting_at xs))"
    using hpx by auto
  also have "... = insert1 w (vc_of_tour G (filter ?f (concat (map hp_starting_at xs))))"
    using hpx vert_hdxy by auto
  also have "... = insert1 w (vc_of_tour G (concat (map hp_starting_at xs)))"
    using Cons no_vert_hdxy filter_vertices_concat_hp by auto
  also have "... = insert1 w (g1.set_of_list (map (\<lambda>(_,u,_). u) (rev xs)))"
    using Cons by auto
  also have "... = g1.set_of_list (map (\<lambda>(_,u,_). u) (rev (x#xs)))"
    by simp
  finally show ?case 
    by auto
qed

lemma concat_order_for_shorten_tour_and_g:
  assumes "g1.ugraph_adj_map_invar G" "card (g1.uedges G) > 1" and "g2.is_hc_Adj (f G) T"
  obtains xs where "xs \<noteq> []" "distinct xs" "g1.uedges G = (\<lambda>(e,_,_). e) ` set xs" 
    and "length xs = card (g1.uedges G)" "set xs \<subseteq> g2.vertices (f G)"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
    and "shorten_tour G T = last (hp_starting_at (last xs))#concat (map hp_starting_at xs)" 
    and "g G T = g1.set_of_list (map (\<lambda>(_,u,_). u) (rev xs))"
  using assms(1)
proof (rule fold4.fold_uedgesE)
  let ?fst3="\<lambda>(x,_,_). x"
  let ?snd3="\<lambda>(_,x,_). x"
  let ?f="\<lambda>(e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2). w\<^sub>1 \<noteq> w\<^sub>2 \<and> rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
  let ?T'="tl (rotate_tour ?f T)"

  have "g2.vertices (f G) = set (tl T)" and "hd T = last T"
    using assms by (auto elim: g2.is_hc_AdjE simp add: g2.hd_path_betw g2.last_path_betw)
  hence "g2.vertices (f G) = set ?T'"
    using set_tl_rotate_tour by auto
  moreover have "finite (g1.uedges G)"
    using assms by auto
  moreover hence "\<exists>e. e \<in> g1.uedges G"
    using assms(2) all_not_in_conv by fastforce
  moreover hence "\<exists>v. v \<in> g2.vertices (f G)"
    using assms vertices_f_non_empty by auto
  ultimately have "?T' \<noteq> []"
    by auto
  hence rhp_T'_non_nil: "replace_hp G ?T' \<noteq> []"
    using replace_hp_non_nil by auto

  fix es             
  assume dist_es: "distinct es" and set_es: "set es = g1.uedges G" 
  moreover have "set (tl T) = g2.vertices (f G)" and "hd T = last T"
    using assms by (auto elim!: g2.is_hc_AdjE simp add: g2.last_path_betw g2.hd_path_betw)
  moreover hence "set ?T' = g2.vertices (f G)"
    using set_tl_rotate_tour by auto
  moreover hence "set ?T' = \<Union> ((g2.vertices o H\<^sub>e) ` set es)"
    using assms vertices_f set_es by auto
  moreover have "\<forall>e \<in> set es. rep1 e = e"
    using calculation g1.rep_of_edge by auto
  ultimately obtain xs where dist_xs_subset: "distinct xs" "set xs \<subseteq> g2.vertices (f G)" 
    and len_xs_es_eq: "length xs = length es" and "set es = (\<lambda>(e,_,_). e) ` set xs" 
    and no_vert_xy: "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
    and "replace_hp G ?T' = concat (map hp_starting_at xs)"
    using assms(1) dist_es set_es 
    by (elim concat_order_for_replace_hp_and_vc_of_tour[where T="?T'"]) blast+ 
  moreover hence xs_non_nil_edges: "xs \<noteq> []" "g1.uedges G = ?fst3 ` set xs"
    using rhp_T'_non_nil set_es dist_es by (auto simp add: distinct_card[symmetric]) 
  moreover hence "last (concat (map hp_starting_at xs)) = last (hp_starting_at (last xs))"
    using hp_starting_at_non_nil by (auto simp add: last_concat_map)
  ultimately have st_concat: "shorten_tour G T = last (hp_starting_at (last xs))#concat (map hp_starting_at xs)" 
    by auto
  hence "g G T = vc_of_tour G (concat (map hp_starting_at xs))"
    by auto
  also have "... = g1.set_of_list (map ?snd3 (rev xs))"
    using assms(1) dist_xs_subset no_vert_xy vc_of_tour_concat_hp by auto
  finally have g_list: "g G T = g1.set_of_list (map ?snd3 (rev xs))"
    by auto

  have len_xs: "length xs = card (g1.uedges G)"
    using dist_es set_es len_xs_es_eq distinct_card by fastforce
  
  show ?thesis
    using that dist_xs_subset len_xs xs_non_nil_edges no_vert_xy st_concat g_list by auto
qed

lemma invar_vc_of_tour: "set_invar1 (vc_of_tour G T)"
  by (induction G T rule: vc_of_tour.induct) (auto simp add: g1.set_specs)
  
lemma invar_g: "set_invar1 (g G T)"
  using invar_vc_of_tour by auto

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

lemma c_geq0: "c G x y \<ge> 0"
  by (cases x; cases y) simp

lemma c_tri_inequality:
  assumes "g1.ugraph_adj_map_invar G" 
      and "x \<in> g2.vertices (f G)" "y \<in> g2.vertices (f G)" "z \<in> g2.vertices (f G)"
  shows "c G x z \<le> c G x y + c G y z"
  \<comment> \<open>The cost function \<open>c\<close> for the graph \<open>f G\<close> satisfies the triangle-inequality.\<close>
  sorry (* TODO *)

lemma g_is_vc:
  assumes "g1.ugraph_adj_map_invar G" "card (g1.uedges G) > 1" and "g2.is_hc_Adj (f G) T"
  shows "g1.is_vc_Adj G (g G T)"
  \<comment> \<open>The function \<open>g\<close> always computes a vertex cover of the graph \<open>G\<close> (feasible solution).\<close>
proof (intro g1.is_vc_AdjI)
  let ?snd3="\<lambda>(_,x,_). x"
  obtain xs where xs_non_nil: "xs \<noteq> []" "distinct xs" 
    and xs_edges: "g1.uedges G = (\<lambda>(e,_,_). e) ` set xs" 
    and xs_vert: "set xs \<subseteq> g2.vertices (f G)"
    and g_list: "g G T = g1.set_of_list (map ?snd3 (rev xs))"
    using assms by (elim concat_order_for_shorten_tour_and_g)

  show "\<And>u v. isin1 (\<N>\<^sub>1 G u) v \<Longrightarrow> isin1 (g G T) u \<or> isin1 (g G T) v"
  proof -
    fix u v
    assume "isin1 (\<N>\<^sub>1 G u) v"
    hence rep_e_isin: "rep1 (uEdge u v) \<in> g1.uedges G" (is "?e \<in> _")
      unfolding g1.uedges_def2 by auto
    then obtain w i where x_in_xs: "(?e,w,i) \<in> set xs" (is "?x \<in> _")
      using xs_edges by auto
    hence "?x \<in> g2.vertices (H\<^sub>e ?e)"
      using assms(1) xs_vert fst_of_vertex_is_edge by auto
    hence "isin2 (V\<^sub>H\<^sub>e ?e) ?x"
      using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
    hence "w \<in> {u,v}"
      using isin_vertices_of_He_iff by (auto simp add: g1.rep_idem)
    then consider "u \<in> set (map ?snd3 (rev xs))" | "v \<in> set (map ?snd3 (rev xs))"
      using x_in_xs by force
    thus "isin1 (g G T) u \<or> isin1 (g G T) v"
      using g_list g1.isin_set_of_list by auto
  qed
  
  show "\<And>v. isin1 (g G T) v \<Longrightarrow> v \<in> g1.vertices G"
  proof -
    fix v
    assume "isin1 (g G T) v"
    then obtain e i where x_in_xs: "(e,v,i) \<in> set xs" (is "?x \<in> _")
      using g_list xs_edges g1.isin_set_of_list by auto
    hence e_is_edge: "e \<in> g1.uedges G" and "?x \<in> g2.vertices (H\<^sub>e e)"
      using assms(1) xs_edges xs_vert fst_of_vertex_is_edge by blast+
    then obtain x y where "e = rep1 (uEdge x y)" and y_isin_Nx: "isin1 (\<N>\<^sub>1 G x) y" and "isin2 (V\<^sub>H\<^sub>e e) ?x"
      unfolding g1.uedges_def2 using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
    hence "v \<in> {x,y}"
      using isin_vertices_of_He_iff by (auto simp add: g1.rep_idem)
    then consider "v = x" | "v = y"
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
      by (intro vertices_of_He_disjoint)

    consider "rep1 (uEdge u x) = uEdge u x" "rep1 (uEdge u y) = uEdge u y" 
      | "rep1 (uEdge u x) = uEdge x u" "rep1 (uEdge u y) = uEdge u y" 
      | "rep1 (uEdge u x) = uEdge u x" "rep1 (uEdge u y) = uEdge y u" 
      | "rep1 (uEdge u x) = uEdge x u" "rep1 (uEdge u y) = uEdge y u" 
      using g1.is_rep by auto
    thus "set (?f x) \<inter> set (?f y) = {}"
      using assms neq vert_disj by cases (auto simp add: vertices_hp_u2[symmetric] vertices_hp_v2[symmetric] simp del: He.simps)
  qed
  ultimately have "distinct (concat (map ?f vs))"
    using assms(1) by (intro distinct_concat_map) 
  thus ?thesis
    using set_vs_fold by (auto simp: fold_concat_map)
qed

lemma set_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 P" 
      and "\<And>v. isin1 P v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  shows "List.set (hp_for_neighborhood u P) = \<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u v | v. isin1 P v})"
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
        by (auto simp add: vertices_hp_u2[symmetric] simp del: He.simps)
    next
      assume "rep1 (uEdge u x) = uEdge x u" "u \<noteq> x"
      thus ?thesis 
        by (auto simp add: vertices_hp_v2[symmetric] simp del: He.simps)
    qed
  qed
  have "List.set (concat (map ?f vs)) = \<Union> ((\<lambda>x. set (?f x)) ` (List.set vs))"
    apply (subst set_concat)
    apply (subst set_map) 
    apply blast
    done
  also have "... = \<Union> ((\<lambda>v. g2.vertices (H\<^sub>e (uEdge u v))) ` (List.set vs))"
    using hp_vert by auto
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

  have "List.set ?hp = \<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u v | v. isin1 P v})"
    using assms(1,2,4) by (rule set_hp_for_neighborhood)
  also have "... = \<Union> ((g2.vertices o H\<^sub>e) ` {rep1 (uEdge u v) | v. isin1 P v})"
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
abbreviation "card2 X \<equiv> int (card (set2 X))"

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
          using vertices_hp_u2[symmetric] by (auto simp del: He.simps)
      next
        case 2
        then show ?thesis    
          using vertices_hp_v2[symmetric] g1.rep_simps by (auto simp del: He.simps)
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
          using vertices_hp_u2[symmetric] by (auto simp del: He.simps)
      next
        case 2
        then show ?thesis    
          using vertices_hp_v2[symmetric] g1.rep_simps by (auto simp del: He.simps)
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

lemma hd_hp_of_vc:
  assumes "g1.ugraph_adj_map_invar G" and "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
      and "g1.is_vc_Adj G X" "set_invar1 X" 
  obtains u v where "isin1 X u" "rep1 (uEdge u v) \<in> g1.uedges G" 
    "hd (hp_of_vc G X) = (rep1 (uEdge u v),u,2)"
  using assms(4)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_vs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"

  have "\<exists>u v. u \<in> set1 X \<and> isin1 (\<P> G X u) v"
    using assms partition_by_vertex_cover by blast
  hence "\<exists>u x. u \<in> set1 X \<and> x \<in> \<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v})"
    using vertices_of_He_non_empty by fastforce
  hence "\<exists>u x. u \<in> set xs \<and> x \<in> \<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v})"
    using set_vs_fold by auto
  hence "\<exists>u x. u \<in> set xs \<and> x \<in> List.set (?f u)"
    using assms(1) invar_partition_for_vertex uedge_of_partition_for_vertex 
    by (auto simp add: set_hp_for_neighborhood simp del: hp_for_neighborhood.simps)
  hence v_with_non_empty_hp: "\<exists>v \<in> set xs. ?f v \<noteq> []" "xs \<noteq> []"
    by force+
  then obtain u where "u \<in> set xs" "?f u \<noteq> []" "hd (concat (map ?f xs)) = hd (?f u)"
    by (elim hd_concat_map_elim)
  moreover hence "\<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v}) \<noteq> {}"
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

lemma last_hp_of_vc:
  assumes "g1.ugraph_adj_map_invar G" and "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
      and "g1.is_vc_Adj G X" "set_invar1 X"
  obtains u v where "isin1 X u" "rep1 (uEdge u v) \<in> g1.uedges G" 
    "last (hp_of_vc G X) = (rep1 (uEdge u v),u,1)"
  using assms(4)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_vs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"

  have "\<exists>u v. u \<in> set1 X \<and> isin1 (\<P> G X u) v"
    using assms partition_by_vertex_cover by blast
  hence "\<exists>u x. u \<in> set1 X \<and> x \<in> \<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v})"
    using vertices_of_He_non_empty by fastforce
  hence "\<exists>u x. u \<in> set xs \<and> x \<in> \<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v})"
    using set_vs_fold by auto
  hence "\<exists>u x. u \<in> set xs \<and> x \<in> List.set (?f u)"
    using assms(1) invar_partition_for_vertex uedge_of_partition_for_vertex 
    by (auto simp add: set_hp_for_neighborhood simp del: hp_for_neighborhood.simps)
  hence v_with_non_empty_hp: "\<exists>v \<in> set xs. ?f v \<noteq> []" "xs \<noteq> []"
    by force+ (* TODO: unify with hd_hp_from_vc *)
  then obtain u where "u \<in> set xs" "?f u \<noteq> []" "last (concat (map ?f xs)) = last (?f u)"
    by (elim last_concat_map_elim)
  moreover hence "\<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u v |v. isin1 (\<P> G X u) v}) \<noteq> {}"
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
  have "\<And>v\<^sub>1 v\<^sub>2. isin1 P\<^sub>1 v\<^sub>1 \<Longrightarrow> isin1 P\<^sub>2 v\<^sub>2 \<Longrightarrow> g2.vertices (H\<^sub>e (uEdge u\<^sub>1 v\<^sub>1)) \<inter> g2.vertices (H\<^sub>e (uEdge u\<^sub>2 v\<^sub>2)) = {}"
    using assms g1.rep_eq_iff by (intro vertices_of_He_disjoint) blast
  thus ?thesis
    using assms by (auto simp add: set_hp_for_neighborhood simp del: vertices_of_He.simps hp_for_neighborhood.simps)
qed

lemma distinct_hp_of_vc:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X"
  shows "distinct (hp_of_vc G X)"
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

lemma set_hp_of_vc:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X"
  shows "List.set (hp_of_vc G X) = g2.vertices (f G)"
  using assms(3)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_vs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"

  have "\<And>u. u \<in> set1 X \<Longrightarrow> List.set (?f u) = \<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u v | v. isin1 (\<P> G X u) v})"
    using assms invar_partition_for_vertex uedge_of_partition_for_vertex
    by (intro set_hp_for_neighborhood) (auto simp add: g1.set_specs simp del: partition_for_vertex.simps)
  hence "List.set (hp_of_vc G X) = \<Union> ((\<lambda>u. \<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u v | v. isin1 (\<P> G X u) v})) ` (set1 X))"
    using set_vs_fold by (auto simp add: fold_concat_map)
  also have "... = \<Union> ((\<lambda>u. \<Union> ((g2.vertices o H\<^sub>e) ` {rep1 (uEdge u v) | v. isin1 (\<P> G X u) v})) ` (set1 X))"
    using vertices_of_He_rep_idem by fastforce
  also have "... = \<Union> ((g2.vertices o H\<^sub>e) ` ((\<Union>u\<in>set1 X. {rep1 (uEdge u v) | v. isin1 (\<P> G X u) v})))"
    by auto
  also have "... = \<Union> ((g2.vertices o H\<^sub>e) ` g1.uedges G)"
    using assms partition_by_vertex_cover by auto
  also have "... = g2.vertices (f G)"
    using assms vertices_f by auto
  finally show ?thesis
    by (auto simp add: fold_concat_map)
qed

lemma path_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" and "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
      and "g1.is_vc_Adj G X" "set_invar1 X" 
  obtains u\<^sub>1 v\<^sub>1 u\<^sub>2 v\<^sub>2 where "isin1 X u\<^sub>1" "isin1 X u\<^sub>2" 
      "rep1 (uEdge u\<^sub>1 v\<^sub>1) \<in> g1.uedges G" "rep1 (uEdge u\<^sub>2 v\<^sub>2) \<in> g1.uedges G" 
    "g2.path_betw (f G) (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2) (hp_of_vc G X) (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)" 
proof -   
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  obtain u\<^sub>1 v\<^sub>1 where uv1_isin: "isin1 X u\<^sub>1" "rep1 (uEdge u\<^sub>1 v\<^sub>1) \<in> g1.uedges G" 
    and "hd (hp_of_vc G X) = (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2)"
    using assms by (elim hd_hp_of_vc)    
  moreover obtain u\<^sub>2 v\<^sub>2 where uv2_isin: "isin1 X u\<^sub>2" "rep1 (uEdge u\<^sub>2 v\<^sub>2) \<in> g1.uedges G" 
    and "last (hp_of_vc G X) = (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)"
    using assms by (elim last_hp_of_vc)
  moreover have "List.set (hp_of_vc G X) = g2.vertices (f G)"
    using assms by (intro set_hp_of_vc)
  moreover hence "hp_of_vc G X \<noteq> []"
    using assms vertices_f_non_empty by (fastforce simp del: hp_of_vc.simps)
  ultimately have "g2.path_betw (f G) (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2) (hp_of_vc G X) (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)"
    apply (simp only: hp_of_vc.simps)
    apply (intro g2.path_betw_in_complete_graph)
    using assms f_is_complete distinct_distinct_adj[OF distinct_hp_of_vc] by auto
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
  hence "\<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u\<^sub>1 v |v. isin1 (\<P> G X u\<^sub>1) v}) \<noteq> {}"
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
    hence "\<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u\<^sub>2 v |v. isin1 (\<P> G X u\<^sub>2) v}) \<noteq> {}"
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

lemma cost_hp_of_vc:
  assumes "g1.ugraph_adj_map_invar G" "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
      and "g1.is_vc_Adj G X" "set_invar1 X"
  shows "cost_of_path (c G) (hp_of_vc G X) \<le> 15 * int (card (g1.uedges G)) + card1 X - 5"
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

(* fun hp_starting_at :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_starting_at (e,x,i) = (case rep1 e of uEdge u v \<Rightarrow>
    if x = v then hp_v1 (rep1 e) else hp_u1 (rep1 e))" *)

lemma cost_rotate_tour_eq:
  assumes "g1.ugraph_adj_map_invar G" and "g2.is_hc_Adj (f G) T"
  shows "cost_of_path (c G) (rotate_tour h T) = cost_of_path (c G) T"
  using assms c_sym
proof (intro cost_rotate_tour)
  show "hd T = last T"
    using assms by (elim g2.is_hc_AdjE) (auto simp add: g2.hd_path_betw g2.last_path_betw)
qed auto

lemma rotate_tour_hc_elim:
  defines "h \<equiv> \<lambda>(e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2). w\<^sub>1 \<noteq> w\<^sub>2 \<and> rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T"
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C" "card1 OPT\<^sub>V\<^sub>C > 1" \<comment> \<open>There has to be at least one edge with weight 5.\<close>
  obtains x y T' where "rotate_tour h T = x#y#T'" "\<not> are_vertices_in_He G x y" "c G x y = 5"
proof -
  have "length T > 2"
    sorry
  hence "length (rotate_tour h T) > 2"
    using length_rotate_tour by metis
  show ?thesis
    sorry
qed

lemma cost_x_y_4_or_5:
  defines "snd3 \<equiv> \<lambda>(_,v,_). v"
  assumes "g1.ugraph_adj_map_invar G"
      and "x \<in> g2.vertices (f G)" "y \<in> g2.vertices (f G)" "\<not> are_vertices_in_He G x y"
  obtains "snd3 x = snd3 y" "c G (last (hp_starting_at x)) (hd (hp_starting_at y)) = 4" 
  | "snd3 x \<noteq> snd3 y" "c G (last (hp_starting_at x)) (hd (hp_starting_at y)) = 5"
proof -
  obtain e\<^sub>x w\<^sub>x i\<^sub>x e\<^sub>y w\<^sub>y i\<^sub>y where [simp]: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)" and [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
    by (cases x; cases y)
  hence vert_x: "x \<in> g2.vertices (H\<^sub>e e\<^sub>x)" "e\<^sub>x \<in> g1.uedges G" 
    and vert_y: "y \<in> g2.vertices (H\<^sub>e e\<^sub>y)" "e\<^sub>y \<in> g1.uedges G"
    using assms fst_of_vertex_is_edge by auto
  hence rep_xy_neq: "rep1 e\<^sub>x \<noteq> rep1 e\<^sub>y" and rep_idem: "rep1 e\<^sub>x = e\<^sub>x" "rep1 e\<^sub>y = e\<^sub>y"
    using assms vertices_in_He_rep_iff g1.rep_of_edge by auto

  have "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x" and "isin2 (V\<^sub>H\<^sub>e e\<^sub>y) y"
    using vert_x vert_y invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  then obtain u\<^sub>x v\<^sub>x u\<^sub>y v\<^sub>y where "rep1 e\<^sub>x = uEdge u\<^sub>x v\<^sub>x" "w\<^sub>x \<in> {u\<^sub>x,v\<^sub>x}" and "rep1 e\<^sub>y = uEdge u\<^sub>y v\<^sub>y" "w\<^sub>y \<in> {u\<^sub>y,v\<^sub>y}"
    by (elim isin_vertices_of_He_elim2) auto
  hence last_x: "last (hp_starting_at x) = (e\<^sub>x,w\<^sub>x,2)" (is "_ = ?last") 
    and hd_y: "hd (hp_starting_at y) = (e\<^sub>y,w\<^sub>y,1)" (is "_ = ?hd") 
    using rep_idem last_hp_starting_at hd_hp_starting_at by auto
  moreover hence "?last \<in> g2.vertices (H\<^sub>e e\<^sub>x)" and "?hd \<in> g2.vertices (H\<^sub>e e\<^sub>y)"
    using assms vert_x vert_y hp_starting_at_non_nil set_hp_starting_at last_in_set hd_in_set by metis+
  ultimately have no_vert_hdx_lasty: "\<not> are_vertices_in_He G ?last ?hd"
    using assms vert_x vert_y rep_xy_neq vertices_in_He_rep_iff by auto
  hence no_edge_hdx_lasty: "\<not> is_edge_in_He G (uEdge ?last ?hd)"
    using assms edge_in_He_are_vertices by blast
  
  show ?thesis
  proof cases
    assume "snd3 x = snd3 y"
    moreover hence "c G ?last ?hd = 4"
      unfolding snd3_def using no_edge_hdx_lasty no_vert_hdx_lasty rep_xy_neq by auto
    ultimately show ?thesis
      using that last_x hd_y by auto
  next
    assume "snd3 x \<noteq> snd3 y"  
    moreover hence "c G ?last ?hd = 5"
      unfolding snd3_def using no_edge_hdx_lasty no_vert_hdx_lasty rep_xy_neq by auto
    ultimately show ?thesis
      using that last_x hd_y by auto
  qed
qed

lemma cost_concat_map:
  defines "snd3 \<equiv> \<lambda>(_,v,_). v"
  assumes "g1.ugraph_adj_map_invar G" and "distinct xs" "set xs \<subseteq> g2.vertices (f G)" 
      and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
 obtains k where "cost_of_path (\<lambda>x y. if snd3 x \<noteq> snd3 y then (1::nat) else 0) xs = k"
   and "cost_of_path (c G) (concat (map hp_starting_at xs)) = (\<Sum>x\<leftarrow>xs. cost_of_path (c G) (hp_starting_at x)) + (length (tl xs)) * 4 + k"
  using assms
proof (induction xs arbitrary: thesis rule: list012_induct)
  case Nil
  thus ?case by auto
next
  case (Singleton e)
  thus ?case by auto
next
  let ?c="\<lambda>x y. if snd3 x \<noteq> snd3 y then (1::nat) else 0"
  let ?sum="\<lambda>xs. \<Sum>x\<leftarrow>(xs). cost_of_path (c G) (hp_starting_at x)"
  case (CCons x y xs)
  then obtain k where cost_eq_k: "cost_of_path ?c (y#xs) = k"
    and cost_concat_eq: "cost_of_path (c G) (concat (map hp_starting_at (y#xs))) = ?sum (y#xs) + (length (tl (y#xs))) * 4 + k"
    by auto

  have no_vert_xy: "\<not> are_vertices_in_He G x y"
    using CCons by auto
  moreover have vert_x: "x \<in> g2.vertices (f G)" and vert_y: "y \<in> g2.vertices (f G)"
    using CCons by auto
  ultimately consider "snd3 x = snd3 y" "c G (last (hp_starting_at x)) (hd (concat (map hp_starting_at (y#xs)))) = 4" 
    | "snd3 x \<noteq> snd3 y" "c G (last (hp_starting_at x)) (hd (concat (map hp_starting_at (y#xs)))) = 5"
    unfolding snd3_def using assms(2) hp_starting_at_non_nil by (elim cost_x_y_4_or_5) auto
  thus ?case
  proof cases
    assume "snd3 x = snd3 y" "c G (last (hp_starting_at x)) (hd (concat (map hp_starting_at (y#xs)))) = 4"
    hence "cost_of_path ?c (x#y#xs) = k"
      and "cost_of_path (c G) (concat (map hp_starting_at (x#y#xs))) = ?sum (x#y#xs) + (length (tl (x#y#xs))) * 4 + k"
      using cost_concat_eq hp_starting_at_non_nil cost_eq_k by (auto simp add: cost_of_path_append2)
    thus ?thesis
      using CCons by auto
  next
    assume "snd3 x \<noteq> snd3 y" "c G (last (hp_starting_at x)) (hd (concat (map hp_starting_at (y#xs)))) = 5"
    hence "cost_of_path ?c (x#y#xs) = k + 1"
      and "cost_of_path (c G) (concat (map hp_starting_at (x#y#xs))) = ?sum (x#y#xs) + (length (tl (x#y#xs))) * 4 + k + 1"
      using cost_concat_eq hp_starting_at_non_nil cost_eq_k by (auto simp add: cost_of_path_append2)
    thus ?thesis
      using CCons by auto
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

lemma cost_shorten_tour_geq:
  assumes "g1.ugraph_adj_map_invar G" "card (g1.uedges G) > 1" 
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C" "card1 OPT\<^sub>V\<^sub>C > 1" \<comment> \<open>There has to be at least one edge with weight 5.\<close>
      and "g2.is_hc_Adj (f G) T"
  obtains k where "card1 (g G T) \<le> k" and "15 * int (card (g1.uedges G)) + k \<le> cost_of_path (c G) (shorten_tour G T)"
proof -
  let ?E="g1.uedges G"
  let ?fst3="\<lambda>(v,_,_). v"
  let ?snd3="\<lambda>(_,v,_). v"
  let ?c="\<lambda>x y. if ?snd3 x \<noteq> ?snd3 y then (1::nat) else 0"
  let ?neq="\<lambda>x y. if x \<noteq> y then (1::nat) else 0"

  obtain xs where xs_non_nil: "xs \<noteq> []" and dist_xs: "distinct xs" and len_xs: "length xs = card ?E"
    and xs_edges: "g1.uedges G = ?fst3 ` set xs" and xs_vert: "set xs \<subseteq> g2.vertices (f G)"
    and no_vert_xy: "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
    and sT_concat: "shorten_tour G T = last (hp_starting_at (last xs))#concat (map hp_starting_at xs)"    
    and g_list: "g G T = g1.set_of_list (map ?snd3 (rev xs))"
    using assms by (elim concat_order_for_shorten_tour_and_g) auto
  moreover hence "concat (map hp_starting_at xs) \<noteq> []"
    using hp_starting_at_non_nil by (cases xs) auto
  ultimately have cost_sT: "cost_of_path (c G) (shorten_tour G T) 
    = c G (last (hp_starting_at (last xs))) (hd (concat (map hp_starting_at xs))) + cost_of_path (c G) (concat (map hp_starting_at xs))"
    by (auto simp add: cost_of_path_cons)

  obtain k where cost_es_leq: "cost_of_path ?c xs = k"
    and "cost_of_path (c G) (concat (map hp_starting_at xs)) = (\<Sum>e\<leftarrow>xs. cost_of_path (c G) (hp_starting_at e)) + (length (tl xs)) * 4 + k"
    using assms dist_xs xs_vert no_vert_xy by (elim cost_concat_map)
  moreover have "(\<Sum>e\<leftarrow>xs. cost_of_path (c G) (hp_starting_at e)) = length xs * 11"
    using assms xs_vert cost_hp_starting_at2 by (intro sum_list_const) auto
  ultimately have "cost_of_path (c G) (concat (map hp_starting_at xs)) = length xs * 11 + (length (tl xs) + 1) * 4 + k - (4::int)"
    by auto
  also have "... = length xs * 11 + (length xs) * 4 + k - (4::int)"
    using xs_non_nil by auto
  finally have cost_concat: "cost_of_path (c G) (concat (map hp_starting_at xs)) = 15 * length xs + k - (4::int)"
    by auto

  have "set1 (g G T) = ?snd3 ` set xs"
    using g_list g1.set_of_list by auto
  hence [simp]: "card1 (g G T) = card (?snd3 ` set xs)"
    using assms by auto
  moreover have "card1 OPT\<^sub>V\<^sub>C \<le> card1 (g G T)"
    using assms g_is_vc by (auto elim!: g1.is_min_vc_AdjE)
  moreover hence "card1 (g G T) > 1"
    using assms by auto
  ultimately have "card (?snd3 ` set xs) > 1"
    by auto

  have "?neq (?snd3 (last xs)) (?snd3 (hd xs)) = ?c (last xs) (hd xs)"
    by auto
  moreover have "last (map ?snd3 xs) = ?snd3 (last xs)"
    using xs_non_nil by (intro last_map)
  moreover have "hd (map ?snd3 xs) = ?snd3 (hd xs)"
    using xs_non_nil by (intro hd_map)
  moreover have "cost_of_path ?neq (map ?snd3 xs) = cost_of_path ?c xs"
    by (induction xs rule: list012_induct) auto
  ultimately have cost_map_eq: "cost_of_path ?neq (map ?snd3 xs) + ?neq (last (map ?snd3 xs)) (hd (map ?snd3 xs)) = cost_of_path ?c xs + ?c (last xs) (hd xs)"
    by auto

  have "card (?snd3 ` set xs) = card (set (map ?snd3 xs))"
    by auto
  also have "... \<le> cost_of_path ?neq (map ?snd3 xs) + ?neq (last (map ?snd3 xs)) (hd (map ?snd3 xs))"
    using \<open>card (?snd3 ` set xs) > 1\<close> by (intro card_leq_cycle_cost_adj) auto
  also have "... = cost_of_path ?c xs + ?c (last xs) (hd xs)"
    using cost_map_eq by auto
  finally have card_es_leq: "card (?snd3 ` set xs) \<le> cost_of_path ?c xs + ?c (last xs) (hd xs)"
    by auto

  have len_xs_gr1: "length xs > 1"
    using assms len_xs by auto
  hence "length xs \<ge> 2"
    by auto
  then obtain x y ys where xs_split: "xs = x#ys @ [y]"
    by (elim list_len_geq2_split_hd_last)
  hence "y \<noteq> x"                  
    using dist_xs len_xs_gr1 distinct_hd_last_neq by fastforce
  hence no_vert_xy: "\<not> are_vertices_in_He G y x"
    using xs_non_nil no_vert_xy xs_split by auto                                             
  moreover have vert_x: "x \<in> g2.vertices (f G)" and vert_y: "y \<in> g2.vertices (f G)"
    using xs_non_nil xs_vert xs_split by auto
  ultimately consider "?snd3 (last xs) = ?snd3 (hd xs)" "c G (last (hp_starting_at (last xs))) (hd (concat (map hp_starting_at xs))) = 4" 
    | "?snd3 (last xs) \<noteq> ?snd3 (hd xs)" "c G (last (hp_starting_at (last xs))) (hd (concat (map hp_starting_at xs))) = 5"
    using assms(1) xs_split hp_starting_at_non_nil by (elim cost_x_y_4_or_5[of _ y x]) auto
  thus ?thesis
  proof cases
    assume "?snd3 (last xs) = ?snd3 (hd xs)" 
      and "c G (last (hp_starting_at (last xs))) (hd (concat (map hp_starting_at xs))) = 4" 
    hence "15 * int (card ?E) + k \<le> cost_of_path (c G) (shorten_tour G T)"
      using len_xs cost_concat cost_sT by auto
    moreover have "card1 (g G T) \<le> k"
      using \<open>?snd3 (last xs) = ?snd3 (hd xs)\<close> card_es_leq cost_es_leq by (auto simp del: g.simps)
    ultimately show ?thesis
      using that by blast
  next
    assume "?snd3 (last xs) \<noteq> ?snd3 (hd xs)"
      and "c G (last (hp_starting_at (last xs))) (hd (concat (map hp_starting_at xs))) = 5"
    hence "15 * int (card ?E) + k + 1 \<le> cost_of_path (c G) (shorten_tour G T)"
      using len_xs cost_concat cost_sT by auto
    moreover have "card1 (g G T) \<le> k + 1"
      using \<open>?snd3 (last xs) \<noteq> ?snd3 (hd xs)\<close> card_es_leq cost_es_leq by (auto simp del: g.simps)
    ultimately show ?thesis
      using that by auto
  qed
qed

lemma rotate_tour_is_hc:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" and "length T > 2"
  shows "g2.is_hc_Adj (f G) (rotate_tour h T)" (is "g2.is_hc_Adj (f G) ?T'")
proof (intro g2.is_hc_AdjI_compl_graph)
  show "g2.is_complete_Adj (f G)"
    using assms by (intro f_is_complete)

  show "length ?T' > 2"
    using assms length_rotate_tour by metis

  have hd_eq_last: "hd T = last T"
    using assms g2.path_non_empty by (auto elim!: g2.is_hc_AdjE simp add: g2.hd_path_betw g2.last_path_betw)
  thus "hd (rotate_tour h T) = last (rotate_tour h T)"
    using rotate_tour_hd_eq_last by auto

  have "g2.vertices (f G) = List.set (tl T)"
    using assms by (elim g2.is_hc_AdjE)
  thus  "g2.vertices (f G) = set (tl (rotate_tour h T))"
    using hd_eq_last set_tl_rotate_tour by auto

  have "distinct (tl T)"
    using assms by (elim g2.is_hc_AdjE)
  thus "distinct (tl (rotate_tour h T))"
    using hd_eq_last distinct_rotate_tour by auto
qed

(* lemma shorten_tour_is_hc:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) (x#y#T @ [x])" (is "g2.is_hc_Adj (f G) ?T") and "e \<in> g1.uedges G"
      and "isin2 (V\<^sub>H G) x" "\<not> isin2 (V\<^sub>H\<^sub>e e) x" "isin2 (V\<^sub>H\<^sub>e e) y" 
   shows "g2.is_hc_Adj (f G) (x#hp_starting_at y @ filter (Not o isin2 (V\<^sub>H\<^sub>e e)) (T @ [x]))" (is "g2.is_hc_Adj (f G) ?T'")
proof (intro g2.is_hc_AdjI)
  have hd_eq_last: "hd ?T = last ?T" and T_non_nil: "?T \<noteq> []"
    using g2.path_non_empty by (auto simp add: g2.hd_path_betw g2.last_path_betw)
  hence rotT_hd_last_eq: "hd ?T' = last ?T'"
    using rotate_tour_hd_eq_last by auto

  have "g2.vertices (f G) = set (tl ?T)"
    using assms by (elim g2.is_hc_AdjE)
  moreover hence "g2.vertices (f G) - set2 (V\<^sub>H\<^sub>e e) = set (filter (Not o isin2 (V\<^sub>H\<^sub>e e)) T @ [x])"
    using invar_vertices_of_He apply (auto simp add: g2.set_specs)
    sorry
  moreover have "set2 (V\<^sub>H\<^sub>e e) = set (hp_starting_at y)"
    using assms vertices_of_He hp_starting_at_set by auto
  ultimately show set_tl_rotT: "g2.vertices (f G) = set (tl ?T')"
    using assms vertices_f set_vertices_of_H by auto

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
qed *)

(* lemma shorten_tour_for_edge:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) (x#y#T @ [x])" (is "g2.is_hc_Adj (f G) ?T") and "e \<in> g1.uedges G"
      and "isin2 (V\<^sub>H G) x" "\<not> isin2 (V\<^sub>H\<^sub>e e) x" "isin2 (V\<^sub>H\<^sub>e e) y"
  shows "cost_of_path (c G) (x#hp_starting_at y @ filter (Not o isin2 (V\<^sub>H\<^sub>e e)) (T @ [x])) \<le> cost_of_path (c G) (x#y#T @ [x])"
  (is "cost_of_path (c G) (x#?hpy @ ?fT) \<le> cost_of_path (c G) ?T")
proof -
  have "y \<in> set2 (V\<^sub>H\<^sub>e e)"
    using assms invar_vertices_of_H invar_vertices_of_He by (auto simp add: g2.set_specs)
  hence y_is_vert: "isin2 (V\<^sub>H G) y"
    using assms invar_vertices_of_H set_vertices_of_H by (auto simp add: g2.set_specs)
  
  obtain e\<^sub>x where "e\<^sub>x \<in> g1.uedges G" "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x"
    using assms by (elim isin_vertices_of_H_obtain_edge)
  moreover hence "rep1 e\<^sub>x \<noteq> rep1 e"
    using assms isin_vertices_of_He_unique[OF \<open>isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x\<close>] by auto
  ultimately have x_y_no_vert: "\<not> are_vertices_in_He G x y"
    using assms vertices_in_He_rep_iff invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)

  obtain w i where "y = (rep1 e,w,i)"
    using assms by (elim isin_vertices_of_He_elim2) auto
  hence "cost_of_path (c G) ?hpy = 11"
    using assms g1.rep_of_edge_is_edge cost_hp_starting_at by simp
  hence "cost_of_path (c G) (x#?hpy @ ?fT) = c G x (hd ?hpy) + 11 + c G (last ?hpy) (hd ?fT) + cost_of_path (c G) ?fT"
    using assms hp_starting_at_non_nil by (auto simp add: cost_of_path_append cost_of_path_cons last_ConsR)
  also have "... \<le> c G x (hd ?hpy) + cost_of_path (c G) (y#T @ [x])"
    sorry
  also have "... \<le> c G x y + cost_of_path (c G) (y#T @ [x])"
    using assms y_is_vert x_y_no_vert cost_hd_hp_starting_at_leq by auto
  also have "... \<le> cost_of_path (c G) ?T"
    by auto
  finally show ?thesis 
    by auto
qed *)

lemma cost_path_geq_len:
  assumes "g1.ugraph_adj_map_invar G" "distinct_adj xs"
  shows "cost_of_path (c G) xs \<ge> int (length xs) - 1"
  using assms  
proof (induction xs rule: list012_induct)
  case (CCons x y xs)
  thus ?case 
    using c_geq1[of G x y] by auto
qed auto

lemma hp_geq_11:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" 
      and "distinct xs" "set xs = g2.vertices (H\<^sub>e e)"
  shows "cost_of_path (c G) xs \<ge> 11"
    using assms(1-2)
proof (rule g1.uedge_not_refl_elim)
  fix u v
  assume rep_e: "rep1 e = uEdge u v" "u \<noteq> v"
  have "length xs = card (g2.vertices (H\<^sub>e e))"
    using assms distinct_card by fastforce
  also have "... = card2 (V\<^sub>H\<^sub>e e)"
    using vertices_of_He by auto
  also have "... = 12"
    using rep_e g2.set_of_list by (auto simp del: g2.set_of_list.simps)
  finally have "length xs = 12"
    by auto
  thus ?thesis
    using assms cost_path_geq_len[OF assms(1) distinct_distinct_adj] by fastforce
qed

(* lemma cost_prepend_no_vertices_leq:
  assumes "g1.ugraph_adj_map_invar G" and "distinct_adj (x#xs)" "\<not> are_vertices_in_He G (last (x#xs)) y"
  shows "cost_of_path (c G) (y#ys) \<le> cost_of_path (c G) (x#xs @ y#ys) - int (length (x#xs)) - 3"
proof -
  have cost_last_y: "c G (last (x#xs)) y \<ge> 4" and cost_xs: "cost_of_path (c G) (x#xs) \<ge> int (length (x#xs)) - 1"
    using assms last_in_set cost_x_y_geq4 cost_path_geq_len[of _ "x#xs"] by auto

  have "cost_of_path (c G) (y#ys) = int (length (x#xs)) - 1 + 4 + cost_of_path (c G) (y#ys) - 3 - int (length (x#xs))"
    by auto
  also have "... \<le> cost_of_path (c G) (x#xs) + c G (last (x#xs)) y + cost_of_path (c G) (y#ys) - 3 - int (length (x#xs))"
    using cost_last_y cost_xs by auto
  also have "... = cost_of_path (c G) (x#xs @ y#ys) - length (x#xs) - 3"
    using Cons cost_of_path_append2[of "x#xs" "y#ys" "c G"] by auto
  finally show ?thesis 
    using Cons by auto 
qed *)

(* lemma cost_prepend_no_vertices_leq:
  assumes "g1.ugraph_adj_map_invar G" and "xs \<noteq> []" "ys \<noteq> []" "distinct_adj (xs @ ys)"
  shows "cost_of_path (c G) ys \<le> cost_of_path (c G) (xs @ ys) - int (length xs)"
  using assms
proof (cases xs; cases ys)
  fix x xs' y ys'
  assume [simp]: "xs = x#xs'" and [simp]: "ys = y#ys'"
  have cost_last_y: "c G (last xs) y \<ge> 1" and cost_xs: "cost_of_path (c G) xs \<ge> int (length xs) - 1"
    using assms distinct_adj_append_iff[of xs ys] c_geq1 cost_path_geq_len[of _ xs] by auto

  have "cost_of_path (c G) ys \<le> cost_of_path (c G) xs + c G (last xs) y + cost_of_path (c G) ys - int (length xs)"
    using cost_last_y cost_xs by auto
  also have "... = cost_of_path (c G) (xs @ ys) - length xs"
    using Cons cost_of_path_append2[of xs ys "c G"] by auto
  finally show ?thesis 
    using Cons by auto 
qed auto *)

lemma cost_hp_starting_at_append_leq:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" 
      and "set (x#xs) = g2.vertices (H\<^sub>e e)" "distinct (x#xs)"
      and "\<And>y. y \<in> set ys \<Longrightarrow> \<not> are_vertices_in_He G x y"
  shows "cost_of_path (c G) (hp_starting_at x @ ys) \<le> cost_of_path (c G) (x#xs @ ys)"
  using assms
proof (cases ys)
  case Nil
  hence "length (x#xs) = 12"
    using assms distinct_card
    sorry
  hence "cost_of_path (c G) (x#xs) \<ge> 11"
    sorry

  have "x \<in> g2.vertices (H\<^sub>e e)"
    sorry
  have "cost_of_path (c G) (hp_starting_at x) = 11"
    thm cost_hp_starting_at
    sorry

  thus ?thesis 
    sorry
next
  case (Cons y ys')
  then show ?thesis sorry
qed

lemma len_drop_drop_less: "length (dropWhile (Not o h) (dropWhile h xs)) < length xs + 1"
proof (induction xs)
  case (Cons x xs)
  then show ?case 
    using Cons
  proof cases
    assume "\<not> h x"
    hence "length (dropWhile (Not o h) (dropWhile h (x#xs))) \<le> length xs"
      using length_dropWhile_le by auto
    also have "... < length (x#xs) + 1"
      by auto
    finally show ?thesis
      by blast
  qed auto
qed auto

function dropWhile_schema where
  "dropWhile_schema h [] = []"
| "dropWhile_schema h (x#xs) = (if h x then dropWhile_schema h (dropWhile (Not o h) (dropWhile h xs)) else [])"
by pat_completeness auto
termination dropWhile_schema
  using len_drop_drop_less by (relation "measure (\<lambda>(h,xs). length xs)") auto

lemmas dropWhile_induct = dropWhile_schema.induct[case_names Nil DropWhile]

(* lemma
  fixes G x
  defines "h \<equiv> \<lambda>y. \<not> are_vertices_in_He G x y"
  assumes "g1.ugraph_adj_map_invar G" "distinct xs"
  obtains k where "cost_of_path (c G) (filter h xs) \<le> cost_of_path (c G) xs - int (length (filter (Not o h) xs)) + 1 - 2*k*4 + k*5"
  sorry *)

lemma cost_filter_leq_aux:
  fixes G x
  defines "h \<equiv> \<lambda>y. \<not> are_vertices_in_He G x y"
  assumes "g1.ugraph_adj_map_invar G" and "ys\<^sub>1 \<noteq> []" "xs\<^sub>1 \<noteq> []"
    and "distinct (ys\<^sub>1 @ xs\<^sub>1 @ ys\<^sub>2)" "set (ys\<^sub>1 @ xs\<^sub>1 @ ys\<^sub>2) \<subseteq> g2.vertices (f G)"
    and "\<And>z. z \<in> set ys\<^sub>1 \<Longrightarrow> h z" "\<And>z. z \<in> set xs\<^sub>1 \<Longrightarrow> \<not> h z" "ys\<^sub>2 \<noteq> [] \<Longrightarrow> h (hd ys\<^sub>2)"
  shows "cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1 @ ys\<^sub>2) \<ge> cost_of_path (c G) (filter h (ys\<^sub>1 @ xs\<^sub>1 @ ys\<^sub>2)) + length (filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1 @ ys\<^sub>2)) + 1"
  using assms
proof (induction h ys\<^sub>2 arbitrary: ys\<^sub>1 xs\<^sub>1 rule: dropWhile_induct)
  case Nil
  moreover hence "distinct_adj xs\<^sub>1"
    by (intro distinct_distinct_adj) auto
  ultimately have cost_xs_geq: "cost_of_path (c G) xs\<^sub>1 \<ge> int (length xs\<^sub>1) - 1"
    using assms cost_path_geq_len by blast 

  have "\<not> are_vertices_in_He G x (last ys\<^sub>1)"
    using Nil by auto
  moreover have "are_vertices_in_He G x (hd xs\<^sub>1)"
    using Nil by auto
  ultimately have "\<not> are_vertices_in_He G (hd xs\<^sub>1) (last ys\<^sub>1)"
    using Nil are_vertices_in_He_trans by blast
  hence c_last_xs_y: "c G (last ys\<^sub>1) (hd xs\<^sub>1) \<ge> 4"
    using Nil are_vertices_in_He_sym cost_x_y_geq4 by blast
  
  have "filter h (ys\<^sub>1 @ xs\<^sub>1) = ys\<^sub>1" and "filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1) = xs\<^sub>1"
    using Nil by (auto simp add: h_def simp del: are_vertices_in_He.simps) 
  hence "cost_of_path (c G) (filter h (ys\<^sub>1 @ xs\<^sub>1)) + length (filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1)) + 1 
    = cost_of_path (c G) ys\<^sub>1 + length xs\<^sub>1 + 1"
    by auto
  also have "... \<le> cost_of_path (c G) ys\<^sub>1 + cost_of_path (c G) xs\<^sub>1 + 4"
    using cost_xs_geq by auto
  also have "... \<le> cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) (hd xs\<^sub>1) + cost_of_path (c G) xs\<^sub>1"
    using c_last_xs_y by auto
  also have "... = cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1)"
    using Nil by (auto simp add: cost_of_path_append2[of ys\<^sub>1 xs\<^sub>1,symmetric])
  finally show ?case
    by (auto simp add: h_def)
next
  case (DropWhile y\<^sub>2 ys\<^sub>2)
  have "distinct_adj xs\<^sub>1"
    using DropWhile(5) by (intro distinct_distinct_adj) auto
  hence cost_xs_geq: "cost_of_path (c G) xs\<^sub>1 \<ge> int (length xs\<^sub>1) - 1"
    using assms cost_path_geq_len by blast 

  let ?ys\<^sub>2="takeWhile h ys\<^sub>2"      
  let ?xs\<^sub>2="takeWhile (Not o h) (dropWhile h ys\<^sub>2)"
  let ?ys\<^sub>3="dropWhile (Not o h) (dropWhile h ys\<^sub>2)"

  show ?case 
  proof (cases ?xs\<^sub>2)
    case Nil
    hence "\<And>z. z \<in> set ys\<^sub>2 \<Longrightarrow> h z"
      by (metis comp_eq_dest_lhs dropWhile_eq_Nil_conv hd_dropWhile takeWhile_eq_Nil_iff)
    hence "filter h (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2) = ys\<^sub>1 @ y\<^sub>2#ys\<^sub>2"
      sorry
    moreover have "filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2) = xs\<^sub>1"
      sorry
    ultimately have "cost_of_path (c G) (filter h (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2)) + length (filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1 @  y\<^sub>2#ys\<^sub>2)) + 1 
      = cost_of_path (c G) (ys\<^sub>1 @ y\<^sub>2#ys\<^sub>2) + length xs\<^sub>1 + 1"
      by auto
    also have "... \<le> cost_of_path (c G) (ys\<^sub>1 @ y\<^sub>2#ys\<^sub>2) + cost_of_path (c G) xs\<^sub>1 + 2"
      using cost_xs_geq by auto
    also have "... = cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) (hd (y\<^sub>2#ys\<^sub>2)) + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2) + cost_of_path (c G) xs\<^sub>1 + 2"
      using DropWhile(3) by (subst cost_of_path_append2[of ys\<^sub>1 "y\<^sub>2#ys\<^sub>2",symmetric]) auto
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + 5 + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2) + cost_of_path (c G) xs\<^sub>1 + 2"
      thm cost_x_y_leq5 (* Every edge has cost \<le> 5! *)
      sorry
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + 4 + cost_of_path (c G) xs\<^sub>1 + 4 + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2)"
      by auto
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) (hd xs\<^sub>1) + cost_of_path (c G) xs\<^sub>1 + c G (last xs\<^sub>1) (hd (y\<^sub>2#ys\<^sub>2)) + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2)"
      thm cost_x_y_geq4 
      sorry
    also have "... = cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1) + c G (last xs\<^sub>1) (hd (y\<^sub>2#ys\<^sub>2)) + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2)"
      using DropWhile(3,4) by (subst cost_of_path_append2[of ys\<^sub>1 xs\<^sub>1,symmetric]) auto
    also have "... = cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1) + c G (last (ys\<^sub>1 @ xs\<^sub>1)) (hd (y\<^sub>2#ys\<^sub>2)) + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2)"
      using DropWhile(4) by auto
    also have "... = cost_of_path (c G) ((ys\<^sub>1 @ xs\<^sub>1) @ y\<^sub>2#ys\<^sub>2)"
      using DropWhile(3,4) by (subst cost_of_path_append2[of "ys\<^sub>1 @ xs\<^sub>1",symmetric]) auto
    finally show ?thesis 
      by (auto simp add: h_def)
  next
    case (Cons x\<^sub>2 xs\<^sub>2)
    moreover hence "?xs\<^sub>2 \<noteq> []"
      by auto
    moreover have "y\<^sub>2#?ys\<^sub>2 \<noteq> []"
      by auto
    moreover have "h y\<^sub>2"
      sorry
    moreover have "distinct ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      using DropWhile(3) Cons
      sorry
    moreover have "set ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3) \<subseteq> g2.vertices (f G)"
      using DropWhile(4) Cons 
      sorry
    moreover have "\<And>z. z \<in> set (y\<^sub>2#?ys\<^sub>2) \<Longrightarrow> h z"
      using DropWhile(7) set_takeWhileD[of _ h ys\<^sub>1] sorry
    moreover have "\<And>z. z \<in> set ?xs\<^sub>2 \<Longrightarrow> \<not> h z"
      using Cons set_takeWhileD[of _ "Not o h" "dropWhile h ys\<^sub>2"] by auto
    moreover have "?ys\<^sub>3 \<noteq> [] \<Longrightarrow> h (hd ?ys\<^sub>3)"
      using hd_dropWhile[of "Not o h" "dropWhile h ys\<^sub>2"] by auto
    ultimately have cost_IH_geq: "cost_of_path (c G) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3) \<ge> 
      cost_of_path (c G) (filter h ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)) + length (filter (Not o h) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)) + 1"
      using DropWhile(2) h_def by (intro DropWhile(1)[folded h_def]) blast+

    have filter_h: "filter h (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2) = ys\<^sub>1 @ filter h ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      sorry

    have filter_noth: "filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2) = xs\<^sub>1 @ filter (Not o h) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      sorry

    have "cost_of_path (c G) (filter h (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2)) + length (filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2)) + 1 
      = cost_of_path (c G) (ys\<^sub>1 @ filter h ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)) + length (xs\<^sub>1 @ filter (Not o h) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)) + 1"
      by (simp only: filter_h filter_noth)
    also have "... = cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) y\<^sub>2 + cost_of_path (c G) (filter h ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3))
      + length xs\<^sub>1 + length (filter (Not o h) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)) + 1"
      thm cost_of_path_append2
      sorry
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) y\<^sub>2 + cost_of_path (c G) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3) + length xs\<^sub>1"
      using cost_IH_geq by auto
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + 5 + cost_of_path (c G) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3) + length xs\<^sub>1"
      thm cost_x_y_leq5 (* Every edge has cost \<le> 5! *)
      sorry

    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + 4 + length xs\<^sub>1 - 1 + 4 + cost_of_path (c G) (y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      by auto
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + 4 + cost_of_path (c G) xs\<^sub>1 + 4 + cost_of_path (c G) (y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      thm cost_path_geq_len
      sorry
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) (hd xs\<^sub>1) + cost_of_path (c G) xs\<^sub>1 + c G (last xs\<^sub>1) (hd (y\<^sub>2#?ys\<^sub>2)) + cost_of_path (c G) (y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      thm cost_x_y_geq4 
      sorry
    also have "... \<le> cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1) + c G (last xs\<^sub>1) (hd (y\<^sub>2#?ys\<^sub>2)) + cost_of_path (c G) (y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      using DropWhile(3,4) by (auto simp add: cost_of_path_append2[of ys\<^sub>1 xs\<^sub>1,symmetric])
    also have "... \<le> cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      using DropWhile(3,4) cost_of_path_append2[of "ys\<^sub>1 @ xs\<^sub>1" "y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3",symmetric]
      sorry
    also have "... \<le> cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2)"
      by auto

    finally show ?thesis 
      by (auto simp add: h_def)
  qed
qed

lemma cost_filter_leq:
  fixes G x
  defines "h \<equiv> \<lambda>y. \<not> are_vertices_in_He G x y"
  assumes "g1.ugraph_adj_map_invar G" 
    and "distinct ys" "set ys \<subseteq> g2.vertices (f G)" and "\<exists>x \<in> set ys. \<not> h x" "h (hd ys)"
  shows "cost_of_path (c G) ys \<ge> cost_of_path (c G) (filter h ys) + length (filter (Not o h) ys) + 1"
proof -
  let ?ys\<^sub>1="takeWhile h ys"
  let ?xs\<^sub>1="takeWhile (Not o h) (dropWhile h ys)"
  let ?ys\<^sub>2="dropWhile (Not o h) (dropWhile h ys)"

  have "?ys\<^sub>1 \<noteq> []"
    using assms by (auto simp add: takeWhile_eq_Nil_iff) 
  moreover have "?xs\<^sub>1 \<noteq> []"
    using assms(5) by (induction ys) auto
  moreover have "distinct (?ys\<^sub>1 @ ?xs\<^sub>1 @ ?ys\<^sub>2)" 
    using assms by auto
  moreover have "set (?ys\<^sub>1 @ ?xs\<^sub>1 @ ?ys\<^sub>2) \<subseteq> g2.vertices (f G)"
    using assms by auto
  moreover have "\<And>z. z \<in> set ?ys\<^sub>1 \<Longrightarrow> h z"
    using set_takeWhileD[of _ h] by auto
  moreover have "\<And>z. z \<in> set ?xs\<^sub>1 \<Longrightarrow> \<not> h z" 
    using set_takeWhileD[of _ "Not o h"] by auto
  moreover have "?ys\<^sub>2 \<noteq> [] \<Longrightarrow> h (hd ?ys\<^sub>2)"
    using hd_dropWhile[of "Not o h"] by auto
  ultimately have "cost_of_path (c G) (?ys\<^sub>1 @ ?xs\<^sub>1 @ ?ys\<^sub>2) \<ge> cost_of_path (c G) (filter h (?ys\<^sub>1 @ ?xs\<^sub>1 @ ?ys\<^sub>2)) + length (filter (Not o h) (?ys\<^sub>1 @ ?xs\<^sub>1 @ ?ys\<^sub>2)) + 1"
    unfolding h_def using assms(2) by (intro cost_filter_leq_aux)
  thus ?thesis
    by auto
qed

lemma cost_replace_hp_step_leq:
  fixes G x
  defines "h \<equiv> \<lambda>y. \<not> are_vertices_in_He G x y"
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" and "x \<in> g2.vertices (H\<^sub>e e)"
      and "distinct (x#T)" "set (x#T) \<subseteq> g2.vertices (f G)" "g2.vertices (H\<^sub>e e) \<subseteq> set (x#T)"
  shows "cost_of_path (c G) (hp_starting_at x @ filter h T) \<le> cost_of_path (c G) (x#T)"
proof -
  let ?xs="takeWhile (Not o h) T"
  let ?ys="dropWhile (Not o h) T"
  have T_split: "T = ?xs @ ?ys"
    by auto
  have set_xs_subset: "set (x#?xs) \<subseteq> g2.vertices (H\<^sub>e e)"
  proof
    fix y
    assume "y \<in> set (x#?xs)"
    moreover have "\<And>y. y \<in> set ?xs \<Longrightarrow> \<not> h y"
      using set_takeWhileD[of _ "Not o h" T] by auto
    moreover have "are_vertices_in_He G x x"
      using assms are_vertices_in_He_refl by auto
    ultimately have "are_vertices_in_He G x y"
      unfolding h_def by (cases "y = x") auto
    thus "y \<in> g2.vertices (H\<^sub>e e)"
      using assms are_vertices_in_He_elim2 by auto
  qed

  show ?thesis
  proof cases
    assume "g2.vertices (H\<^sub>e e) \<subseteq> set (x#?xs)"
    hence set_xs: "set (x#?xs) = g2.vertices (H\<^sub>e e)"
      using set_xs_subset by auto
    moreover have "\<And>y. \<not> h y \<Longrightarrow> y \<in> g2.vertices (H\<^sub>e e)"
      unfolding h_def using assms are_vertices_in_He_elim2 by blast
    ultimately have "\<And>y. y \<notin> set (x#?xs) \<Longrightarrow> h y"
      by auto
    moreover have "\<And>y. y \<in> set ?ys \<Longrightarrow> y \<notin> set (x#?xs)" 
      using assms(5) distinct_append[of "x#?xs" ?ys] by auto 
    ultimately have ys_h: "\<And>y. y \<in> set ?ys \<Longrightarrow> h y" 
      by auto 
    hence "filter h ?ys = ?ys"
      by auto
    hence filter_T_eq_ys: "filter h T = ?ys"
      by (induction T) auto

    have "x \<notin> set ?xs" and "distinct T"
      using assms set_takeWhileD[of x] by auto
    moreover hence "distinct (x#?xs)"
      using assms distinct_takeWhile by auto
    moreover have no_vert_ys: "\<And>y. y \<in> set ?ys \<Longrightarrow> \<not> are_vertices_in_He G x y" 
      using ys_h by (auto simp add: h_def)
    ultimately have "cost_of_path (c G) (hp_starting_at x @ ?ys) \<le> cost_of_path (c G) (x#?xs @ ?ys)"
      using assms set_xs by (intro cost_hp_starting_at_append_leq)
    also have "... = cost_of_path (c G) (x#T)"
      using T_split by auto
    finally have "cost_of_path (c G) (hp_starting_at x @ ?ys) \<le> cost_of_path (c G) (x#T)"
      by auto
    thus ?thesis
      using filter_T_eq_ys by auto
  next
    assume vert_no_subset_ys: "\<not> g2.vertices (H\<^sub>e e) \<subseteq> set (x#?xs)"
    hence "\<exists>z \<in> set T. z \<notin> set (x#?xs)"
      using assms by auto
    hence ys_non_nil: "?ys \<noteq> []"
      by (induction T) auto
    then obtain y ys where ys: "?ys = y#ys"
      by (cases ?ys) auto
    hence filter_T: "filter h T = y#filter h ys"
      by (induction T) auto
    hence no_vert_x_y: "\<not> are_vertices_in_He G x y"
      unfolding h_def by (metis Cons_eq_filterD)
    moreover have "are_vertices_in_He G x (last (x#?xs))"
      using assms set_xs_subset by (intro are_vertices_in_He_intro) auto
    ultimately have no_vert_last_xs_y: "\<not> are_vertices_in_He G (last (x#?xs)) y"
      using assms are_vertices_in_He_trans by blast

    have "set (hp_starting_at x) = g2.vertices (H\<^sub>e e)"
      using assms set_hp_starting_at by auto
    hence "last (hp_starting_at x) \<in> g2.vertices (H\<^sub>e e)"
      using hp_starting_at_non_nil last_in_set by blast
    hence "are_vertices_in_He G x (last (hp_starting_at x))"
      using assms by (intro are_vertices_in_He_intro) auto
    hence no_vert_lasthpx_y: "\<not> are_vertices_in_He G (last (hp_starting_at x)) y"
      using assms no_vert_x_y are_vertices_in_He_trans by blast

    have "x \<notin> set T"
      using assms by auto
    hence "x \<notin> set ?xs"
      by (induction T) auto
    moreover have "distinct ?xs"
      using assms by auto
    ultimately have "distinct (x#?xs)"
      by auto
    hence dist_adj_xs: "distinct_adj (x#?xs)"
      using distinct_distinct_adj by blast

    have vert_noth_iff: "\<And>y. y \<in> g2.vertices (H\<^sub>e e) \<longleftrightarrow> \<not> h y"
      unfolding h_def using assms are_vertices_in_He_intro are_vertices_in_He_elim2 by blast
    moreover hence "set (filter (Not o h) (x#T)) \<subseteq> g2.vertices (H\<^sub>e e)"
      by auto
    moreover have "\<And>y. y \<in> g2.vertices (H\<^sub>e e) \<Longrightarrow> y \<in> set (x#T)"
      using assms by auto
    ultimately have "g2.vertices (H\<^sub>e e) = set (filter (Not o h) (x#T))"
      by fastforce
    moreover have "distinct (filter (Not o h) (x#T))"
      using assms by auto
    moreover have "card (g2.vertices (H\<^sub>e e)) = 12"
      using assms card_vertices_of_He by auto
    ultimately have "length (filter (Not o h) (x#T)) = 12"
      using distinct_card by metis
    moreover have "filter (Not o h) T = ?xs @ filter (Not o h) ?ys"
      by (induction T) auto
    ultimately have len_xs: "length (x#?xs) = 12 - int (length (filter (Not o h) ?ys))"
      using assms are_vertices_in_He_refl by (auto simp add: h_def)

    have "distinct ?ys"
      using assms by auto
    moreover have "set ?ys \<subseteq> g2.vertices (f G)"
      using assms set_dropWhileD[of _ "Not o h" T] by auto
    moreover have "set (x#T) = set (x#?xs) \<union> set ?ys"
      using T_split by (metis Cons_eq_appendI set_append)
    moreover hence "g2.vertices (H\<^sub>e e) \<inter> set ?ys \<noteq> {}"
      using assms(7) vert_no_subset_ys by auto
    moreover hence "\<exists>x \<in> set ?ys. \<not> h x"
      using vert_noth_iff by blast
    moreover have hd_ys: "h (hd ?ys)"
      using ys_non_nil hd_dropWhile[of "Not o h"] by auto
    ultimately have "cost_of_path (c G) ?ys \<ge> cost_of_path (c G) (filter h ?ys) + int (length (filter (Not o h) ?ys)) + 1"
      using assms(2) unfolding h_def by (intro cost_filter_leq)
    hence cost_yfilter_ys: "cost_of_path (c G) (y#filter h ys) \<le> cost_of_path (c G) ?ys - int (length (filter (Not o h) ?ys)) - 1"
      using ys hd_ys by auto

    have "cost_of_path (c G) (hp_starting_at x @ filter h T) = cost_of_path (c G) (hp_starting_at x @ y#filter h ys)"
      using filter_T by auto
    also have "... = cost_of_path (c G) (hp_starting_at x) + c G (last (hp_starting_at x)) y + cost_of_path (c G) (y#filter h ys)"
      using hp_starting_at_non_nil by (auto simp add: cost_of_path_append2)
    also have "... = 11 + c G (last (hp_starting_at x)) y + cost_of_path (c G) (y#filter h ys)"
      using assms vertices_f cost_hp_starting_at2[of _ x] by auto 
    also have "... \<le> 11 + 5 + cost_of_path (c G) (y#filter h ys)"
      using assms no_vert_lasthpx_y cost_x_y_leq5 by auto
    also have "... \<le> 11 + 5 + cost_of_path (c G) ?ys - int (length (filter (Not o h) ?ys)) - 1"
      using cost_yfilter_ys by auto
    also have "... = 11 + 4 + cost_of_path (c G) ?ys - int (length (filter (Not o h) ?ys))"
      by auto
    also have "... \<le> 12 - int (length (filter (Not o h) ?ys)) - 1 + 4 + cost_of_path (c G) ?ys"
      by auto
    also have "... = length (x#?xs) - 1 + 4 + cost_of_path (c G) ?ys"
      using len_xs by auto
    also have "... \<le> cost_of_path (c G) (x#?xs) + 4 + cost_of_path (c G) ?ys"
      using assms dist_adj_xs cost_path_geq_len[of _ "x#?xs"] by auto
    also have "... \<le> cost_of_path (c G) (x#?xs) + c G (last (x#?xs)) y + cost_of_path (c G) ?ys"
      using assms no_vert_last_xs_y cost_x_y_geq4 by auto
    also have "... \<le> cost_of_path (c G) (x#?xs) + c G (last (x#?xs)) y + cost_of_path (c G) (y#ys)"
      using ys by auto
    also have "... = cost_of_path (c G) ((x#?xs) @ (y#ys))"
      by (subst cost_of_path_append2) auto
    also have "... = cost_of_path (c G) (x#?xs @ ?ys)"
      using ys by auto
    also have "... = cost_of_path (c G) (x#T)"
      by auto
    finally show ?thesis
      by auto
  qed
qed

lemma replace_hp_tour_leq:
  assumes "g1.ugraph_adj_map_invar G" 
      and "distinct T" "set T \<subseteq> g2.vertices (f G)" 
      and "\<exists>es. set es \<subseteq> g1.uedges G \<and> set T = \<Union> ((g2.vertices \<circ> H\<^sub>e) ` set es)"
  shows "cost_of_path (c G) (replace_hp G T) \<le> cost_of_path (c G) T"
  using assms
proof (induction G T rule: replace_hp.induct[case_names Nil Cons])
  case (Nil G)
  thus ?case by auto
next
  case Cons_T: (Cons G x T)
  let ?h="\<lambda>y. \<not> are_vertices_in_He G x y"
  let ?fT="filter ?h T"

  obtain es where edges_es: "set es \<subseteq> g1.uedges G" and set_xT: "set (x#T) = \<Union> ((g2.vertices \<circ> H\<^sub>e) ` set es)"
    using Cons_T(5) by auto
  then obtain e where e_in_es: "e \<in> set es" and edge_e: "e \<in> g1.uedges G" and vert_x_He: "x \<in> g2.vertices (H\<^sub>e e)"
    by fastforce
  hence "\<And>y. ?h y \<longleftrightarrow> y \<notin> g2.vertices (H\<^sub>e e)"
    using Cons_T(2) vert_x_He are_vertices_in_He_intro are_vertices_in_He_elim2 by blast
  hence "set ?fT = set (x#T) - g2.vertices (H\<^sub>e e)"
    using vert_x_He by auto
  moreover have "set (x#T) =  g2.vertices (H\<^sub>e e) \<union> \<Union> ((g2.vertices o H\<^sub>e) ` set (filter ((\<noteq>) e) es))"
    using set_xT e_in_es by auto
  moreover have "\<forall>e' \<in> set (filter ((\<noteq>) e) es). g2.vertices (H\<^sub>e e') \<inter> g2.vertices (H\<^sub>e e) = {}" (is "\<forall>_ \<in> set ?es'. _")
  proof
    fix e'
    assume "e' \<in> set ?es'"
    hence "e' \<noteq> e" and "rep1 e' = e'" "rep1 e = e"
      using edges_es e_in_es by (auto simp add: g1.rep_of_edge)
    hence "rep1 e' \<noteq> rep1 e"
      by auto
    thus "g2.vertices (H\<^sub>e e') \<inter> g2.vertices (H\<^sub>e e) = {}"
      using vertices_of_He_disjoint by auto
  qed
  ultimately have "set ?fT = \<Union> ((g2.vertices o H\<^sub>e) ` set ?es')"
    by auto
  hence "\<exists>es. set es \<subseteq> g1.uedges G \<and> set ?fT = \<Union> ((g2.vertices \<circ> H\<^sub>e) ` set es)"
    using edges_es filter_is_subset[of "(\<noteq>) e" es] by blast
  moreover have "distinct ?fT"
    using Cons_T by auto
  moreover have "set ?fT \<subseteq> g2.vertices (f G)"
    using Cons_T filter_is_subset[of ?h T] by auto
  ultimately have cost_IH_leq: "cost_of_path (c G) (replace_hp G ?fT) \<le> cost_of_path (c G) ?fT"
    using Cons_T(2) by (intro Cons_T(1))

  have "g2.vertices (H\<^sub>e e) \<subseteq> set (x#T)"
    using set_xT e_in_es by auto
  hence cost_hpx_filter_leq: "cost_of_path (c G) (hp_starting_at x @ ?fT) \<le> cost_of_path (c G) (x#T)"
    using Cons_T(2-4) edge_e vert_x_He by (intro cost_replace_hp_step_leq)

  show ?case
  proof (cases ?fT)
    case Nil
    thus ?thesis 
      using cost_hpx_filter_leq by auto
  next
    case Cons_fT: (Cons y fT)
    moreover have "set ?fT \<subseteq> set T"
      by auto 
    ultimately have "y \<in> set ?fT"
      by auto
    hence "x \<in> g2.vertices (f G)" "y \<in> g2.vertices (f G)"
      using Cons_T by auto
    moreover have "\<not> are_vertices_in_He G x y"
      using Cons_eq_filterD[OF Cons_fT[symmetric]] by auto
    ultimately have c_lastx_hdy_leq: "c G (last (hp_starting_at x)) (hd (hp_starting_at y)) \<le> c G (last (hp_starting_at x)) y"
      using Cons_T(2) by (intro cost_last_hp_x_hd_hp_y_leq)

    have "cost_of_path (c G) (replace_hp G (x#T)) = cost_of_path (c G) (hp_starting_at x @ replace_hp G ?fT)"
      by auto
    also have "... = cost_of_path (c G) (hp_starting_at x) + c G (last (hp_starting_at x)) (hd (hp_starting_at y)) + cost_of_path (c G) (replace_hp G ?fT)"
      using Cons_fT hp_starting_at_non_nil replace_hp_Cons_non_nil by (simp add: cost_of_path_append2)
    also have "... \<le> cost_of_path (c G) (hp_starting_at x) + c G (last (hp_starting_at x)) y + cost_of_path (c G) (replace_hp G ?fT)"
      using c_lastx_hdy_leq by auto
    also have "... \<le> cost_of_path (c G) (hp_starting_at x) + c G (last (hp_starting_at x)) y + cost_of_path (c G) ?fT"
      using cost_IH_leq by auto
    also have "... = cost_of_path (c G) (hp_starting_at x @ y#fT)"
      using Cons_fT hp_starting_at_non_nil by (simp add: cost_of_path_append2)
    also have "... \<le> cost_of_path (c G) (x#T)"
      using Cons_fT cost_hpx_filter_leq by auto
    finally show ?thesis
      by auto
  qed
qed

lemma cost_shorten_tour_leq:
  assumes "g1.ugraph_adj_map_invar G" "card (g1.uedges G) > 1" "g2.is_hc_Adj (f G) T" 
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C" "card1 OPT\<^sub>V\<^sub>C > 1" \<comment> \<open>There has to be at least one edge with weight 5.\<close>
  shows "cost_of_path (c G) (shorten_tour G T) \<le> cost_of_path (c G) T"
  using assms
proof -
  let ?f="\<lambda>(e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2). w\<^sub>1 \<noteq> w\<^sub>2 \<and> rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
  let ?T'="rotate_tour ?f T"

  have "finite (g1.uedges G)"
    using assms by auto
  hence edge_exists: "\<exists>e. e \<in> g1.uedges G"
    using assms(2) all_not_in_conv by fastforce

  have hdT_eq_lastT: "hd T = last T"
    using assms by (auto elim: g2.is_hc_AdjE simp add: g2.hd_path_betw g2.last_path_betw)

  obtain x y T' where T'_CCons: "?T' = x#y#T'" and "\<not> are_vertices_in_He G x y" and c_xy: "c G x y = 5"
    using assms by (elim rotate_tour_hc_elim)

  have "\<not> are_vertices_in_He G (last (replace_hp G (tl ?T'))) (hd (replace_hp G (tl ?T')))" 
    (is "\<not> are_vertices_in_He G ?last ?hd")
    sorry
  hence c_last_hd: "c G ?last ?hd \<le> 5"
    using assms cost_x_y_leq5 by auto

  have "length T > 2"
    sorry
  hence hc_T': "g2.is_hc_Adj (f G) ?T'"
    using assms rotate_tour_is_hc by auto
  hence set_tlT': "g2.vertices (f G) = set (tl ?T')"
    by (elim g2.is_hc_AdjE)
  moreover have "\<exists>v. v \<in> g2.vertices (f G)"
    using assms edge_exists vertices_f_non_empty by auto
  ultimately have "tl ?T' \<noteq> []"
    by auto
  hence rhp_tlT_non_nil: "replace_hp G (tl ?T') \<noteq> []"
    using replace_hp_non_nil by auto

  have "distinct (tl ?T')"
    using hc_T' by (elim g2.is_hc_AdjE)
  moreover have "\<exists>es. set es \<subseteq> g1.uedges G \<and> set (tl ?T') = \<Union> ((g2.vertices \<circ> H\<^sub>e) ` set es)"
    using assms(1)
  proof (rule fold1.fold_uedgesE)
    fix es
    assume "set es = g1.uedges G"
    moreover hence "set (tl ?T') = \<Union> ((g2.vertices \<circ> H\<^sub>e) ` set es)"
      using assms(1) set_tlT' vertices_f by auto
    ultimately show ?thesis
      by auto
  qed
  ultimately have cost_rph: "cost_of_path (c G) (replace_hp G (tl ?T')) \<le> cost_of_path (c G) (tl ?T')"
    using assms(1) set_tlT' by (intro replace_hp_tour_leq) auto

  have "cost_of_path (c G) (shorten_tour G T) = cost_of_path (c G) (last (replace_hp G (tl ?T'))#replace_hp G (tl ?T'))"
    by (auto simp add: Let_def)
  also have "... = c G ?last ?hd + cost_of_path (c G) (replace_hp G (tl ?T'))"
    using rhp_tlT_non_nil by (auto simp add: cost_of_path_cons)
  also have "... \<le> c G ?last ?hd + cost_of_path (c G) (tl ?T')"
    using cost_rph by auto
  also have "... \<le> c G x y + cost_of_path (c G) (tl ?T')"
    using c_xy c_last_hd by auto
  also have "... = cost_of_path (c G) ?T'"
    using T'_CCons by auto
  also have "... = cost_of_path (c G) T"
    using assms cost_rotate_tour[OF hdT_eq_lastT c_sym] by auto
  finally show ?thesis
    by auto
qed

end

section \<open>Reduction Proof\<close>

context VC4_To_mTSP
begin

lemma hp_of_vc:
  assumes "g1.ugraph_adj_map_invar G" and "card (g1.uedges G) > 1" "card1 X > 1"
      and "g1.is_vc_Adj G X" "set_invar1 X"
  obtains T where "g2.is_hc_Adj (f G) T" "cost_of_path (c G) T \<le> 15 * int (card (g1.uedges G)) + card1 X"
proof -
  have "finite (g1.uedges G)"
    using assms by auto
  hence edge_exists: "\<exists>e. e \<in> g1.uedges G"
    using assms(2) all_not_in_conv by fastforce

  have distinct: "distinct (hp_of_vc G X)" 
    using assms(1,4,5) by (rule distinct_hp_of_vc)
  moreover have set: "List.set (hp_of_vc G X) = g2.vertices (f G)"
    using assms(1,4,5) by (rule set_hp_of_vc)
  moreover obtain u\<^sub>1 v\<^sub>1 u\<^sub>2 v\<^sub>2 where uv12_isin: "isin1 X u\<^sub>1" "isin1 X u\<^sub>2" "rep1 (uEdge u\<^sub>1 v\<^sub>1) \<in> g1.uedges G" 
    "rep1 (uEdge u\<^sub>2 v\<^sub>2) \<in> g1.uedges G" and
    path: "g2.path_betw (f G) (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2) (hp_of_vc G X) (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)" 
      (is "g2.path_betw (f G) ?u\<^sub>2 _ ?u\<^sub>1")
    using assms edge_exists by (elim path_hp_from_vc)
  moreover have cost_hp: "cost_of_path (c G) (hp_of_vc G X) \<le> 15 * int (card (g1.uedges G)) + card1 X - 5"
    using assms edge_exists by (intro cost_hp_of_vc)
  moreover have "distinct_adj (?u\<^sub>1#hp_of_vc G X)" (is "distinct_adj ?T")
      and "last (hp_of_vc G X) = ?u\<^sub>1"
      and "?u\<^sub>1 \<in> List.set (hp_of_vc G X)" "List.set (hp_of_vc G X) \<subseteq> g2.vertices (f G)"
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
  moreover have "hp_of_vc G X \<noteq> []"
    using path by (auto intro!: g2.path_non_empty)
  moreover have "hd (hp_of_vc G X) = ?u\<^sub>2"
    using path by (auto intro!: g2.hd_path_betw)
  ultimately have cost: "cost_of_path (c G) (?u\<^sub>1#hp_of_vc G X) \<le> 15 * card (g1.uedges G) + card (set1 X)" 
    using cost_hp by (auto simp add: cost_of_path_cons)
  thus ?thesis
    using that hc by auto
qed

lemma cost_of_opt_mTSP:
  assumes "g1.ugraph_adj_map_invar G"
      and "card (g1.uedges G) > 1" "card1 OPT\<^sub>V\<^sub>C > 1" (* TODO: How to deal with these assumptions? *)
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
    using assms by (elim hp_of_vc) 
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
  assumes "g1.ugraph_adj_map_invar G" and "card (g1.uedges G) > 1" (is "card ?E > _") 
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C" "card1 OPT\<^sub>V\<^sub>C > 1" \<comment> \<open>There has to be at least one edge with weight 5.\<close>
      and "g2.is_hc_Adj (f G) T" 
  obtains k where "card1 (g G T) \<le> k" and "15 * int (card (g1.uedges G)) + k \<le> cost_of_path (c G) T"
    \<comment> \<open>The cost of the vertex cover computed by the function \<open>g\<close> is linked to the cost of the 
    given Hamiltonian cycle of the graph \<open>f G\<close>.\<close>
  using assms
proof (rule cost_shorten_tour_geq)
  fix k               
  assume "card1 (g G T) \<le> k" "15 * int (card ?E) + k \<le> cost_of_path (c G) (shorten_tour G T)"
  moreover have "cost_of_path (c G) (shorten_tour G T) \<le> cost_of_path (c G) T"
    using assms by (intro cost_shorten_tour_leq)
  ultimately show ?thesis
    using that by auto
qed

lemma l_reduction2:
  assumes "g1.ugraph_adj_map_invar G" and "card (g1.uedges G) > 1" (is "card ?E > _") 
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C" "card1 OPT\<^sub>V\<^sub>C > 1" (is "?\<tau>_G > 1")
      and opt_mtsp: "g2.is_tsp_Adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P" 
      and "g2.is_hc_Adj (f G) T"
  shows "\<bar> card1 (g G T) - card1 OPT\<^sub>V\<^sub>C \<bar> \<le> 1 * \<bar> cost_of_path (c G) T - cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>" 
  \<comment> \<open>Second condition for a L-Reduction.\<close>
  using assms(1-5,7)
proof (rule card_g_leq_k)
  fix k 
  assume card_leq_k: "card1 (g G T) \<le> k" 
    and cost_T_geq: "15 * int (card ?E) + k \<le> cost_of_path (c G) T"
  
  have cost_mtsp: "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 15 * int (card (g1.uedges G)) + ?\<tau>_G"
    using assms cost_of_opt_mTSP by auto

  have "g1.is_vc_Adj G (g G T)"
    using assms by (intro g_is_vc)
  hence "g1.is_vc_Adj G OPT\<^sub>V\<^sub>C" and tauG_leq: "?\<tau>_G \<le> card1 (g G T)"
    using assms by (auto elim: g1.is_min_vc_AdjE)

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