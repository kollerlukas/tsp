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
(uEdge u v,u,1) --- (uEdge u v,u,3) --- (uEdge u v,v,2)
       |                                        |
(uEdge u v,u,4) --- (uEdge u v,v,6) --- (uEdge u v,u,5)
       |                                        |
(uEdge u v,v,5) --- (uEdge u v,u,6) --- (uEdge u v,v,4)
       |                                        |
(uEdge u v,u,2) --- (uEdge u v,v,3) --- (uEdge u v,v,1)
\<close>

fun vertices_of_He :: "'v1 uedge \<Rightarrow> 'v2set" ("V\<^sub>H\<^sub>e") where 
  "vertices_of_He e = (case rep1 e of uEdge u v \<Rightarrow>
    g2.set_of_list ([(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),
      (rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]))"

fun neighborhood_in_He :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> 'v2set" ("\<N>\<^sub>H\<^sub>e") where
  "neighborhood_in_He (e,w,i) = (case rep1 e of uEdge u v \<Rightarrow>
    if w = u \<and> i = 1 then g2.set_of_list [(rep1 e,u,3),(rep1 e,u,4)]
    else if w = u \<and> i = 2 then g2.set_of_list [(rep1 e,v,3),(rep1 e,v,5)]
    else if w = u \<and> i = 3 then g2.set_of_list [(rep1 e,u,1),(rep1 e,v,2)]
    else if w = u \<and> i = 4 then g2.set_of_list [(rep1 e,u,1),(rep1 e,v,5),(rep1 e,v,6)]
    else if w = u \<and> i = 5 then g2.set_of_list [(rep1 e,v,2),(rep1 e,v,4),(rep1 e,v,6)]
    else if w = u \<and> i = 6 then g2.set_of_list [(rep1 e,v,4),(rep1 e,v,5)]
    else if w = v \<and> i = 1 then g2.set_of_list [(rep1 e,v,3),(rep1 e,v,4)]
    else if w = v \<and> i = 2 then g2.set_of_list [(rep1 e,u,3),(rep1 e,u,5)]
    else if w = v \<and> i = 3 then g2.set_of_list [(rep1 e,v,1),(rep1 e,u,2)]
    else if w = v \<and> i = 4 then g2.set_of_list [(rep1 e,v,1),(rep1 e,u,5),(rep1 e,u,6)]
    else if w = v \<and> i = 5 then g2.set_of_list [(rep1 e,u,2),(rep1 e,u,4),(rep1 e,u,6)]
    else if w = v \<and> i = 6 then g2.set_of_list [(rep1 e,u,4),(rep1 e,u,5)]
    else g2.set_of_list [])"

fun He :: "'v1 uedge \<Rightarrow> 'g2" ("H\<^sub>e") where
  "H\<^sub>e e = graph_of_vertices \<N>\<^sub>H\<^sub>e (V\<^sub>H\<^sub>e e)"

abbreviation "hp e \<equiv> (case e of uEdge u v \<Rightarrow>
    [(rep1 e,u,1::nat),(rep1 e,u,3),(rep1 e,v,2),(rep1 e,u,5),(rep1 e,v,6),(rep1 e,u,4),
      (rep1 e,v,5),(rep1 e,u,6),(rep1 e,v,4),(rep1 e,v,1),(rep1 e,v,3),(rep1 e,u,2)])"

fun hp_u1 where 
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
  "min_dist_in_He G x y = fold_g1_uedges3 (\<lambda>e d. min (g2.path_dist (H\<^sub>e e) x y) d) G (enat 5)" (* \<infinity> *)
  \<comment> \<open>This function returns the minimum distance between \<open>x\<close> and \<open>y\<close> in \<open>H\<^sub>e e\<close> for an edge \<open>e\<close> in \<open>G\<close>.
  The longest path in \<open>H\<^sub>e e\<close> has the length 5. Therefore, we can initialize the accumulator with the 
  value 5. Thus, we can easily conclude that the highest cost in the graph \<open>f G\<close> is 5.\<close>

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


(* fun hp_starting_at :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_starting_at (e,w,i) = (case rep1 e of uEdge u v \<Rightarrow> if w = v \<and> (i = 1 \<or> i = 2) then hp_v1 e else hp_u1 e)" *)

(* fun hp_starting_at :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_starting_at (e,w,i) = (case rep1 e of uEdge u v \<Rightarrow> if w = v then hp_v1 e else hp_u1 e)"

fun replace_hp :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "replace_hp G [] = []"
| "replace_hp G (x#T) = hp_starting_at x @ replace_hp G (filter (\<lambda>y. \<not> are_vertices_in_He G x y) T)" *)

fun to_covering_vertex :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1" where
  "to_covering_vertex G (x#T) = (case (x,last (takeWhile (are_vertices_in_He G x) (x#T))) of
      ((e,w\<^sub>1,i\<^sub>1),(_,w\<^sub>2,i\<^sub>2)) \<Rightarrow> case rep1 e of uEdge u v \<Rightarrow>
        if (i\<^sub>1 = 1 \<or> i\<^sub>1 = 2) then w\<^sub>1
        else if (i\<^sub>2 = 1 \<or> i\<^sub>2 = 2) then w\<^sub>2 
        else u)"
| "to_covering_vertex G [] = undefined" 

fun hp_starting_at :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_starting_at G ((e,w,i)#T) = (case rep1 e of uEdge u v \<Rightarrow> 
    if to_covering_vertex G ((e,w,i)#T) = u then hp_u1 e else hp_v1 e)"
| "hp_starting_at G [] = undefined"

fun replace_hp :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "replace_hp G [] = []"
| "replace_hp G (x#T) = hp_starting_at G (x#T) @ replace_hp G (filter (\<lambda>y. \<not> are_vertices_in_He G x y) T)"

fun shorten_tour :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "shorten_tour G T = (case rotate_tour (\<lambda>(e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2). rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2) T of
      x#y#T' \<Rightarrow> last (hp_starting_at G (y#T'))#replace_hp G (filter (\<lambda>z. \<not> are_vertices_in_He G y z) T') @ hp_starting_at G (y#T'))"

(* fun to_covering_vertex :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> 'v1" where
  "to_covering_vertex (e,w,i) = (case rep1 e of uEdge u v \<Rightarrow> if w = v \<and> (i = 1 \<or> i = 2) then v else u)" *)

(* fun to_covering_vertex :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> 'v1" where
  "to_covering_vertex (e,w,i) = (case rep1 e of uEdge u v \<Rightarrow> if w = v then v else u)"

fun vc_of_tour :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1set" where
  "vc_of_tour G [] = set_empty1"
| "vc_of_tour G (x#T) = 
    insert1 (to_covering_vertex x) (vc_of_tour G (filter (\<lambda>y. \<not> are_vertices_in_He G x y) T))" *)

fun vc_of_tour :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1set" where
  "vc_of_tour G [] = set_empty1"
| "vc_of_tour G (x#T) = 
    insert1 (to_covering_vertex G (x#T)) (vc_of_tour G (filter (\<lambda>y. \<not> are_vertices_in_He G x y) T))"

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
    else if rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2 \<and> w\<^sub>1 = w\<^sub>2 \<and> (i\<^sub>1 = 1 \<or> i\<^sub>1 = 2) \<and> (i\<^sub>2 = 1 \<or> i\<^sub>2 = 2) then 4
    else 5)"

fun g :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1set" where
  "g G T = vc_of_tour G (tl (shorten_tour G T))"

end

section \<open>Properties of Auxiliary Functions\<close>

context VC4_To_mTSP
begin

lemma vertices_of_He_rep_idem: "V\<^sub>H\<^sub>e (rep1 e) = V\<^sub>H\<^sub>e e"
  by (simp only: vertices_of_He.simps g1.rep_idem)

lemma invar_vertices_of_He: "set_invar2 (V\<^sub>H\<^sub>e e)"
  by (auto simp add: g2.invar_set_of_list simp del: g2.set_of_list.simps split: uedge.splits)

lemma isin_vertices_of_He_iff: 
  assumes "rep1 e = rep1 (uEdge u v)"
  shows "isin2 (V\<^sub>H\<^sub>e e) x \<longleftrightarrow> x \<in> set [(rep1 e,u,1::nat),(rep1 e,u,2),
    (rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),
    (rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]" 
  using assms by (rule g1.rep_cases) (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)

lemma set_vertices_of_He: 
  assumes "rep1 e = rep1 (uEdge u v)" 
  shows "set2 (V\<^sub>H\<^sub>e e) = set [(rep1 e,u,1::nat),(rep1 e,u,2),
    (rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),
    (rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
  using assms by (rule g1.rep_cases) (auto simp add: g2.set_of_list simp del: g2.set_of_list.simps)

lemma isin_vertices_of_He_intro: 
  assumes "rep1 e = rep1 (uEdge u v)" 
    "x \<in> set [(rep1 e,u,1::nat),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),
      (rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
  shows "isin2 (V\<^sub>H\<^sub>e e) x" 
  using assms isin_vertices_of_He_iff by auto

lemma isin_vertices_of_He_elim:
  assumes "isin2 (V\<^sub>H\<^sub>e e) x"
  obtains u v where "rep1 e = rep1 (uEdge u v)" 
    "x \<in> set [(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6)]"
proof -
  obtain u v where [simp]: "e = uEdge u v"
    using uedge.exhaust by auto
  hence "x \<in> List.set [(rep1 e,u,1),(rep1 e,u,2),
    (rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),
    (rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
    using assms isin_vertices_of_He_iff by blast
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
    using assms g1.rep_idem by metis
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
      g2.set_of_list [(rep1 (uEdge u v),u,3),(rep1 (uEdge u v),u,4)]
    else if i = 2 then 
      g2.set_of_list [(rep1 (uEdge u v),v,3),(rep1 (uEdge u v),v,5)]
    else if i = 3 then 
      g2.set_of_list [(rep1 (uEdge u v),u,1),(rep1 (uEdge u v),v,2)]
    else if i = 4 then 
      g2.set_of_list [(rep1 (uEdge u v),u,1),(rep1 (uEdge u v),v,5),(rep1 (uEdge u v),v,6)]
    else if i = 5 then 
      g2.set_of_list [(rep1 (uEdge u v),v,2),(rep1 (uEdge u v),v,4),(rep1 (uEdge u v),v,6)]
    else if i = 6 then 
      g2.set_of_list [(rep1 (uEdge u v),v,4),(rep1 (uEdge u v),v,5)]
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
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,3),(rep1 e,u,4)]"
    | u v where "x = (rep1 e,u,2)" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,v,3),(rep1 e,v,5)]"
    | u v where "x = (rep1 e,u,3)" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,v,2)]"
    | u v where "x = (rep1 e,u,4)" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,v,5),(rep1 e,v,6)]"
    | u v where "x = (rep1 e,u,5)" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,v,2),(rep1 e,v,4),(rep1 e,v,6)]"
    | u v where "x = (rep1 e,u,6)" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,v,4),(rep1 e,v,5)]"
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
  apply (intro isin_vertices_of_He_intro)

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
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,3),(rep1 e,u,4)]"
  thus ?thesis
    using assms neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,2)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,v,3),(rep1 e,v,5)]"
  thus ?thesis
    using assms neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,3)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,v,2)]"
  thus ?thesis
    using assms neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,4)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,v,5),(rep1 e,v,6)]"
  thus ?thesis
    using assms neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,5)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,v,2),(rep1 e,v,4),(rep1 e,v,6)]"
  thus ?thesis
    using assms neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,6)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,v,4),(rep1 e,v,5)]"
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

lemma min_dist_in_He_def2:
  assumes "g1.ugraph_adj_map_invar G"
  shows "min_dist_in_He G x y = Min ({g2.path_dist (H\<^sub>e e) x y | e. e \<in> g1.uedges G} \<union> {enat 5})"
  using assms(1)
proof (rule fold3.fold_uedgesE)
  let ?f="\<lambda>e d. min (g2.path_dist (H\<^sub>e e) x y) d"
  fix es
  assume "distinct es" and set_es: "set es = g1.uedges G" 
    and [simp]: "fold_g1_uedges3 ?f G (enat 5) = fold ?f es (enat 5)"
  moreover have "\<And>a. fold ?f es a = fold min (map (\<lambda>e. g2.path_dist (H\<^sub>e e) x y) es) a"
    by (induction es) auto
  ultimately have "min_dist_in_He G x y = fold min (map (\<lambda>e. g2.path_dist (H\<^sub>e e) x y) es) (enat 5)"
    by auto
  also have "... = Min (set (enat 5#(map (\<lambda>e. g2.path_dist (H\<^sub>e e) x y) es)))"
    using Min.set_eq_fold[symmetric] by fastforce
  also have "... = Min ({g2.path_dist (H\<^sub>e e) x y | e. e \<in> g1.uedges G} \<union> {enat 5})"
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
  assume "distinct es" and set_es: "List.set es = g1.uedges G" and [simp]: "fold_g1_uedges3 ?f G (enat 5) = fold ?f es (enat 5)"
  moreover hence "e \<in> set es"
    using assms by auto
  moreover hence "\<And>d. fold ?f es d \<le> ?f e d"
    by (intro fold_enat_min_leq_member)
  ultimately show ?thesis
    by auto
qed

lemma min_dist_in_He_leq5: "g1.ugraph_adj_map_invar G \<Longrightarrow> min_dist_in_He G x y \<le> enat 5"
  using min_dist_in_He_def2 by auto

lemma min_dist_in_He_geq1:
  assumes "g1.ugraph_adj_map_invar G" "x \<noteq> y"
  shows "min_dist_in_He G x y \<ge> enat 1"
proof (rule ccontr)
  assume "\<not> min_dist_in_He G x y \<ge> enat 1"
  hence "min_dist_in_He G x y < enat 1"
    by auto
  hence "Min ({g2.path_dist (H\<^sub>e e) x y |e. e \<in> g1.uedges G} \<union> {enat 5}) < enat 1" (is "Min ?D < _")
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
    using g2.path_non_nil[OF path] g2.hd_path_betw[OF path] by (cases P) fastforce+
  ultimately have "x = y"
    using g2.last_path_betw[OF path] by auto
  thus "False"
    using assms by auto
qed

lemma min_dist_in_He_sym:
  assumes "g1.ugraph_adj_map_invar G"
  shows "min_dist_in_He G x y = min_dist_in_He G y x"
  unfolding min_dist_in_He_def2[OF assms]
  using invar_He g2.path_dist_sym by auto

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

(* lemma vertices_in_He_of_edge_in_He:
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
qed *)

lemma vertices_in_He_of_edge_in_He:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
  shows "is_edge_in_He G (uEdge x y) \<and> x \<in> g2.vertices (H\<^sub>e e) \<and> y \<in> g2.vertices (H\<^sub>e e) \<longleftrightarrow> rep2 (uEdge x y) \<in> g2.uedges (H\<^sub>e e)"
proof
  assume "is_edge_in_He G (uEdge x y) \<and> x \<in> g2.vertices (H\<^sub>e e) \<and> y \<in> g2.vertices (H\<^sub>e e)"
  moreover then obtain e' where edge_e': "e' \<in> g1.uedges G" and edge_xy: "rep2 (uEdge x y) \<in> g2.uedges (H\<^sub>e e')"
    using assms by (elim is_edge_in_He_elim) auto
  moreover hence "x \<in> g2.vertices (H\<^sub>e e')"
    using g2.set_of_rep_uedge by (intro g2.vs_uedges_subset_vertices) blast
  ultimately have "rep1 e = rep1 e'"
    using assms vertices_of_He_disjoint by auto
  thus "rep2 (uEdge x y) \<in> g2.uedges (H\<^sub>e e)"
    using assms edge_e' edge_xy by (auto simp add: g1.rep_of_edge)
next
  assume "rep2 (uEdge x y) \<in> g2.uedges (H\<^sub>e e)"
  hence y_isin_Nx: "isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y" and "is_edge_in_He G (uEdge x y)"
    using assms g2.rep_isin_uedges_elim[of "H\<^sub>e e", OF invar_He] is_edge_in_He_intro by blast+
  moreover hence "x \<in> g2.vertices (H\<^sub>e e)"
    using y_isin_Nx by (auto intro!: g2.vertices_memberI1)
  moreover have "y \<in> g2.vertices (H\<^sub>e e)"
    using y_isin_Nx by (auto intro!: g2.vertices_memberI2)
  ultimately show "is_edge_in_He G (uEdge x y) \<and> x \<in> g2.vertices (H\<^sub>e e) \<and> y \<in> g2.vertices (H\<^sub>e e)"
    by auto
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
proof (cases x; cases y)
  fix e\<^sub>x w\<^sub>x i\<^sub>x e\<^sub>y w\<^sub>y i\<^sub>y 
  assume [simp]: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)" and [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
  consider 
    "is_edge_in_He G (uEdge x y)" 
    | "\<not> is_edge_in_He G (uEdge x y)" "are_vertices_in_He G x y" 
    | "\<not> is_edge_in_He G (uEdge x y)" "\<not> are_vertices_in_He G x y" "w\<^sub>x = w\<^sub>y" "rep1 e\<^sub>x \<noteq> rep1 e\<^sub>y" 
    | "\<not> is_edge_in_He G (uEdge x y)" "\<not> are_vertices_in_He G x y" "w\<^sub>x \<noteq> w\<^sub>y \<or> rep1 e\<^sub>x = rep1 e\<^sub>y"
    by auto
  thus ?thesis
  proof cases
    assume "\<not> is_edge_in_He G (uEdge x y)" "are_vertices_in_He G x y"
    moreover hence "min_dist_in_He G x y \<ge> enat 1" and "min_dist_in_He G x y \<le> enat 5"
      using assms min_dist_in_He_geq1 min_dist_in_He_leq5 by auto
    moreover then obtain k where "min_dist_in_He G x y = enat k"
      using enat_ile by auto                                    
    ultimately show ?thesis
      by auto
  qed auto
qed

lemma c_sym: 
  assumes "g1.ugraph_adj_map_invar G"
  shows "c G x y = c G y x"
proof (cases x; cases y)
  fix e\<^sub>x w\<^sub>x i\<^sub>x e\<^sub>y w\<^sub>y i\<^sub>y 
  assume [simp]: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)" and [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
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
  moreover hence "is_edge_in_He G (uEdge (rep1 e,u,1) (rep1 e,u,3))"
    "is_edge_in_He G (uEdge (rep1 e,u,3) (rep1 e,v,2))"
    "is_edge_in_He G (uEdge (rep1 e,v,2) (rep1 e,u,5))"
    "is_edge_in_He G (uEdge (rep1 e,u,5) (rep1 e,v,6))"
    "is_edge_in_He G (uEdge (rep1 e,v,6) (rep1 e,u,4))"
    "is_edge_in_He G (uEdge (rep1 e,u,4) (rep1 e,v,5))"
    "is_edge_in_He G (uEdge (rep1 e,v,5) (rep1 e,u,6))"
    "is_edge_in_He G (uEdge (rep1 e,u,6) (rep1 e,v,4))"
    "is_edge_in_He G (uEdge (rep1 e,v,4) (rep1 e,v,1))"
    "is_edge_in_He G (uEdge (rep1 e,v,1) (rep1 e,v,3))" 
    "is_edge_in_He G (uEdge (rep1 e,v,3) (rep1 e,u,2))"
    using assms g1.rep_simps by (fastforce intro!: is_edge_in_He_intro 
        simp add: g2.uedges_def2 neighborhood_He g2.isin_set_of_list 
        simp del: is_edge_in_He.simps He.simps g2.set_of_list.simps)+
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

lemma distinct_hp_u1:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
  shows "distinct (hp_u1 e)"
  using assms by (rule g1.uedge_not_refl_elim) auto

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

lemma distinct_hp_u2:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
  shows "distinct (hp_u2 e)"
  using assms by (rule g1.uedge_not_refl_elim) auto

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
  moreover hence "is_edge_in_He G (uEdge (rep1 e,v,1) (rep1 e,v,3))"
    "is_edge_in_He G (uEdge (rep1 e,v,3) (rep1 e,u,2))"
    "is_edge_in_He G (uEdge (rep1 e,u,2) (rep1 e,v,5))"
    "is_edge_in_He G (uEdge (rep1 e,v,5) (rep1 e,u,6))"
    "is_edge_in_He G (uEdge (rep1 e,u,6) (rep1 e,v,4))"
    "is_edge_in_He G (uEdge (rep1 e,v,4) (rep1 e,u,5))"
    "is_edge_in_He G (uEdge (rep1 e,u,5) (rep1 e,v,6))"
    "is_edge_in_He G (uEdge (rep1 e,v,6) (rep1 e,u,4))"
    "is_edge_in_He G (uEdge (rep1 e,u,4) (rep1 e,u,1))"
    "is_edge_in_He G (uEdge (rep1 e,u,1) (rep1 e,u,3))" 
    "is_edge_in_He G (uEdge (rep1 e,u,3) (rep1 e,v,2))"
    using assms g1.rep_simps by (fastforce intro!: is_edge_in_He_intro 
        simp add: g2.uedges_def2 neighborhood_He g2.isin_set_of_list 
        simp del: is_edge_in_He.simps He.simps g2.set_of_list.simps)+
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
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
  shows "distinct (hp_v2 e)"
  using assms by (rule g1.uedge_not_refl_elim) auto

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
  hence "isin2 (g2.set_of_list [(rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,3),(rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,4)]) ?y"
    using neighborhood_in_He_def2 by auto
  hence "?y \<in> set [(rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,3),(rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,4)]"
    using g2.isin_set_of_list by blast
  thus "False"
    by auto
qed

lemma card_vertices_of_He: 
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
  shows "card (g2.vertices (H\<^sub>e e)) = 12"
proof -
  have "length (hp_u1 e) = 12"
    by (auto split: uedge.splits)
  moreover have "distinct (hp_u1 e)"
    using assms distinct_hp_u1 by auto
  ultimately have "card (set (hp_u1 e)) = 12"
    using distinct_card by fastforce
  thus ?thesis
    using vertices_hp_u1 by auto
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
    have "isin2 (\<N>\<^sub>H\<^sub>e ?x) (?e,u,4)" "isin2 (\<N>\<^sub>H\<^sub>e (?e,u,4)) (?e,v,5)" "isin2 (\<N>\<^sub>H\<^sub>e (?e,v,5)) ?y"
      using g1.is_rep neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (fastforce simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)+
    moreover hence "isin2 (V\<^sub>H\<^sub>e ?e) ?x" "isin2 (V\<^sub>H\<^sub>e ?e) (?e,u,4)" "isin2 (V\<^sub>H\<^sub>e ?e) (?e,v,5)"
      using x_vert neighborhood_in_He_subset_of_vertices_of_He by blast+
    ultimately have "isin2 (\<N>\<^sub>2 (H\<^sub>e ?e) ?x) (?e,u,4)" 
      "isin2 (\<N>\<^sub>2 (H\<^sub>e ?e) (?e,u,4)) (?e,v,5)" 
      "isin2 (\<N>\<^sub>2 (H\<^sub>e ?e) (?e,v,5)) ?y"
      using neighborhood_He by auto
    hence path: "g2.path_betw (H\<^sub>e ?e) ?x [?x,(?e,u,4),(?e,v,5),?y] ?y"
      using y_vert by (auto intro!: g2.path_betw.intros)
    thus ?thesis
      using that by auto
  next
    assume [simp]: "w = v"
    have "isin2 (\<N>\<^sub>H\<^sub>e ?x) (?e,u,3)" "isin2 (\<N>\<^sub>H\<^sub>e (?e,u,3)) ?y"
      using neighborhood_in_He_def2 by (fastforce simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)+
    moreover hence "isin2 (V\<^sub>H\<^sub>e ?e) ?x" "isin2 (V\<^sub>H\<^sub>e ?e) (?e,u,3)"
      using x_vert neighborhood_in_He_subset_of_vertices_of_He by blast+
    ultimately have "isin2 (\<N>\<^sub>2 (H\<^sub>e ?e) ?x) (?e,u,3)" "isin2 (\<N>\<^sub>2 (H\<^sub>e ?e) (?e,u,3)) ?y"
      using neighborhood_He by auto
    hence path: "g2.path_betw (H\<^sub>e ?e) ?x [?x,(?e,u,3),?y] ?y"
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

lemma cost_x_y_eq4_iff:
  assumes "g1.ugraph_adj_map_invar G" "\<not> are_vertices_in_He G (e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2)" 
  shows "c G (e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2) = 4 \<longleftrightarrow> (rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2 \<and> w\<^sub>1 = w\<^sub>2 \<and> (i\<^sub>1 = 1 \<or> i\<^sub>1 = 2) \<and> (i\<^sub>2 = 1 \<or> i\<^sub>2 = 2))"
  using assms edge_in_He_are_vertices by (intro iffI) (auto split: if_splits)

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
  assumes "g1.ugraph_adj_map_invar G"
  shows "c G x y \<le> 5"
proof (cases x; cases y)
  fix e\<^sub>x w\<^sub>x i\<^sub>x e\<^sub>y w\<^sub>y i\<^sub>y
  assume [simp]: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)" and [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
  consider "is_edge_in_He G (uEdge x y)" 
    | "\<not> is_edge_in_He G (uEdge x y)" "are_vertices_in_He G x y" 
    | "\<not> is_edge_in_He G (uEdge x y)" "\<not> are_vertices_in_He G x y"
    by auto
  thus ?thesis
  proof cases
    assume "\<not> is_edge_in_He G (uEdge x y)" "are_vertices_in_He G x y" 
    moreover obtain k where "min_dist_in_He G x y = enat k" "k \<le> 5"
      using assms min_dist_in_He_leq5 enat_ile by (metis enat_ord_simps(1))
    ultimately show ?thesis 
      by auto
  qed auto
qed

(* lemma cost_u1_u2_leq5:
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
qed (* TODO: combine with lemma above! *) *)

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

lemma vertices_f: "g1.ugraph_adj_map_invar G \<Longrightarrow> g2.vertices (f G) = \<Union> ((g2.vertices o H\<^sub>e) ` g1.uedges G)"
  using vertices_f_eq_vertices_of_H set_vertices_of_H vertices_of_He by simp

lemma finite_vertices_f: "g1.ugraph_adj_map_invar G \<Longrightarrow> finite (g2.vertices (f G))"
  using finite_sets vertices_f_eq_vertices_of_H by auto

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

(* lemma set_hp_starting_at:
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
  consider "w = v" "i = 1 \<or> i = 2" | "w \<noteq> v \<or> (i \<noteq> 1 \<and> i \<noteq> 2)"
    by auto
  thus ?thesis
  proof cases
    assume "w = v" "i = 1 \<or> i = 2"
    thus ?thesis
      by (auto simp add: vertices_hp_v1[symmetric] simp del: He.simps)
  next
    assume "w \<noteq> v \<or> (i \<noteq> 1 \<and> i \<noteq> 2)"
    thus ?thesis
      by (auto simp add: vertices_hp_u1[symmetric] simp del: He.simps)
  qed
qed

lemma hd_hp_starting_at: 
  assumes "rep1 e = uEdge u v" "w \<in> {u,v}"
  obtains "i = 1 \<or> i = 2" "hd (hp_starting_at (e,w,i)) = (rep1 e,w,1)" 
  | "w = u \<or> (i \<noteq> 1 \<and> i \<noteq> 2)" "hd (hp_starting_at (e,w,i)) = (rep1 e,u,1)"
proof -
  consider "w = v" "i = 1 \<or> i = 2" | "w \<noteq> v \<or> (i \<noteq> 1 \<and> i \<noteq> 2)"
    by auto
  thus ?thesis
    using assms that g1.rep_simps by cases auto
qed

lemma last_hp_starting_at: 
  assumes "rep1 e = uEdge u v" "w \<in> {u,v}"
  obtains "i = 1 \<or> i = 2" "last (hp_starting_at (e,w,i)) = (rep1 e,w,2)" 
  | "w = u \<or> (i \<noteq> 1 \<and> i \<noteq> 2)" "last (hp_starting_at (e,w,i)) = (rep1 e,u,2)"
proof -
  consider "w = v" "i = 1 \<or> i = 2" | "w \<noteq> v \<or> (i \<noteq> 1 \<and> i \<noteq> 2)"
    by auto
  thus ?thesis
    using assms that g1.rep_simps by cases auto
qed 

lemma covering_vertex_hd_hp_starting_at:
  assumes "g1.ugraph_adj_map_invar G" "x \<in> g2.vertices (f G)"
  shows "to_covering_vertex (hd (hp_starting_at x)) = to_covering_vertex x"
proof (cases x)
  fix e w i
  assume [simp]: "x = (e,w,i)"
  hence vert_x_He: "x \<in> g2.vertices (H\<^sub>e e)" and edge_e: "e \<in> g1.uedges G" 
    using assms fst_of_vertex_is_edge by auto
  moreover hence "isin2 (V\<^sub>H\<^sub>e e) x"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately obtain u v where rep_e: "rep1 e = uEdge u v" and "w \<in> {u,v}"
    by (elim isin_vertices_of_He_elim2) (auto simp add: g1.rep_of_edge)
  then consider "i = 1 \<or> i = 2" "hd (hp_starting_at x) = (e,w,1)" 
    | "w = u \<or> (i \<noteq> 1 \<and> i \<noteq> 2)" "hd (hp_starting_at x) = (e,u,1)"
    using edge_e by (elim hd_hp_starting_at) (auto simp add: g1.rep_of_edge)
  thus ?thesis
    using rep_e by cases auto
qed

lemma covering_vertex_last_hp_starting_at:
  assumes "g1.ugraph_adj_map_invar G" "x \<in> g2.vertices (f G)"
  shows "to_covering_vertex (last (hp_starting_at x)) = to_covering_vertex x"
proof (cases x)
  fix e w i
  assume [simp]: "x = (e,w,i)"
  hence vert_x_He: "x \<in> g2.vertices (H\<^sub>e e)" and edge_e: "e \<in> g1.uedges G" 
    using assms fst_of_vertex_is_edge by auto
  moreover hence "isin2 (V\<^sub>H\<^sub>e e) x"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately obtain u v where rep_e: "rep1 e = uEdge u v" and "w \<in> {u,v}"
    by (elim isin_vertices_of_He_elim2) (auto simp add: g1.rep_of_edge)
  then consider "i = 1 \<or> i = 2" "last (hp_starting_at x) = (e,w,2)" 
    | "w = u \<or> (i \<noteq> 1 \<and> i \<noteq> 2)" "last (hp_starting_at x) = (e,u,2)"
    using edge_e by (elim last_hp_starting_at) (auto simp add: g1.rep_of_edge)
  thus ?thesis
    using rep_e by cases auto
qed *)

lemma last_takeWhile_vert_isin_He:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" and "x \<in> g2.vertices (H\<^sub>e e)"
  shows "last (takeWhile (are_vertices_in_He G x) (x#T)) \<in> g2.vertices (H\<^sub>e e)" (is "last ?tW \<in> _")
proof -
  have "x \<in> g2.vertices (f G)"
    using assms vertices_f by auto
  hence "are_vertices_in_He G x x"
    using assms are_vertices_in_He_refl by auto
  hence "?tW \<noteq> []"
    by auto
  hence "last ?tW \<in> set ?tW"
    using last_in_set by blast
  hence "are_vertices_in_He G x (last ?tW)"
    using set_takeWhileD by metis
  moreover then obtain e' where "e' \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e')" 
    and last_in_He: "last ?tW \<in> g2.vertices (H\<^sub>e e')"
    using assms by (elim are_vertices_in_He_elim)
  ultimately have "e' = e"
    using assms vertices_in_He_rep_iff[of G e e'] by (auto simp add: g1.rep_of_edge)
  thus ?thesis
    using last_in_He by auto
qed

lemma covering_vertex_cases:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" and "x \<in> g2.vertices (H\<^sub>e e)"
  obtains w\<^sub>1 i\<^sub>1 w\<^sub>2 i\<^sub>2 where "x = (e,w\<^sub>1,i\<^sub>1)" "last (takeWhile (are_vertices_in_He G x) (x#T)) = (e,w\<^sub>2,i\<^sub>2)" 
    and "i\<^sub>1 = 1 \<or> i\<^sub>1 = 2" "to_covering_vertex G (x#T) = w\<^sub>1" 
  | w\<^sub>1 i\<^sub>1 w\<^sub>2 i\<^sub>2 where "x = (e,w\<^sub>1,i\<^sub>1)" "last (takeWhile (are_vertices_in_He G x) (x#T)) = (e,w\<^sub>2,i\<^sub>2)" 
    and "i\<^sub>1 \<noteq> 1 \<and> i\<^sub>1 \<noteq> 2" "i\<^sub>2 = 1 \<or> i\<^sub>2 = 2" "to_covering_vertex G (x#T) = w\<^sub>2" 
  | u v w\<^sub>1 i\<^sub>1 w\<^sub>2 i\<^sub>2 where "rep1 e = uEdge u v" "x = (e,w\<^sub>1,i\<^sub>1)" "last (takeWhile (are_vertices_in_He G x) (x#T)) = (e,w\<^sub>2,i\<^sub>2)" 
    and "i\<^sub>1 \<noteq> 1 \<and> i\<^sub>1 \<noteq> 2" "i\<^sub>2 \<noteq> 1 \<and> i\<^sub>2 \<noteq> 2" "to_covering_vertex G (x#T) = u"
proof -
  obtain u v where rep_e: "rep1 e = uEdge u v"
    using assms by (elim g1.uedge_not_refl_elim)
  moreover have "isin2 (V\<^sub>H\<^sub>e e) x"
    using assms invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately obtain w\<^sub>1 i\<^sub>1 where x_case: "x = (e,w\<^sub>1,i\<^sub>1)" and "w\<^sub>1 \<in> {u,v}"
    using assms by (elim isin_vertices_of_He_elim2) (auto simp add: g1.rep_of_edge)

  have "last (takeWhile (are_vertices_in_He G x) (x#T)) \<in> g2.vertices (H\<^sub>e e)" (is "?last \<in> _")
    using assms last_takeWhile_vert_isin_He by blast
  hence "isin2 (V\<^sub>H\<^sub>e e) ?last"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  then obtain w\<^sub>2 i\<^sub>2 where last_case: "?last = (e,w\<^sub>2,i\<^sub>2)" and "w\<^sub>2 \<in> {u,v}"
    using assms rep_e by (elim isin_vertices_of_He_elim2) (auto simp add: g1.rep_of_edge)

  consider "i\<^sub>1 = 1 \<or> i\<^sub>1 = 2" | "i\<^sub>1 \<noteq> 1 \<and> i\<^sub>1 \<noteq> 2" "i\<^sub>2 = 1 \<or> i\<^sub>2 = 2" | "i\<^sub>1 \<noteq> 1 \<and> i\<^sub>1 \<noteq> 2" "i\<^sub>2 \<noteq> 1 \<and> i\<^sub>2 \<noteq> 2"
    by blast
  thus ?thesis
    using assms that rep_e x_case last_case by cases simp+
qed

lemma covering_vertex_of_corner:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" 
      and "(e,w,i) \<in> g2.vertices (H\<^sub>e e)" "i = 1 \<or> i = 2"
  shows "to_covering_vertex G ((e,w,i)#T) = w"
  using assms by (elim covering_vertex_cases) simp+

(* lemma covering_vertex_of_corner:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" 
      and "rep1 e = uEdge u v" "w \<in> {u,v}" "i = 1 \<or> i = 2"
  shows "to_covering_vertex G ((e,w,i)#T) = w"
proof -
  have "isin2 (V\<^sub>H\<^sub>e e) (rep1 e,w,i)"
    using assms isin_vertices_of_He_intro2 by auto
  hence vert_ewi: "(e,w,i) \<in> g2.vertices (H\<^sub>e e)"
    using assms invar_vertices_of_He vertices_of_He 
    by (auto simp add: g1.rep_of_edge g2.set_specs simp del: He.simps)
  show ?thesis
    using assms(1-2) vert_ewi
  proof (rule covering_vertex_cases)
    fix w\<^sub>1 i\<^sub>1
    assume "(e,w,i) = (e,w\<^sub>1,i\<^sub>1)"
    thus ?thesis
      using assms by auto
  next
    fix w\<^sub>1 i\<^sub>1
    assume "(e,w,i) = (e,w\<^sub>1,i\<^sub>1)" "i\<^sub>1 \<noteq> 1 \<and> i\<^sub>1 \<noteq> 2"
    thus ?thesis
      using assms by auto
  next
    fix w\<^sub>1 i\<^sub>1
    assume "(e,w,i) = (e,w\<^sub>1,i\<^sub>1)" "i\<^sub>1 \<noteq> 1 \<and> i\<^sub>1 \<noteq> 2"
    thus ?thesis
      using assms by auto
  qed
qed *)

lemma covering_vertex_is_vertex:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)"
  shows "to_covering_vertex G (x#T) \<in> set_of_uedge (rep1 e)"
proof -
  obtain u v where rep_e: "rep1 e = uEdge u v"
    using assms by (elim g1.uedge_not_refl_elim)
  show ?thesis
    using assms(1-2) assms(3)
  proof (rule covering_vertex_cases)
    fix w\<^sub>1 i\<^sub>1
    assume "x = (e,w\<^sub>1,i\<^sub>1)" "to_covering_vertex G (x#T) = w\<^sub>1"
    moreover hence "isin2 (V\<^sub>H\<^sub>e e) (e,w\<^sub>1,i\<^sub>1)"
      using assms(3) invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
    moreover hence "w\<^sub>1 \<in> {u,v}"
      using rep_e by (elim isin_vertices_of_He_elim2) auto
    ultimately show ?thesis
      using assms rep_e by (auto simp add: set_of_uedge_def g1.rep_of_edge)
  next
    fix w\<^sub>1 i\<^sub>1 w\<^sub>2 i\<^sub>2 
    assume "last (takeWhile (are_vertices_in_He G x) (x#T)) = (e,w\<^sub>2,i\<^sub>2)" and cov_xT: "to_covering_vertex G (x#T) = w\<^sub>2"
    hence "(e,w\<^sub>2,i\<^sub>2) \<in> g2.vertices (H\<^sub>e e)"
      using assms last_takeWhile_vert_isin_He by metis
    moreover hence "isin2 (V\<^sub>H\<^sub>e e) (e,w\<^sub>2,i\<^sub>2)"
      using assms(3) invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
    moreover hence "w\<^sub>2 \<in> {u,v}"
      using rep_e by (elim isin_vertices_of_He_elim2) auto
    thus ?thesis
      using assms rep_e cov_xT by (auto simp add: set_of_uedge_def g1.rep_of_edge)
  next
    fix u' v'
    assume "rep1 e = uEdge u' v'" "to_covering_vertex G (x#T) = u'"
    thus ?thesis
      using assms rep_e by (auto simp add: set_of_uedge_def g1.rep_of_edge)
  qed
qed

lemma covering_vertex_append:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)"
      and "\<And>z. z \<in> set zs \<Longrightarrow> \<not> are_vertices_in_He G x z"
  shows "to_covering_vertex G (x#T @ zs) = to_covering_vertex G (x#T)"
proof (cases zs)
  case (Cons z zs')
  moreover hence "takeWhile (are_vertices_in_He G x) ((x#T) @ z#zs') = takeWhile (are_vertices_in_He G x) (x#T)"
    using assms by (intro takeWhile_tail) auto
  ultimately have last_tW_eq: 
    "last (takeWhile (are_vertices_in_He G x) (x#T @ zs)) = last (takeWhile (are_vertices_in_He G x) (x#T))"
    by auto
  thus ?thesis 
    using assms by (elim covering_vertex_cases) simp+
qed auto

lemma hp_starting_at_non_nil: "hp_starting_at G (x#T) \<noteq> []"
  by (cases x) (auto split: uedge.splits)

lemma hp_starting_at_cases:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" and "x \<in> g2.vertices (H\<^sub>e e)"
  obtains u v where "rep1 e = uEdge u v" "to_covering_vertex G (x#T) = u" "hp_starting_at G (x#T) = hp_u1 e"
  | u v where "rep1 e = uEdge u v" "to_covering_vertex G (x#T) = v" "hp_starting_at G (x#T) = hp_v1 e"
proof -
  have "isin2 (V\<^sub>H\<^sub>e e) x"
    using assms invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  then obtain u v w i where [simp]: "x = (e,w,i)" and rep_e: "rep1 e = uEdge u v"
    using assms by (elim isin_vertices_of_He_elim2) (auto simp add: g1.rep_of_edge)
  hence "to_covering_vertex G (x#T) \<in> set_of_uedge (rep1 e)"
    using assms covering_vertex_is_vertex g1.rep_simps by blast
  moreover have "set_of_uedge (rep1 e) = {u,v}"
    using rep_e by (auto simp add: set_of_uedge_def)
  ultimately consider "to_covering_vertex G (x#T) = u" | "to_covering_vertex G (x#T) = v"
    by auto
  thus ?thesis
    using that assms rep_e by cases auto
qed

lemma set_hp_starting_at:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)"
  shows "set (hp_starting_at G (x#T)) = g2.vertices (H\<^sub>e e)"
  using assms
proof (rule hp_starting_at_cases)
  assume "hp_starting_at G (x#T) = hp_u1 e"
  thus ?thesis
    using vertices_hp_u1 by metis
next
  assume "hp_starting_at G (x#T) = hp_v1 e"
  thus ?thesis
    using vertices_hp_v1 by metis
qed

lemma hp_starting_at_corner:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)"
  shows "hp_starting_at G ((e,to_covering_vertex G (x#T),1)#T') = hp_starting_at G (x#T)" 
    (is "hp_starting_at G (?x#T') = _")
  using assms
proof (rule hp_starting_at_cases)
  fix u v
  assume rep_e: "rep1 e = uEdge u v" "to_covering_vertex G (x#T) = u" "hp_starting_at G (x#T) = hp_u1 e"
  moreover have "to_covering_vertex G (?x#T') = u"
    using assms rep_e covering_vertex_of_corner by auto
  moreover hence "isin2 (V\<^sub>H\<^sub>e e) ?x"
    using assms rep_e by (auto intro!: isin_vertices_of_He_intro2 simp add: g1.rep_of_edge simp del: vertices_of_He.simps)
  moreover hence "?x \<in> g2.vertices (H\<^sub>e e)"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately show ?thesis
    using assms by (elim hp_starting_at_cases) auto
next
  fix u v
  assume rep_e: "rep1 e = uEdge u v" "to_covering_vertex G (x#T) = v" "hp_starting_at G (x#T) = hp_v1 e"
  moreover have "to_covering_vertex G (?x#T') = v"
    using assms rep_e covering_vertex_of_corner by auto
  moreover hence "isin2 (V\<^sub>H\<^sub>e e) ?x"
    using assms rep_e by (auto intro!: isin_vertices_of_He_intro2 simp add: g1.rep_of_edge simp del: vertices_of_He.simps)
  moreover hence "?x \<in> g2.vertices (H\<^sub>e e)"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately show ?thesis
    using assms by (elim hp_starting_at_cases) auto
qed

lemma hd_hp_starting_at: 
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)"
  shows "hd (hp_starting_at G (x#T)) = (e,to_covering_vertex G (x#T),1)"
  using assms
proof (rule hp_starting_at_cases)
  fix u v
  assume "rep1 e = uEdge u v" "to_covering_vertex G (x#T) = u" "hp_starting_at G (x#T) = hp_u1 e"
  thus ?thesis
    using assms by (auto simp add: g1.rep_of_edge)
next
  fix u v
  assume "rep1 e = uEdge u v" "to_covering_vertex G (x#T) = v" "hp_starting_at G (x#T) = hp_v1 e"
  thus ?thesis
    using assms g1.is_rep by (auto simp add: g1.rep_of_edge)
qed

lemma last_hp_starting_at: 
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)"
  shows "last (hp_starting_at G (x#T)) = (e,to_covering_vertex G (x#T),2)"
  using assms
proof (rule hp_starting_at_cases)
  fix u v
  assume "rep1 e = uEdge u v" "to_covering_vertex G (x#T) = u" "hp_starting_at G (x#T) = hp_u1 e"
  thus ?thesis
    using assms by (auto simp add: g1.rep_of_edge)
next
  fix u v
  assume "rep1 e = uEdge u v" "to_covering_vertex G (x#T) = v" "hp_starting_at G (x#T) = hp_v1 e"
  thus ?thesis
    using assms g1.is_rep by (auto simp add: g1.rep_of_edge)
qed

lemma hp_starting_at_append:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)"
      and "\<And>z. z \<in> set zs \<Longrightarrow> \<not> are_vertices_in_He G x z"
  shows "hp_starting_at G (x#T @ zs) = hp_starting_at G (x#T)"
  thm covering_vertex_append
  using assms(1-3)
proof (rule hp_starting_at_cases)
  fix u v
  assume "rep1 e = uEdge u v" "to_covering_vertex G (x#T @ zs) = u" 
    and hp_xT_zs: "hp_starting_at G (x#T @ zs) = hp_u1 e"
  moreover hence "to_covering_vertex G (x#T) = u"
    using assms covering_vertex_append by auto
  ultimately have "hp_starting_at G (x#T) = hp_u1 e"
    using assms by (elim hp_starting_at_cases[of G e x T]) auto
  thus ?thesis
    using hp_xT_zs by auto
next
  fix u v
  assume "rep1 e = uEdge u v" "to_covering_vertex G (x#T @ zs) = v" 
    and hp_xT_zs: "hp_starting_at G (x#T @ zs) = hp_v1 e"
  moreover hence "to_covering_vertex G (x#T) = v"
    using assms covering_vertex_append by auto
  ultimately have "hp_starting_at G (x#T) = hp_v1 e"
    using assms by (elim hp_starting_at_cases[of G e x T]) auto
  thus ?thesis
    using hp_xT_zs by auto
qed

lemma cost_last_hp_x_hd_hp_y_4_or_5:
  assumes "g1.ugraph_adj_map_invar G"
      and "x \<in> g2.vertices (f G)" "y \<in> g2.vertices (f G)" "\<not> are_vertices_in_He G x y"
  obtains "to_covering_vertex G (x#T\<^sub>x) = to_covering_vertex G (y#T\<^sub>y)" 
      "c G (last (hp_starting_at G (x#T\<^sub>x))) (hd (hp_starting_at G (y#T\<^sub>y))) = 4" 
  | "to_covering_vertex G (x#T\<^sub>x) \<noteq> to_covering_vertex G (y#T\<^sub>y)" 
      "c G (last (hp_starting_at G (x#T\<^sub>x))) (hd (hp_starting_at G (y#T\<^sub>y))) = 5"   
proof -
  obtain e\<^sub>x w\<^sub>x i\<^sub>x e\<^sub>y w\<^sub>y i\<^sub>y where x_case: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)" and y_case: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
    by (cases x; cases y)
  hence vert_x_He: "x \<in> g2.vertices (H\<^sub>e e\<^sub>x)" "e\<^sub>x \<in> g1.uedges G" 
    and vert_y_He: "y \<in> g2.vertices (H\<^sub>e e\<^sub>y)" "e\<^sub>y \<in> g1.uedges G"
    using assms fst_of_vertex_is_edge by auto
  moreover hence rep_xy_neq: "rep1 e\<^sub>x \<noteq> rep1 e\<^sub>y" and "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x" and "isin2 (V\<^sub>H\<^sub>e e\<^sub>y) y"
    using assms vertices_in_He_rep_iff invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  moreover then obtain u\<^sub>x v\<^sub>x u\<^sub>y v\<^sub>y where rep_ex: "rep1 e\<^sub>x = uEdge u\<^sub>x v\<^sub>x" "w\<^sub>x \<in> {u\<^sub>x,v\<^sub>x}"    
    and rep_ey: "rep1 e\<^sub>y = uEdge u\<^sub>y v\<^sub>y" "w\<^sub>y \<in> {u\<^sub>y,v\<^sub>y}"
    using x_case y_case by (elim isin_vertices_of_He_elim2) auto
  ultimately have "set (hp_starting_at G (x#T\<^sub>x)) = g2.vertices (H\<^sub>e e\<^sub>x)"
    and "set (hp_starting_at G (y#T\<^sub>y)) = g2.vertices (H\<^sub>e e\<^sub>y)"
    using assms set_hp_starting_at by blast+
  hence "last (hp_starting_at G (x#T\<^sub>x)) \<in> g2.vertices (H\<^sub>e e\<^sub>x)" and "hd (hp_starting_at G (y#T\<^sub>y)) \<in> g2.vertices (H\<^sub>e e\<^sub>y)"
    using hp_starting_at_non_nil last_in_set hd_in_set by blast+
  hence no_vert_last_x_hd_y: "\<not> are_vertices_in_He G (last (hp_starting_at G (x#T\<^sub>x))) (hd (hp_starting_at G (y#T\<^sub>y)))"
    using assms rep_xy_neq vert_x_He vert_y_He vertices_in_He_rep_iff by blast

  have last_x: "last (hp_starting_at G (x#T\<^sub>x)) = (e\<^sub>x,to_covering_vertex G (x#T\<^sub>x),2)" 
    and hd_y: "hd (hp_starting_at G (y#T\<^sub>y)) = (e\<^sub>y,to_covering_vertex G (y#T\<^sub>y),1)"
    using assms vert_x_He vert_y_He last_hp_starting_at hd_hp_starting_at by auto

  show ?thesis
  proof cases
    assume cov_eq: "to_covering_vertex G (x#T\<^sub>x) = to_covering_vertex G (y#T\<^sub>y)"
    hence "c G (last (hp_starting_at G (x#T\<^sub>x))) (hd (hp_starting_at G (y#T\<^sub>y))) = 4"
      using assms last_x hd_y no_vert_last_x_hd_y rep_xy_neq edge_in_He_are_vertices by (auto simp add: g1.rep_idem)
    thus ?thesis 
      using that cov_eq by auto 
  next
    assume cov_neq: "to_covering_vertex G (x#T\<^sub>x) \<noteq> to_covering_vertex G (y#T\<^sub>y)"
    hence "c G (last (hp_starting_at G (x#T\<^sub>x))) (hd (hp_starting_at G (y#T\<^sub>y))) = 5"
      using assms last_x hd_y no_vert_last_x_hd_y rep_xy_neq edge_in_He_are_vertices by (auto simp add: g1.rep_idem)
    thus ?thesis 
      using that cov_neq by auto
  qed
qed

lemma cost_hp_starting_at2: 
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" and "x \<in> g2.vertices (H\<^sub>e e)"
  shows "cost_of_path (c G) (hp_starting_at G (x#T)) = 11"
  using assms
proof (rule hp_starting_at_cases)
  fix u v
  assume "rep1 e = uEdge u v" "to_covering_vertex G (x#T) = u" "hp_starting_at G (x#T) = hp_u1 e"
  thus ?thesis
    using assms cost_of_hp_u1 g1.rep_of_edge_is_edge by metis
next
  fix u v
  assume "rep1 e = uEdge u v" "to_covering_vertex G (x#T) = v" "hp_starting_at G (x#T) = hp_v1 e"
  thus ?thesis
    using assms cost_of_hp_v1 g1.rep_of_edge_is_edge by metis
qed

lemma replace_hp_non_nil: "T \<noteq> [] \<Longrightarrow> replace_hp G T \<noteq> []"
  using hp_starting_at_non_nil by (cases T) auto

lemma replace_hp_Cons_non_nil: "replace_hp G (x#T) \<noteq> []"
  using hp_starting_at_non_nil by auto

lemma dist_map_inj: "distinct (map h xs) \<Longrightarrow> inj_on h (set xs)"
  by (induction xs) auto

lemma replace_hp_induct_prems:
  assumes "g1.ugraph_adj_map_invar G"  
      and "set es \<subseteq> g1.uedges G" "distinct es" "set (x#T) = \<Union> ((g2.vertices o H\<^sub>e) ` set es)"
  obtains e\<^sub>x where "x \<in> g2.vertices (H\<^sub>e e\<^sub>x)" "set es = set (filter ((\<noteq>) e\<^sub>x) es) \<union> {e\<^sub>x}"
    and "distinct (filter ((\<noteq>) e\<^sub>x) es)" 
    and "set (filter (\<lambda>y. \<not> are_vertices_in_He G x y) T) = \<Union> ((g2.vertices o H\<^sub>e) ` set (filter ((\<noteq>) e\<^sub>x) es))"
proof -
  let ?h="\<lambda>y. \<not> are_vertices_in_He G x y"
  obtain e\<^sub>x where vert_x_He: "x \<in> g2.vertices (H\<^sub>e e\<^sub>x)"
    and ex_in_es: "e\<^sub>x \<in> set es" and ex_is_edge: "e\<^sub>x \<in> g1.uedges G"
    using assms(2,4) by (fastforce simp del: He.simps f.simps)

  have vert_x: "x \<in> g2.vertices (f G)"
    using assms vert_x_He ex_is_edge vertices_f by auto
  hence "\<forall>y. are_vertices_in_He G x y \<longleftrightarrow> y \<in> g2.vertices (H\<^sub>e e\<^sub>x)"
    using assms(1) ex_is_edge vert_x_He are_vertices_in_He_intro are_vertices_in_He_elim2 by blast
  hence set_filter: "set (filter ?h T) = set (x#T) - g2.vertices (H\<^sub>e e\<^sub>x)" (is "set ?fT = _")
    using vert_x_He by auto
  moreover have "set (x#T) = g2.vertices (H\<^sub>e e\<^sub>x) \<union> \<Union> ((g2.vertices o H\<^sub>e) ` set (filter ((\<noteq>) e\<^sub>x) es))"
    using assms ex_in_es by auto
  moreover have "\<And>e. e \<in> set (filter ((\<noteq>) e\<^sub>x) es) \<Longrightarrow> g2.vertices (H\<^sub>e e\<^sub>x) \<inter> g2.vertices (H\<^sub>e e) = {}" 
  proof (intro vertices_of_He_disjoint)
    fix e
    assume "e \<in> set (filter ((\<noteq>) e\<^sub>x) es)"
    hence "e\<^sub>x \<noteq> e" and "rep1 e\<^sub>x = e\<^sub>x" "rep1 e = e"
      using assms ex_in_es g1.rep_of_edge by auto
    thus "rep1 e\<^sub>x \<noteq> rep1 e"
      by auto
  qed
  ultimately have "set ?fT = \<Union> ((g2.vertices o H\<^sub>e) ` set (filter ((\<noteq>) e\<^sub>x) es))" 
    by auto
  moreover have set_es_es': "set es = set (filter ((\<noteq>) e\<^sub>x) es) \<union> {e\<^sub>x}"
    using ex_in_es by (induction es) auto
  moreover have dist_es': "distinct (filter ((\<noteq>) e\<^sub>x) es)"
    using assms by auto
  ultimately show ?thesis
    using that vert_x_He by blast
qed

abbreviation "hp_starting_at' G \<equiv> \<lambda>x. hp_starting_at G [x]"
abbreviation "to_covering_vertex' G \<equiv> \<lambda>x. to_covering_vertex G [x]"
                                      
lemma covering_vertex_hd_hp_starting_at:
  assumes "g1.ugraph_adj_map_invar G" "x \<in> g2.vertices (f G)"
  shows "to_covering_vertex' G (hd (hp_starting_at' G x)) = to_covering_vertex' G x"
proof -
  obtain e where edge_e: "e \<in> g1.uedges G" and vert_x_He: "x \<in> g2.vertices (H\<^sub>e e)"
    using assms vertices_f by auto
  moreover then obtain u v where rep_e: "rep1 e = uEdge u v"
    using assms by (elim g1.uedge_not_refl_elim)
  ultimately have "hd (hp_starting_at' G x) = (e,to_covering_vertex' G x,1)" (is "?hd = _")
    using assms hd_hp_starting_at by auto
  moreover have "to_covering_vertex' G x \<in> set_of_uedge (rep1 e)"
    using assms edge_e vert_x_He covering_vertex_is_vertex by (auto simp add: set_of_uedge_def)
  moreover have "set_of_uedge (rep1 e) = {u,v}"
    using rep_e by (auto simp add: set_of_uedge_def)
  ultimately show "to_covering_vertex' G ?hd = to_covering_vertex' G x"
    using assms edge_e rep_e covering_vertex_of_corner by auto
qed

lemma concat_order_for_replace_hp_and_vc_of_tour:
  assumes "g1.ugraph_adj_map_invar G" "set es \<subseteq> g1.uedges G" 
      and "distinct es" "set T = \<Union> ((g2.vertices o H\<^sub>e) ` set es)"
  obtains xs where "set xs \<subseteq> set T" "distinct xs" "length xs = length es" 
    and "set es = (\<lambda>(e,_,_). e) ` set xs" "set xs \<subseteq> g2.vertices (f G)"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
    and "replace_hp G T = concat (map (hp_starting_at' G) xs)"
  using assms
proof (induction G T arbitrary: es thesis rule: replace_hp.induct[case_names Nil Cons])
  case (Nil G)
  moreover have "\<And>e. g2.vertices (H\<^sub>e e) \<noteq> {}"
    using vertices_of_He_non_empty by blast
  moreover hence "es = []"
    using Nil(5) by auto
  ultimately show ?case 
    by auto 
next
  case (Cons G x T)
  let ?h="\<lambda>y. \<not> are_vertices_in_He G x y"
  obtain e\<^sub>x where vert_x_He: "x \<in> g2.vertices (H\<^sub>e e\<^sub>x)" 
    and set_es_es': "set es = set (filter ((\<noteq>) e\<^sub>x) es) \<union> {e\<^sub>x}"
    and dist_es': "distinct (filter ((\<noteq>) e\<^sub>x) es)" 
    and "set (filter ?h T) = \<Union> ((g2.vertices o H\<^sub>e) ` set (filter ((\<noteq>) e\<^sub>x) es))"
    using Cons by (elim replace_hp_induct_prems)
  moreover hence edge_ex: "e\<^sub>x \<in> g1.uedges G" and "set (filter ((\<noteq>) e\<^sub>x) es) \<subseteq> g1.uedges G"
    using Cons(4) by blast+
  moreover hence vert_x: "x \<in> g2.vertices (f G)"
    using Cons(3) vert_x_He vertices_f by (auto simp del: He.simps f.simps)
  ultimately obtain xs where xs_subset: "set xs \<subseteq> set (filter ?h T)" 
    and dist_xs: "distinct xs" 
    and len_xs: "length xs = length (filter ((\<noteq>) e\<^sub>x) es)" 
    and map_xs: "set (filter ((\<noteq>) e\<^sub>x) es) = (\<lambda>(e,_,_). e) ` set xs" 
    and vert_xs: "set xs \<subseteq> g2.vertices (f G)"
    and no_vert_xs: "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
    and rhp_fT: "replace_hp G (filter ?h T) = concat (map (hp_starting_at' G) xs)"
    using Cons(3) by (elim Cons.IH) blast+

  obtain x' where hp_x': "hp_starting_at' G x' = hp_starting_at G (x#T)" and vert_x'_He: "x' \<in> g2.vertices (H\<^sub>e e\<^sub>x)"
  proof -
    let ?x'="hd (hp_starting_at G (x#T))"
    have [simp]: "?x' = (e\<^sub>x,to_covering_vertex G (x#T),1)"
      using Cons(3) edge_ex vert_x_He hd_hp_starting_at by auto
    have "to_covering_vertex G (x#T) \<in> set_of_uedge (rep1 e\<^sub>x)"
      using Cons(3) vert_x_He edge_ex by (intro covering_vertex_is_vertex)
    hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) ?x'"
      using edge_ex by (cases "rep1 e\<^sub>x") 
        (auto intro!: isin_vertices_of_He_intro2 simp add: set_of_uedge_def g1.rep_of_edge simp del: vertices_of_He.simps)
    hence "?x' \<in> g2.vertices (H\<^sub>e e\<^sub>x)"
      using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
    moreover have "hp_starting_at' G ?x' = hp_starting_at G (x#T)" 
      using Cons(3) edge_ex vert_x_He hp_starting_at_corner by auto
    ultimately show ?thesis
      using that by blast
  qed
  hence vert_x': "x' \<in> g2.vertices (f G)"
    using Cons(3) edge_ex vertices_f by auto

  have "e\<^sub>x \<in> set es"
    using set_es_es' by auto
  hence x'_in_xT: "x' \<in> set (x#T)"
    using Cons(6) vert_x'_He by auto

  have "are_vertices_in_He G x x'" 
    using edge_ex vert_x_He vert_x'_He vertices_in_He_rep_iff[OF Cons(3), of e\<^sub>x] by auto
  hence vert_x'y_iff: "\<And>y. are_vertices_in_He G x' y \<longleftrightarrow> are_vertices_in_He G x y"
    using Cons(3) are_vertices_in_He_sym are_vertices_in_He_trans by blast
  
  have "replace_hp G (x#T) = concat (map (hp_starting_at' G) (x'#xs))"
    using hp_x' rhp_fT by auto
  moreover have "set (x'#xs) \<subseteq> set (x#T)"
    using x'_in_xT xs_subset by auto
  moreover have vert_xxs: "set (x'#xs) \<subseteq> g2.vertices (f G)"
    using vert_x' vert_xs by auto
  moreover have "distinct (x'#xs)"
    using dist_xs xs_subset vert_x'y_iff are_vertices_in_He_refl[OF Cons(3) vert_x'] by fastforce
  moreover have "(\<lambda>(e,_,_). e) x' = e\<^sub>x"
  proof -
    have "isin2 (V\<^sub>H\<^sub>e e\<^sub>x) x'"
      using vert_x'_He invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
    moreover have "rep1 e\<^sub>x = e\<^sub>x"
      using edge_ex by (auto simp add: g1.rep_of_edge)
    ultimately show ?thesis
      using isin_vertices_of_He_elim2 by fastforce
  qed
  moreover hence map_xxs: "set es = (\<lambda>(e,_,_). e) ` set (x'#xs)"
    using set_es_es' map_xs by auto
  moreover have len_xxs: "length (x'#xs) = length es"
  proof -
    have "length es = card (set es)"
      using Cons(5) distinct_card[symmetric] by auto
    also have "... = card (set (filter ((\<noteq>) e\<^sub>x) es) \<union> {e\<^sub>x})"
      using set_es_es' by auto
    also have "... = length (filter ((\<noteq>) e\<^sub>x) es) + 1"
      using dist_es' distinct_card[of "filter ((\<noteq>) e\<^sub>x) es"] by auto
    also have "... = length xs + 1"
      using len_xs by auto
    finally show ?thesis
      by auto
  qed
  moreover have "\<And>y z. y \<in> set (x'#xs) \<Longrightarrow> z \<in> set (x'#xs) \<Longrightarrow> y \<noteq> z \<Longrightarrow> \<not> are_vertices_in_He G y z"
  proof -
    fix y z
    assume y_in_xxs: "y \<in> set (x'#xs)" and z_in_xxs: "z \<in> set (x'#xs)" and yz_neq: "y \<noteq> z"
    then consider "y = x'" "z \<in> set xs" | "y \<in> set xs" "z = x'" | "y \<in> set xs" "z \<in> set xs"
      by auto
    thus "\<not> are_vertices_in_He G y z"
    proof cases
      assume "y = x'" "z \<in> set xs"
      thus ?thesis 
        using xs_subset vert_x'y_iff by auto
    next
      assume "y \<in> set xs" "z = x'" 
      hence "\<not> are_vertices_in_He G z y"
        using xs_subset vert_x'y_iff by auto
      thus ?thesis 
        using Cons(3) are_vertices_in_He_sym by blast
    next
      assume "y \<in> set xs" "z \<in> set xs"
      thus ?thesis 
        using no_vert_xs yz_neq by auto
    qed
  qed
  ultimately show ?case 
    using Cons by blast
qed

lemma filter_vertices_concat_hp:
  assumes "g1.ugraph_adj_map_invar G" and "set xs \<subseteq> g2.vertices (f G)" "\<And>y. y \<in> set xs \<Longrightarrow> \<not> are_vertices_in_He G x y"
  shows "filter (\<lambda>y. \<not> are_vertices_in_He G x y) (concat (map (hp_starting_at' G) xs)) = concat (map (hp_starting_at' G) xs)"
    (is "filter ?f _ = _")
  using assms
proof (induction xs)
  case (Cons y xs)
  hence "\<not> are_vertices_in_He G x y"
    by auto
  moreover obtain e where "e \<in> g1.uedges G" "y \<in> g2.vertices (H\<^sub>e e)"
    using Cons(2,3) vertices_f by auto
  moreover hence "\<And>z. z \<in> set (hp_starting_at' G y) \<Longrightarrow> are_vertices_in_He G z y"
    using assms(1) are_vertices_in_He set_hp_starting_at by blast
  ultimately have "\<And>z. z \<in> set (hp_starting_at' G y) \<Longrightarrow> \<not> are_vertices_in_He G x z"
    using assms are_vertices_in_He_trans by blast
  thus ?case 
    using Cons by auto
qed auto

lemma vc_of_tour_concat_hp:
  assumes "g1.ugraph_adj_map_invar G" 
    and "distinct xs" "set xs \<subseteq> g2.vertices (f G)" 
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
  shows "vc_of_tour G (concat (map (hp_starting_at' G) xs)) = g1.set_of_list (map (to_covering_vertex' G) (rev xs))"
  using assms
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then obtain e where vert_x_He: "x \<in> g2.vertices (H\<^sub>e e)" and edge_e: "e \<in> g1.uedges G"
    using vertices_f by auto
  hence "\<And>y. y \<in> set (hp_starting_at' G x) \<Longrightarrow> are_vertices_in_He G x y"
    using assms(1) are_vertices_in_He set_hp_starting_at by blast
  moreover hence vert_hdxx: "are_vertices_in_He G (hd (hp_starting_at' G x)) x"
    using hp_starting_at_non_nil are_vertices_in_He_sym[OF Cons(2)] 
    by (auto simp del: are_vertices_in_He.simps hp_starting_at.simps)
  ultimately have vert_hdxy: 
    "\<And>y. y \<in> set (hp_starting_at' G x) \<Longrightarrow> are_vertices_in_He G (hd (hp_starting_at' G x)) y"
    using Cons are_vertices_in_He_trans by blast

  have "\<And>y. y \<in> set xs \<Longrightarrow> x \<noteq> y"
    using Cons by auto
  hence "\<And>y. y \<in> set xs \<Longrightarrow> \<not> are_vertices_in_He G x y"
    using Cons by auto
  hence no_vert_hdxy: "\<And>y. y \<in> set xs \<Longrightarrow> \<not> are_vertices_in_He G (hd (hp_starting_at' G x)) y"
    using Cons(2) vert_hdxx are_vertices_in_He_sym are_vertices_in_He_trans by blast

  let ?f="\<lambda>y. \<not> are_vertices_in_He G (hd (hp_starting_at' G x)) y"

  obtain x' hp where hpx: "hp_starting_at' G x = x'#hp"
    using hp_starting_at_non_nil by (cases "hp_starting_at' G x") auto
  hence hd_hpx: "hd (hp_starting_at' G x) = x'" and "x' \<in> g2.vertices (H\<^sub>e e)"
    using set_hp_starting_at[OF Cons(2) edge_e vert_x_He, where T="[]"] hd_in_set[OF hp_starting_at_non_nil] by auto
  moreover hence cov_x'_eq_cov_x: "to_covering_vertex' G x' = to_covering_vertex' G x"
    and "x' = (e,to_covering_vertex' G x,1)"
    using Cons edge_e vert_x_He covering_vertex_hd_hp_starting_at[of G x] hd_hp_starting_at[where T="[]"] by auto
  ultimately have cov_x'_app: "to_covering_vertex G (x'#hp @ concat (map (hp_starting_at' G) xs)) = to_covering_vertex' G x"
    using Cons(2) edge_e covering_vertex_of_corner by auto             
  
  have "vc_of_tour G (concat (map (hp_starting_at' G) (x#xs))) = vc_of_tour G (x'#hp @ concat (map (hp_starting_at' G) xs))"
    using hpx by auto
  also have "... = insert1 (to_covering_vertex G (x'#hp @ concat (map (hp_starting_at' G) xs))) 
    (vc_of_tour G (filter ?f (hp @ concat (map (hp_starting_at' G) xs))))"
    using hd_hpx by auto
  also have "... = insert1 (to_covering_vertex' G x) (vc_of_tour G (filter ?f (hp @ concat (map (hp_starting_at' G) xs))))"
    using cov_x'_app by auto
  also have "... = insert1 (to_covering_vertex' G x) (vc_of_tour G (filter ?f (concat (map (hp_starting_at' G) xs))))"
    using hpx vert_hdxy by auto
  also have "... = insert1 (to_covering_vertex' G x) (vc_of_tour G (concat (map (hp_starting_at' G) xs)))"
    using Cons no_vert_hdxy filter_vertices_concat_hp by auto
  also have "... = insert1 (to_covering_vertex' G x) (g1.set_of_list (map (to_covering_vertex' G) (rev xs)))"
    using Cons by auto
  also have "... = g1.set_of_list (map (to_covering_vertex' G) (rev (x#xs)))"
    by simp
  finally show ?case 
    by auto
qed

lemma hc_len_gr2:
  assumes "g1.ugraph_adj_map_invar G" "card (g1.uedges G) > 0" and "g2.is_hc_Adj (f G) T"
  shows "length T > 2"
proof -
  have "finite (g1.uedges G)"
    using assms by auto
  hence edge_exists: "\<exists>e. e \<in> g1.uedges G"
    using assms(2) all_not_in_conv by fastforce
  then obtain e where edge_e: "e \<in> g1.uedges G"
    by auto
  moreover then obtain u\<^sub>1 v\<^sub>1 where "rep1 e = uEdge u\<^sub>1 v\<^sub>1" "u\<^sub>1 \<noteq> v\<^sub>1"
    using assms by (elim g1.uedge_not_refl_elim)
  ultimately have "g2.vertices (H\<^sub>e e) \<subseteq> g2.vertices (f G)"
    using assms vertices_f by (auto simp del: f.simps) 
  moreover have "card (g2.vertices (H\<^sub>e e)) = 12"
    using assms edge_e card_vertices_of_He by auto
  moreover have "finite (g2.vertices (f G))"
    using assms finite_vertices_f by auto
  ultimately have "card (g2.vertices (f G)) \<ge> 12"
    using card_mono by metis
  moreover have "distinct (tl T)" "g2.vertices (f G) = set (tl T)"
    using assms by (auto elim!: g2.is_hc_AdjE)
  ultimately have "length (tl T) > 2"
    using distinct_card[of "tl T"] by auto
  thus ?thesis
    by auto
qed

lemma rotate_tour_hc_elim:
  defines "h \<equiv> \<lambda>(e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2). rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
  assumes "g1.ugraph_adj_map_invar G" "card (g1.uedges G) > 1" and "g2.is_hc_Adj (f G) T" 
  obtains x y T' where "rotate_tour h T = x#y#T'" "\<not> are_vertices_in_He G x y"
proof -
  let ?h'="\<lambda>(e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2::'v1 uedge,w\<^sub>2::'v1,i\<^sub>2::'nat). rep1 e\<^sub>1 = rep1 e\<^sub>2"
  have "finite (g1.uedges G)" and "card (g1.uedges G) \<ge> 2"
    using assms by auto
  then obtain e\<^sub>1 e\<^sub>2 where edge_e1_e2: "e\<^sub>1 \<in> g1.uedges G" "e\<^sub>2 \<in> g1.uedges G" and "e\<^sub>1 \<noteq> e\<^sub>2"
    using finite_card_geq2 by blast
  moreover then obtain u\<^sub>1 v\<^sub>1 u\<^sub>2 v\<^sub>2 where "e\<^sub>1 = uEdge u\<^sub>1 v\<^sub>1" "e\<^sub>2 = uEdge u\<^sub>2 v\<^sub>2"
    by (cases e\<^sub>1; cases e\<^sub>2)
  ultimately have "(e\<^sub>1,u\<^sub>1,1) \<in> g2.vertices (H\<^sub>e e\<^sub>1)" "(e\<^sub>2,u\<^sub>2,1) \<in> g2.vertices (H\<^sub>e e\<^sub>2)"
    and "(e\<^sub>1,u\<^sub>1,1) \<noteq> (e\<^sub>2,u\<^sub>2,1)" and "\<not> ?h' (e\<^sub>1,u\<^sub>1,1) (e\<^sub>2,u\<^sub>2,1)"
    using isin_vertices_of_He_intro2 invar_vertices_of_He vertices_of_He
    by (auto intro!: isin_vertices_of_He_intro2 simp add: g1.rep_of_edge g2.set_specs simp del: vertices_of_He.simps)
  moreover hence "(e\<^sub>1,u\<^sub>1,1) \<in> g2.vertices (f G)" "(e\<^sub>2,u\<^sub>2,1) \<in> g2.vertices (f G)"
    using assms edge_e1_e2 vertices_f by auto
  moreover have "set (tl T) = g2.vertices (f G)"
    using assms by (auto elim: g2.is_hc_AdjE)
  moreover hence "g2.vertices (f G) \<subseteq> set T"
    using set_tl_subset by fastforce
  ultimately obtain x y where "x \<in> set T" "y \<in> set T" "x \<noteq> y" "\<not> ?h' x y"
    by blast
  hence "cost_of_path (\<lambda>x y. if \<not> ?h' x y then (1::nat) else 0) T > 0"
    by (intro rotate_tour_invariant_intro) auto
  moreover have "\<And>x y. \<not> ?h' x y \<longleftrightarrow> h x y"
    unfolding h_def by auto
  ultimately have rot_T_invar: "cost_of_path (\<lambda>x y. if h x y then (1::nat) else 0) T > 0"
    by auto 

  have "length T > 2"
    using assms hc_len_gr2 by auto
  hence "length (rotate_tour h T) \<ge> 2"
    using length_rotate_tour[of h T] by auto
  then obtain x y T' where rot_T: "rotate_tour h T = x#y#T'"
    by (elim list_len_geq2_elim)
  hence hxy: "h x y"
    using rot_T_invar not_hd_snd_rotate_tour[of h T] by blast
  moreover have "x \<in> g2.vertices (f G)" and "y \<in> g2.vertices (f G)"
  proof -
    have "hd T = last T" and "g2.vertices (f G) = set (tl T)"
      using assms by (auto elim: g2.is_hc_AdjE simp add: g2.hd_path_betw g2.last_path_betw)
    moreover hence "hd (rotate_tour h T) = last (rotate_tour h T)" and "set (tl (rotate_tour h T)) = set (tl T)"
      using rotate_tour_hd_eq_last set_tl_rotate_tour by blast+
    ultimately show "x \<in> g2.vertices (f G)" "y \<in> g2.vertices (f G)"
      using rot_T by fastforce+
  qed
  moreover obtain e\<^sub>x w\<^sub>x i\<^sub>x e\<^sub>y w\<^sub>y i\<^sub>y where [simp]: "x = (e\<^sub>x,w\<^sub>x,i\<^sub>x)" and [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"
    using assms fst_of_vertex_is_edge by (cases x; cases y) 
  moreover have "e\<^sub>x \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e\<^sub>x)" and "e\<^sub>y \<in> g1.uedges G" "y \<in> g2.vertices (H\<^sub>e e\<^sub>y)"
    using assms calculation fst_of_vertex_is_edge by blast+
  ultimately have "\<not> are_vertices_in_He G x y"
    unfolding h_def using assms vertices_in_He_rep_iff by blast
  thus ?thesis
    using that rot_T by auto
qed

lemma concat_order_for_shorten_tour_and_g:
  assumes "g1.ugraph_adj_map_invar G" "card (g1.uedges G) > 1" and "g2.is_hc_Adj (f G) T"
  obtains xs where "xs \<noteq> []" "distinct xs" "g1.uedges G = (\<lambda>(e,_,_). e) ` set xs" 
    and "length xs = card (g1.uedges G)" "set xs \<subseteq> g2.vertices (f G)"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
    and "shorten_tour G T = last (hp_starting_at' G (last xs))#concat (map (hp_starting_at' G) xs)" 
    and "g G T = g1.set_of_list (map (to_covering_vertex' G) (rev xs))"
  using assms(1)
proof (rule fold4.fold_uedgesE)
  let ?fst3="\<lambda>(x,_,_). x"
  let ?snd3="\<lambda>(_,x,_). x"
  let ?f="\<lambda>(e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2). rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"

  fix es
  obtain x y T' where rot_T: "rotate_tour ?f T = x#y#T'" and no_vert_xy: "\<not> are_vertices_in_He G x y"
    using assms by (elim rotate_tour_hc_elim)
  moreover have set_tlT: "set (tl T) = g2.vertices (f G)" and "hd T = last T"
    using assms by (auto elim: g2.is_hc_AdjE simp add: g2.hd_path_betw g2.last_path_betw)
  moreover hence "hd (rotate_tour ?f T) = last (rotate_tour ?f T)"
    and set_tl_rot_T: "set (tl (rotate_tour ?f T)) = set (tl T)"
    using rotate_tour_hd_eq_last set_tl_rotate_tour by blast+
  ultimately have "x \<in> set (tl T)" and "y \<in> set (tl T)"
    by fastforce+
  hence vert_x: "x \<in> g2.vertices (f G)" and vert_y: "y \<in> g2.vertices (f G)"
    using set_tlT by auto

  let ?h="\<lambda>z. \<not> are_vertices_in_He G y z"

  assume dist_es: "distinct es" and set_es: "set es = g1.uedges G"
  moreover hence set_yT': "set (y#T') = \<Union> ((g2.vertices \<circ> H\<^sub>e) ` set es)"
    using assms(1) rot_T set_tlT set_tl_rot_T vertices_f by auto
  ultimately obtain e\<^sub>y where vert_y_He: "y \<in> g2.vertices (H\<^sub>e e\<^sub>y)" 
    and set_es_fes: "set es = set (filter ((\<noteq>) e\<^sub>y) es) \<union> {e\<^sub>y}"
    and dist_es': "distinct (filter ((\<noteq>) e\<^sub>y) es)" 
    and "set (filter ?h T') = \<Union> ((g2.vertices o H\<^sub>e) ` set (filter ((\<noteq>) e\<^sub>y) es))"
    using assms by (elim replace_hp_induct_prems) blast+
  moreover hence edge_ey: "e\<^sub>y \<in> g1.uedges G" and "set (filter ((\<noteq>) e\<^sub>y) es) \<subseteq> g1.uedges G"
    using set_es by blast+
  ultimately obtain xs where xs_subset: "set xs \<subseteq> set (filter ?h T')" 
    and dist_xs: "distinct xs" 
    and len_xs: "length xs = length (filter ((\<noteq>) e\<^sub>y) es)" 
    and set_fes: "set (filter ((\<noteq>) e\<^sub>y) es) = (\<lambda>(e,_,_). e) ` set xs" 
    and vert_xs: "set xs \<subseteq> g2.vertices (f G)"
    and no_vert_xs: "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
    and rhp_yfT: "replace_hp G (filter ?h T') = concat (map (hp_starting_at' G) xs)"
    using assms by (elim concat_order_for_replace_hp_and_vc_of_tour) blast+

  obtain y' where hp_y': "hp_starting_at' G y' = hp_starting_at G (y#T')" and vert_y'_He: "y' \<in> g2.vertices (H\<^sub>e e\<^sub>y)"
  proof -
    let ?y'="hd (hp_starting_at G (y#T'))"
    have [simp]: "?y' = (e\<^sub>y,to_covering_vertex G (y#T'),1)"
      using assms edge_ey vert_y_He hd_hp_starting_at by auto
    have "to_covering_vertex G (y#T') \<in> set_of_uedge (rep1 e\<^sub>y)"
      using assms vert_y_He edge_ey by (intro covering_vertex_is_vertex)
    hence "isin2 (V\<^sub>H\<^sub>e e\<^sub>y) ?y'"
      using edge_ey by (cases "rep1 e\<^sub>y") 
        (auto intro!: isin_vertices_of_He_intro2 simp add: set_of_uedge_def g1.rep_of_edge simp del: vertices_of_He.simps)
    hence "?y' \<in> g2.vertices (H\<^sub>e e\<^sub>y)"
      using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
    moreover have "hp_starting_at' G ?y' = hp_starting_at G (y#T')" 
      using assms edge_ey vert_y_He hp_starting_at_corner by auto
    ultimately show ?thesis
      using that by blast
  qed
  hence vert_y': "y' \<in> g2.vertices (f G)"
    using assms edge_ey vertices_f by auto
  
  have "e\<^sub>y \<in> set es"
    using set_es_fes by auto
  hence y'_in_yT: "y' \<in> set (y#T')"
    using set_yT' vert_y'_He by auto

  have "are_vertices_in_He G y y'" 
    using edge_ey vert_y_He vert_y'_He vertices_in_He_rep_iff[OF assms(1), of e\<^sub>y] by auto
  hence vert_y'z_iff: "\<And>z. are_vertices_in_He G y' z \<longleftrightarrow> are_vertices_in_He G y z"
    using assms(1) are_vertices_in_He_sym are_vertices_in_He_trans by blast

  have dist_xsx: "distinct (xs @ [y'])"
    using dist_xs xs_subset no_vert_xy vert_y'z_iff are_vertices_in_He_refl[OF assms(1) vert_y'] by fastforce
  moreover have set_xsx: "set (xs @ [y']) \<subseteq> g2.vertices (f G)"
    using vert_y' vert_xs by auto
  moreover have "\<And>x. x \<in> set xs \<Longrightarrow> \<not> are_vertices_in_He G y' x"
    using xs_subset vert_y'z_iff by auto
  moreover hence no_vert_xsx:"\<And>x z. x \<in> set (xs @ [y']) \<Longrightarrow> z \<in> set (xs @ [y']) \<Longrightarrow> x \<noteq> z \<Longrightarrow> \<not> are_vertices_in_He G x z"
  proof -
    fix x z
    assume "x \<in> set (xs @ [y'])" "z \<in> set (xs @ [y'])" and yz_neq: "x \<noteq> z"
    then consider "x = y'" "z \<in> set xs" | "x \<in> set xs" "z = y'" | "x \<in> set xs" "z \<in> set xs"
      by auto
    thus "\<not> are_vertices_in_He G x z"
      using xs_subset no_vert_xs yz_neq vert_y'z_iff
    proof cases
      assume "x \<in> set xs" "z = y'"
      hence "\<not> are_vertices_in_He G z x"
        using xs_subset vert_y'z_iff by auto
      thus ?thesis 
        using assms(1) are_vertices_in_He_sym by blast
    qed auto
  qed
  moreover have "shorten_tour G T = last (hp_starting_at' G (last (xs @ [y'])))#concat (map (hp_starting_at' G) (xs @ [y']))"
    using rot_T rhp_yfT hp_y' by auto
  moreover hence "g G T = g1.set_of_list (map (to_covering_vertex' G) (rev (xs @ [y'])))"
    using assms(1) dist_xsx set_xsx no_vert_xsx vc_of_tour_concat_hp[of _ "xs @ [y']"] by auto
  moreover have "xs @ [y'] \<noteq> []" 
    by auto
  moreover have "g1.uedges G = (\<lambda>(e,_,_). e) ` set (xs @ [y'])"
  proof -
    have "(\<lambda>(e,_,_). e) y' = e\<^sub>y"
    proof -
      have "isin2 (V\<^sub>H\<^sub>e e\<^sub>y) y'"
        using vert_y'_He invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
      moreover have "rep1 e\<^sub>y = e\<^sub>y"
        using edge_ey by (auto simp add: g1.rep_of_edge)
      ultimately show ?thesis
        using isin_vertices_of_He_elim2 by fastforce
    qed
    hence "(\<lambda>(e,_,_). e) ` set (xs @ [y']) = (\<lambda>(e,_,_). e) ` set xs \<union> {e\<^sub>y}"
      by auto
    also have "... = set (filter ((\<noteq>) e\<^sub>y) es) \<union> {e\<^sub>y}"
      using set_fes by auto
    also have "... = set es"
      using set_es_fes by auto
    also have "... = g1.uedges G"
      using set_es by auto
    finally show ?thesis 
      by auto
  qed
  moreover have "length (xs @ [y']) = card (g1.uedges G)" 
  proof -
    have "length (xs @ [y']) = length (filter ((\<noteq>) e\<^sub>y) es) + 1"
      using len_xs by auto
    also have "... = card (set (filter ((\<noteq>) e\<^sub>y) es) \<union> {e\<^sub>y})"
      using dist_es' distinct_card[of "filter ((\<noteq>) e\<^sub>y) es"] by auto
    also have "... = card (set es)"
      using set_es_fes by auto
    also have "... = card (g1.uedges G)"
      using set_es by auto
    finally show ?thesis
      by auto
  qed
  ultimately show ?thesis
    using that by blast
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
  obtain xs where xs_non_nil: "xs \<noteq> []" "distinct xs" 
    and xs_edges: "g1.uedges G = (\<lambda>(e,_,_). e) ` set xs" 
    and xs_vert: "set xs \<subseteq> g2.vertices (f G)"
    and g_list: "g G T = g1.set_of_list (map (to_covering_vertex' G) (rev xs))"
    using assms by (elim concat_order_for_shorten_tour_and_g)

  show "\<And>u v. isin1 (\<N>\<^sub>1 G u) v \<Longrightarrow> isin1 (g G T) u \<or> isin1 (g G T) v"
  proof -
    fix u v
    assume "isin1 (\<N>\<^sub>1 G u) v"
    hence rep_e_isin: "rep1 (uEdge u v) \<in> g1.uedges G" (is "?e \<in> _")
      unfolding g1.uedges_def2 by auto
    moreover then obtain w i where x_in_xs: "(?e,w,i) \<in> set xs" (is "?x \<in> _")
      using xs_edges by auto
    moreover hence "?x \<in> g2.vertices (H\<^sub>e ?e)"
      using assms(1) xs_vert fst_of_vertex_is_edge by auto
    ultimately have "to_covering_vertex' G ?x \<in> set_of_uedge (rep1 ?e)"
      using g1.is_rep assms by (intro covering_vertex_is_vertex) (simp add: g1.rep_idem)+
    hence "to_covering_vertex' G ?x \<in> {u,v}"
      using g1.set_of_rep_uedge by (auto simp add: g1.rep_idem)
    hence "u \<in> set (map (to_covering_vertex' G) (rev xs)) \<or> v \<in> set (map (to_covering_vertex' G) (rev xs))"
      using x_in_xs by force
    thus "isin1 (g G T) u \<or> isin1 (g G T) v"
      using g_list g1.isin_set_of_list by auto
  qed
  
  show "\<And>v. isin1 (g G T) v \<Longrightarrow> v \<in> g1.vertices G"
  proof -
    fix v
    assume "isin1 (g G T) v"
    then obtain x where "x \<in> set xs" and cov_x: "to_covering_vertex' G x = v"
      using g_list xs_edges g1.isin_set_of_list by auto
    hence "x \<in> g2.vertices (f G)"
      using xs_vert by auto
    then obtain e w i where [simp]: "x = (e,w,i)" and edge_e: "e \<in> g1.uedges G" "x \<in> g2.vertices (H\<^sub>e e)"
      using assms fst_of_vertex_is_edge by (cases x) auto
    then obtain y z where "e = rep1 (uEdge y z)" and y_isin_Nx: "isin1 (\<N>\<^sub>1 G y) z" and "isin2 (V\<^sub>H\<^sub>e e) x"
      unfolding g1.uedges_def2 using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
    moreover hence "to_covering_vertex' G x \<in> set_of_uedge (rep1 e)"
      using assms edge_e by (intro covering_vertex_is_vertex) 
    ultimately consider "v = y" | "v = z"
      using cov_x g1.set_of_rep_uedge by (auto simp add: g1.rep_idem)
    thus "v \<in> g1.vertices G"
    proof cases
      assume "v = y"
      thus ?thesis
        using y_isin_Nx by (auto intro!: g1.vertices_memberI1)
    next
      assume "v = z"
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
    consider "rep1 (uEdge u x) = uEdge u x" | "rep1 (uEdge u x) = uEdge x u" "u \<noteq> x"
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
  hence vs_non_nil: "vs \<noteq> []" and uv_edge: "\<And>v. v \<in> List.set vs \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G"
    using assms by (auto simp add: g1.set_specs)

  have "List.set ?hp = \<Union> ((g2.vertices o H\<^sub>e) ` {uEdge u v | v. isin1 P v})"
    using assms(1,2,4) by (rule set_hp_for_neighborhood)
  also have "... = \<Union> ((g2.vertices o H\<^sub>e) ` {rep1 (uEdge u v) | v. isin1 P v})"
    by (auto simp add: set_hp_for_neighborhood vertices_of_He_rep_idem simp del: vertices_of_He.simps)
  finally have set_subset_f: "List.set ?hp \<subseteq> g2.vertices (f G)"
    using assms set_vertices_of_H vertices_f by (auto simp del: f.simps vertices_of_He.simps)

  have "?f (hd vs) \<noteq> []"
    using hp_u2_non_nil hp_v2_non_nil vs_non_nil by auto
  moreover have "hp_for_neighborhood u P = concat (map ?f vs)"
    using set_vs_fold fold_concat_map[of ?f vs "[]"] by auto
  ultimately have "?hp \<noteq> []"
    using vs_non_nil by fastforce
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
      using assms cost_x_y_leq5 by blast
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

lemma cost_rotate_tour_eq:
  assumes "g1.ugraph_adj_map_invar G" and "g2.is_hc_Adj (f G) T"
  shows "cost_of_path (c G) (rotate_tour h T) = cost_of_path (c G) T"
  using assms c_sym
proof (intro cost_rotate_tour)
  show "hd T = last T"
    using assms by (elim g2.is_hc_AdjE) (auto simp add: g2.hd_path_betw g2.last_path_betw)
qed auto

find_theorems "c" "hp_starting_at" "hd"

(* lemma cost_x_y_4_or_5:
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
qed *)

lemma cost_concat_map:
  defines "snd3 \<equiv> \<lambda>(_,v,_). v"
  assumes "g1.ugraph_adj_map_invar G" and "distinct xs" "set xs \<subseteq> g2.vertices (f G)" 
      and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
 obtains k where "cost_of_path (\<lambda>x y. if to_covering_vertex' G x \<noteq> to_covering_vertex' G y then (1::nat) else 0) xs = k"
   and "cost_of_path (c G) (concat (map (hp_starting_at' G) xs)) = (\<Sum>x\<leftarrow>xs. cost_of_path (c G) (hp_starting_at' G x)) + (length (tl xs)) * 4 + k"
  using assms
proof (induction xs arbitrary: thesis rule: list012_induct)
  case Nil
  thus ?case by auto
next
  case (Singleton e)
  thus ?case by auto
next
  let ?c="\<lambda>x y. if to_covering_vertex' G x \<noteq> to_covering_vertex' G y then (1::nat) else 0"
  let ?sum="\<lambda>xs. \<Sum>x\<leftarrow>(xs). cost_of_path (c G) (hp_starting_at' G x)"
  case (CCons x y xs)
  then obtain k where cost_eq_k: "cost_of_path ?c (y#xs) = k"
    and cost_concat_eq: "cost_of_path (c G) (concat (map (hp_starting_at' G) (y#xs))) = ?sum (y#xs) + (length (tl (y#xs))) * 4 + k"
    by auto

  have no_vert_xy: "\<not> are_vertices_in_He G x y"
    using CCons by auto
  moreover have vert_x: "x \<in> g2.vertices (f G)" and vert_y: "y \<in> g2.vertices (f G)"
    using CCons by auto
  ultimately consider "to_covering_vertex' G x = to_covering_vertex' G y" "c G (last (hp_starting_at' G x)) (hd (concat (map (hp_starting_at' G) (y#xs)))) = 4" 
    | "to_covering_vertex' G x \<noteq> to_covering_vertex' G y" "c G (last (hp_starting_at' G x)) (hd (concat (map (hp_starting_at' G) (y#xs)))) = 5"
    unfolding snd3_def using assms(2) hp_starting_at_non_nil by (elim cost_last_hp_x_hd_hp_y_4_or_5) auto
  thus ?case
  proof cases
    assume "to_covering_vertex' G x = to_covering_vertex' G y" "c G (last (hp_starting_at' G x)) (hd (concat (map (hp_starting_at' G) (y#xs)))) = 4"
    hence "cost_of_path ?c (x#y#xs) = k"
      and "cost_of_path (c G) (concat (map (hp_starting_at' G) (x#y#xs))) = ?sum (x#y#xs) + (length (tl (x#y#xs))) * 4 + k"
      using cost_concat_eq hp_starting_at_non_nil cost_eq_k by (auto simp add: cost_of_path_append)
    thus ?thesis
      using CCons by auto
  next
    assume "to_covering_vertex' G x \<noteq> to_covering_vertex' G y" "c G (last (hp_starting_at' G x)) (hd (concat (map (hp_starting_at' G) (y#xs)))) = 5"
    hence "cost_of_path ?c (x#y#xs) = k + 1"
      and "cost_of_path (c G) (concat (map (hp_starting_at' G) (x#y#xs))) = ?sum (x#y#xs) + (length (tl (x#y#xs))) * 4 + k + 1"
      using cost_concat_eq hp_starting_at_non_nil cost_eq_k by (auto simp add: cost_of_path_append)
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
  let ?c="\<lambda>x y. if to_covering_vertex' G x \<noteq> to_covering_vertex' G y then (1::nat) else 0"
  let ?neq="\<lambda>x y. if x \<noteq> y then (1::nat) else 0"

  obtain xs where xs_non_nil: "xs \<noteq> []" and dist_xs: "distinct xs" and len_xs: "length xs = card ?E"
    and xs_edges: "g1.uedges G = ?fst3 ` set xs" and xs_vert: "set xs \<subseteq> g2.vertices (f G)"
    and no_vert_xy: "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> are_vertices_in_He G x y"
    and sT_concat: "shorten_tour G T = last (hp_starting_at' G (last xs))#concat (map (hp_starting_at' G) xs)"    
    and g_list: "g G T = g1.set_of_list (map (to_covering_vertex' G) (rev xs))"
    using assms by (elim concat_order_for_shorten_tour_and_g) auto
  moreover hence "concat (map (hp_starting_at' G) xs) \<noteq> []"
    using hp_starting_at_non_nil by (cases xs) auto
  ultimately have cost_sT: "cost_of_path (c G) (shorten_tour G T) 
    = c G (last (hp_starting_at' G (last xs))) (hd (concat (map (hp_starting_at' G) xs))) 
      + cost_of_path (c G) (concat (map (hp_starting_at' G) xs))"
    by (auto simp add: cost_of_path_cons)

  obtain k where cost_es_leq: "cost_of_path ?c xs = k"
    and "cost_of_path (c G) (concat (map (hp_starting_at' G) xs)) 
      = (\<Sum>x\<leftarrow>xs. cost_of_path (c G) (hp_starting_at' G x)) + (length (tl xs)) * 4 + k"
    using assms dist_xs xs_vert no_vert_xy by (elim cost_concat_map)
  moreover have "(\<Sum>x\<leftarrow>xs. cost_of_path (c G) (hp_starting_at' G x)) = length xs * 11"
    using assms xs_vert vertices_f cost_hp_starting_at2 by (intro sum_list_const) (auto simp del: f.simps He.simps)
  ultimately have "cost_of_path (c G) (concat (map (hp_starting_at' G) xs)) 
    = length xs * 11 + (length (tl xs) + 1) * 4 + k - (4::int)"
    by auto
  also have "... = length xs * 11 + (length xs) * 4 + k - (4::int)"
    using xs_non_nil by auto
  finally have cost_concat: "cost_of_path (c G) (concat (map (hp_starting_at' G) xs)) = 15 * length xs + k - (4::int)"
    by auto

  have "set1 (g G T) = to_covering_vertex' G ` set xs"
    using g_list g1.set_of_list by auto
  hence [simp]: "card1 (g G T) = card (to_covering_vertex' G ` set xs)"
    using assms by auto
  moreover have "card1 OPT\<^sub>V\<^sub>C \<le> card1 (g G T)"
    using assms g_is_vc by (auto elim!: g1.is_min_vc_AdjE)
  moreover hence "card1 (g G T) > 1"
    using assms by auto
  ultimately have "card (to_covering_vertex' G ` set xs) > 1"
    by auto

  have "?neq (to_covering_vertex' G (last xs)) (to_covering_vertex' G (hd xs)) = ?c (last xs) (hd xs)"
    by auto
  moreover have "last (map (to_covering_vertex' G) xs) = to_covering_vertex' G (last xs)"
    using xs_non_nil by (intro last_map)
  moreover have "hd (map (to_covering_vertex' G) xs) = to_covering_vertex' G (hd xs)"
    using xs_non_nil by (intro hd_map)
  moreover have "cost_of_path ?neq (map (to_covering_vertex' G) xs) = cost_of_path ?c xs"
    by (induction xs rule: list012_induct) auto
  ultimately have cost_map_eq: "cost_of_path ?neq (map (to_covering_vertex' G) xs) 
    + ?neq (last (map (to_covering_vertex' G) xs)) (hd (map (to_covering_vertex' G) xs)) 
      = cost_of_path ?c xs + ?c (last xs) (hd xs)"
    by auto

  have "card (to_covering_vertex' G ` set xs) = card (set (map (to_covering_vertex' G) xs))"
    by auto
  also have "... \<le> cost_of_path ?neq (map (to_covering_vertex' G) xs) 
    + ?neq (last (map (to_covering_vertex' G) xs)) (hd (map (to_covering_vertex' G) xs))"
    using \<open>card (to_covering_vertex' G ` set xs) > 1\<close> by (intro card_leq_cycle_cost_adj) auto
  also have "... = cost_of_path ?c xs + ?c (last xs) (hd xs)"
    using cost_map_eq by auto
  finally have card_es_leq: "card (to_covering_vertex' G ` set xs) \<le> cost_of_path ?c xs + ?c (last xs) (hd xs)"
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
  ultimately consider 
    "to_covering_vertex' G (last xs) = to_covering_vertex' G (hd xs)" 
      "c G (last (hp_starting_at' G (last xs))) (hd (concat (map (hp_starting_at' G) xs))) = 4" 
  | "to_covering_vertex' G (last xs) \<noteq> to_covering_vertex' G (hd xs)" 
      "c G (last (hp_starting_at' G (last xs))) (hd (concat (map (hp_starting_at' G) xs))) = 5"
    using assms(1) xs_split hp_starting_at_non_nil by (elim cost_last_hp_x_hd_hp_y_4_or_5[of _ y x]) auto
  thus ?thesis
  proof cases
    assume "to_covering_vertex' G (last xs) = to_covering_vertex' G (hd xs)" 
      and "c G (last (hp_starting_at' G (last xs))) (hd (concat (map (hp_starting_at' G) xs))) = 4" 
    hence "15 * int (card ?E) + k \<le> cost_of_path (c G) (shorten_tour G T)" and "card1 (g G T) \<le> k"
      using len_xs cost_concat cost_sT card_es_leq cost_es_leq by (auto simp del: g.simps)
    thus ?thesis
      using that by blast
  next
    assume "to_covering_vertex' G (last xs) \<noteq> to_covering_vertex' G (hd xs)"
      and "c G (last (hp_starting_at' G (last xs))) (hd (concat (map (hp_starting_at' G) xs))) = 5"
    hence "15 * int (card ?E) + k + 1 \<le> cost_of_path (c G) (shorten_tour G T)" and "card1 (g G T) \<le> k + 1"
      using len_xs cost_concat cost_sT card_es_leq cost_es_leq by (auto simp del: g.simps)
    thus ?thesis
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
    using assms g2.path_non_nil by (auto elim!: g2.is_hc_AdjE simp add: g2.hd_path_betw g2.last_path_betw)
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

lemma cost_path_geq_len:
  assumes "g1.ugraph_adj_map_invar G" "distinct_adj xs"
  shows "cost_of_path (c G) xs \<ge> int (length xs) - 1"
  using assms  
proof (induction xs rule: list012_induct)
  case (CCons x y xs)
  thus ?case 
    using c_geq1[of G x y] by auto
qed auto

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
    finally show ?thesis .
  qed auto
qed auto

function dropWhile_schema where
  "dropWhile_schema h [] = []"
| "dropWhile_schema h (x#xs) = (if h x then dropWhile_schema h (dropWhile (Not o h) (dropWhile h xs)) else [])"
by pat_completeness auto
termination dropWhile_schema
  using len_drop_drop_less by (relation "measure (\<lambda>(h,xs). length xs)") auto

lemmas dropWhile_induct = dropWhile_schema.induct[case_names Nil DropWhile]

lemma cost_filter_leq_aux:
  fixes G x
  defines "h \<equiv> \<lambda>y. \<not> are_vertices_in_He G x y"
  assumes "g1.ugraph_adj_map_invar G" and "ys\<^sub>1 \<noteq> []" "xs\<^sub>1 \<noteq> []"
    and "distinct (ys\<^sub>1 @ xs\<^sub>1 @ ys\<^sub>2)" "set (ys\<^sub>1 @ xs\<^sub>1 @ ys\<^sub>2) \<subseteq> g2.vertices (f G)"
    and "\<And>z. z \<in> set ys\<^sub>1 \<Longrightarrow> h z" "\<And>z. z \<in> set xs\<^sub>1 \<Longrightarrow> \<not> h z" "ys\<^sub>2 \<noteq> [] \<Longrightarrow> h (hd ys\<^sub>2)"
  shows "cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1 @ ys\<^sub>2) \<ge> cost_of_path (c G) (filter h (ys\<^sub>1 @ xs\<^sub>1 @ ys\<^sub>2)) + length (filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1 @ ys\<^sub>2)) + 2"
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
  hence "cost_of_path (c G) (filter h (ys\<^sub>1 @ xs\<^sub>1)) + length (filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1)) + 3 
    = cost_of_path (c G) ys\<^sub>1 + length xs\<^sub>1 + 3"
    by auto
  also have "... \<le> cost_of_path (c G) ys\<^sub>1 + cost_of_path (c G) xs\<^sub>1 + 4"
    using cost_xs_geq by auto
  also have "... \<le> cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) (hd xs\<^sub>1) + cost_of_path (c G) xs\<^sub>1"
    using c_last_xs_y by auto
  also have "... = cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1)"
    using Nil by (auto simp add: cost_of_path_append[of ys\<^sub>1 xs\<^sub>1,symmetric])
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

  have "\<not> are_vertices_in_He G x (last ys\<^sub>1)" and "are_vertices_in_He G x (hd xs\<^sub>1)" 
    and "are_vertices_in_He G x (last xs\<^sub>1)" and "\<not> are_vertices_in_He G x (hd (y\<^sub>2#ys\<^sub>2))" 
    using DropWhile(3-4,7-9) by auto
  hence no_vert_x1_y2: "\<not> are_vertices_in_He G (last xs\<^sub>1) (hd (y\<^sub>2#ys\<^sub>2))" 
    and no_vert_y1_x1: "\<not> are_vertices_in_He G (last ys\<^sub>1) (hd xs\<^sub>1)"
    using DropWhile(2) are_vertices_in_He_sym are_vertices_in_He_trans by blast+

  show ?case 
  proof (cases ?xs\<^sub>2)
    case Nil
    hence "\<And>z. z \<in> set ys\<^sub>2 \<Longrightarrow> h z"
      by (induction ys\<^sub>2) (auto split: if_splits)
    hence "filter h (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2) = ys\<^sub>1 @ y\<^sub>2#ys\<^sub>2" and "filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2) = xs\<^sub>1"
      using DropWhile(7-9) by (auto simp add: h_def)
    hence "cost_of_path (c G) (filter h (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2)) + length (filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1 @  y\<^sub>2#ys\<^sub>2)) + 2 
      = cost_of_path (c G) (ys\<^sub>1 @ y\<^sub>2#ys\<^sub>2) + length xs\<^sub>1 + 2"
      by auto
    also have "... \<le> cost_of_path (c G) (ys\<^sub>1 @ y\<^sub>2#ys\<^sub>2) + cost_of_path (c G) xs\<^sub>1 + 3"
      using cost_xs_geq by auto
    also have "... = cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) (hd (y\<^sub>2#ys\<^sub>2)) + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2) + cost_of_path (c G) xs\<^sub>1 + 3"
      using DropWhile(3) by (subst cost_of_path_append[of ys\<^sub>1 "y\<^sub>2#ys\<^sub>2",symmetric]) auto
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + 5 + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2) + cost_of_path (c G) xs\<^sub>1 + 3"
      using DropWhile(2) cost_x_y_leq5 by auto
    also have "... = cost_of_path (c G) ys\<^sub>1 + 4 + cost_of_path (c G) xs\<^sub>1 + 4 + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2)"
      by auto
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) (hd xs\<^sub>1) + cost_of_path (c G) xs\<^sub>1 + 4 + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2)"
      using DropWhile(2) no_vert_y1_x1 cost_x_y_geq4 by auto
    also have "... = cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1) + 4 + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2)"
      using DropWhile(3,4) by (subst cost_of_path_append[of ys\<^sub>1 xs\<^sub>1,symmetric]) auto
    also have "... \<le> cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1) + c G (last xs\<^sub>1) (hd (y\<^sub>2#ys\<^sub>2)) + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2)"
      using DropWhile(2) no_vert_x1_y2 cost_x_y_geq4 by auto
    also have "... = cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1) + c G (last (ys\<^sub>1 @ xs\<^sub>1)) (hd (y\<^sub>2#ys\<^sub>2)) + cost_of_path (c G) (y\<^sub>2#ys\<^sub>2)"
      using DropWhile(4) by auto
    also have "... = cost_of_path (c G) ((ys\<^sub>1 @ xs\<^sub>1) @ y\<^sub>2#ys\<^sub>2)"
      using DropWhile(3,4) by (subst cost_of_path_append[of "ys\<^sub>1 @ xs\<^sub>1",symmetric]) auto
    finally show ?thesis 
      by (auto simp add: h_def)
  next
    case (Cons x\<^sub>2 xs\<^sub>2)
    moreover hence "?xs\<^sub>2 \<noteq> []"
      by auto
    moreover have "y\<^sub>2#?ys\<^sub>2 \<noteq> []"
      by auto
    moreover have hy2: "h y\<^sub>2"
      using DropWhile(9) by (auto simp add: h_def)
    moreover have "distinct ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      using DropWhile(5) by auto
    moreover have "set ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3) \<subseteq> g2.vertices (f G)"
      using DropWhile(6) by auto 
    moreover have "\<And>z. z \<in> set (y\<^sub>2#?ys\<^sub>2) \<Longrightarrow> h z"
      using calculation(4) DropWhile(7) set_takeWhileD[of _ h ys\<^sub>2] by auto
    moreover have "\<And>z. z \<in> set ?xs\<^sub>2 \<Longrightarrow> \<not> h z"
      using Cons set_takeWhileD[of _ "Not o h" "dropWhile h ys\<^sub>2"] by auto
    moreover have "?ys\<^sub>3 \<noteq> [] \<Longrightarrow> h (hd ?ys\<^sub>3)"
      using hd_dropWhile[of "Not o h" "dropWhile h ys\<^sub>2"] by auto
    ultimately have cost_IH_geq: "cost_of_path (c G) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3) \<ge> 
      cost_of_path (c G) (filter h ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)) + length (filter (Not o h) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)) + 2"
      using DropWhile(2) h_def by (intro DropWhile(1)[folded h_def]) blast+

    have dist_adj_xs1: "distinct_adj xs\<^sub>1"
      using DropWhile(5) distinct_distinct_adj by auto

    have "cost_of_path (c G) (filter h (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2)) + length (filter (Not o h) (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2)) + 2 
      = cost_of_path (c G) (ys\<^sub>1 @ filter h ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)) + length (xs\<^sub>1 @ filter (Not o h) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)) + 2"
      using DropWhile(7-9) by (auto simp add: h_def)
    also have "... = cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) y\<^sub>2 + cost_of_path (c G) (filter h ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3))
      + length xs\<^sub>1 + length (filter (Not o h) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3)) + 2"
      using hy2 DropWhile(3) by (subst cost_of_path_append) auto
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) y\<^sub>2 + cost_of_path (c G) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3) + length xs\<^sub>1"
      using cost_IH_geq by auto
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + 5 + cost_of_path (c G) ((y\<^sub>2#?ys\<^sub>2) @ ?xs\<^sub>2 @ ?ys\<^sub>3) + length xs\<^sub>1"
      using DropWhile(2) cost_x_y_leq5 by auto
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + 4 + int (length xs\<^sub>1) - 1 + 4 + cost_of_path (c G) (y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      by auto
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + 4 + cost_of_path (c G) xs\<^sub>1 + 4 + cost_of_path (c G) (y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      using DropWhile(2) dist_adj_xs1 cost_path_geq_len[of _ xs\<^sub>1] by fastforce
    also have "... \<le> cost_of_path (c G) ys\<^sub>1 + c G (last ys\<^sub>1) (hd xs\<^sub>1) + cost_of_path (c G) xs\<^sub>1 + 4 + cost_of_path (c G) (y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      using DropWhile(2) no_vert_y1_x1 cost_x_y_geq4 by auto 
    also have "... = cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1) + 4 + cost_of_path (c G) (y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      using DropWhile(3,4) by (auto simp add: cost_of_path_append[of ys\<^sub>1 xs\<^sub>1,symmetric])
    also have "... \<le> cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1) + c G (last xs\<^sub>1) (hd (y\<^sub>2#?ys\<^sub>2)) + cost_of_path (c G) (y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
       using DropWhile(2) no_vert_x1_y2 cost_x_y_geq4 by auto
    also have "... = cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3)"
      using DropWhile(3,4) cost_of_path_append[of "ys\<^sub>1 @ xs\<^sub>1" "y\<^sub>2#?ys\<^sub>2 @ ?xs\<^sub>2 @ ?ys\<^sub>3",symmetric] by auto
    also have "... = cost_of_path (c G) (ys\<^sub>1 @ xs\<^sub>1 @ y\<^sub>2#ys\<^sub>2)"
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
  shows "cost_of_path (c G) ys \<ge> cost_of_path (c G) (filter h ys) + length (filter (Not o h) ys) + 2"
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
  ultimately have "cost_of_path (c G) (?ys\<^sub>1 @ ?xs\<^sub>1 @ ?ys\<^sub>2) \<ge> 
    cost_of_path (c G) (filter h (?ys\<^sub>1 @ ?xs\<^sub>1 @ ?ys\<^sub>2)) + length (filter (Not o h) (?ys\<^sub>1 @ ?xs\<^sub>1 @ ?ys\<^sub>2)) + 2"
    unfolding h_def using assms(2) by (intro cost_filter_leq_aux)
  thus ?thesis
    by auto
qed

lemma path_ui_v1_len_odd:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" and "e = rep1 (uEdge u v)" "u \<noteq> v"
      and "g2.path_betw (H\<^sub>e e) x xs (e,v,1)" "x = (e,u,i\<^sub>1) \<or> x = (e,v,1)" "i\<^sub>1 \<noteq> 1"
  shows "odd (length xs)"
  using g2.path_non_nil[OF assms(5)] assms
proof (induction xs arbitrary: x i\<^sub>1 rule: even_induct_non_nil)
  case (Singleton x)
  thus ?case 
    by (auto elim: g2.path_betw.cases intro: g2.path_betw.intros)
next
  case (Doubleton x' y)
  hence [simp]: "x' = x" and [simp]: "y = (e,v,1)" and "isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y"
    by (auto elim: g2.path_betw.cases intro: g2.path_betw.intros simp del: He.simps)
  moreover have "isin2 (V\<^sub>H\<^sub>e e) x"
    using g2.path_vertices[OF Doubleton(5)] invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately have x_isin_Ny: "isin2 (\<N>\<^sub>H\<^sub>e y) x"
    using neighborhood_He neighborhood_in_He_sym by metis
  then consider "x = (e,v,3)" | "x = (e,v,4)" 
    using Doubleton neighborhood_in_He_def2 neighborhood_in_He_def2[of v u]
    by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
  thus ?case
    using Doubleton by cases auto
next
  case (CCons x' y z xs)
  have [simp]: "x' = x" and "isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y" "g2.path_betw (H\<^sub>e e) y (y#z#xs) (e,v,1)"
    using CCons(6) by (auto elim: g2.path_betw.cases intro: g2.path_betw.intros simp del: He.simps)
  moreover hence "isin2 (\<N>\<^sub>2 (H\<^sub>e e) y) z" and path_zxs: "g2.path_betw (H\<^sub>e e) z (z#xs) (e,v,1)"
    by (auto elim: g2.path_betw.cases intro: g2.path_betw.intros simp del: He.simps)
  moreover hence last_zxs: "last (z#xs) = (e,v,1)"
    using g2.last_path_betw by blast
  moreover have vert_x: "isin2 (V\<^sub>H\<^sub>e e) x" and "isin2 (V\<^sub>H\<^sub>e e) y"
    using g2.path_vertices[OF CCons(6)] invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  ultimately have y_isin_Nx: "isin2 (\<N>\<^sub>H\<^sub>e x) y" and z_isin_Ny: "isin2 (\<N>\<^sub>H\<^sub>e y) z" 
    using neighborhood_He by auto

  have "x = (e,u,i\<^sub>1) \<Longrightarrow> i\<^sub>1 \<in> {1..6}"
    using vert_x by (auto elim!: isin_vertices_of_He_elim2 simp del: vertices_of_He.simps)
  then consider "x = (e,v,1)" | "x = (e,u,2)" | "x = (e,u,3)" | "x = (e,u,4)" | "x = (e,u,5)" | "x = (e,u,6)"
    using CCons by force
  thus ?case
  proof cases
    assume "x = (e,v,1)"
    then consider "y = (e,v,3)" "z = (e,u,2)" | "y = (e,v,3)" "z = (e,v,1)" 
      | "y = (e,v,4)" "z = (e,u,6)" | "y = (e,v,4)" "z = (e,u,5)" | "y = (e,v,4)" "z = (e,v,1)"
      using CCons y_isin_Nx z_isin_Ny neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
    thus ?thesis
      using CCons path_zxs by cases auto
  next
    assume "x = (e,u,2)"
    then consider "y = (e,v,3)" "z = (e,v,1)" | "y = (e,v,3)" "z = (e,u,2)" 
      | "y = (e,v,5)" "z = (e,u,2)" | "y = (e,v,5)" "z = (e,u,4)" | "y = (e,v,5)" "z = (e,u,6)"
      using CCons y_isin_Nx z_isin_Ny neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
    thus ?thesis
      using CCons path_zxs by cases auto
  next
    assume "x = (e,u,3)"
    then consider "y = (e,u,1)" "z = (e,u,3)" | "y = (e,u,1)" "z = (e,u,4)"
      | "y = (e,v,2)" "z = (e,u,3)" | "y = (e,v,2)" "z = (e,u,5)"
      using CCons y_isin_Nx z_isin_Ny neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
    thus ?thesis
      using CCons path_zxs by cases auto
  next
    assume "x = (e,u,4)"
    then consider "y = (e,u,1)" "z = (e,u,3)" | "y = (e,u,1)" "z = (e,u,4)" 
      | "y = (e,v,5)" "z = (e,u,2)" | "y = (e,v,5)" "z = (e,u,4)" | "y = (e,v,5)" "z = (e,u,6)" 
      | "y = (e,v,6)" "z = (e,u,4)" | "y = (e,v,6)" "z = (e,u,5)"
      using CCons y_isin_Nx z_isin_Ny neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
    thus ?thesis
      using CCons path_zxs by cases auto
  next
    assume "x = (e,u,5)"
    then consider "y = (e,v,2)" "z = (e,u,3)" | "y = (e,v,2)" "z = (e,u,5)"
      | "y = (e,v,4)" "z = (e,v,1)" | "y = (e,v,4)" "z = (e,u,5)" | "y = (e,v,4)" "z = (e,u,6)"
      | "y = (e,v,6)" "z = (e,u,4)" | "y = (e,v,6)" "z = (e,u,5)"
      using CCons y_isin_Nx z_isin_Ny neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
    thus ?thesis
      using CCons path_zxs by cases auto
  next
    assume "x = (e,u,6)"
    then consider "y = (e,v,4)" "z = (e,v,1)" | "y = (e,v,4)" "z = (e,u,5)" | "y = (e,v,4)" "z = (e,u,6)"
      | "y = (e,v,5)" "z = (e,u,2)" | "y = (e,v,5)" "z = (e,u,4)" | "y = (e,v,5)" "z = (e,u,6)"
      using CCons y_isin_Nx z_isin_Ny neighborhood_in_He_def2 neighborhood_in_He_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
    thus ?thesis
      using CCons path_zxs by cases auto
  qed
qed

lemma hamiltonian_paths_with_cost_11:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" "rep1 e = uEdge u v" 
      and "set xs = g2.vertices (H\<^sub>e e)" "distinct xs" and "cost_of_path (c G) xs = 11"
  obtains "hd xs = (e,u,1)" "last xs = (e,u,2)"
  | "hd xs = (e,u,1)" "last xs = (e,u,6)"
  | "hd xs = (e,u,2)" "last xs = (e,u,1)"
  | "hd xs = (e,u,2)" "last xs = (e,v,6)"
  | "hd xs = (e,u,6)" "last xs = (e,u,1)"
  | "hd xs = (e,u,6)" "last xs = (e,v,2)"
  | "hd xs = (e,u,6)" "last xs = (e,v,6)"
  | "hd xs = (e,v,1)" "last xs = (e,v,2)"
  | "hd xs = (e,v,1)" "last xs = (e,v,6)"
  | "hd xs = (e,v,2)" "last xs = (e,v,1)"
  | "hd xs = (e,v,2)" "last xs = (e,u,6)"
  | "hd xs = (e,v,6)" "last xs = (e,v,1)"
  | "hd xs = (e,v,6)" "last xs = (e,u,2)"
  | "hd xs = (e,v,6)" "last xs = (e,u,6)"
  sorry

lemma cost_hd_plus_last_leq:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
      and "set (x#xs) = g2.vertices (H\<^sub>e e)" "distinct (x#xs @ ys)" "set ys \<subseteq> g2.vertices (f G)" 
      and "cost_of_path (c G) (x#xs) = 11" and "\<not> are_vertices_in_He G z x" "\<not> are_vertices_in_He G x y" 
  shows "c G z (hd (hp_starting_at G (x#xs @ ys))) + c G (last (hp_starting_at G (x#xs @ ys))) y \<le> c G z x + c G (last (x#xs)) y"
proof (cases z; cases y)
  let ?T="xs @ ys"
  let ?hd_x="hd (hp_starting_at G (x#?T))"
  let ?last_x="last (hp_starting_at G (x#?T))"

  fix e\<^sub>z w\<^sub>z i\<^sub>z e\<^sub>y w\<^sub>y i\<^sub>y
  assume [simp]: "z = (e\<^sub>z,w\<^sub>z,i\<^sub>z)" and [simp]: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)"

  obtain u v where rep_e: "rep1 e = uEdge u v"
    using assms by (elim g1.uedge_not_refl_elim)

  have vert_x_He: "x \<in> g2.vertices (H\<^sub>e e)" and vert_last_x_He: "last (x#xs) \<in> g2.vertices (H\<^sub>e e)"
    using assms last_in_set by auto

  have "\<And>y. y \<in> set (x#xs) \<Longrightarrow> are_vertices_in_He G x y"
    using assms by (intro are_vertices_in_He_intro) auto
  hence tW_xxs: "takeWhile (are_vertices_in_He G x) (x#xs) = x#xs"
    using takeWhile_eq_all_conv[of "are_vertices_in_He G x" "x#xs"] by auto
  hence "takeWhile (are_vertices_in_He G x) ((x#xs) @ ys) = x#xs"
  proof (cases ys)
    case (Cons y ys)
    hence "y \<notin> g2.vertices (H\<^sub>e e)"
      using assms by auto
    moreover obtain e' where "e' \<in> g1.uedges G" "y \<in> g2.vertices (H\<^sub>e e')"
      using assms Cons vertices_f by auto
    ultimately have "\<not> are_vertices_in_He G x y"
      using assms vert_x_He vertices_in_He_rep_iff by (auto simp add: g1.rep_of_edge)
    thus ?thesis 
      using Cons tW_xxs takeWhile_tail[of "are_vertices_in_He G x" y "x#xs"] by auto
  qed auto
  hence last_tW: "last (takeWhile (are_vertices_in_He G x) (x#xs @ ys)) = last (x#xs)"
    by auto

  have "?hd_x \<in> g2.vertices (H\<^sub>e e)"
    using assms vert_x_He set_hp_starting_at hp_starting_at_non_nil hd_in_set by blast
  hence "are_vertices_in_He G ?hd_x x"
    using assms vert_x_He by (intro are_vertices_in_He_intro)
  hence no_vert_z_hd_x: "\<not> are_vertices_in_He G z ?hd_x"
    using assms are_vertices_in_He_trans by blast
  hence "c G z ?hd_x \<ge> 4" "c G z ?hd_x \<le> 5"
    using assms cost_x_y_geq4 cost_x_y_leq5 by blast+
  hence cost_z_hd_x_4or5: "c G z ?hd_x = 4 \<or> c G z ?hd_x = 5"
    by auto

  have "?last_x \<in> g2.vertices (H\<^sub>e e)"
    using assms vert_x_He set_hp_starting_at hp_starting_at_non_nil last_in_set by blast
  hence "are_vertices_in_He G x ?last_x"
    using assms vert_x_He by (intro are_vertices_in_He_intro)
  hence no_vert_last_x_y: "\<not> are_vertices_in_He G ?last_x y"
    using assms are_vertices_in_He_trans by blast
  hence "c G ?last_x y \<ge> 4" "c G ?last_x y \<le> 5"
    using assms cost_x_y_geq4 cost_x_y_leq5 by blast+
  hence cost_last_x_y_4or5: "c G ?last_x y = 4 \<or> c G ?last_x y = 5"
    by auto

  have "c G z x \<ge> 4" "c G z x \<le> 5"
    using assms cost_x_y_geq4 cost_x_y_leq5 by blast+
  hence cost_z_x_4or5: "c G z x = 4 \<or> c G z x = 5"
    by auto

  have "are_vertices_in_He G x (last (x#xs))"
    using assms vert_x_He vert_last_x_He by (intro are_vertices_in_He_intro)
  hence no_vert_last_xxs_y: "\<not> are_vertices_in_He G (last (x#xs)) y"
    using assms are_vertices_in_He_trans by blast
  hence "c G (last (x#xs)) y \<ge> 4" "c G (last (x#xs)) y \<le> 5"
    using assms cost_x_y_geq4 cost_x_y_leq5 by blast+
  hence cost_last_xxs_y_4or5: "c G (last (x#xs)) y = 4 \<or> c G (last (x#xs)) y = 5"
    by auto

  have dist_xxs: "distinct (x#xs)"
    using assms by auto
  show ?thesis
    using assms(1-2) rep_e assms(3) dist_xxs assms(6) 
  proof (rule hamiltonian_paths_with_cost_11)
    assume "hd (x#xs) = (e,u,1)" "last (x#xs) = (e,u,2)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = u"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,u,1)" and "?last_x = (e,u,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G z ?hd_x = 4 \<longleftrightarrow> c G z x = 4"
      and "c G ?last_x y = 4 \<longleftrightarrow> c G (last (x#xs)) y = 4"
      using assms no_vert_z_hd_x no_vert_last_xxs_y no_vert_last_x_y cost_x_y_eq4_iff by auto
    hence "c G z ?hd_x = c G z x" and "c G ?last_x y = c G (last (x#xs)) y"
      using cost_z_x_4or5 cost_z_hd_x_4or5 cost_last_xxs_y_4or5 cost_last_x_y_4or5 by argo+
    thus ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,u,1)" "last (x#xs) = (e,u,6)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = u"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,u,1)" and "?last_x = (e,u,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G z ?hd_x = 4 \<longleftrightarrow> c G z x = 4"
      and "c G (last (x#xs)) y = 5"
      using assms no_vert_z_hd_x no_vert_last_xxs_y edge_in_He_are_vertices cost_x_y_eq4_iff by auto
    moreover hence "c G z ?hd_x = c G z x"
      using cost_z_x_4or5 cost_z_hd_x_4or5 by argo
    moreover have "c G ?last_x y \<le> 5"
      using assms cost_x_y_leq5 by auto
    ultimately show ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,u,2)" "last (x#xs) = (e,u,1)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = u"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,u,1)" and "?last_x = (e,u,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G z ?hd_x = 4 \<longleftrightarrow> c G z x = 4"
      and "c G ?last_x y = 4 \<longleftrightarrow> c G (last (x#xs)) y = 4"
      using assms no_vert_z_hd_x no_vert_last_xxs_y no_vert_last_x_y cost_x_y_eq4_iff by auto
    hence "c G z ?hd_x = c G z x" and "c G ?last_x y = c G (last (x#xs)) y"
      using cost_z_x_4or5 cost_z_hd_x_4or5 cost_last_xxs_y_4or5 cost_last_x_y_4or5 by argo+
    thus ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,u,2)" "last (x#xs) = (e,v,6)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = u"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,u,1)" and "?last_x = (e,u,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G z ?hd_x = 4 \<longleftrightarrow> c G z x = 4"
      and "c G (last (x#xs)) y = 5"
      using assms no_vert_z_hd_x no_vert_last_xxs_y edge_in_He_are_vertices cost_x_y_eq4_iff by auto
    moreover hence "c G z ?hd_x = c G z x"
      using cost_z_x_4or5 cost_z_hd_x_4or5 by argo
    moreover have "c G ?last_x y \<le> 5"
      using assms cost_x_y_leq5 by auto
    ultimately show ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,u,6)" "last (x#xs) = (e,u,1)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = u"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,u,1)" and "?last_x = (e,u,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G ?last_x y = 4 \<longleftrightarrow> c G (last (x#xs)) y = 4"
      and "c G z x = 5"
      using assms no_vert_last_x_y no_vert_last_xxs_y edge_in_He_are_vertices cost_x_y_eq4_iff by auto
    moreover hence "c G ?last_x y = c G (last (x#xs)) y"
      using cost_last_x_y_4or5 cost_last_xxs_y_4or5 by argo
    moreover have "c G z ?hd_x \<le> 5"
      using assms cost_x_y_leq5 by auto
    ultimately show ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,u,6)" "last (x#xs) = (e,v,2)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = v"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,v,1)" and "?last_x = (e,v,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G ?last_x y = 4 \<longleftrightarrow> c G (last (x#xs)) y = 4"
      and "c G z x = 5"
      using assms no_vert_last_x_y no_vert_last_xxs_y edge_in_He_are_vertices cost_x_y_eq4_iff by auto
    moreover hence "c G ?last_x y = c G (last (x#xs)) y"
      using cost_last_x_y_4or5 cost_last_xxs_y_4or5 by argo
    moreover have "c G z ?hd_x \<le> 5"
      using assms cost_x_y_leq5 by auto
    ultimately show ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,u,6)" "last (x#xs) = (e,v,6)"
    hence "c G z x = 5" "c G (last (x#xs)) y = 5"
      using assms no_vert_last_xxs_y edge_in_He_are_vertices by auto
    moreover have "c G z ?hd_x \<le> 5" "c G ?last_x y \<le> 5"
      using assms cost_x_y_leq5 by auto
    ultimately show ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,v,1)" "last (x#xs) = (e,v,2)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = v"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,v,1)" and "?last_x = (e,v,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G z ?hd_x = 4 \<longleftrightarrow> c G z x = 4"
      and "c G ?last_x y = 4 \<longleftrightarrow> c G (last (x#xs)) y = 4"
      using assms no_vert_z_hd_x no_vert_last_xxs_y no_vert_last_x_y cost_x_y_eq4_iff by auto
    hence "c G z ?hd_x = c G z x" and "c G ?last_x y = c G (last (x#xs)) y"
      using cost_z_x_4or5 cost_z_hd_x_4or5 cost_last_xxs_y_4or5 cost_last_x_y_4or5 by argo+
    thus ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,v,1)" "last (x#xs) = (e,v,6)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = v"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,v,1)" and "?last_x = (e,v,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G z ?hd_x = 4 \<longleftrightarrow> c G z x = 4"
      and "c G (last (x#xs)) y = 5"
      using assms no_vert_z_hd_x no_vert_last_xxs_y edge_in_He_are_vertices cost_x_y_eq4_iff by auto
    moreover hence "c G z ?hd_x = c G z x"
      using cost_z_x_4or5 cost_z_hd_x_4or5 by argo
    moreover have "c G ?last_x y \<le> 5"
      using assms cost_x_y_leq5 by auto
    ultimately show ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,v,2)" "last (x#xs) = (e,v,1)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = v"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,v,1)" and "?last_x = (e,v,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G z ?hd_x = 4 \<longleftrightarrow> c G z x = 4"
      and "c G ?last_x y = 4 \<longleftrightarrow> c G (last (x#xs)) y = 4"
      using assms no_vert_z_hd_x no_vert_last_xxs_y no_vert_last_x_y cost_x_y_eq4_iff by auto
    hence "c G z ?hd_x = c G z x" and "c G ?last_x y = c G (last (x#xs)) y"
      using cost_z_x_4or5 cost_z_hd_x_4or5 cost_last_xxs_y_4or5 cost_last_x_y_4or5 by argo+
    thus ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,v,2)" "last (x#xs) = (e,u,6)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = v"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,v,1)" and "?last_x = (e,v,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G z ?hd_x = 4 \<longleftrightarrow> c G z x = 4"
      and "c G (last (x#xs)) y = 5"
      using assms no_vert_z_hd_x no_vert_last_xxs_y edge_in_He_are_vertices cost_x_y_eq4_iff by auto
    moreover hence "c G z ?hd_x = c G z x"
      using cost_z_x_4or5 cost_z_hd_x_4or5 by argo
    moreover have "c G ?last_x y \<le> 5"
      using assms cost_x_y_leq5 by auto
    ultimately show ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,v,6)" "last (x#xs) = (e,v,1)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = v"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,v,1)" and "?last_x = (e,v,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G ?last_x y = 4 \<longleftrightarrow> c G (last (x#xs)) y = 4"
      and "c G z x = 5"
      using assms no_vert_last_x_y no_vert_last_xxs_y edge_in_He_are_vertices cost_x_y_eq4_iff by auto
    moreover hence "c G ?last_x y = c G (last (x#xs)) y"
      using cost_last_x_y_4or5 cost_last_xxs_y_4or5 by argo
    moreover have "c G z ?hd_x \<le> 5"
      using assms cost_x_y_leq5 by auto
    ultimately show ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,v,6)" "last (x#xs) = (e,u,2)"
    moreover hence "to_covering_vertex G (x#xs @ ys) = u"
      using assms(1,2) vert_x_He last_tW by (elim covering_vertex_cases[of G e x "xs @ ys"]) auto
    moreover hence "?hd_x = (e,u,1)" and "?last_x = (e,u,2)"
      using assms vert_x_He hd_hp_starting_at[of G e x] last_hp_starting_at[of G e x] by auto
    ultimately have "c G ?last_x y = 4 \<longleftrightarrow> c G (last (x#xs)) y = 4"
      and "c G z x = 5"
      using assms no_vert_last_x_y no_vert_last_xxs_y edge_in_He_are_vertices cost_x_y_eq4_iff by auto
    moreover hence "c G ?last_x y = c G (last (x#xs)) y"
      using cost_last_x_y_4or5 cost_last_xxs_y_4or5 by argo
    moreover have "c G z ?hd_x \<le> 5"
      using assms cost_x_y_leq5 by auto
    ultimately show ?thesis
      by auto
  next
    assume "hd (x#xs) = (e,v,6)" "last (x#xs) = (e,u,6)"
    hence "c G z x = 5" "c G (last (x#xs)) y = 5"
      using assms no_vert_last_xxs_y edge_in_He_are_vertices by auto
    moreover have "c G z ?hd_x \<le> 5" "c G ?last_x y \<le> 5"
      using assms cost_x_y_leq5 by auto
    ultimately show ?thesis
      by auto
  qed
qed

lemma cost_hd_plus_last_plus1_leq:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G"
      and "set (x#xs) = g2.vertices (H\<^sub>e e)" "distinct (x#xs @ ys)"
      and "\<not> are_vertices_in_He G z x" "\<not> are_vertices_in_He G x y"
  shows "c G z (hd (hp_starting_at G (x#xs @ ys))) + c G (last (hp_starting_at G (x#xs @ ys))) y \<le> c G z x + c G (last (x#xs)) y + 1"
proof (rule ccontr)
  let ?hd_x="hd (hp_starting_at G (x#xs @ ys))"
  let ?last_x="last (hp_starting_at G (x#xs @ ys))"

  obtain e\<^sub>y w\<^sub>y i\<^sub>y e\<^sub>z w\<^sub>z i\<^sub>z where y_case: "y = (e\<^sub>y,w\<^sub>y,i\<^sub>y)" and z_case: "z = (e\<^sub>z,w\<^sub>z,i\<^sub>z)"
    by (cases y; cases z)

  have vert_x_He: "x \<in> g2.vertices (H\<^sub>e e)" and vert_last_x_He: "last (x#xs) \<in> g2.vertices (H\<^sub>e e)"
    using assms last_in_set by auto
  hence "isin2 (V\<^sub>H\<^sub>e e) x" and "isin2 (V\<^sub>H\<^sub>e e) (last (x#xs))"
    using invar_vertices_of_He vertices_of_He by (auto simp add: g2.set_specs)
  then obtain u v w\<^sub>x i\<^sub>x w\<^sub>x' i\<^sub>x'  where rep_e: "rep1 e = uEdge u v" and x_case: "x = (e,w\<^sub>x,i\<^sub>x)"
    and last_xxs_case: "last (x#xs) = (e,w\<^sub>x',i\<^sub>x')" and wx_in: "w\<^sub>x \<in> {u,v}" "w\<^sub>x' \<in> {u,v}"
    using assms by (elim isin_vertices_of_He_elim2) (auto simp add: g1.rep_of_edge)

  have hd_x_case: "?hd_x = (e,to_covering_vertex G (x#xs @ ys),1)"
    and last_x_case: "?last_x = (e,to_covering_vertex G (x#xs @ ys),2)"
    using assms vert_x_He hd_hp_starting_at last_hp_starting_at by auto

  have "?hd_x \<in> g2.vertices (H\<^sub>e e)"
    using assms vert_x_He set_hp_starting_at hp_starting_at_non_nil hd_in_set by blast
  hence "are_vertices_in_He G ?hd_x x"
    using assms vert_x_He by (intro are_vertices_in_He_intro)
  hence no_vert_z_hd_x: "\<not> are_vertices_in_He G z ?hd_x"
    using assms are_vertices_in_He_trans by blast
  hence "c G z ?hd_x \<ge> 4" "c G z ?hd_x \<le> 5"
    using assms cost_x_y_geq4 cost_x_y_leq5 by blast+

  have "?last_x \<in> g2.vertices (H\<^sub>e e)"
    using assms vert_x_He set_hp_starting_at hp_starting_at_non_nil last_in_set by blast
  hence "are_vertices_in_He G x ?last_x"
    using assms vert_x_He by (intro are_vertices_in_He_intro)
  hence no_vert_last_x_y: "\<not> are_vertices_in_He G ?last_x y"
    using assms are_vertices_in_He_trans by blast
  hence "c G ?last_x y \<ge> 4" "c G ?last_x y \<le> 5"
    using assms cost_x_y_geq4 cost_x_y_leq5 by blast+

  have "are_vertices_in_He G x (last (x#xs))"
    using assms vert_x_He vert_last_x_He by (intro are_vertices_in_He_intro)
  hence no_vert_last_xxs_y: "\<not> are_vertices_in_He G (last (x#xs)) y"
    using assms are_vertices_in_He_trans by blast
  hence "c G (last (x#xs)) y \<ge> 4" "c G (last (x#xs)) y \<le> 5"
    using assms cost_x_y_geq4 cost_x_y_leq5 by blast+

  assume "\<not> c G z ?hd_x + c G ?last_x y \<le> c G z x + c G (last (x#xs)) y + 1"
  moreover have "c G z ?hd_x \<ge> 4" "c G z ?hd_x \<le> 5"
    using assms no_vert_z_hd_x cost_x_y_geq4 cost_x_y_leq5 by blast+
  moreover have "c G ?last_x y \<ge> 4" "c G ?last_x y \<le> 5"
    using assms no_vert_last_x_y cost_x_y_geq4 cost_x_y_leq5 by blast+
  moreover have "c G z x \<ge> 4" "c G z x \<le> 5"
    using assms cost_x_y_geq4 cost_x_y_leq5 by blast+
  moreover have "c G (last (x#xs)) y \<ge> 4" "c G (last (x#xs)) y \<le> 5"
    using assms no_vert_last_xxs_y cost_x_y_geq4 cost_x_y_leq5 by blast+
  ultimately have "c G z ?hd_x = 5" "c G ?last_x y = 5" "c G z x = 4" "c G (last (x#xs)) y = 4"
    by linarith+
  hence "rep1 e\<^sub>z \<noteq> rep1 e \<and> w\<^sub>z = w\<^sub>x \<and> (i\<^sub>z = 1 \<or> i\<^sub>z = 2) \<and> (i\<^sub>x = 1 \<or> i\<^sub>x = 2)"
    and "rep1 e \<noteq> rep1 e\<^sub>y \<and> w\<^sub>x' = w\<^sub>y \<and> (i\<^sub>x' = 1 \<or> i\<^sub>x' = 2) \<and> (i\<^sub>y = 1 \<or> i\<^sub>y = 2)"
    and "c G z ?hd_x \<noteq> 4" "c G ?last_x y \<noteq> 4"
    using assms z_case x_case last_xxs_case y_case no_vert_last_xxs_y cost_x_y_eq4_iff by auto
  moreover hence "\<not> (rep1 e\<^sub>z \<noteq> rep1 e \<and> w\<^sub>z = to_covering_vertex G (x#xs @ ys) \<and> (i\<^sub>z = 1 \<or> i\<^sub>z = 2))"
    and "\<not> (rep1 e \<noteq> rep1 e\<^sub>y \<and> to_covering_vertex G (x#xs @ ys) = w\<^sub>y \<and> (i\<^sub>y = 1 \<or> i\<^sub>y = 2))"
    using assms z_case hd_x_case last_x_case y_case no_vert_z_hd_x no_vert_last_x_y cost_x_y_eq4_iff by auto
  moreover hence "rep1 e\<^sub>z = rep1 e \<or> w\<^sub>z \<noteq> to_covering_vertex G (x#xs @ ys) \<or> (i\<^sub>z \<noteq> 1 \<and> i\<^sub>z \<noteq> 2)"
    and "rep1 e = rep1 e\<^sub>y \<or> to_covering_vertex G (x#xs @ ys) \<noteq> w\<^sub>y \<or> (i\<^sub>y \<noteq> 1 \<and> i\<^sub>y \<noteq> 2)"
    by auto
  ultimately have "i\<^sub>x = 1 \<or> i\<^sub>x = 2" "w\<^sub>z = w\<^sub>x" "w\<^sub>x' = w\<^sub>y" "w\<^sub>z \<noteq> to_covering_vertex G (x#xs @ ys)" "to_covering_vertex G (x#xs @ ys) \<noteq> w\<^sub>y"
    by blast+
  moreover hence "to_covering_vertex G (x#xs @ ys) = w\<^sub>x"
    using assms vert_x_He x_case covering_vertex_of_corner by blast
  ultimately show "False"
    by blast
qed

lemma cost_hp_starting_at_prepend_append_leq:
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" 
      and "set (x#xs) = g2.vertices (H\<^sub>e e)" "distinct (x#(xs @ ys))"
      and "ys \<noteq> []" "set ys \<subseteq> g2.vertices (f G)" "\<And>y. y \<in> set ys \<Longrightarrow> \<not> are_vertices_in_He G x y"
      and "z \<in> g2.vertices (f G)" "\<not> are_vertices_in_He G z x"
  shows "cost_of_path (c G) (z#hp_starting_at G (x#xs @ ys) @ ys) \<le> cost_of_path (c G) (z#x#xs @ ys)"
  using assms
proof (cases ys)
  case (Cons y ys')
  let ?hd_x="hd (hp_starting_at G (x#xs @ ys))"
  let ?last_x="last (hp_starting_at G (x#xs @ ys))"

  have vert_x_He: "x \<in> g2.vertices (H\<^sub>e e)" and no_vert_x_y: "\<not> are_vertices_in_He G x y"
    using assms Cons by auto

  have "distinct (x#xs)"
    using assms by auto
  hence "length (x#xs) = 12"
    using assms card_vertices_of_He distinct_card by metis
  moreover have "distinct_adj (x#xs)"
    using assms by (intro distinct_distinct_adj) auto
  ultimately have "cost_of_path (c G) (x#xs) \<ge> 11"
    using assms cost_path_geq_len[of _ "x#xs"] by auto 
  then consider "cost_of_path (c G) (x#xs) = 11" | "cost_of_path (c G) (x#xs) \<ge> 12"
    by linarith
  hence cost_hd_last_leq: 
    "c G z ?hd_x + 11 + c G ?last_x y \<le> c G z x + cost_of_path (c G) (x#xs) + c G (last (x#xs)) y"
  proof cases
    case 1
    moreover hence cost_hd_last_leq: "c G z ?hd_x + c G ?last_x y \<le> c G z x + c G (last (x#xs)) y"
      using assms no_vert_x_y cost_hd_plus_last_leq by auto
    ultimately show ?thesis
      by auto
  next
    case 2
    moreover hence cost_hd_last_leq: "c G z ?hd_x + c G ?last_x y \<le> c G z x + c G (last (x#xs)) y + 1"
      using assms no_vert_x_y cost_hd_plus_last_plus1_leq by auto
    ultimately show ?thesis 
      by auto
  qed

  have "cost_of_path (c G) (z#hp_starting_at G (x#xs @ ys) @ y#ys') 
    = c G z ?hd_x + cost_of_path (c G) (hp_starting_at G (x#xs @ ys)) + c G ?last_x y + cost_of_path (c G) (y#ys')"
    using assms hp_starting_at_non_nil by (auto simp add: cost_of_path_cons cost_of_path_append)
  also have "... \<le> c G z ?hd_x + 11 + c G ?last_x y + cost_of_path (c G) (y#ys')"
    using assms vert_x_He cost_hp_starting_at2[of G e x "xs @ ys"] by auto
  also have "... \<le> c G z x + cost_of_path (c G) (x#xs) + c G (last (x#xs)) y + cost_of_path (c G) (y#ys')"
    using cost_hd_last_leq by auto
  also have "... = c G z x + cost_of_path (c G) ((x#xs) @ y#ys')"
    using assms hp_starting_at_non_nil by (auto simp add: cost_of_path_cons cost_of_path_append)
  also have "... = cost_of_path (c G) (z#x#xs @ y#ys')"
    by auto
  finally show ?thesis
    using Cons by auto
qed auto

lemma cost_replace_hp_step_leq:
  fixes G x
  defines "h \<equiv> \<lambda>y. \<not> are_vertices_in_He G x y"
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" and "x \<in> g2.vertices (H\<^sub>e e)"
      and "distinct (x#T @ zs)" "filter h T @ zs \<noteq> []" "set (x#T) \<subseteq> g2.vertices (f G)" "g2.vertices (H\<^sub>e e) \<subseteq> set (x#T)"
      and "z\<^sub>1 \<in> g2.vertices (f G)" "\<not> are_vertices_in_He G z\<^sub>1 x"
      and "set zs \<subseteq> g2.vertices (f G)" "\<And>y z. y \<in> set (x#T) \<Longrightarrow> z \<in> set zs \<Longrightarrow> \<not> are_vertices_in_He G y z"
  shows "cost_of_path (c G) (z\<^sub>1#hp_starting_at G (x#T) @ filter h T @ zs) \<le> cost_of_path (c G) (z\<^sub>1#x#T @ zs)"
proof -
  let ?xs="takeWhile (Not o h) T"
  let ?ys="dropWhile (Not o h) T"
  have T_split: "T = ?xs @ ?ys"
    by auto
  have set_xs_subset: "set (x#?xs) \<subseteq> g2.vertices (H\<^sub>e e)"
  proof
    fix x'
    assume "x' \<in> set (x#?xs)"
    moreover have "\<And>y. y \<in> set ?xs \<Longrightarrow> \<not> h y"
      using set_takeWhileD[of _ "Not o h" T] by auto
    moreover have "are_vertices_in_He G x x"
      using assms are_vertices_in_He_refl by auto
    ultimately have "are_vertices_in_He G x x'"
      unfolding h_def by (cases "x' = x") auto
    thus "x' \<in> g2.vertices (H\<^sub>e e)"
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

    moreover have "distinct (x#?xs @ ?ys @ zs)"
      using assms T_split append_assoc[of ?xs ?ys zs] by argo
    moreover have "?ys @ zs \<noteq> []"
      using assms by auto
    moreover have "set (?ys @ zs) \<subseteq> g2.vertices (f G)"
      using assms set_dropWhileD[of _ "Not o h" T] by auto
    moreover have "\<And>z. z \<in> set zs \<Longrightarrow> \<not> are_vertices_in_He G x z"
      using assms by auto
    moreover hence no_vert_ys: "\<And>y. y \<in> set (?ys @ zs) \<Longrightarrow> \<not> are_vertices_in_He G x y" 
      using ys_h by (auto simp add: h_def)
    ultimately have "cost_of_path (c G) (z\<^sub>1#hp_starting_at G (x#?xs @ ?ys @ zs) @ ?ys @ zs) \<le> cost_of_path (c G) (z\<^sub>1#x#?xs @ ?ys @ zs)"
      using assms set_xs by (intro cost_hp_starting_at_prepend_append_leq)
    also have "... = cost_of_path (c G) (z\<^sub>1#x#T @ zs)"
      using T_split by (subst append_assoc[of ?xs ?ys,symmetric]) auto
    finally have "cost_of_path (c G) (z\<^sub>1#hp_starting_at G (x#(?xs @ ?ys) @ zs) @ ?ys @ zs) \<le> cost_of_path (c G) (z\<^sub>1#x#T @ zs)"
      using append_assoc[of ?xs ?ys zs] by argo  
    moreover have "hp_starting_at G (x#T @ zs) = hp_starting_at G (x#T)"
      using assms by (intro hp_starting_at_append) auto
    ultimately show ?thesis
      using filter_T_eq_ys by auto
  next
    assume vert_no_subset_ys: "\<not> g2.vertices (H\<^sub>e e) \<subseteq> set (x#?xs)"
    hence "\<exists>z \<in> set T. z \<notin> set (x#?xs)"
      using assms(8) by auto
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

    have vert_x: "x \<in> g2.vertices (f G)"
      using assms by auto

    have "set (hp_starting_at G (x#T)) = g2.vertices (H\<^sub>e e)"
      using assms set_hp_starting_at by auto
    hence "last (hp_starting_at G (x#T)) \<in> g2.vertices (H\<^sub>e e)"
      using hp_starting_at_non_nil last_in_set by blast
    hence "are_vertices_in_He G x (last (hp_starting_at G (x#T)))"
      using assms by (intro are_vertices_in_He_intro) auto
    hence no_vert_lasthpx_y: "\<not> are_vertices_in_He G (last (hp_starting_at G (x#T))) y"
      using assms no_vert_x_y are_vertices_in_He_trans by blast

    have "last ?ys \<in> set (x#T)"
      using ys_non_nil set_dropWhileD[OF last_in_set, of "Not o h" T] by auto
    hence no_vert_lastys_zs: "\<And>z. z \<in> set zs \<Longrightarrow> \<not> are_vertices_in_He G (last ?ys) z"  
      using assms by auto

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

    have "set T \<inter> set zs = {}"
      using assms by auto
    hence "set ?ys \<inter> set zs = {}"
      using assms set_dropWhileD[of _ "Not o h" T] by blast
    hence "distinct (?ys @ zs)"
      using assms by auto
    moreover have "set (?ys @ zs) \<subseteq> g2.vertices (f G)"
      using assms set_dropWhileD[of _ "Not o h" T] by auto
    moreover have "set (x#T) = set (x#?xs) \<union> set ?ys"
      using T_split by (metis Cons_eq_appendI set_append)
    moreover hence "g2.vertices (H\<^sub>e e) \<inter> set ?ys \<noteq> {}"
      using assms(8) vert_no_subset_ys by auto
    moreover hence "\<exists>x \<in> set (?ys @ zs). \<not> h x"
      using vert_noth_iff by auto
    moreover have hd_ys: "h (hd (?ys @ zs))"
      using ys_non_nil hd_dropWhile[of "Not o h"] by auto
    ultimately have "cost_of_path (c G) (?ys @ zs) \<ge> cost_of_path (c G) (filter h (?ys @ zs)) + int (length (filter (Not o h) (?ys @ zs))) + 2"
      using assms(2) unfolding h_def by (intro cost_filter_leq)
    moreover have "filter h (?ys @ zs) = filter h ?ys @ zs" and "filter (Not o h) (?ys @ zs) = filter (Not o h) ?ys"
      using assms by (auto simp add: h_def)
    ultimately have cost_yfilter_ys_zs: "cost_of_path (c G) (y#filter h ys @ zs) \<le> cost_of_path (c G) (?ys @ zs) - int (length (filter (Not o h) ?ys)) - 2"
      using ys hd_ys by auto

    have "cost_of_path (c G) (z\<^sub>1#hp_starting_at G (x#T) @ filter h T @ zs) = cost_of_path (c G) (z\<^sub>1#hp_starting_at G (x#T) @ y#filter h ys @ zs)"
      using filter_T by auto
    also have "... = c G z\<^sub>1 (hd (hp_starting_at G (x#T))) + cost_of_path (c G) (hp_starting_at G (x#T)) 
      + c G (last (hp_starting_at G (x#T))) y + cost_of_path (c G) (y#filter h ys @ zs)"
      using hp_starting_at_non_nil by (auto simp add: cost_of_path_cons cost_of_path_append)
    also have "... \<le> 5 + cost_of_path (c G) (hp_starting_at G (x#T)) + c G (last (hp_starting_at G (x#T))) y 
      + cost_of_path (c G) (y#filter h ys @ zs)"
      using assms cost_x_y_leq5 by auto
    also have "... = 5 + 11 + c G (last (hp_starting_at G (x#T))) y + cost_of_path (c G) (y#filter h ys @ zs)"
      using assms vertices_f cost_hp_starting_at2[of G e x T] by auto 
    also have "... \<le> 5 + 11 + 5 + cost_of_path (c G) (y#filter h ys @ zs)"
      using assms cost_x_y_leq5 by auto
    also have "... \<le> 5 + 11 + 5 + cost_of_path (c G) (?ys @ zs) - int (length (filter (Not o h) ?ys)) - 2"
      using cost_yfilter_ys_zs by auto
    also have "... = 4 + 11 + 4 + cost_of_path (c G) (?ys @ zs) - int (length (filter (Not o h) ?ys))"
      by auto
    also have "... = 4 + 12 - int (length (filter (Not o h) ?ys)) - 1 + 4 + cost_of_path (c G) (?ys @ zs)"
      by auto
    also have "... = 4 + length (x#?xs) - 1 + 4 + cost_of_path (c G) (?ys @ zs)"
      using len_xs by auto
    also have "... \<le> 4 + cost_of_path (c G) (x#?xs) + 4 + cost_of_path (c G) (?ys @ zs)"
      using assms dist_adj_xs cost_path_geq_len[of _ "x#?xs"] by auto
    also have "... \<le> c G z\<^sub>1 x + cost_of_path (c G) (x#?xs) + 4 + cost_of_path (c G) (?ys @ zs)"
      using assms cost_x_y_geq4 by auto
    also have "... \<le> cost_of_path (c G) (z\<^sub>1#x#?xs) + c G (last (x#?xs)) y + cost_of_path (c G) (?ys @ zs)"
      using assms no_vert_last_xs_y cost_x_y_geq4 by auto
    also have "... = cost_of_path (c G) (z\<^sub>1#x#?xs) + c G (last (x#?xs)) y + cost_of_path (c G) (y#ys @ zs)"
      using ys by auto
    also have "... = cost_of_path (c G) ((z\<^sub>1#x#?xs) @ (y#ys @ zs))"
      by (subst cost_of_path_append) auto
    also have "... = cost_of_path (c G) (z\<^sub>1#x#(?xs @ ?ys) @ zs)"
      using ys by auto
    also have "... = cost_of_path (c G) (z\<^sub>1#x#T @ zs)"
      by auto
    finally show ?thesis
      by auto
  qed
qed

lemma replace_hp_tour_leq:
  assumes "g1.ugraph_adj_map_invar G" 
      and "distinct T" "set T \<subseteq> g2.vertices (f G)" 
      and "\<exists>es. set es \<subseteq> g1.uedges G \<and> set T = \<Union> ((g2.vertices \<circ> H\<^sub>e) ` set es)"
      and "z\<^sub>1 \<in> g2.vertices (f G)" "T \<noteq> [] \<Longrightarrow> \<not> are_vertices_in_He G z\<^sub>1 (hd T)" 
      and "z\<^sub>2 \<in> g2.vertices (f G)" "\<And>y. y \<in> set T \<Longrightarrow> \<not> are_vertices_in_He G y z\<^sub>2"
  shows "cost_of_path (c G) (z\<^sub>1#replace_hp G T @ [z\<^sub>2]) \<le> cost_of_path (c G) (z\<^sub>1#T @ [z\<^sub>2])"
  using assms
proof (induction G T arbitrary: z\<^sub>1 rule: replace_hp.induct[case_names Nil Cons])
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
  hence set_fT: "\<exists>es. set es \<subseteq> g1.uedges G \<and> set ?fT = \<Union> ((g2.vertices \<circ> H\<^sub>e) ` set es)"
    using edges_es filter_is_subset[of "(\<noteq>) e" es] by blast

  have "z\<^sub>2 \<notin> set (x#T)"
    using Cons_T(2,4,9) are_vertices_in_He_refl by blast
  moreover have "g2.vertices (H\<^sub>e e) \<subseteq> set (x#T)"
    using set_xT e_in_es by auto
  moreover have "\<not> are_vertices_in_He G z\<^sub>1 x"
    using Cons_T(7) by auto
  ultimately have cost_hpx_filter_leq:
    "cost_of_path (c G) (z\<^sub>1#hp_starting_at G (x#T) @ ?fT @ [z\<^sub>2]) \<le> cost_of_path (c G) (z\<^sub>1#x#T @ [z\<^sub>2])"
    using Cons_T(2-4,6,8-9) edge_e vert_x_He by (intro cost_replace_hp_step_leq) auto

  show ?case
  proof (cases ?fT)
    case Nil
    thus ?thesis 
      using cost_hpx_filter_leq by auto
  next
    case Cons_fT: (Cons y fT)

    have "set (hp_starting_at G (x#T)) = g2.vertices (H\<^sub>e e)"
      using Cons_T(2) edge_e vert_x_He set_hp_starting_at by auto
    hence vert_lastx_He: "last (hp_starting_at G (x#T)) \<in> g2.vertices (H\<^sub>e e)"
      using hp_starting_at_non_nil last_in_set by blast
    hence vert_x_lastx: "are_vertices_in_He G x (last (hp_starting_at G (x#T)))"
      using Cons_T(2) edge_e vert_x_He by (intro are_vertices_in_He_intro) auto
    moreover have "\<not> are_vertices_in_He G x y"
      using Cons_eq_filterD[OF Cons_fT[symmetric]] by auto
    ultimately have "\<not> are_vertices_in_He G (last (hp_starting_at G (x#T))) y"
      using Cons_T(2) are_vertices_in_He_trans by blast

    have "\<not> are_vertices_in_He G x (hd ?fT)"
      using Cons_eq_filterD[OF Cons_fT[symmetric]] by auto
    hence "?fT \<noteq> [] \<Longrightarrow> \<not> are_vertices_in_He G (last (hp_starting_at G (x#T))) (hd ?fT)"
      using Cons_T(2) vert_x_lastx are_vertices_in_He_trans by blast
    moreover have "last (hp_starting_at G (x#T)) \<in> g2.vertices (f G)"
      using Cons_T(2) vert_lastx_He edge_e vertices_f by auto
    moreover have "distinct ?fT"
      using Cons_T by auto
    moreover have "set ?fT \<subseteq> g2.vertices (f G)"
      using Cons_T filter_is_subset[of ?h T] by auto
    moreover have "\<And>y. y \<in> set ?fT \<Longrightarrow> \<not> are_vertices_in_He G y z\<^sub>2"
      using Cons_T(9) by auto
    ultimately have cost_IH_leq: 
      "cost_of_path (c G) (last (hp_starting_at G (x#T))#replace_hp G ?fT @ [z\<^sub>2]) 
        \<le> cost_of_path (c G) (last (hp_starting_at G (x#T))#?fT @ [z\<^sub>2])"
      using Cons_T(2,8) set_fT by (intro Cons_T(1))

    have "cost_of_path (c G) (z\<^sub>1#replace_hp G (x#T) @ [z\<^sub>2]) = cost_of_path (c G) (z\<^sub>1#hp_starting_at G (x#T) @ replace_hp G ?fT @ [z\<^sub>2])"
      by auto
    also have "... =  cost_of_path (c G) (z\<^sub>1#hp_starting_at G (x#T)) + cost_of_path (c G) (last (hp_starting_at G (x#T))#replace_hp G ?fT @ [z\<^sub>2])"
      using Cons_fT hp_starting_at_non_nil replace_hp_Cons_non_nil by (simp add: cost_of_path_cons cost_of_path_append)
    also have "... \<le> cost_of_path (c G) (z\<^sub>1#hp_starting_at G (x#T)) + cost_of_path (c G) (last (hp_starting_at G (x#T))#?fT @ [z\<^sub>2])"
      using cost_IH_leq by auto
    also have "... = cost_of_path (c G) ((z\<^sub>1#hp_starting_at G (x#T)) @ ?fT @ [z\<^sub>2])"
      using hp_starting_at_non_nil cost_of_path_append_last[of "z\<^sub>1#hp_starting_at G (x#T)",symmetric] by auto
    also have "... \<le> cost_of_path (c G) (z\<^sub>1#x#T @ [z\<^sub>2])"
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
  let ?h\<^sub>1="\<lambda>(e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2). rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"

  have "finite (g1.uedges G)"
    using assms by auto
  hence edge_exists: "\<exists>e. e \<in> g1.uedges G"
    using assms(2) all_not_in_conv by fastforce

  have hdT_eq_lastT: "hd T = last T" and "distinct (tl T)" and set_tl_T: "set (tl T) = g2.vertices (f G)"
    using assms by (auto elim: g2.is_hc_AdjE simp add: g2.hd_path_betw g2.last_path_betw)
  moreover obtain x y T' where rot_T_CCons: "rotate_tour ?h\<^sub>1 T = x#y#T'" and no_vert_xy: "\<not> are_vertices_in_He G x y"
    using assms by (elim rotate_tour_hc_elim)
  ultimately have "hd (rotate_tour ?h\<^sub>1 T) = last (rotate_tour ?h\<^sub>1 T)"
    and dist_tl_rot_T: "distinct (tl (rotate_tour ?h\<^sub>1 T))" 
    and set_tl_rot_T: "set (tl (rotate_tour ?h\<^sub>1 T)) = set (tl T)"
    using rotate_tour_hd_eq_last distinct_rotate_tour set_tl_rotate_tour by blast+
  moreover hence vert_y: "y \<in> g2.vertices (f G)"
    using set_tl_T rot_T_CCons by auto 
  moreover hence "are_vertices_in_He G y y"
    using assms are_vertices_in_He_refl by auto
  ultimately have dist_yT': "distinct (y#T')" and T'_non_nil: "T' \<noteq> []" and last_T': "last T' = x"
    using rot_T_CCons no_vert_xy by auto
  moreover hence vert_x: "x \<in> g2.vertices (f G)"
    using set_tl_T rot_T_CCons set_tl_rot_T by fastforce
  moreover have "\<not> are_vertices_in_He G y x"
    using assms no_vert_xy are_vertices_in_He_sym by blast
  ultimately have last_fT': "last (filter (\<lambda>z. \<not> are_vertices_in_He G y z) T') = x" (is "last (filter ?h\<^sub>2 _) = _")
    and fT'_non_nil: "filter (\<lambda>z. \<not> are_vertices_in_He G y z) T' \<noteq> []"
    using filter_empty_conv[of ?h\<^sub>2 T'] by (auto intro!: last_filter)

  obtain e\<^sub>y where vert_y_He: "y \<in> g2.vertices (H\<^sub>e e\<^sub>y)" and edge_ey: "e\<^sub>y \<in> g1.uedges G"
    using assms vert_y vertices_f by auto
  moreover hence vert_hdy_He: "hd (hp_starting_at G (y#T')) \<in> g2.vertices (H\<^sub>e e\<^sub>y)" 
    and vert_lasty_He: "last (hp_starting_at G (y#T')) \<in> g2.vertices (H\<^sub>e e\<^sub>y)"
    using assms set_hp_starting_at hp_starting_at_non_nil hd_in_set last_in_set by blast+
  moreover have set_yT': "set (y#T') = g2.vertices (f G)"
    using rot_T_CCons set_tl_rot_T set_tl_T by simp
  ultimately have vert_ey_subset_yT': "g2.vertices (H\<^sub>e e\<^sub>y) \<subseteq> set (y#T')"
    using assms vertices_f by auto

  have "distinct (tl (rotate_tour ?h\<^sub>1 T))"
    using dist_tl_rot_T by auto
  hence "distinct (filter ?h\<^sub>2 T')"
    using dist_yT' by auto
  moreover have "\<exists>es. set es \<subseteq> g1.uedges G \<and> set (filter ?h\<^sub>2 T') = \<Union> ((g2.vertices \<circ> H\<^sub>e) ` set es)"
    using assms(1)
  proof (rule fold1.fold_uedgesE)
    fix es
    assume "distinct es" and set_es: "set es = g1.uedges G"
    moreover hence "set (y#T') = \<Union> ((g2.vertices \<circ> H\<^sub>e) ` set es)"
      using assms(1) set_yT' vertices_f by auto
    ultimately obtain e\<^sub>y where "set es = set (filter ((\<noteq>) e\<^sub>y) es) \<union> {e\<^sub>y}"
      and "set (filter ?h\<^sub>2 T') = \<Union> ((g2.vertices o H\<^sub>e) ` set (filter ((\<noteq>) e\<^sub>y) es))"
      using assms by (elim replace_hp_induct_prems) blast+
    thus ?thesis
      using set_es by blast
  qed
  moreover have "set (filter ?h\<^sub>2 T') \<subseteq> g2.vertices (f G)"
    using set_tl_T rot_T_CCons set_tl_rot_T by auto
  moreover have "last (hp_starting_at G (y#T')) \<in> g2.vertices (f G)"
    using assms edge_ey vert_lasty_He vertices_f by auto 
  moreover have "hd (hp_starting_at G (y#T')) \<in> g2.vertices (f G)"
    using assms edge_ey vert_hdy_He vertices_f by auto 
  moreover have "filter ?h\<^sub>2 T' \<noteq> [] \<Longrightarrow> \<not> are_vertices_in_He G (last (hp_starting_at G (y#T'))) (hd (filter ?h\<^sub>2 T'))"
  proof -
    assume "filter ?h\<^sub>2 T' \<noteq> []"
    hence "hd (filter ?h\<^sub>2 T') \<in> set (filter ?h\<^sub>2 T')"
      using hd_in_set by blast
    hence "\<not> are_vertices_in_He G y (hd (filter ?h\<^sub>2 T'))"
      by auto
    moreover have "are_vertices_in_He G y (last (hp_starting_at G (y#T')))"
      using assms edge_ey vert_y_He vert_lasty_He by (intro are_vertices_in_He_intro)
    ultimately show "\<not> are_vertices_in_He G (last (hp_starting_at G (y#T'))) (hd (filter ?h\<^sub>2 T'))"
      using assms are_vertices_in_He_trans by blast
  qed
  moreover have "\<And>z. z \<in> set (filter ?h\<^sub>2 T') \<Longrightarrow> \<not> are_vertices_in_He G z (hd (hp_starting_at G (y#T')))"
  proof -
    fix z
    assume "z \<in> set (filter ?h\<^sub>2 T')"
    hence "\<not> are_vertices_in_He G y z"
      by auto
    moreover have "are_vertices_in_He G y (hd (hp_starting_at G (y#T')))"
      using assms edge_ey vert_y_He vert_hdy_He by (intro are_vertices_in_He_intro)
    ultimately show "\<not> are_vertices_in_He G z (hd (hp_starting_at G (y#T')))"
      using assms are_vertices_in_He_trans are_vertices_in_He_sym by blast
  qed
  ultimately have rhp_leq: "cost_of_path (c G) (last (hp_starting_at G (y#T'))#replace_hp G (filter ?h\<^sub>2 T') @ [hd (hp_starting_at G (y#T'))])
    \<le> cost_of_path (c G) (last (hp_starting_at G (y#T'))#filter ?h\<^sub>2 T' @ [hd (hp_starting_at G (y#T'))])"
    using assms(1) by (intro replace_hp_tour_leq)

  have "cost_of_path (c G) (last (hp_starting_at G (y#T'))#filter ?h\<^sub>2 T' @ hp_starting_at G (y#T')) = cost_of_path (c G) (x#hp_starting_at G (y#T') @ filter ?h\<^sub>2 T' @ [])"
    using assms last_fT' fT'_non_nil c_sym hp_starting_at_non_nil by (subst rearrange_tour) auto
  also have "... \<le> cost_of_path (c G) (x#y#T' @ [])"
    using assms(1) edge_ey vert_y_He dist_yT' set_yT' vert_ey_subset_yT' vert_x no_vert_xy fT'_non_nil by (intro cost_replace_hp_step_leq) auto
  finally have filter_leq: "cost_of_path (c G) (last (hp_starting_at G (y#T'))#filter ?h\<^sub>2 T' @ hp_starting_at G (y#T')) \<le> cost_of_path (c G) (x#y#T')"
    by auto

  have "cost_of_path (c G) (shorten_tour G T) = cost_of_path (c G) ((last (hp_starting_at G (y#T'))#replace_hp G (filter ?h\<^sub>2 T')) @ hp_starting_at G (y#T'))"
    using rot_T_CCons by (auto simp add: Let_def)
  also have "... = cost_of_path (c G) (last (hp_starting_at G (y#T'))#replace_hp G (filter ?h\<^sub>2 T') @ [hd (hp_starting_at G (y#T'))]) + cost_of_path (c G) (hp_starting_at G (y#T'))"
    using hp_starting_at_non_nil by (subst cost_of_path_append_hd) auto
  also have "... \<le> cost_of_path (c G) (last (hp_starting_at G (y#T'))#filter ?h\<^sub>2 T' @ [hd (hp_starting_at G (y#T'))]) + cost_of_path (c G) (hp_starting_at G (y#T'))"
    using rhp_leq by auto
  also have "... = cost_of_path (c G) ((last (hp_starting_at G (y#T'))#filter ?h\<^sub>2 T') @ hp_starting_at G (y#T'))"
    using hp_starting_at_non_nil by (subst cost_of_path_append_hd) auto
  also have "... \<le> cost_of_path (c G) (x#y#T')"
    using filter_leq by auto
  also have "... = cost_of_path (c G) (rotate_tour ?h\<^sub>1 T)"
    using rot_T_CCons by auto
  also have "... = cost_of_path (c G) T"
    using assms(1) cost_rotate_tour[OF hdT_eq_lastT c_sym] by auto
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
    using distinct set distinct_distinct_adj path g2.path_non_nil g2.hd_path_betw apply (intro iffD2[OF distinct_adj_Cons]) apply auto[1]
    using path apply (intro g2.last_path_betw) apply simp
    using path g2.last_path_betw g2.path_non_nil last_in_set apply metis
    using path g2.path_vertices apply simp
    done
  moreover hence "g2.path_betw (f G) ?u\<^sub>1 ?T ?u\<^sub>1" 
    using assms f_is_complete by (intro g2.path_betw_in_complete_graph) auto
  ultimately have hc: "g2.is_hc_Adj (f G) ?T"
    by (intro g2.is_hc_AdjI) auto

  have "c G ?u\<^sub>1 ?u\<^sub>2 \<le> 5"
    using assms by (intro cost_x_y_leq5)
  moreover have "hp_of_vc G X \<noteq> []"
    using path by (auto intro!: g2.path_non_nil)
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