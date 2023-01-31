theory VertexCover4ToMetricTravelingSalesman
  imports Main tsp.GraphAdjMap WeightedGraph
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
  assumes fold_g1_uedges1: "\<And>M f a. ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges1 f M a = fold f es a"
  fixes fold_g1_uedges2 :: "('v1 uedge \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 'g1 \<Rightarrow> bool \<Rightarrow> bool"
  assumes fold_g1_uedges2: "\<And>M f a. ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges2 f M a = fold f es a"
  fixes fold_g1_uedges3 :: "('v1 uedge \<Rightarrow> enat \<Rightarrow> enat) \<Rightarrow> 'g1 \<Rightarrow> enat \<Rightarrow> enat"
  assumes fold_g1_uedges3: "\<And>M f a. ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges3 f M a = fold f es a"
  fixes fold_g1_uedges4 :: "('v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list) 
    \<Rightarrow> 'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list"
  assumes fold_g1_uedges4: "\<And>M f a. ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges4 f M a = fold f es a"
  fixes fold_g1_uedges5 :: "('v1 uedge \<Rightarrow> 'v1set \<Rightarrow> 'v1set) \<Rightarrow> 'g1 \<Rightarrow> 'v1set \<Rightarrow> 'v1set"
  assumes fold_g1_uedges5: "\<And>M f a. ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
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

  fixes fold_g2_vset1 :: "(('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> 'g2 \<Rightarrow> 'g2) \<Rightarrow> 'v2set \<Rightarrow> 'g2 \<Rightarrow> 'g2"
    \<comment> \<open>Function that folds the vertices of a graph represented by an adjacency map.\<close>
  assumes finite_sets2: "\<And>X. finite (set2 X)"
  assumes fold_g2_vset1: "\<And>X f a. set_invar2 X \<Longrightarrow> \<exists>xs. distinct xs \<and> List.set xs = set2 X 
      \<and> fold_g2_vset1 f X a = fold f xs a" \<comment> \<open>For locale \<open>graph_of_vertices_for_ugraph_adj_map\<close>.\<close>
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
  set_empty2 insert2 set_delete2 isin2 set2 set_invar2 union2 inter2 diff2 rep2 fold_g2_vset1
  using fold_g2_vset1 finite_sets2 by unfold_locales

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

(* fun H\<^sub>e :: "'v1 uedge \<Rightarrow> 'g2" where
  "H\<^sub>e e = (case rep1 e of uEdge u v \<Rightarrow> let e = uEdge u v in
    fold_g2_vset (\<lambda>x. update2 x (neighborhood_in_He x)) (vertices_of_He e) map_empty2)" *)

fun He :: "'v1 uedge \<Rightarrow> 'g2" ("H\<^sub>e") where
  "H\<^sub>e e = graph_of_vertices \<N>\<^sub>H\<^sub>e (V\<^sub>H\<^sub>e e)"

abbreviation "hp e \<equiv> (case e of uEdge u v \<Rightarrow>
    [(rep1 e,u,1::nat),(rep1 e,u,5),(rep1 e,v,2),(rep1 e,v,4),(rep1 e,u,6),(rep1 e,u,3),
      (rep1 e,u,4),(rep1 e,v,6),(rep1 e,v,3),(rep1 e,v,1),(rep1 e,v,5),(rep1 e,u,2)])"

fun hp_u1 where 
  "hp_u1 e = hp e" 
  (* "hp_u1 e = (case rep1 e of uEdge u v \<Rightarrow> hp (uEdge u v))" *)
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

(* use Misc.rotate_tour *)

(* fun rotate_T_rec :: "'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list 
  \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list option" where
  "rotate_T_rec e (x#y#T) T' = 
    (if \<not> isin2 (V\<^sub>H\<^sub>e e) x \<and> isin2 (V\<^sub>H\<^sub>e e) y then Some (y#T @ rev (y#T'))
    else rotate_T_rec e (y#T) (x#T'))"
| "rotate_T_rec e _ _ = None"

fun rotate_T :: "'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "rotate_T e T = the_default (rotate_T_rec e (tl T) []) T" *)
  \<comment> \<open>Rotate given Hamiltonian cycle \<open>T\<close> to first vertex of \<open>H\<^sub>e e\<close>.\<close>
(* "(let f = \<lambda>(e',x,i). rep1 e \<noteq> rep1 e' in
    dropWhile f T @ rev (takeWhile f (butlast T)) @ (case find f T of Some e \<Rightarrow> [e] | None \<Rightarrow> []))"*)

fun map_edge_to_hp_start_vertex :: 
  "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat)" where
  (* "g'_map_edge G e T = (let T' = rotate_T e T in 
    case hd T' of (e',w,i) \<Rightarrow> case rep1 e' of uEdge u v \<Rightarrow>
      if (w = u \<and> i = 1) \<or> (w = u \<and> i = 2) \<or> (w = v \<and> i = 1) \<or> (w = v \<and> i = 2) then 
        (uEdge u v,w,i)
      else 
        (uEdge u v,u,1))" *)
  "map_edge_to_hp_start_vertex G T e = (case rotate_tour (isin2 (V\<^sub>H\<^sub>e e)) T of 
    x#(e',w,i)#T \<Rightarrow> (case rep1 e' of uEdge u v \<Rightarrow>
      if (w = u \<or> w = v) \<and> (i = 1 \<or> i = 2) then (uEdge u v,w,i)
      else (uEdge u v,u,1))
    | _ \<Rightarrow> undefined)"
  \<comment> \<open>Map an edge \<open>e\<close> of the VC4-graph to a start-edge \<open>(uEdge u v,x,i)\<close> of a Hamiltonian path in 
    \<open>H\<^sub>e e\<close>.\<close>

fun map_tour_to_hp_staring_vertices :: 
  "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "map_tour_to_hp_staring_vertices G T = 
    fold_g1_uedges4 (\<lambda>e X'. map_edge_to_hp_start_vertex G T e#X') G []"

fun map_edge_to_covering_vertex :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1 uedge \<Rightarrow> 'v1" where
  "map_edge_to_covering_vertex G T e = (case map_edge_to_hp_start_vertex G T e of (e,w,i) \<Rightarrow> w)"
  \<comment> \<open>Map an edge \<open>e\<close> of the VC4-graph to a vertex \<open>x\<close> that covers \<open>e\<close> in \<open>G\<close>.\<close>

fun hp_for_neighborhood :: "'v1 \<Rightarrow> 'v1set \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where 
  "hp_for_neighborhood u N\<^sub>u = fold_v1set1 (\<lambda>v T. T @ hp_u2 (uEdge u v)) N\<^sub>u []"
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

fun c :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> nat" where
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

context VC4_To_mTSP
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

end

context VC4_To_mTSP
begin

lemma vertices_of_He_rep_idem: "V\<^sub>H\<^sub>e (rep1 e) = V\<^sub>H\<^sub>e e"
  by (simp only: vertices_of_He.simps g1.rep_idem)

lemma invar_vertices_of_He: "set_invar2 (V\<^sub>H\<^sub>e e)"
  by (auto simp add: g2.invar_set_of_list simp del: g2.set_of_list.simps split: uedge.splits)

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

lemma isin_vertices_of_He_elim2:
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
qed

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

lemma are_vertices_in_He_sym:
  assumes "g1.ugraph_adj_map_invar G" "are_vertices_in_He G x y"
  shows "are_vertices_in_He G y x"
  using assms are_vertices_in_He by auto

lemma vertices_in_H\<^sub>e_path_dist: 
  assumes "g1.ugraph_adj_map_invar G" "e \<in> g1.uedges G" 
      and "x \<in> g2.vertices (H\<^sub>e e)" "y \<in> g2.vertices (H\<^sub>e e)"
  shows "g2.path_dist (H\<^sub>e e) x y < \<infinity>"
  using invar_He
  apply (intro g2.path_dist_less_inf)
  apply simp
  sorry (* TODO: How to prove? *)

lemma are_vertices_in_He_min_dist: 
  assumes "g1.ugraph_adj_map_invar G" "are_vertices_in_He G x y"
  shows "min_dist_in_He G x y < \<infinity>"
  using assms(1)
proof (rule fold3.fold_uedgesE)
  obtain e where e_isin_G: "e \<in> g1.uedges G" and "x \<in> g2.vertices (H\<^sub>e e)" "y \<in> g2.vertices (H\<^sub>e e)"
    using assms by (elim are_vertices_in_He_elim)
  hence d\<^sub>x\<^sub>y_le_inf: "g2.path_dist (H\<^sub>e e) x y < \<infinity>" (is "?d\<^sub>x\<^sub>y < \<infinity>")
    using assms vertices_in_H\<^sub>e_path_dist by auto

  let ?f="\<lambda>e d. min (g2.path_dist (H\<^sub>e e) x y) d"
  fix es
  assume "distinct es" "map rep1 es = es" and set_es: "List.set es = g1.uedges G" and
    [simp]: "fold_g1_uedges3 ?f G \<infinity> = fold ?f es \<infinity>"
  hence "e \<in> List.set es"
    using e_isin_G by auto
  then obtain es\<^sub>1 es\<^sub>2 where [simp]: "es = es\<^sub>1 @ e#es\<^sub>2"
    by (meson split_list)
  have "fold ?f es \<infinity> = fold ?f es\<^sub>2 (min ?d\<^sub>x\<^sub>y (fold ?f es\<^sub>1 \<infinity>))"
    by auto
  also have "... < \<infinity>"
    using d\<^sub>x\<^sub>y_le_inf by (intro fold_enat_min; intro linorder_class.min.strict_coboundedI1)
  finally show "min_dist_in_He G x y < \<infinity>"
    by (auto simp del: He.simps)
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

lemma edge_in_He_are_vertices:
  assumes "g1.ugraph_adj_map_invar G" "is_edge_in_He G (uEdge x y)"
  shows "are_vertices_in_He G x y"
  using assms
proof (rule is_edge_in_He_elim)
  fix e
  assume e_is_edge: "e \<in> g1.uedges G" and "rep2 (uEdge x y) \<in> g2.uedges (H\<^sub>e e)"
  hence y_isin_Nx: "isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y"
    using g2.rep_isin_uedges_elim[of "H\<^sub>e e", OF invar_He] by blast
  moreover hence "x \<in> g2.vertices (H\<^sub>e e)"
    by (auto intro!: g2.vertices_memberI1)
  moreover have "y \<in> g2.vertices (H\<^sub>e e)"
    using y_isin_Nx by (auto intro!: g2.vertices_memberI2)
  ultimately show ?thesis
    using assms e_is_edge by (intro are_vertices_in_He_intro)
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

lemma path_hp_u1: 
  "g2.path_betw (H\<^sub>e (uEdge u v)) (rep1 (uEdge u v),u,1) (hp_u1 (uEdge u v)) (rep1 (uEdge u v),u,2)" 
    (is "g2.path_betw (H\<^sub>e ?e) ?u\<^sub>1 _ ?u\<^sub>2")    
proof (rule g1.rep_cases)
  show "rep1 ?e = rep1 (uEdge u v)"
    by auto
next
  assume "rep1 (uEdge u v) = uEdge u v"
  moreover have "?u\<^sub>2 \<in> g2.vertices (H\<^sub>e ?e)"
    using vertices_of_He by (auto simp add: set_vertices_of_He simp del: vertices_of_He.simps)
  ultimately show "g2.path_betw (H\<^sub>e ?e) ?u\<^sub>1 (hp_u1 ?e) ?u\<^sub>2"
    by (fastforce intro!: g2.path_betw.intros isin_vertices_of_He_intro2 
        simp add: neighborhood_He g2.isin_set_of_list simp del: He.simps g2.set_of_list.simps)
next
  assume "rep1 (uEdge u v) = uEdge v u"
  moreover hence "rep1 (uEdge v u) = rep1 (uEdge u v)"
    using g1.rep_idem by metis
  moreover have "?u\<^sub>2 \<in> g2.vertices (H\<^sub>e ?e)"
    using vertices_of_He by (auto simp add: set_vertices_of_He simp del: vertices_of_He.simps)
  ultimately show "g2.path_betw (H\<^sub>e ?e) ?u\<^sub>1 (hp_u1 ?e) ?u\<^sub>2"
    by (fastforce intro!: g2.path_betw.intros isin_vertices_of_He_intro2 
        simp add: neighborhood_He g2.isin_set_of_list simp del: He.simps g2.set_of_list.simps)
qed

lemma cost_of_hp_u1: 
  assumes "g1.ugraph_adj_map_invar G" "rep1 e \<in> g1.uedges G"
  shows "cost_of_path (c G) (hp_u1 e) = 11"
  apply (cases e; rule g1.rep_cases)
  apply simp
proof -
  fix u v
  assume "e = uEdge u v" "rep1 (uEdge u v) = uEdge u v"
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
next
  fix u v
  assume "e = uEdge u v" "rep1 (uEdge u v) = uEdge v u"
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
qed (* TODO: clean up! *)

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

lemma hp_u1_disjoint:
  assumes "g1.ugraph_adj_map_invar G" "rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
  shows "List.set (hp_u1 e\<^sub>1) \<inter> List.set (hp_u1 e\<^sub>2) = {}"
proof -
  have "g2.vertices (H\<^sub>e e\<^sub>1) \<inter> g2.vertices (H\<^sub>e e\<^sub>2) = {}"
    using assms by (auto intro!: vertices_of_He_disjoint 
      simp add: vertices_of_He simp del: He.simps vertices_of_He.simps)
  thus ?thesis
    using assms vertices_hp_u1 by auto
qed

lemma hp_u2_non_nil: "hp_u2 e \<noteq> []"
  by (auto split: uedge.splits)

lemma path_hp_u2: 
  "g2.path_betw (H\<^sub>e (uEdge u v)) (rep1 (uEdge u v),u,2) (hp_u2 (uEdge u v)) (rep1 (uEdge u v),u,1)" 
  using path_hp_u1 by (simp del: He.simps hp_u1.simps) (intro g2.rev_path[OF _ invar_He])

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

lemma hp_u2_disjoint:
  assumes "g1.ugraph_adj_map_invar G" "rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2"
  shows "List.set (hp_u2 e\<^sub>1) \<inter> List.set (hp_u2 e\<^sub>2) = {}"
  using assms vertices_hp_u1 vertices_hp_u2 hp_u1_disjoint by blast

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

lemma distinct_hp:
  assumes "g1.ugraph_adj_map_invar G" "rep1 e \<in> g1.uedges G"
  shows "distinct (hp_u1 e)" "distinct (hp_u2 e)"
    (* "distinct (hp_v1 e)" "distinct (hp_v2 e)" *)
  using assms 
  sorry (* by (rule g1.uedge_not_refl; simp)+ *)

(*fun hp_starting_at :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_starting_at (e,x,i) = (case rep1 e of uEdge u v \<Rightarrow>
    if x = u \<and> i = 1 then hp_u1 (rep1 e)
    else if x = u \<and> i = 2 then hp_u2 (rep1 e)
    else if x = v \<and> i = 1 then hp_v1 (rep1 e)
    else if x = v \<and> i = 2 then hp_v2 (rep1 e)
    else hp_u1 (rep1 e))"

fun tour_of_hp_starting_vertices :: "('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "tour_of_hp_starting_vertices [] = []"
| "tour_of_hp_starting_vertices X' = concat (map hp_starting_at X') @ [hd X']"
  \<comment> \<open>Given a list of vertices \<open>X'\<close>, where each vertex marks the start of a Hamiltonian path, we 
  return a full tour.\<close>

lemma
  assumes "g2.is_hc_Adj (f G) T"
  shows "g2.is_hc_Adj (f G) (tour_of_hp_starting_vertices (map_tour_to_hp_staring_vertices G T))"
  \<comment> \<open>The induced tour computed by the function \<open>g\<close> is indeed a tour of the graph \<open>f G\<close>.\<close>
  apply (intro g2.is_hc_AdjI)
  sorry

lemma
  assumes "g1.ugraph_adj_map_invar G"
  shows "cost_of_path (c G) (tour_of_hp_starting_vertices (map_tour_to_hp_staring_vertices G T)) \<le> cost_of_path (c G) T"
  \<comment> \<open>The induced tour computed by the function \<open>g\<close> has lower cost compared to the original tour \<open>T\<close>.\<close>
  sorry (* TODO: tricky! *) *)

lemma cost_leq4:
  assumes "g1.ugraph_adj_map_invar G"
    and "rep1 (uEdge u v) \<in> g1.uedges G" "rep1 (uEdge u w) \<in> g1.uedges G" "v \<noteq> w"
  shows "c G (rep1 (uEdge u v),u,i\<^sub>v) (rep1 (uEdge u w),u,i\<^sub>w) \<le> 4"
proof -
  have "rep1 (uEdge u v) \<noteq> rep1 (uEdge u w)"
    using assms g1.rep_elim by auto
  hence "\<And>e. isin2 (V\<^sub>H\<^sub>e e) (rep1 (uEdge u v),u,i\<^sub>v) \<Longrightarrow> \<not> isin2 (V\<^sub>H\<^sub>e e) (rep1 (uEdge u w),u,i\<^sub>w)"
    using isin_vertices_of_He_edge by metis
  hence "\<not> are_vertices_in_He G (rep1 (uEdge u v),u,i\<^sub>v) (rep1 (uEdge u w),u,i\<^sub>w)"
    using assms are_vertices_in_He using invar_vertices_of_He g2.set_specs 
      by (auto simp add: vertices_of_He simp del: He.simps vertices_of_He.simps)
  moreover hence "\<not> is_edge_in_He G (uEdge (rep1 (uEdge u v),u,i\<^sub>v) (rep1 (uEdge u w),u,i\<^sub>w))"
    using assms edge_in_He_are_vertices by auto
  ultimately show "c G (rep1 (uEdge u v),u,i\<^sub>v) (rep1 (uEdge u w),u,i\<^sub>w) \<le> 4"
    using assms \<open>rep1 (uEdge u v) \<noteq> rep1 (uEdge u w)\<close> 
    by (auto simp add: g1.rep_idem simp del: He.simps vertices_of_He.simps)
qed

lemma cost_leq5:
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
  shows "c G (e\<^sub>1,u\<^sub>1,1) (e\<^sub>2,u\<^sub>2,2) \<le> 5" (is "c G ?x ?y \<le> 5")
proof cases 
  assume "are_vertices_in_He G ?x ?y"
  (* e\<^sub>1 = e\<^sub>2. e\<^sub>1 = uEdge u v \<Longrightarrow> different cases. 
    (i) u\<^sub>1 = u\<^sub>2. \<Longrightarrow> path (uEdge u v,u,1),(uEdge u v,u,5),(uEdge u v,v,2)
    (ii) u\<^sub>1 \<noteq> u\<^sub>2. \<Longrightarrow> path (uEdge u v,u,1),(uEdge u v,u,3),(uEdge u v,u,4),(uEdge u v,u,2) 
  *)
  have "\<not> is_edge_in_He G (uEdge ?x ?y)"
    sorry
  thus ?thesis
    sorry
next
  assume "\<not> are_vertices_in_He G ?x ?y"
  thus ?thesis
    using assms cost_leq5 by auto
qed

lemma cost_last_hd_hp_u2:
  assumes "g1.ugraph_adj_map_invar G"
    and "rep1 (uEdge u v) \<in> g1.uedges G" "rep1 (uEdge u w) \<in> g1.uedges G" "v \<noteq> w"
  shows "c G (last (hp_u2 (uEdge u v))) (hd (hp_u2 (uEdge u w))) \<le> 4"
proof -
  have "last (hp_u2 (uEdge u v)) = (rep1 (uEdge u v),u,1)" 
    "hd (hp_u2 (uEdge u w)) = (rep1 (uEdge u w),u,2)"
    using assms by (auto simp add: g1.rep_of_edge)
  thus ?thesis
    using assms cost_leq4 by auto
qed

lemma hd_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 N\<^sub>u" and "\<exists>v. isin1 N\<^sub>u v" \<comment> \<open>The neighborhood is non-empty.\<close>
      and "\<And>v. isin1 N\<^sub>u v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  obtains v where "isin1 N\<^sub>u v" "hd (hp_for_neighborhood u N\<^sub>u) = (rep1 (uEdge u v),u,2)"
  using assms(2)
proof (rule fold6.fold_setE)
  let ?f="\<lambda>v. hp_u2 (uEdge u v)"
  fix vs
  assume "distinct vs" "List.set vs = set1 N\<^sub>u" "fold_v1set1 (\<lambda>v T. T @ ?f v) N\<^sub>u [] = fold (\<lambda>v T. T @ ?f v) vs []"
  moreover hence "vs \<noteq> []" "\<exists>v \<in> set vs. ?f v \<noteq> []"
    using assms by (auto simp add: g1.set_specs)
  moreover then obtain v where "v \<in> set vs" "hd (concat (map ?f vs)) = hd (?f v)"
    by (elim hd_concat_map)
  ultimately show ?thesis
    using assms that by (auto simp add: g1.set_specs fold_concat_map)

qed

lemma last_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 N\<^sub>u" and "\<exists>v. isin1 N\<^sub>u v" \<comment> \<open>The neighborhood is non-empty.\<close>
      and "\<And>v. isin1 N\<^sub>u v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  obtains v where "isin1 N\<^sub>u v" "last (hp_for_neighborhood u N\<^sub>u) = (rep1 (uEdge u v),u,1)"
  using assms(2)
proof (rule fold6.fold_setE)
  let ?f="\<lambda>v. hp_u2 (uEdge u v)"
  fix vs
  assume "distinct vs" "List.set vs = set1 N\<^sub>u" "fold_v1set1 (\<lambda>v T. T @ ?f v) N\<^sub>u [] = fold (\<lambda>v T. T @ ?f v) vs []"
  moreover hence "vs \<noteq> []" "\<exists>v \<in> set vs. ?f v \<noteq> []"
    using assms by (auto simp add: g1.set_specs)
  moreover then obtain v where "v \<in> set vs" "last (concat (map ?f vs)) = last (?f v)"
    by (elim last_concat_map)
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

thm not_hd_snd_rotate_tour

lemma 
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" "length T > 3" and "e \<in> g1.uedges G"
  shows "cost_of_path (\<lambda>x y. if \<not> isin2 (V\<^sub>H\<^sub>e e) x \<and> isin2 (V\<^sub>H\<^sub>e e) y then (1::nat) else 0) T > 0"
  sorry

(* lemma 
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" and "e \<in> g1.uedges G"
  obtains x where "x \<in> List.set T" "x \<in> set2 (V\<^sub>H\<^sub>e e)"
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
qed *)

lemma map_edge_to_hp_start_vertex_is_vertex:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" and "e \<in> g1.uedges G"
  shows "map_edge_to_hp_start_vertex G T e \<in> List.set T"
proof -
  have "hd T = last T"
    using assms g2.is_hc_AdjE sorry
  hence "set T = set (rotate_tour (isin2 (V\<^sub>H\<^sub>e e)) T)"
    by (intro set_rotate_tour)

  show ?thesis
    sorry
qed

lemma map_edge_to_hp_start_vertex_cases:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" 
      and "e \<in> g1.uedges G" "rep1 e = rep1 (uEdge u v)"
  shows "map_edge_to_hp_start_vertex G T e \<in> {(rep1 e,u,1),(rep1 e,u,2),(rep1 e,v,1),(rep1 e,v,2)}"
proof -

  show ?thesis
    sorry
qed

lemma map_edge_to_covering_vertex_cases:
  assumes "g1.ugraph_adj_map_invar G" "g2.is_hc_Adj (f G) T" 
      and "e \<in> g1.uedges G" "rep1 e = rep1 (uEdge u v)"
  shows "map_edge_to_covering_vertex G T e \<in> {u,v}"
  using assms(2)
proof -
  let ?x="map_edge_to_hp_start_vertex G T e"
  consider "?x = (rep1 e,u,1)" | "?x = (rep1 e,u,2)" | "?x = (rep1 e,v,1)" | "?x = (rep1 e,v,2)"
    using assms map_edge_to_hp_start_vertex_cases by blast
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

lemma partition_for_vertex_disjoint:
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
    using assms isin_partition_for_vertex g1.rep_eq by auto
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

lemma c_tri_inequality:
  assumes "x \<in> g2.vertices (f G)" "y \<in> g2.vertices (f G)" "z \<in> g2.vertices (f G)"
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

lemma hp_for_neighborhood_empty: "set_invar1 P \<Longrightarrow> \<nexists>v. isin1 P v \<Longrightarrow> hp_for_neighborhood u P = []"
  by (rule fold6.fold_setE) (auto simp add: g1.set_specs)

lemma distinct_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 P" 
      and "\<And>v. isin1 P v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  shows "distinct (hp_for_neighborhood u P)"
  using assms(2)
proof (rule fold6.fold_setE)
  let ?f="\<lambda>v. hp_u2 (uEdge u v)"
  fix vs 
  assume distinct_vs: "distinct vs" and set_vs_fold: "List.set vs = set1 P" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) P [] = fold (\<lambda>v T. T @ ?f v) vs []"
  moreover hence "\<And>v. v \<in> List.set vs \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G"
    using assms by (auto simp add: g1.set_specs)
  ultimately have "distinct (concat (map ?f vs))"
    using assms(1) by (intro distinct_concat_map) 
      (auto intro!: distinct_hp(2) hp_u2_disjoint simp add: g1.rep_eq simp del: hp_u2.simps)
  thus ?thesis
    using set_vs_fold by (auto simp: fold_concat_map)
qed

lemma set_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 P" 
      and "\<And>v. isin1 P v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  shows "List.set (hp_for_neighborhood u P) = \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` {uEdge u v | v. isin1 P v})"
  using assms(2)
proof (rule fold6.fold_setE)
  let ?f="\<lambda>v. hp_u2 (uEdge u v)"
  fix vs 
  assume distinct_vs: "distinct vs" and set_vs_fold: "List.set vs = set1 P" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) P [] = fold (\<lambda>v T. T @ ?f v) vs []"
  have "List.set (concat (map ?f vs)) = \<Union> ((\<lambda>v. g2.vertices (H\<^sub>e (uEdge u v))) ` (List.set vs))"
    by (auto simp add: vertices_hp_u2 simp del: He.simps)
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
  let ?f="\<lambda>v. hp_u2 (uEdge u v)"
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
    using vs_nonnil hp_u2_non_nil set_vs_fold by (auto simp: fold_concat_map)
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

lemma cost_hp_for_neighborhood:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 P" 
      and "\<And>v. isin1 P v \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
  shows"cost_of_path (c G) (hp_for_neighborhood u P) \<le> card (set1 P) * 11 + (card (set1 P) - 1) * 4"
using assms(2)
proof (rule fold6.fold_setE)
  let ?hp="hp_for_neighborhood u P"
  let ?f="\<lambda>v. hp_u2 (uEdge u v)"
  fix vs 
  assume distinct_vs: "distinct vs" and set_vs_fold: "List.set vs = set1 P" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) P [] = fold (\<lambda>v T. T @ ?f v) vs []"
  moreover hence uv_edge: "\<And>v. v \<in> List.set vs \<Longrightarrow> rep1 (uEdge u v) \<in> g1.uedges G"
    using assms by (auto simp add: g1.set_specs)
  ultimately have "cost_of_path (c G) (concat (map ?f vs)) \<le> (\<Sum>v\<leftarrow>vs. cost_of_path (c G) (?f v)) + (length vs - 1) * 4"
    using assms(1) by (intro cost_concat_map) (auto intro!: cost_last_hd_hp_u2 simp del: cost_of_path.simps c.simps hp_u2.simps)
  also have "... = length vs * 11 + (length vs - 1) * 4"
    using assms(1) uv_edge cost_of_hp_u2 
    by (auto simp add: sum_list_const simp del: cost_of_path.simps c.simps hp_u2.simps)
  finally show ?thesis
    using set_vs_fold distinct_vs by (auto simp add: fold_concat_map distinct_card[symmetric])
qed

lemma hd_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X" 
      and "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
  obtains u v where "hd (hp_from_vc G X) = (rep1 (uEdge u v),u,2)"
  using assms(3)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_vs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"

  obtain e where "e \<in> g1.uedges G"
    using assms by auto
  hence "\<exists>u v. u \<in> g1.vertices G \<and> isin1 (\<N>\<^sub>1 G u) v"
    unfolding g1.uedges_def2 using assms by (auto simp add: g1.vertices_def2)
  hence "\<exists>u v. isin1 X u \<and> isin1 (\<N>\<^sub>1 G u) v"
    using assms g1.is_vc_AdjE by blast
  hence "xs \<noteq> []"
    using assms set_vs_fold by (auto simp add: g1.set_specs)
  moreover have "\<exists>v \<in> set xs. ?f v \<noteq> []"
    sorry (* TODO: should follow from assms *) thm set_hp_for_neighborhood
  ultimately obtain u where "u \<in> set xs" "hd (concat (map ?f xs)) = hd (?f u)"
    by (elim hd_concat_map)
  moreover obtain v where "isin1 (\<P> G X u) v" "hd (hp_for_neighborhood u (\<P> G X u)) = (rep1 (uEdge u v),u,2)"
    using assms(1) apply (elim hd_hp_for_neighborhood[of G "\<P> G X u"])
    using assms(1) invar_partition_for_vertex apply simp
    subgoal
      sorry
    using assms(1) uedge_of_partition_for_vertex apply blast
    apply simp
    done
  ultimately show ?thesis
    using assms that set_vs_fold by (auto simp add: g1.set_specs fold_concat_map)
qed

lemma last_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X" 
      and "\<exists>e. e \<in> g1.uedges G" \<comment> \<open>The set of edges of the graph \<open>G\<close> is non-empty.\<close>
  obtains u v where "last (hp_from_vc G X) = (rep1 (uEdge u v),u,1)"
  using assms(3)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_vs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"
  show ?thesis
    sorry
qed

lemma hp_for_neighborhood_disjoint:
  assumes "g1.ugraph_adj_map_invar G" "set_invar1 P\<^sub>1" "set_invar1 P\<^sub>2" 
      and "\<And>v. isin1 P\<^sub>1 v \<Longrightarrow> rep1 (uEdge u\<^sub>1 v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
      and "\<And>v. isin1 P\<^sub>2 v \<Longrightarrow> rep1 (uEdge u\<^sub>2 v) \<in> g1.uedges G" \<comment> \<open>Condition for partition of \<open>g1.uedges G\<close>.\<close>
      and "{rep1 (uEdge u\<^sub>1 v) |v. isin1 P\<^sub>1 v} \<inter> {rep1 (uEdge u\<^sub>2 v) |v. isin1 P\<^sub>2 v} = {}" \<comment> \<open>Set of edges are disjoint.\<close>
  shows "List.set (hp_for_neighborhood u\<^sub>1 P\<^sub>1) \<inter> List.set (hp_for_neighborhood u\<^sub>2 P\<^sub>2) = {}"
proof - 
  have "\<And>v\<^sub>1 v\<^sub>2. isin1 P\<^sub>1 v\<^sub>1 \<Longrightarrow> isin1 P\<^sub>2 v\<^sub>2 \<Longrightarrow> set2 (V\<^sub>H\<^sub>e (uEdge u\<^sub>1 v\<^sub>1)) \<inter> set2 (V\<^sub>H\<^sub>e (uEdge u\<^sub>2 v\<^sub>2)) = {}"
    using assms g1.rep_eq by (auto simp add: g1.set_specs intro!: vertices_of_He_disjoint simp del: vertices_of_He.simps)
  thus ?thesis
    using assms by (auto simp add: set_hp_for_neighborhood simp del: vertices_of_He.simps hp_for_neighborhood.simps)
qed

lemma distinct_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X" and "\<exists>v. isin1 X v" \<comment> \<open>The vertex cover is non-empty.\<close>
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
    using assms(1) apply (intro partition_for_vertex_disjoint)
    using assms(1,3) set_vs_fold apply (auto simp add: g1.set_specs)
    done (* TODO: clean up *)
  ultimately show ?thesis
    by (simp add: fold_concat_map)
qed

lemma set_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X" and "\<exists>v. isin1 X v" \<comment> \<open>The vertex cover is non-empty.\<close>
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
  also have "... = \<Union> ((set2 \<circ> V\<^sub>H\<^sub>e) ` (\<Union> {{rep1 (uEdge u v) |v. isin1 (\<P> G X u) v} |u. isin1 X u}))"
    using assms by (auto simp add: g1.set_specs)
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
    using set_vs_fold by (auto simp add: fold_concat_map)
qed

lemma path_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X" and "\<exists>v. isin1 X v" \<comment> \<open>The vertex cover is non-empty.\<close>
  obtains u\<^sub>1 v\<^sub>1 u\<^sub>2 v\<^sub>2 where 
    "g2.path_betw (f G) (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2) (hp_from_vc G X) (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)" 
  using assms(3)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_vs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"

  have "\<exists>e. e \<in> g1.uedges G"
    sorry (* TODO: we need at least one edge *)

  obtain u\<^sub>1 v\<^sub>1 where "hd (hp_from_vc G X) = (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2)"
    using assms \<open>\<exists>e. e \<in> g1.uedges G\<close> by (elim hd_hp_from_vc)    
  moreover obtain u\<^sub>2 v\<^sub>2 where "last (hp_from_vc G X) = (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)"
    using assms \<open>\<exists>e. e \<in> g1.uedges G\<close> by (elim last_hp_from_vc)
  moreover have "List.set (hp_from_vc G X) = g2.vertices (f G)"
    using assms by (rule set_hp_from_vc)
  ultimately have "g2.path_betw (f G) (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2) (hp_from_vc G X) (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)"
    apply (simp only: hp_from_vc.simps)
    apply (intro g2.path_betw_in_complete_graph)
    using assms f_is_complete apply simp
    subgoal
      sorry
    using assms distinct_distinct_adj[OF distinct_hp_from_vc] by auto
  thus ?thesis
    using that by auto
qed

lemma cost_hp_from_vc:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X"
      and "\<exists>v. isin1 X v" \<comment> \<open>The vertex cover is non-empty.\<close>
  obtains u\<^sub>1 v\<^sub>1 u\<^sub>2 v\<^sub>2 where "rep1 (uEdge u\<^sub>1 v\<^sub>1) \<in> g1.uedges G" "rep1 (uEdge u\<^sub>2 v\<^sub>2) \<in> g1.uedges G"
    "distinct (hp_from_vc G X)" "List.set (hp_from_vc G X) = g2.vertices (f G)"
    "g2.path_betw (f G) (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2) (hp_from_vc G X) (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)" 
    "cost_of_path (c G) (hp_from_vc G X) + 5 \<le> 15 * (card (set_of_uedge ` g1.uedges G)) + card (set1 X)"
  using assms(3)
proof (rule fold6.fold_setE)     
  let ?f="\<lambda>u. hp_for_neighborhood u (\<P> G X u)"
  fix xs
  assume distinct_xs: "distinct xs" and set_vs_fold: "List.set xs = set1 X" 
    "fold_v1set1 (\<lambda>v T. T @ ?f v) X [] = fold (\<lambda>v T. T @ ?f v) xs []"

  \<comment> \<open>cost\<close>
  thm cost_concat_map
  thm invar_partition_for_vertex uedge_of_partition_for_vertex

  have "cost_of_path (c G) (concat (map ?f xs)) 
    \<le> (\<Sum>x\<leftarrow>xs. cost_of_path (c G) (?f x)) + (length xs - 1) * 5"
    apply (intro cost_concat_map)
    using distinct_xs apply simp
    using cost_leq5
    sorry
  also have "... \<le> (\<Sum>x\<leftarrow>xs. cost_of_path (c G) (?f x)) + (length xs - 1) * 5"
    sorry

  hence "cost_of_path (c G) (hp_from_vc G X) + 5 \<le> 15 * (card (\<Union> {{rep1 (uEdge u v) |v. isin1 (\<P> G X u) v} |u. isin1 X u})) + card (set1 X)"
    using assms set_vs_fold distinct_xs 
    apply (auto simp add: fold_concat_map distinct_card[symmetric] g1.set_specs)
    sorry
  also have "... \<le> 15 * (card (g1.uedges G)) + card (set1 X)"
    using assms partition_by_vertex_cover by auto
  also have "... \<le> 15 * (card (set_of_uedge ` g1.uedges G)) + card (set1 X)"
    sorry

  show ?thesis
    sorry
qed

end

section \<open>Reduction Proof\<close>

context VC4_To_mTSP
begin

lemma hc_from_vc:
  assumes "g1.ugraph_adj_map_invar G" "g1.is_vc_Adj G X" "set_invar1 X"
  obtains T where "g2.is_hc_Adj (f G) T" 
    "cost_of_path (c G) T \<le> 15 * card (set_of_uedge ` g1.uedges G) + card (set1 X)" 
proof -
  have "\<exists>v. isin1 X v" \<comment> \<open>The vertex cover is non-empty.\<close>
    sorry (* assume: graph contains at least one edge \<Longrightarrow> vertex cover is non empty *)
  then obtain u\<^sub>1 v\<^sub>1 u\<^sub>2 v\<^sub>2 where "rep1 (uEdge u\<^sub>1 v\<^sub>1) \<in> g1.uedges G" "rep1 (uEdge u\<^sub>2 v\<^sub>2) \<in> g1.uedges G"
    and distinct_set: "distinct (hp_from_vc G X)" "List.set (hp_from_vc G X) = g2.vertices (f G)"
    and path: "g2.path_betw (f G) (rep1 (uEdge u\<^sub>1 v\<^sub>1),u\<^sub>1,2) (hp_from_vc G X) (rep1 (uEdge u\<^sub>2 v\<^sub>2),u\<^sub>2,1)" (is "g2.path_betw (f G) ?u\<^sub>2 _ ?u\<^sub>1")
    and cost_hp: "cost_of_path (c G) (hp_from_vc G X) + 5 \<le> 15 * (card (set_of_uedge ` g1.uedges G)) + card (set1 X)"
    using assms by (elim hp_from_vc)
  moreover have "distinct_adj (?u\<^sub>1#hp_from_vc G X)" (is "distinct_adj ?T")
      and "last (hp_from_vc G X) = ?u\<^sub>1"
      and "?u\<^sub>1 \<in> List.set (hp_from_vc G X)" "List.set (hp_from_vc G X) \<subseteq> g2.vertices (f G)"
    using distinct_set distinct_distinct_adj path g2.path_non_empty g2.hd_path_betw apply (intro iffD2[OF distinct_adj_Cons]) apply auto[1]
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
  ultimately have cost: "cost_of_path (c G) (?u\<^sub>1#hp_from_vc G X) \<le> 15 * card (set_of_uedge ` g1.uedges G) + card (set1 X)" 
    using cost_hp by (auto simp add: cost_of_path_cons)

  show ?thesis
    using that hc cost by auto
qed

lemma cost_of_opt_mTSP:
  assumes "g1.ugraph_adj_map_invar G"
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C"
      and opt_mtsp: "g2.is_tsp_Adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 15 * card (set_of_uedge ` g1.uedges G) + card (set1 OPT\<^sub>V\<^sub>C)"
    (is "_ \<le> 15 * card ?E + ?\<tau>_G")
  \<comment> \<open>The cost of the optimal Hamiltonian cycle in the graph \<open>f G\<close> is bounded.\<close>
proof -
  have "g1.is_vc_Adj G OPT\<^sub>V\<^sub>C"
    using assms by (elim g1.is_min_vc_AdjE)
  then obtain T where "g2.is_hc_Adj (f G) T" "cost_of_path (c G) T \<le> 15 * card ?E + ?\<tau>_G"
    using assms by (elim hc_from_vc)
  moreover hence "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> cost_of_path (c G) T"
    using assms g2.is_tsp_AdjE by blast
  ultimately show ?thesis
    by auto
qed

(* ----- 1st condition for a L-reduction ----- *)

lemma l_reduction1:
  assumes "g1.ugraph_adj_map_invar G" 
      and max_degree: "\<And>v. v \<in> g1.vertices G \<Longrightarrow> g1.degree_Adj G v \<le> enat 4"
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C"
      and opt_mtsp: "g2.is_tsp_Adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * card (set1 OPT\<^sub>V\<^sub>C)" (is "?c' OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> ?\<alpha> * ?\<tau>_G")
  \<comment> \<open>First condition for a L-Reduction.\<close>
proof -
  let ?E="set_of_uedge ` g1.uedges G"
  have "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 15 * card ?E + ?\<tau>_G"
    using assms by (auto simp: cost_of_opt_mTSP)
  also have "... \<le> 15 * (4 * ?\<tau>_G) + ?\<tau>_G"
    using assms by (auto intro!: g1.uedges_leq_max_degree_card_vc elim: g1.is_min_vc_AdjE)
  also have "... = 61 * ?\<tau>_G"
    by auto
  finally show ?thesis .
qed

(* ----- 2nd condition for a L-reduction ----- *)

lemma card_g_leq_k:
  assumes "g1.ugraph_adj_map_invar G"
      and "g2.is_hc_Adj (f G) T"
  obtains k where "card (set1 (g G T)) \<le> k"
    and "cost_of_path (c G) T = 15 * card (set_of_uedge ` g1.uedges G) + k"
    \<comment> \<open>The cost of the vertex cover computed by the function \<open>g\<close> is linked to the cost of the 
    given Hamiltonian cycle of the graph \<open>f G\<close>.\<close>
  sorry (* needed for proof of \<open>l_reduction2\<close> *)

lemma l_reduction2:
  assumes "g1.ugraph_adj_map_invar G"
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C"
      and opt_mtsp: "g2.is_tsp_Adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P" 
      and "g2.is_hc_Adj (f G) T"
  shows "\<bar> card (set1 (g G T)) - card (set1 OPT\<^sub>V\<^sub>C) \<bar> 
    \<le> 1 * \<bar> cost_of_path (c G) T - cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>" (is "\<bar> card _ - ?\<tau>_G \<bar> \<le> _")
  \<comment> \<open>Second condition for a L-Reduction.\<close>
proof -
  let ?E="set_of_uedge ` g1.uedges G"
  obtain k where "card (set1 (g G T)) \<le> k" and cost_T_eq: "cost_of_path (c G) T = 15 * card ?E + k"
    using assms by (elim card_g_leq_k)
  hence "\<bar> card (set1 (g G T)) - ?\<tau>_G \<bar> \<le> \<bar> k - ?\<tau>_G \<bar>"
    by auto
  also have "... = \<bar> 15 * card ?E + k - (15 * card ?E + ?\<tau>_G) \<bar>"
    by auto
  also have "... = \<bar> cost_of_path (c G) T - (15 * card ?E + ?\<tau>_G) \<bar>"
    by (auto simp: cost_T_eq)
  also have "... \<le> \<bar> cost_of_path (c G) T - cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>"
    using assms cost_of_opt_mTSP by (auto simp add: diff_le_mono2)
  finally show ?thesis 
    by auto
qed

end

end