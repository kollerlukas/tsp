theory VC4_To_mTSP
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
  assumes fold_g1_uedges1: "\<And>M f a\<^sub>0. ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges1 f M a\<^sub>0 = fold f es a\<^sub>0"
  fixes fold_g1_uedges2 :: "('v1 uedge \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 'g1 \<Rightarrow> bool \<Rightarrow> bool"
  assumes fold_g1_uedges2: "\<And>M f a\<^sub>0. ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges2 f M a\<^sub>0 = fold f es a\<^sub>0"
  fixes fold_g1_uedges3 :: "('v1 uedge \<Rightarrow> enat \<Rightarrow> enat) \<Rightarrow> 'g1 \<Rightarrow> enat \<Rightarrow> enat"
  assumes fold_g1_uedges3: "\<And>M f a\<^sub>0. ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges3 f M a\<^sub>0 = fold f es a\<^sub>0"
  fixes fold_g1_uedges4 :: "('v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list) 
    \<Rightarrow> 'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list"
  assumes fold_g1_uedges4: "\<And>M f a\<^sub>0. ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges4 f M a\<^sub>0 = fold f es a\<^sub>0"
  fixes fold_g1_uedges5 :: "('v1 uedge \<Rightarrow> 'v1set \<Rightarrow> 'v1set) \<Rightarrow> 'g1 \<Rightarrow> 'v1set \<Rightarrow> 'v1set"
  assumes fold_g1_uedges5: "\<And>M f a\<^sub>0. ugraph_adj_map_invar M \<Longrightarrow> \<exists>es. distinct es \<and> map rep1 es = es 
      \<and> List.set es = g1.uedges M \<and> fold_g1_uedges5 f M a\<^sub>0 = fold f es a\<^sub>0"

  fixes fold_g2_vset :: "(('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> 'g2 \<Rightarrow> 'g2) \<Rightarrow> 'v2set \<Rightarrow> 'g2 \<Rightarrow> 'g2"
    \<comment> \<open>Function that folds the vertices of a graph represented by an adjacency map.\<close>
  assumes finite_sets2: "\<And>X. finite (set2 X)"
  assumes fold_g2_vset:  "\<And>X f M\<^sub>0. set_invar2 X \<Longrightarrow> \<exists>xs. distinct xs \<and> List.set xs = set2 X 
      \<and> fold_g2_vset f X M\<^sub>0 = fold f xs M\<^sub>0"
begin

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

abbreviation "vertices_of_H\<^sub>e e \<equiv> case rep1 e of uEdge u v \<Rightarrow>
  g2.set_of_list ([(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),
    (rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)])"

fun neighborhood_in_H\<^sub>e :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> 'v2set" where
  "neighborhood_in_H\<^sub>e (e,x,i) = (case rep1 e of uEdge u v \<Rightarrow>
    if x = u \<and> i = 1 then g2.set_of_list [(rep1 e,u,3),(rep1 e,u,5)]
    else if x = u \<and> i = 2 then g2.set_of_list [(rep1 e,u,4),(rep1 e,v,5)]
    else if x = u \<and> i = 3 then g2.set_of_list [(rep1 e,u,1),(rep1 e,u,4),(rep1 e,u,6)]
    else if x = u \<and> i = 4 then g2.set_of_list [(rep1 e,u,2),(rep1 e,u,3),(rep1 e,v,6)]
    else if x = u \<and> i = 5 then g2.set_of_list [(rep1 e,u,1),(rep1 e,v,2)]
    else if x = u \<and> i = 6 then g2.set_of_list [(rep1 e,u,3),(rep1 e,v,4)]
    else if x = v \<and> i = 1 then g2.set_of_list [(rep1 e,v,3),(rep1 e,v,5)]
    else if x = v \<and> i = 2 then g2.set_of_list [(rep1 e,v,4),(rep1 e,u,5)]
    else if x = v \<and> i = 3 then g2.set_of_list [(rep1 e,v,1),(rep1 e,v,4),(rep1 e,v,6)]
    else if x = v \<and> i = 4 then g2.set_of_list [(rep1 e,v,2),(rep1 e,v,3),(rep1 e,u,6)]
    else if x = v \<and> i = 5 then g2.set_of_list [(rep1 e,v,1),(rep1 e,u,2)]
    else if x = v \<and> i = 6 then g2.set_of_list [(rep1 e,v,3),(rep1 e,u,4)]
    else g2.set_of_list [])"

fun H\<^sub>e :: "'v1 uedge \<Rightarrow> 'g2" where
  "H\<^sub>e e = (case rep1 e of uEdge u v \<Rightarrow> let e = uEdge u v in
    fold_g2_vset (\<lambda>x. update2 x (neighborhood_in_H\<^sub>e x)) (vertices_of_H\<^sub>e e) map_empty2)"

abbreviation "hc1_in_H\<^sub>e e \<equiv> (case rep1 e of uEdge u v \<Rightarrow>
  [(rep1 e,u,1),(rep1 e,u,5),(rep1 e,v,2),(rep1 e,v,4),(rep1 e,u,6),(rep1 e,u,3),
  (rep1 e,u,4),(rep1 e,v,6),(rep1 e,v,3),(rep1 e,v,1),(rep1 e,v,5),(rep1 e,u,2)])" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,u,1)\<close>.\<close>

abbreviation "hc2_in_H\<^sub>e e \<equiv> rev (hc1_in_H\<^sub>e e)" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,u,2)\<close>.\<close>

abbreviation "hc3_in_H\<^sub>e e \<equiv> (case rep1 e of uEdge u v \<Rightarrow>
  [(rep1 e,v,1),(rep1 e,v,5),(rep1 e,u,2),(rep1 e,u,4),(rep1 e,v,6),(rep1 e,v,3),
  (rep1 e,v,4),(rep1 e,u,6),(rep1 e,u,3),(rep1 e,u,1),(rep1 e,u,5),(rep1 e,v,2)])" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,v,1)\<close>.\<close>

abbreviation "hc4_in_H\<^sub>e e \<equiv> rev (hc3_in_H\<^sub>e e)" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,v,2)\<close>.\<close>

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

sublocale complete_graph_for_ugraph_adj_map map_empty2 update2 map_delete2 lookup2 map_invar2 
  set_empty2 insert2 set_delete2 isin2 set2 set_invar2 union2 inter2 diff2 rep2 fold_g2_vset
  using fold_g2_vset finite_sets2 by unfold_locales

end

section \<open>Implementation of Auxiliary Functions\<close>

context VC4_To_mTSP
begin

fun is_edge_in_H\<^sub>e :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) uedge \<Rightarrow> bool" where
  "is_edge_in_H\<^sub>e G (uEdge u v) = 
    fold_g1_uedges2 (\<lambda>e b. b \<or> isin2 (\<N>\<^sub>2 (H\<^sub>e e) v) u) G False"
  \<comment> \<open>Return \<open>True\<close> if the graph \<open>G\<close> contains an edge \<open>e\<close> in s.t. \<open>(uEdge u v)\<close> is an edge in the 
  subgraph \<open>H\<^sub>e e\<close>; return \<open>False\<close> otherwise.\<close>

fun min_dist_in_H\<^sub>e :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> enat" where
  "min_dist_in_H\<^sub>e G u v = fold_g1_uedges3 (\<lambda>e d. min (g2.path_dist (H\<^sub>e e) u v) d) G \<infinity>"
  \<comment> \<open>This function returns the minimum distance between \<open>u\<close> and \<open>v\<close> in \<open>H\<^sub>e e\<close> for an edge \<open>e\<close> in \<open>G\<close>.\<close>

fun are_vertices_in_H\<^sub>e :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> bool" where
  "are_vertices_in_H\<^sub>e G u v = 
    fold_g1_uedges2 (\<lambda>e b. b \<or> (isin2 (vertices_of_H\<^sub>e e) v \<and> isin2 (vertices_of_H\<^sub>e e) u)) G False"
  \<comment> \<open>Return \<open>True\<close> if the graph \<open>G\<close> contains an edge \<open>e\<close> in s.t. \<open>u\<close> and \<open>v\<close> are vertices in the 
  subgraph \<open>H\<^sub>e e\<close>; return \<open>False\<close> otherwise.\<close>
  (* alternate definition:  min_dist_in_H\<^sub>e < \<infinity> *)

fun rotate_T_rec :: "'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list 
  \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list option" where
  "rotate_T_rec e [] T' = None"
| "rotate_T_rec e ((e',x,i)#T) T' = 
    (if rep1 e = rep1 e' then Some ((e',x,i)#T @ T' @ [(e',x,i)])
    else rotate_T_rec e T ((e',x,i)#T'))"

fun rotate_T :: "'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "rotate_T e T = the_default (rotate_T_rec e (tl T) []) T"
  \<comment> \<open>Rotate given Hamiltonian cycle \<open>T\<close> to first vertex of \<open>H\<^sub>e e\<close>.\<close>
(* "(let f = \<lambda>(e',x,i). rep1 e \<noteq> rep1 e' in
    dropWhile f T @ rev (takeWhile f (butlast T)) @ (case find f T of Some e \<Rightarrow> [e] | None \<Rightarrow> []))"*)

fun g'_map_edge :: "'g1 \<Rightarrow> 'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat)" where
  "g'_map_edge G e T = (let T' = rotate_T e T in 
    case hd T' of (e',x,i) \<Rightarrow> case rep1 e' of uEdge u v \<Rightarrow>
      if (x = u \<and> i = 1) \<or> (x = u \<and> i = 2) \<or> (x = v \<and> i = 1) \<or> (x = v \<and> i = 2) then 
        (uEdge u v,x,i)
      else 
        (uEdge u v,u,1))"
  \<comment> \<open>Map an edge \<open>e\<close> of the VC4-graph to a start-edge \<open>(uEdge u v,x,i)\<close> of a Hamiltonian path in 
    \<open>H\<^sub>e e\<close>.\<close>

fun g'_map_tour :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "g'_map_tour G T = fold_g1_uedges4 (\<lambda>e X'. g'_map_edge G e T#X') G []"

fun g_map_edge :: "'g1 \<Rightarrow> 'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1" where
  "g_map_edge G e T = (case g'_map_edge G e T of (uEdge u v,x,i) \<Rightarrow> x)"
  \<comment> \<open>Map an edge \<open>e\<close> of the VC4-graph to a vertex \<open>x\<close> that covers \<open>e\<close> in \<open>G\<close>.\<close>

end

section \<open>Implementation of Reduction-Functions\<close>

context VC4_To_mTSP
begin

fun V\<^sub>H :: "'g1 \<Rightarrow> 'v2set" where 
  "V\<^sub>H G = fold_g1_uedges1 (union2 o vertices_of_H\<^sub>e) G set_empty2"
  \<comment> \<open>Compute the vertices of the graph \<open>H := f G\<close>.\<close>

fun f :: "'g1 \<Rightarrow> 'g2" where
  "f G = complete_graph (V\<^sub>H G)" \<comment> \<open>The graph \<open>H\<close> is the complete graph for the vertices \<open>V\<^sub>H\<close>.\<close>

fun c :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> nat" where
  "c G (e\<^sub>1,v\<^sub>1,i\<^sub>1) (e\<^sub>2,v\<^sub>2,i\<^sub>2) = 
    (if is_edge_in_H\<^sub>e G (uEdge (e\<^sub>1,v\<^sub>1,i\<^sub>1) (e\<^sub>2,v\<^sub>2,i\<^sub>2)) then 1
    else if are_vertices_in_H\<^sub>e G (e\<^sub>1,v\<^sub>1,i\<^sub>1) (e\<^sub>2,v\<^sub>2,i\<^sub>2) then 
      the_enat (min_dist_in_H\<^sub>e G (e\<^sub>1,v\<^sub>1,i\<^sub>1) (e\<^sub>2,v\<^sub>2,i\<^sub>2))
    else if v\<^sub>1 = v\<^sub>2 \<and> rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2 then 4
    else 5)"

fun g :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1set" where
  "g G T = fold_g1_uedges5 (\<lambda>e X. insert1 (g_map_edge G e T) X) G set_empty1"

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

lemma invar_vertices_of_H\<^sub>e: "set_invar2 (vertices_of_H\<^sub>e e)"
  by (auto simp add: g2.invar_set_of_list simp del: g2.set_of_list.simps split: uedge.splits)

lemma isin_vertices_of_H\<^sub>e:
  assumes "isin2 (vertices_of_H\<^sub>e e) x"
  obtains u v where "rep1 e = uEdge u v" 
    "x \<in> List.set [(rep1 e,u,1::nat),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),
      (rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
proof -
  obtain u v where "e = uEdge u v"
    using uedge.exhaust by auto
  then consider "rep1 e = uEdge u v" | "rep1 e = uEdge v u"
    using g1.is_rep by auto
  thus ?thesis
    using that assms g2.set_specs by cases (auto simp: g2.set_of_list[symmetric])
qed

lemma set_invar_V\<^sub>H_G:
  assumes "g1.ugraph_adj_map_invar G"
  shows "set_invar2 (V\<^sub>H G)"
proof -
  let ?f="union2 \<circ> vertices_of_H\<^sub>e"
  obtain es where "distinct es" "map rep1 es = es" "List.set es = g1.uedges G" 
    "V\<^sub>H G = fold ?f es set_empty2"
    using assms by (auto elim!: fold1.fold_uedgesE)
  moreover have "set_invar2 (fold ?f es set_empty2)"
    using invar_vertices_of_H\<^sub>e by (auto intro!: g2.invar_fold_union simp: fold_map g2.set_specs)
  ultimately show ?thesis
    by auto
qed

lemma set_V\<^sub>H_G:
  assumes "g1.ugraph_adj_map_invar G"
  shows "set2 (V\<^sub>H G) = \<Union> ((set2 o vertices_of_H\<^sub>e) ` g1.uedges G)"
proof -
  let ?f="union2 \<circ> vertices_of_H\<^sub>e"
  obtain es where "distinct es" "map rep1 es = es" "List.set es = g1.uedges G" 
    "V\<^sub>H G = fold ?f es set_empty2"
    using assms by (auto elim!: fold1.fold_uedgesE)
  moreover have "set2 (fold ?f es set_empty2) = \<Union> (List.set (map (set2 o vertices_of_H\<^sub>e) es))" 
    apply (subst fold_map)
    apply (subst map_map)
    apply (intro g2.fold_union_empty)
    using invar_vertices_of_H\<^sub>e by (auto intro!: g2.fold_union_empty simp: g2.set_specs)
  ultimately show ?thesis
    by auto
qed

lemma isin_V\<^sub>H_obtain_edge:
  assumes "g1.ugraph_adj_map_invar G" "isin2 (V\<^sub>H G) x"
  obtains e where "e \<in> g1.uedges G" "isin2 (vertices_of_H\<^sub>e e) x"
proof -
  have "set2 (V\<^sub>H G) = \<Union> ((set2 o vertices_of_H\<^sub>e) ` g1.uedges G)"
    using assms by (intro set_V\<^sub>H_G)
  then obtain e where "e \<in> g1.uedges G" "isin2 (vertices_of_H\<^sub>e e) x"
    using assms set_invar_V\<^sub>H_G invar_vertices_of_H\<^sub>e g2.set_specs by auto
  thus ?thesis
    using that by auto
qed

lemma obtain_other_vertex_in_V\<^sub>H:
  assumes "g1.ugraph_adj_map_invar G" "isin2 (V\<^sub>H G) x"
  obtains y where "isin2 (V\<^sub>H G) y" "x \<noteq> y"
proof -
  obtain e where isin_e: "e \<in> g1.uedges G" and isin_x: "isin2 (vertices_of_H\<^sub>e e) x"
    using assms by (elim isin_V\<^sub>H_obtain_edge)
  then obtain u v where [simp]: "rep1 e = uEdge u v" and
    "x \<in> List.set [(rep1 e,u,1::nat),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),
      (rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]" 
      (is "x \<in> List.set ?es")
    by (elim isin_vertices_of_H\<^sub>e)
  consider "x = (rep1 e,u,1::nat)" | "x \<noteq> (rep1 e,u,1::nat)"
    by auto
  then obtain y where "isin2 (vertices_of_H\<^sub>e e) y" and x_neq_y: "x \<noteq> y"
  proof cases
    let ?y="(rep1 e,u,2::nat)"
    assume [simp]: "x = (rep1 e,u,1::nat)"
    have "isin2 (vertices_of_H\<^sub>e e) ?y"
      using invar_vertices_of_H\<^sub>e g2.set_specs by auto
    thus ?thesis
      using that isin_x by auto
  next
    let ?y="(rep1 e,u,1::nat)"
    assume "x \<noteq> (rep1 e,u,1::nat)"
    moreover have "isin2 (vertices_of_H\<^sub>e e) ?y"
      using invar_vertices_of_H\<^sub>e g2.set_specs by auto
    ultimately show ?thesis
      using that isin_x by auto
  qed
  hence "y \<in> set2 (vertices_of_H\<^sub>e e)"
    using assms invar_vertices_of_H\<^sub>e g2.set_specs by auto
  hence "y \<in> \<Union> ((set2 o vertices_of_H\<^sub>e) ` g1.uedges G)"
    using isin_e by fastforce
  hence "isin2 (V\<^sub>H G) y"
    using assms set_invar_V\<^sub>H_G set_V\<^sub>H_G g2.set_specs by auto
  thus ?thesis
    using that x_neq_y by auto
qed

lemma at_least_two_vertices_in_V\<^sub>H:
  assumes "g1.ugraph_adj_map_invar G" "isin2 (V\<^sub>H G) x"
  shows "\<exists>y. isin2 (set_delete2 x (V\<^sub>H G)) y"
proof -
  obtain y where "isin2 (V\<^sub>H G) y" "x \<noteq> y"
    using assms by (elim obtain_other_vertex_in_V\<^sub>H)
  hence "isin2 (set_delete2 x (V\<^sub>H G)) y"
    using assms set_invar_V\<^sub>H_G g2.set_specs by auto
  thus ?thesis
    by blast
qed  

lemma vertices_of_H\<^sub>e: "g2.vertices (H\<^sub>e e) = set2 (vertices_of_H\<^sub>e e)"
  sorry

lemma "are_vertices_in_H\<^sub>e G u v \<longleftrightarrow> (\<exists>e. e \<in> g1.uedges G \<longrightarrow> u \<in> g2.vertices (H\<^sub>e e) \<and> v \<in> g2.vertices (H\<^sub>e e))"
  sorry

lemma "are_vertices_in_H\<^sub>e G u v \<Longrightarrow> min_dist_in_H\<^sub>e G u v < \<infinity>"
  sorry

lemma "is_edge_in_H\<^sub>e G e' \<longleftrightarrow> (\<exists>e. e \<in> g1.uedges G \<longrightarrow> e' \<in> g2.uedges (H\<^sub>e e))"
  sorry

fun hp_starting_at :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_starting_at (e,x,i) = (case rep1 e of uEdge u v \<Rightarrow>
    if x = u \<and> i = 1 then hc1_in_H\<^sub>e (rep1 e)
    else if x = u \<and> i = 2 then hc2_in_H\<^sub>e (rep1 e)
    else if x = v \<and> i = 1 then hc3_in_H\<^sub>e (rep1 e)
    else if x = v \<and> i = 2 then hc4_in_H\<^sub>e (rep1 e)
    else hc1_in_H\<^sub>e (rep1 e))"

fun tour_of_g'_map :: "('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "tour_of_g'_map [] = []"
| "tour_of_g'_map X' = concat (map hp_starting_at X') @ [hd X']"
  \<comment> \<open>Given a list of vertices \<open>X'\<close>, where each vertex marks the start of a Hamiltonian path, we 
  return a full tour.\<close>

lemma
  assumes "g1.ugraph_adj_map_invar G"
  shows "cost_of_path (c G) (tour_of_g'_map (g'_map_tour G T)) \<le> cost_of_path (c G) T"
  \<comment> \<open>The induced tour computed by the function \<open>g\<close> has lower cost compared to the original tour \<open>T\<close>.\<close>
  sorry (* TODO: tricky! *)

lemma
  obtains u where "g2.path_betw (f G) u (tour_of_g'_map (g'_map_tour G T)) u"
    sorry

lemma
  assumes "g2.is_hc_adj (f G) T"
  shows "g2.is_hc_adj (f G) (tour_of_g'_map (g'_map_tour G T))"
  \<comment> \<open>The induced tour computed by the function \<open>g\<close> is indeed a tour of the graph \<open>f G\<close>.\<close>
proof (intro g2.is_hcI)

  show "\<exists>u. g2.path_betw (f G) u (tour_of_g'_map (g'_map_tour G T)) u"
    sorry
    
  show "distinct (tl (tour_of_g'_map (g'_map_tour G T)))"
    sorry

  show "g2.vertices (f G) = set (tl (tour_of_g'_map (g'_map_tour G T)))"
    sorry
qed

end

section \<open>Properties of Reduction-Functions\<close>

context VC4_To_mTSP
begin
 

lemma f_is_complete: 
  assumes "g1.ugraph_adj_map_invar G"
  shows "is_complete (set_of_uedge ` g2.uedges (f G))"
  using assms set_invar_V\<^sub>H_G at_least_two_vertices_in_V\<^sub>H
  by (simp del: complete_graph.simps; intro complete_graph_is_complete) auto

end

section \<open>Reduction Proofs\<close>

context VC4_To_mTSP
begin

lemma hc_from_vc:
  assumes "g1.is_vc_adj G X"
  obtains T where "g2.is_hc_adj (f G) T" 
    "cost_of_path (c G) T = 15 * card (g1.uedges G) + card (set1 X)"
  sorry

lemma cost_of_mTSP:
  assumes opt_vc: "g1.is_min_vc_adj G OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "g2.is_tsp_adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 15 * card (g1.uedges G) + card (set1 OPT\<^sub>V\<^sub>C)"
proof -
  have "g1.is_vc_adj G OPT\<^sub>V\<^sub>C"
    using assms by (elim g1.is_min_vcE)
  then obtain T where "g2.is_hc_adj (f G) T" 
    "cost_of_path (c G) T = 15 * card (g1.uedges G) + card (set1 OPT\<^sub>V\<^sub>C)"
    by (elim hc_from_vc)
  moreover have "\<And>T. g2.is_hc_adj (f G) T \<Longrightarrow> cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> cost_of_path (c G) T"
    using assms by (elim g2.is_tspE)
  ultimately show ?thesis
    by fastforce
qed

(* ----- 1st condition for a L-reduction ----- *)

lemma l_reduction1:
  assumes opt_vc: "g1.is_min_vc_adj G OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "g2.is_tsp_adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * card (set1 OPT\<^sub>V\<^sub>C)" (is "?c' OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> ?\<alpha> * ?c OPT\<^sub>V\<^sub>C")
  sorry (* TODO: use lemma VertexCover.vc_card_E_leq_max_degree *)

(* ----- 2nd condition for a L-reduction ----- *)

lemma
  assumes "g2.is_hc_adj (f G) T"
  shows "g1.is_vc_adj G (g G T)"
  sorry

lemma
  assumes "cost_of_path (c G) T \<le> 15 * card (g1.uedges G) + k"
  obtains k where "card (set1 (g G T)) \<le> k"
  sorry (* needed for proof of \<open>l_reduction2\<close> *)

lemma l_reduction2:
  assumes opt_vc: "g1.is_min_vc_adj G OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "g2.is_tsp_adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P" 
      and "g2.is_hc_adj (f G) T"
  shows "\<bar> card (set1 (g G T)) - card (set1 OPT\<^sub>V\<^sub>C) \<bar> 
    \<le> 1 * \<bar> cost_of_path (c G) T - cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>"
  sorry

end

end