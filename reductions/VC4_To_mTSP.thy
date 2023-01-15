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
  set_empty2 insert2 set_delete2 isin2 set2 set_invar2 union2 inter2 diff2 rep2 fold_g2_vset
  using fold_g2_vset finite_sets2 by unfold_locales

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

fun vertices_of_H\<^sub>e :: "'v1 uedge \<Rightarrow> 'v2set" ("V\<^sub>H\<^sub>e") where 
  "vertices_of_H\<^sub>e e = (case rep1 e of uEdge u v \<Rightarrow>
    g2.set_of_list ([(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),
      (rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]))"

fun neighborhood_in_H\<^sub>e :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> 'v2set" ("\<N>\<^sub>H\<^sub>e") where
  "neighborhood_in_H\<^sub>e (e,w,i) = (case rep1 e of uEdge u v \<Rightarrow>
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
    fold_g2_vset (\<lambda>x. update2 x (neighborhood_in_H\<^sub>e x)) (vertices_of_H\<^sub>e e) map_empty2)" *)

fun H\<^sub>e :: "'v1 uedge \<Rightarrow> 'g2" where
  "H\<^sub>e e = graph_of_vertices \<N>\<^sub>H\<^sub>e (V\<^sub>H\<^sub>e e)"

abbreviation "hc_u1_in_H\<^sub>e e \<equiv> (case rep1 e of uEdge u v \<Rightarrow>
  [(rep1 e,u,1),(rep1 e,u,5),(rep1 e,v,2),(rep1 e,v,4),(rep1 e,u,6),(rep1 e,u,3),
  (rep1 e,u,4),(rep1 e,v,6),(rep1 e,v,3),(rep1 e,v,1),(rep1 e,v,5),(rep1 e,u,2)])" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,u,1)\<close>.\<close>

abbreviation "hc_u2_in_H\<^sub>e e \<equiv> rev (hc_u1_in_H\<^sub>e e)" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,u,2)\<close>.\<close>

abbreviation "hc_v1_in_H\<^sub>e e \<equiv> (case rep1 e of uEdge u v \<Rightarrow>
  [(rep1 e,v,1),(rep1 e,v,5),(rep1 e,u,2),(rep1 e,u,4),(rep1 e,v,6),(rep1 e,v,3),
  (rep1 e,v,4),(rep1 e,u,6),(rep1 e,u,3),(rep1 e,u,1),(rep1 e,u,5),(rep1 e,v,2)])" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,v,1)\<close>.\<close>

abbreviation "hc_v2_in_H\<^sub>e e \<equiv> rev (hc_v1_in_H\<^sub>e e)" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,v,2)\<close>.\<close>

end

section \<open>Implementation of Auxiliary Functions\<close>

context VC4_To_mTSP
begin

fun neighborhood_compl :: "'v2set \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> 'v2set" ("\<N>\<^sup>C") where
  "neighborhood_compl X x = (if isin2 X x then set_delete2 x X else set_empty2)"

fun complete_graph :: "'v2set \<Rightarrow> 'g2" where
  "complete_graph X = graph_of_vertices (\<N>\<^sup>C X) X"

fun is_edge_in_H\<^sub>e :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) uedge \<Rightarrow> bool" where
  "is_edge_in_H\<^sub>e G (uEdge x y) = 
    fold_g1_uedges2 (\<lambda>e b. b \<or> isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y) G False"
  \<comment> \<open>Return \<open>True\<close> if the graph \<open>G\<close> contains an edge \<open>e\<close> in s.t. \<open>(uEdge x y)\<close> is an edge in the 
  subgraph \<open>H\<^sub>e e\<close>; return \<open>False\<close> otherwise.\<close>

fun min_dist_in_H\<^sub>e :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> enat" where
  "min_dist_in_H\<^sub>e G x y = fold_g1_uedges3 (\<lambda>e d. min (g2.path_dist (H\<^sub>e e) x y) d) G \<infinity>"
  \<comment> \<open>This function returns the minimum distance between \<open>x\<close> and \<open>y\<close> in \<open>H\<^sub>e e\<close> for an edge \<open>e\<close> in \<open>G\<close>.\<close>

fun are_vertices_in_H\<^sub>e :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> bool" where
  "are_vertices_in_H\<^sub>e G x y = 
    fold_g1_uedges2 (\<lambda>e b. b \<or> (isin2 (V\<^sub>H\<^sub>e e) x \<and> isin2 (V\<^sub>H\<^sub>e e) y)) G False"
  \<comment> \<open>Return \<open>True\<close> if the graph \<open>G\<close> contains an edge \<open>e\<close> in s.t. \<open>u\<close> and \<open>y\<close> are vertices in the 
  subgraph \<open>H\<^sub>e e\<close>; return \<open>False\<close> otherwise.\<close>
  (* alternate definition:  min_dist_in_H\<^sub>e < \<infinity> *)

fun rotate_T_rec :: "'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list 
  \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list option" where
  "rotate_T_rec e [] T' = None"
| "rotate_T_rec e ((e',w,i)#T) T' = 
    (if rep1 e = rep1 e' then Some ((e',w,i)#T @ T' @ [(e',w,i)])
    else rotate_T_rec e T ((e',w,i)#T'))"

fun rotate_T :: "'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "rotate_T e T = the_default (rotate_T_rec e (tl T) []) T"
  \<comment> \<open>Rotate given Hamiltonian cycle \<open>T\<close> to first vertex of \<open>H\<^sub>e e\<close>.\<close>
(* "(let f = \<lambda>(e',x,i). rep1 e \<noteq> rep1 e' in
    dropWhile f T @ rev (takeWhile f (butlast T)) @ (case find f T of Some e \<Rightarrow> [e] | None \<Rightarrow> []))"*)

fun g'_map_edge :: "'g1 \<Rightarrow> 'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat)" where
  "g'_map_edge G e T = (let T' = rotate_T e T in 
    case hd T' of (e',w,i) \<Rightarrow> case rep1 e' of uEdge u v \<Rightarrow>
      if (w = u \<and> i = 1) \<or> (w = u \<and> i = 2) \<or> (w = v \<and> i = 1) \<or> (w = v \<and> i = 2) then 
        (uEdge u v,w,i)
      else 
        (uEdge u v,u,1))"
  \<comment> \<open>Map an edge \<open>e\<close> of the VC4-graph to a start-edge \<open>(uEdge u v,x,i)\<close> of a Hamiltonian path in 
    \<open>H\<^sub>e e\<close>.\<close>

fun g'_map_tour :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "g'_map_tour G T = fold_g1_uedges4 (\<lambda>e X'. g'_map_edge G e T#X') G []"

fun g_map_edge :: "'g1 \<Rightarrow> 'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1" where
  "g_map_edge G e T = (case g'_map_edge G e T of (uEdge u v,w,i) \<Rightarrow> w)"
  \<comment> \<open>Map an edge \<open>e\<close> of the VC4-graph to a vertex \<open>x\<close> that covers \<open>e\<close> in \<open>G\<close>.\<close>

end

section \<open>Implementation of Reduction-Functions\<close>

context VC4_To_mTSP
begin

fun V\<^sub>H :: "'g1 \<Rightarrow> 'v2set" where 
  "V\<^sub>H G = fold_g1_uedges1 (union2 o V\<^sub>H\<^sub>e) G set_empty2"
  \<comment> \<open>Compute the vertices of the graph \<open>H := f G\<close>.\<close>

fun f :: "'g1 \<Rightarrow> 'g2" where
  "f G = complete_graph (V\<^sub>H G)" \<comment> \<open>The graph \<open>H\<close> is the complete graph for the vertices \<open>V\<^sub>H\<close>.\<close>

fun c :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> nat" where
  "c G (e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2) = 
    (if is_edge_in_H\<^sub>e G (uEdge (e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2)) then 1
    else if are_vertices_in_H\<^sub>e G (e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2) then 
      the_enat (min_dist_in_H\<^sub>e G (e\<^sub>1,w\<^sub>1,i\<^sub>1) (e\<^sub>2,w\<^sub>2,i\<^sub>2))
    else if w\<^sub>1 = w\<^sub>2 \<and> rep1 e\<^sub>1 \<noteq> rep1 e\<^sub>2 then 4
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

lemma neighborhood_compl_sym: 
  assumes "set_invar2 X" "isin2 (\<N>\<^sup>C X x) y"
  shows "isin2 (\<N>\<^sup>C X y) x"
proof -
  have "isin2 X x"
    using assms g2.set_specs empty_iff by (cases "isin2 X x") auto
  thus ?thesis
    using assms g2.set_specs by auto
qed

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
proof (simp only: complete_graph.simps; intro vertices_graph_of_vertices)
  show "\<And>x y. isin2 (\<N>\<^sup>C X x) y \<Longrightarrow> isin2 X y"
  proof -
    fix x y
    assume "isin2 (\<N>\<^sup>C X x) y"
    thus "isin2 X y"
      using assms g2.set_specs by (cases "isin2 X x") auto
  qed
qed auto

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

lemma complete_graph_is_complete: 
  assumes "set_invar2 X"
    and "\<And>x. isin2 X x \<Longrightarrow> \<exists>y. isin2 (set_delete2 x X) y" 
      \<comment> \<open>The set \<open>X\<close> contains at least two vertices.\<close>
  shows "is_complete (set_of_uedge ` g2.uedges (complete_graph X))" (is "is_complete ?E")
proof (intro is_completeI)
  let ?f="\<lambda>v. set_delete2 v X"
  fix u v
  assume "u \<in> Vs ?E" "v \<in> Vs ?E" "u \<noteq> v"
  hence "isin2 X u" and "isin2 (?f u) v"
    using assms g2.set_specs 
    by (auto simp: g2.vs_uedges vertices_complete_graph[OF assms,symmetric])
  hence "isin2 (\<N>\<^sub>2 (complete_graph X) u) v"
    using assms complete_graph_neighborhood by (auto simp: g2.neighborhood_def)
  thus "{u,v} \<in> ?E"
    by (intro g2.isin_neighborhood_set_edge)
qed

lemma invar_vertices_of_H\<^sub>e: "set_invar2 (V\<^sub>H\<^sub>e e)"
  by (auto simp add: g2.invar_set_of_list simp del: g2.set_of_list.simps split: uedge.splits)

lemma isin_vertices_of_H\<^sub>e_iff: 
  assumes "rep1 e = rep1 (uEdge u v)"
  shows "isin2 (V\<^sub>H\<^sub>e e) x \<longleftrightarrow> isin2 (g2.set_of_list ([(rep1 e,u,1),(rep1 e,u,2),
    (rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),
    (rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)])) x" 
    (is "_ \<longleftrightarrow> isin2 (g2.set_of_list ?V) x")
  using assms by (rule g1.rep_cases) 
    (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)

lemma isin_vertices_of_H\<^sub>eI: 
  assumes "rep1 e = rep1 (uEdge u v)" 
    "x \<in> List.set [(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),
      (rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),(rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
  shows "isin2 (V\<^sub>H\<^sub>e e) x" 
  using assms(1) apply (rule g1.rep_cases) 
  using assms(2) apply (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)
  done

lemma isin_vertices_of_H\<^sub>eE:
  assumes "isin2 (V\<^sub>H\<^sub>e e) x"
  obtains u v where "rep1 e = rep1 (uEdge u v)" 
    "x \<in> List.set [(rep1 e,u,1),(rep1 e,u,2),(rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6)]"
proof -
  obtain u v where [simp]: "e = uEdge u v"
    using uedge.exhaust by auto
  hence "x \<in> List.set [(rep1 e,u,1),(rep1 e,u,2),
    (rep1 e,u,3),(rep1 e,u,4),(rep1 e,u,5),(rep1 e,u,6),(rep1 e,v,1),(rep1 e,v,2),(rep1 e,v,3),
    (rep1 e,v,4),(rep1 e,v,5),(rep1 e,v,6)]"
    using assms isin_vertices_of_H\<^sub>e_iff g2.isin_set_of_list 
      by (auto simp del: vertices_of_H\<^sub>e.simps g2.set_of_list.simps)
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

lemma isin_vertices_of_H\<^sub>eI2:
  assumes "rep1 e = uEdge u v" "w \<in> {u,v}" "i \<in> {1..6}" 
  shows "isin2 (V\<^sub>H\<^sub>e e) (uEdge u v,w,i)" (is "isin2 _ ?x")
proof (intro isin_vertices_of_H\<^sub>eI)
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

lemma isin_vertices_of_H\<^sub>eE2:
  assumes "isin2 (V\<^sub>H\<^sub>e e) (uEdge u v,w,i)" (is "isin2 _ ?x")
  shows "rep1 e = uEdge u v \<and> w \<in> {u,v} \<and> i \<in> {1..6}"
  using assms
proof (rule isin_vertices_of_H\<^sub>eE)
  fix u' v' 
  assume "rep1 e = rep1 (uEdge u' v')" and
    x_isin: "?x \<in> List.set [(rep1 e,u',1),(rep1 e,u',2),(rep1 e,u',3),(rep1 e,u',4),(rep1 e,u',5),(rep1 e,u',6)]" 
  then consider "rep1 e = uEdge u' v'" | "rep1 e = uEdge v' u'"
    using g1.is_rep by auto
  thus ?thesis
    using x_isin by cases auto
qed

lemma neighborhood_in_H\<^sub>e_def2:
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

lemma isin_vertices_of_H\<^sub>e_neighborhood_elim:
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
    using assms by (elim isin_vertices_of_H\<^sub>eE)
  then consider "x = (rep1 e,u,1)" | "x = (rep1 e,u,2)" | "x = (rep1 e,u,3)" 
    | "x = (rep1 e,u,4)" | "x = (rep1 e,u,5)" | "x = (rep1 e,u,6)"
    by auto
  thus ?thesis
    using that neighborhood_in_H\<^sub>e_def2 by cases auto
qed

lemma neighborhood_in_H\<^sub>e_non_empty:
  assumes "isin2 (V\<^sub>H\<^sub>e e) x"
  shows "\<exists>y. isin2 (\<N>\<^sub>H\<^sub>e x) y"
  using assms by (rule isin_vertices_of_H\<^sub>e_neighborhood_elim) 
    (auto simp: g2.set_of_list g2.set_specs)

lemma neighborhood_in_H\<^sub>e_subset_of_vertices_of_H\<^sub>e:
  assumes "isin2 (V\<^sub>H\<^sub>e e) x" "isin2 (\<N>\<^sub>H\<^sub>e x) y"
  shows "isin2 (V\<^sub>H\<^sub>e e) y"
  using assms(1) apply (rule isin_vertices_of_H\<^sub>e_neighborhood_elim)
  using assms(2) by (auto intro!: isin_vertices_of_H\<^sub>eI simp add: g2.isin_set_of_list 
      simp del: g2.set_of_list.simps vertices_of_H\<^sub>e.simps)

(* lemma neighborhood_in_H\<^sub>e_elim:
  obtains 
    u v e where "x = (rep1 e,u,1)" "isin2 (V\<^sub>H\<^sub>e e) x" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,3),(rep1 e,u,5)]"
    | u v e where "x = (rep1 e,u,2)" "isin2 (V\<^sub>H\<^sub>e e) x" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,4),(rep1 e,v,5)]"
    | u v e where "x = (rep1 e,u,3)" "isin2 (V\<^sub>H\<^sub>e e) x" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,u,4),(rep1 e,u,6)]"
    | u v e where "x = (rep1 e,u,4)" "isin2 (V\<^sub>H\<^sub>e e) x" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,2),(rep1 e,u,3),(rep1 e,v,6)]"
    | u v e where "x = (rep1 e,u,5)" "isin2 (V\<^sub>H\<^sub>e e) x" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,v,2)]"
    | u v e where "x = (rep1 e,u,6)" "isin2 (V\<^sub>H\<^sub>e e) x" "rep1 e = rep1 (uEdge u v)" 
      "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,3),(rep1 e,v,4)]"
    | "\<And>e. \<not> isin2 (V\<^sub>H\<^sub>e e) x" "\<And>e y. isin2 (V\<^sub>H\<^sub>e e) y \<Longrightarrow> \<not> isin2 (\<N>\<^sub>H\<^sub>e y) x"
proof -
  consider e where "isin2 (V\<^sub>H\<^sub>e e) x" | "\<And>e. \<not> isin2 (V\<^sub>H\<^sub>e e) x"
    by auto
  thus ?thesis
  proof cases
    fix e
    assume is_vertex: "isin2 (V\<^sub>H\<^sub>e e) x"
    thus ?thesis
      apply (rule isin_vertices_of_H\<^sub>e_neighborhood_elim)
      using that is_vertex by auto
  next
    assume not_isin_x: "\<And>e. \<not> isin2 (V\<^sub>H\<^sub>e e) x"
    moreover obtain e w i where "x = (e,w,i)"
      by (cases x)
    moreover then obtain u v where [simp]: "e = uEdge u v" "x = (uEdge u v,w,i)"
      by (cases e) auto
    ultimately have "\<not> isin2 (V\<^sub>H\<^sub>e e) x"
      by auto
    hence "rep1 e \<noteq> uEdge u v \<or> w \<notin> {u,v} \<or> i \<notin> {1..6}"
      using g1.is_rep isin_vertices_of_H\<^sub>eI2 by auto
    then consider "rep1 (uEdge u v) = uEdge v u" 
      | "rep1 (uEdge u v) = uEdge u v" "w \<notin> {u,v}" 
      | "rep1 (uEdge u v) = uEdge u v" "i \<notin> {1..6}"
      using g1.is_rep g1.rep_simps by auto
    hence "\<N>\<^sub>H\<^sub>e x = g2.set_of_list []"
    proof cases
      assume "rep1 (uEdge u v) = uEdge v u"
      thus ?thesis 
        apply (subst \<open>x = (uEdge u v,w,i)\<close>)
        apply (simp del: g2.set_of_list.simps)
        sorry
    next
      assume  "rep1 (uEdge u v) = uEdge u v" "w \<notin> {u,v}"
      thus ?thesis 
        by (auto simp del: g2.set_of_list.simps)
    next
      assume  "rep1 (uEdge u v) = uEdge u v" "i \<notin> {1..6}"
      moreover hence "i \<noteq> 1" "i \<noteq> 2" "i \<noteq> 3" "i \<noteq> 4" "i \<noteq> 5" "i \<noteq> 6"
        by auto
      ultimately show ?thesis 
        by (auto simp del: g2.set_of_list.simps)
    qed
    

    have "\<And>e y. isin2 (V\<^sub>H\<^sub>e e) y \<Longrightarrow> \<not> isin2 (\<N>\<^sub>H\<^sub>e y) x"
    proof -
      fix e y
      assume "isin2 (V\<^sub>H\<^sub>e e) y"
      thus "\<not> isin2 (\<N>\<^sub>H\<^sub>e y) x"
        using neighborhood_in_H\<^sub>e_subset_of_vertices_of_H\<^sub>e[of e y] not_isin_x by auto
    qed
    thus ?thesis
      using that not_isin_x by auto
  qed
qed *)

lemma isin_vertices_of_H\<^sub>e_edge: "isin2 (V\<^sub>H\<^sub>e e) (e',w,i) \<Longrightarrow> rep1 e = e'"
  by (auto elim!: isin_vertices_of_H\<^sub>eE simp del: vertices_of_H\<^sub>e.simps)

lemma set_invar_neighborhood_in_H\<^sub>e: "set_invar2 (\<N>\<^sub>H\<^sub>e x)"
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

lemma vertices_of_H\<^sub>e: "g2.vertices (H\<^sub>e e) = set2 (V\<^sub>H\<^sub>e e)"
  using invar_vertices_of_H\<^sub>e set_invar_neighborhood_in_H\<^sub>e neighborhood_in_H\<^sub>e_non_empty
proof (simp only: H\<^sub>e.simps; intro vertices_graph_of_vertices)
  show "\<And>x. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> \<exists>y. isin2 (\<N>\<^sub>H\<^sub>e x) y"
    by (rule neighborhood_in_H\<^sub>e_non_empty)
  show "\<And>x y. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> isin2 (\<N>\<^sub>H\<^sub>e x) y \<Longrightarrow> isin2 (V\<^sub>H\<^sub>e e) y"
    by (rule neighborhood_in_H\<^sub>e_subset_of_vertices_of_H\<^sub>e)
qed auto

lemma neighborhood_in_H\<^sub>e_irreflexive: 
  assumes "isin2 (V\<^sub>H\<^sub>e e) x"
  shows "\<not> isin2 (\<N>\<^sub>H\<^sub>e x) x"
  using assms by (rule isin_vertices_of_H\<^sub>e_neighborhood_elim)
    (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)

lemma neighborhood_in_H\<^sub>e_symmetric: 
  assumes "isin2 (V\<^sub>H\<^sub>e e) x" "isin2 (\<N>\<^sub>H\<^sub>e x) y"
  shows "isin2 (\<N>\<^sub>H\<^sub>e y) x"
  using assms(1)
proof (rule isin_vertices_of_H\<^sub>e_neighborhood_elim)
  fix u v
  assume "x = (rep1 e,u,1)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,3),(rep1 e,u,5)]" 
  thus ?thesis
    using assms neighborhood_in_H\<^sub>e_def2 
      by (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,2)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,4),(rep1 e,v,5)]" 
  thus ?thesis
    using assms neighborhood_in_H\<^sub>e_def2 neighborhood_in_H\<^sub>e_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,3)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,u,4),(rep1 e,u,6)]" 
  thus ?thesis
    using assms neighborhood_in_H\<^sub>e_def2 
      by (auto simp add: g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,4)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,2),(rep1 e,u,3),(rep1 e,v,6)]" 
  thus ?thesis
    using assms neighborhood_in_H\<^sub>e_def2 neighborhood_in_H\<^sub>e_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,5)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,1),(rep1 e,v,2)]" 
  thus ?thesis
    using assms neighborhood_in_H\<^sub>e_def2 neighborhood_in_H\<^sub>e_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
next
  fix u v
  assume "x = (rep1 e,u,6)" "rep1 e = rep1 (uEdge u v)" 
    and "\<N>\<^sub>H\<^sub>e x = g2.set_of_list [(rep1 e,u,3),(rep1 e,v,4)]" 
  thus ?thesis
    using assms neighborhood_in_H\<^sub>e_def2 neighborhood_in_H\<^sub>e_def2[of v u] 
      by (auto simp add: g1.is_rep g2.isin_set_of_list simp del: g2.set_of_list.simps)
qed

lemma invar_H\<^sub>e: "g2.ugraph_adj_map_invar (H\<^sub>e e)"
  using invar_vertices_of_H\<^sub>e set_invar_neighborhood_in_H\<^sub>e
proof (simp only: H\<^sub>e.simps; intro invar_graph_of_vertices)
  show "\<And>x. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> \<exists>y. isin2 (\<N>\<^sub>H\<^sub>e x) y"
    by (rule neighborhood_in_H\<^sub>e_non_empty)
  show "\<And>x y. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> isin2 (\<N>\<^sub>H\<^sub>e x) y \<Longrightarrow> isin2 (V\<^sub>H\<^sub>e e) y"
    by (rule neighborhood_in_H\<^sub>e_subset_of_vertices_of_H\<^sub>e)
  show "\<And>x. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> \<not> isin2 (\<N>\<^sub>H\<^sub>e x) x"
    by (rule neighborhood_in_H\<^sub>e_irreflexive)
  show "\<And>x y. isin2 (V\<^sub>H\<^sub>e e) x \<Longrightarrow> isin2 (\<N>\<^sub>H\<^sub>e x) y \<Longrightarrow> isin2 (\<N>\<^sub>H\<^sub>e y) x"
    by (rule neighborhood_in_H\<^sub>e_symmetric)
qed auto

lemma "are_vertices_in_H\<^sub>e G u v \<longleftrightarrow> (\<exists>e. e \<in> g1.uedges G \<longrightarrow> u \<in> g2.vertices (H\<^sub>e e) \<and> v \<in> g2.vertices (H\<^sub>e e))"
  sorry

lemma "are_vertices_in_H\<^sub>e G u v \<Longrightarrow> min_dist_in_H\<^sub>e G u v < \<infinity>"
  sorry

lemma "is_edge_in_H\<^sub>e G e' \<longleftrightarrow> (\<exists>e. e \<in> g1.uedges G \<longrightarrow> e' \<in> g2.uedges (H\<^sub>e e))"
  sorry

fun hp_starting_at :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_starting_at (e,x,i) = (case rep1 e of uEdge u v \<Rightarrow>
    if x = u \<and> i = 1 then hc_u1_in_H\<^sub>e (rep1 e)
    else if x = u \<and> i = 2 then hc_u2_in_H\<^sub>e (rep1 e)
    else if x = v \<and> i = 1 then hc_v1_in_H\<^sub>e (rep1 e)
    else if x = v \<and> i = 2 then hc_v2_in_H\<^sub>e (rep1 e)
    else hc_u1_in_H\<^sub>e (rep1 e))"

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

lemma set_invar_V\<^sub>H_G:
  assumes "g1.ugraph_adj_map_invar G"
  shows "set_invar2 (V\<^sub>H G)"
proof -
  let ?f="union2 \<circ> V\<^sub>H\<^sub>e"
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
  shows "set2 (V\<^sub>H G) = \<Union> ((set2 o V\<^sub>H\<^sub>e) ` g1.uedges G)"
proof -
  let ?f="union2 \<circ> V\<^sub>H\<^sub>e"
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
  obtains e where "e \<in> g1.uedges G" "isin2 (V\<^sub>H\<^sub>e e) x"
proof -
  have "set2 (V\<^sub>H G) = \<Union> ((set2 o V\<^sub>H\<^sub>e) ` g1.uedges G)"
    using assms by (intro set_V\<^sub>H_G)
  then obtain e where "e \<in> g1.uedges G" "isin2 (V\<^sub>H\<^sub>e e) x"
    using assms set_invar_V\<^sub>H_G invar_vertices_of_H\<^sub>e g2.set_specs by auto
  thus ?thesis
    using that by auto
qed

lemma obtain_other_vertex_in_V\<^sub>H:
  assumes "g1.ugraph_adj_map_invar G" "isin2 (V\<^sub>H G) x"
  obtains y where "isin2 (V\<^sub>H G) y" "x \<noteq> y"
proof -
  obtain e where isin_e: "e \<in> g1.uedges G" and isin_x: "isin2 (V\<^sub>H\<^sub>e e) x"
    using assms by (elim isin_V\<^sub>H_obtain_edge)
  then obtain u v where [simp]: "rep1 e = rep1 (uEdge u v)"
    by (elim isin_vertices_of_H\<^sub>eE) thm isin_vertices_of_H\<^sub>eI
  consider "x = (rep1 e,u,1::nat)" | "x \<noteq> (rep1 e,u,1::nat)"
    by auto
  then obtain y where "isin2 (V\<^sub>H\<^sub>e e) y" and x_neq_y: "x \<noteq> y"
  proof cases
    let ?y="(rep1 e,u,2::nat)"
    assume "x = (rep1 e,u,1::nat)"
    moreover have "isin2 (V\<^sub>H\<^sub>e e) ?y"
      by (intro isin_vertices_of_H\<^sub>eI) auto
    ultimately show ?thesis
      using that isin_x by auto
  next
    let ?y="(rep1 e,u,1::nat)"
    assume "x \<noteq> (rep1 e,u,1::nat)"
    moreover have "isin2 (V\<^sub>H\<^sub>e e) ?y"
      by (intro isin_vertices_of_H\<^sub>eI) auto
    ultimately show ?thesis
      using that isin_x by auto
  qed
  hence "y \<in> set2 (V\<^sub>H\<^sub>e e)"
    using assms invar_vertices_of_H\<^sub>e g2.set_specs by blast
  hence "y \<in> \<Union> ((set2 o V\<^sub>H\<^sub>e) ` g1.uedges G)"
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