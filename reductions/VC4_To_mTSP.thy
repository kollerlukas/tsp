theory VC4_To_mTSP
  imports Main tsp.GraphAdjMap WeightedGraph
begin

locale VC4_To_mTSP = 
  G1: ugraph_adj_map map_empty1 update1 map_delete1 lookup1 map_invar1 set_empty1 insert1
      set_delete1 isin1 set1 set_invar1 rep1 \<comment> \<open>Adjacency map of the graph for VC4.\<close> +
  G2: ugraph_adj_map map_empty2 update2 map_delete2 lookup2 map_invar2 set_empty2 insert2
      set_delete2 isin2 set2 set_invar2 rep2 \<comment> \<open>Adjacency map of the graph for mTSP.\<close> +
  \<comment> \<open>Locales for the different fold functions (essentialy all fold functions are the same, but we 
  need to instantiate different locales because we cannot quantify over types).\<close>
  ugraph_adj_map_fold map_empty1 update1 map_delete1 lookup1 map_invar1 set_empty1 insert1
      set_delete1 isin1 set1 set_invar1 rep1 fold_G1_uedges1 +
  ugraph_adj_map_fold map_empty1 update1 map_delete1 lookup1 map_invar1 set_empty1 insert1
      set_delete1 isin1 set1 set_invar1 rep1 fold_G1_uedges2 +
  ugraph_adj_map_fold map_empty1 update1 map_delete1 lookup1 map_invar1 set_empty1 insert1
      set_delete1 isin1 set1 set_invar1 rep1 fold_G1_uedges3 +
  ugraph_adj_map_fold map_empty1 update1 map_delete1 lookup1 map_invar1 set_empty1 insert1
      set_delete1 isin1 set1 set_invar1 rep1 fold_G1_uedges4 +
  ugraph_adj_map_fold map_empty1 update1 map_delete1 lookup1 map_invar1 set_empty1 insert1
      set_delete1 isin1 set1 set_invar1 rep1 fold_G1_uedges5 +
  complete_graph_for_ugraph_adj_map map_empty2 update2 map_delete2 lookup2 map_invar2 set_empty2 insert2
      set_delete2 isin2 set2 set_invar2 fold_G2_vset
  for map_empty1 :: "'g1" and update1 :: "'v1 \<Rightarrow> 'v1set \<Rightarrow> 'g1 \<Rightarrow> 'g1" and map_delete1 lookup1 
      map_invar1 and set_empty1 :: "'v1set" and insert1 :: "'v1 \<Rightarrow> 'v1set \<Rightarrow> 'v1set" and set_delete1 
      isin1 set1 set_invar1 rep1 
  and map_empty2 :: "'g2" and update2 :: "'v1 uedge \<times> 'v1 \<times> nat \<Rightarrow> 'v2set \<Rightarrow> 'g2 \<Rightarrow> 'g2" and 
      map_delete2 lookup2 map_invar2 and set_empty2 :: "'v2set" and 
      insert2 :: "'v1 uedge \<times> 'v1 \<times> nat \<Rightarrow> 'v2set \<Rightarrow> 'v2set" and set_delete2 isin2 set2 set_invar2 
      rep2
  \<comment> \<open>Functions that fold the undirected edges of the graph for VC4. Multiple functions are needed 
  for types.\<close>
  and fold_G1_uedges1 :: "('v1 uedge \<Rightarrow> 'v2set \<Rightarrow> 'v2set) \<Rightarrow> 'g1 \<Rightarrow> 'v2set \<Rightarrow> 'v2set" 
  and fold_G1_uedges2 :: "('v1 uedge \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 'g1 \<Rightarrow> bool \<Rightarrow> bool"
  and fold_G1_uedges3 :: "('v1 uedge \<Rightarrow> enat \<Rightarrow> enat) \<Rightarrow> 'g1 \<Rightarrow> enat \<Rightarrow> enat"
  and fold_G1_uedges4 :: "('v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list) 
    \<Rightarrow> 'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list"
  and fold_G1_uedges5 :: "('v1 uedge \<Rightarrow> 'v1set \<Rightarrow> 'v1set) \<Rightarrow> 'g1 \<Rightarrow> 'v1set \<Rightarrow> 'v1set"
  \<comment> \<open>Function that fold over the finite set of vertices.\<close>
  and fold_G2_vset
begin

text \<open>
(uEdge u v,u,1) --- (uEdge u v,u,5) --- (uEdge u v,v,2)
       |                                        |
(uEdge u v,u,3) --- (uEdge u v,u,6) --- (uEdge u v,v,4)
       |                                        |
(uEdge u v,u,4) --- (uEdge u v,v,6) --- (uEdge u v,v,3)
       |                                        |
(uEdge u v,u,2) --- (uEdge u v,v,5) --- (uEdge u v,v,1)
\<close>

fun H\<^sub>e :: "'v1 uedge \<Rightarrow> 'g2" where
  "H\<^sub>e e = (case rep1 e of uEdge u v \<Rightarrow> let e = uEdge u v in
    update2 (e,u,1) (G2.set_of_list [(e,u,3),(e,u,5)])
    (update2 (e,u,2) (G2.set_of_list [(e,u,4),(e,v,5)])
    (update2 (e,u,3) (G2.set_of_list [(e,u,1),(e,u,4),(e,u,6)])
    (update2 (e,u,4) (G2.set_of_list [(e,u,2),(e,u,3),(e,v,6)])
    (update2 (e,u,5) (G2.set_of_list [(e,u,1),(e,v,2)])
    (update2 (e,u,6) (G2.set_of_list [(e,u,3),(e,v,4)])
    (update2 (e,v,1) (G2.set_of_list [(e,v,3),(e,v,5)])
    (update2 (e,v,2) (G2.set_of_list [(e,v,4),(e,u,5)])
    (update2 (e,v,3) (G2.set_of_list [(e,v,1),(e,v,4),(e,v,6)])
    (update2 (e,v,4) (G2.set_of_list [(e,v,2),(e,v,3),(e,u,6)])
    (update2 (e,v,5) (G2.set_of_list [(e,v,1),(e,u,2)])
    (update2 (e,v,6) (G2.set_of_list [(e,v,3),(e,u,4)]) map_empty2))))))))))))"

abbreviation "V_H\<^sub>e e \<equiv> case rep1 e of uEdge u v \<Rightarrow> G2.set_of_list (
  [(e,u,1),(e,u,2),(e,u,3),(e,u,4),(e,u,5),(e,u,6),
  (e,v,1),(e,v,2),(e,v,3),(e,v,4),(e,v,5),(e,v,6)])"

abbreviation "hc1_in_H\<^sub>e e \<equiv> (case rep1 e of uEdge u v \<Rightarrow> let e = uEdge u v in
  [(e,u,1),(e,u,5),(e,v,2),(e,v,4),(e,u,6),(e,u,3),
  (e,u,4),(e,v,6),(e,v,3),(e,v,1),(e,v,5),(e,u,2)])" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,u,1)\<close>.\<close>

abbreviation "hc2_in_H\<^sub>e e \<equiv> rev (hc1_in_H\<^sub>e e)" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,u,2)\<close>.\<close>

abbreviation "hc3_in_H\<^sub>e e \<equiv> (case rep1 e of uEdge u v \<Rightarrow> let e = uEdge u v in
  [(e,v,1),(e,v,5),(e,u,2),(e,u,4),(e,v,6),(e,v,3),
  (e,v,4),(e,u,6),(e,u,3),(e,u,1),(e,u,5),(e,v,2)])" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,v,1)\<close>.\<close>

abbreviation "hc4_in_H\<^sub>e e \<equiv> rev (hc3_in_H\<^sub>e e)" 
  \<comment> \<open>Hamiltonian path in \<open>H\<^sub>e e\<close> starting at \<open>(uEdge u v,v,2)\<close>.\<close>

end

section \<open>Implementation of Auxiliary Functions\<close>

context VC4_To_mTSP
begin

fun is_edge_in_H\<^sub>e :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) uedge \<Rightarrow> bool" where
  "is_edge_in_H\<^sub>e G (uEdge u v) = 
    fold_G1_uedges2 (\<lambda>e b. b \<or> isin2 (G2.neighborhood (H\<^sub>e e) v) u) G False"
  \<comment> \<open>Return \<open>True\<close> if the graph \<open>G\<close> contains an edge \<open>e\<close> in s.t. \<open>(uEdge u v)\<close> is an edge in the 
  subgraph \<open>H\<^sub>e e\<close>; return \<open>False\<close> otherwise.\<close>

fun are_vertices_in_H\<^sub>e :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> bool" where
  "are_vertices_in_H\<^sub>e G u v = 
    fold_G1_uedges2 (\<lambda>e b. b \<or> (isin2 (V_H\<^sub>e e) v \<and> isin2 (V_H\<^sub>e e) u)) G False"
  \<comment> \<open>Return \<open>True\<close> if the graph \<open>G\<close> contains an edge \<open>e\<close> in s.t. \<open>u\<close> and \<open>v\<close> are vertices in the 
  subgraph \<open>H\<^sub>e e\<close>; return \<open>False\<close> otherwise.\<close>

fun min_dist_in_H\<^sub>e :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> enat" where
  "min_dist_in_H\<^sub>e G u v = fold_G1_uedges3 (\<lambda>e d. min (G2.path_dist (H\<^sub>e e) u v) d) G \<infinity>"

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
  "g'_map_tour G T = fold_G1_uedges4 (\<lambda>e X'. g'_map_edge G e T#X') G []"

fun g_map_edge :: "'g1 \<Rightarrow> 'v1 uedge \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1" where
  "g_map_edge G e T = (case g'_map_edge G e T of (uEdge u v,x,i) \<Rightarrow> x)"
  \<comment> \<open>Map an edge \<open>e\<close> of the VC4-graph to a vertex \<open>x\<close> that covers \<open>e\<close> in \<open>G\<close>.\<close>

end

section \<open>Implementation of Reduction-Functions\<close>

context VC4_To_mTSP
begin

fun f :: "'g1 \<Rightarrow> 'g2" where
  "f G1 = complete_graph (fold_G1_uedges1 (G2.union o V_H\<^sub>e) G1 set_empty2)"

fun c :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> nat" where
  "c G (e\<^sub>1,v\<^sub>1,i\<^sub>1) (e\<^sub>2,v\<^sub>2,i\<^sub>2) = 
    (if is_edge_in_H\<^sub>e G (uEdge (e\<^sub>1,v\<^sub>1,i\<^sub>1) (e\<^sub>2,v\<^sub>2,i\<^sub>2)) then 1
    else if are_vertices_in_H\<^sub>e G (e\<^sub>1,v\<^sub>1,i\<^sub>1) (e\<^sub>2,v\<^sub>2,i\<^sub>2) then 
      the_enat (min_dist_in_H\<^sub>e G (e\<^sub>1,v\<^sub>1,i\<^sub>1) (e\<^sub>2,v\<^sub>2,i\<^sub>2))
    else if v\<^sub>1 = v\<^sub>2 \<and> e\<^sub>1 \<noteq> e\<^sub>2 then 4
    else 5)"

fun g :: "'g1 \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> 'v1set" where
  "g G T = fold_G1_uedges5 (\<lambda>e X. insert1 (g_map_edge G e T) X) G set_empty1"

(*
  Algorithm: given a Hamiltonian cycle T of G2.
  0. T' := T;
  1. for each {u,v} \<in> G1.
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

lemma vertices_of_H\<^sub>e: "G2.vertices (H\<^sub>e e) = set2 (V_H\<^sub>e e)"
  sorry

lemma "are_vertices_in_H\<^sub>e G u v \<longleftrightarrow> (\<exists>e. e \<in> G1.uedges G \<longrightarrow> u \<in> G2.vertices (H\<^sub>e e) \<and> v \<in> G2.vertices (H\<^sub>e e))"
  sorry

lemma "are_vertices_in_H\<^sub>e G u v \<Longrightarrow> min_dist_in_H\<^sub>e G u v < \<infinity>"
  sorry

lemma "is_edge_in_H\<^sub>e G e' \<longleftrightarrow> (\<exists>e. e \<in> G1.uedges G \<longrightarrow> e' \<in> G2.uedges (H\<^sub>e e))"
  sorry

fun hp_starting_at :: "('v1 uedge \<times> 'v1 \<times> nat) \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "hp_starting_at (e,x,i) = (case rep1 e of uEdge u v \<Rightarrow> let e = uEdge u v in
    if x = u \<and> i = 1 then hc1_in_H\<^sub>e e
    else if x = u \<and> i = 2 then hc2_in_H\<^sub>e e
    else if x = v \<and> i = 1 then hc3_in_H\<^sub>e e
    else if x = v \<and> i = 2 then hc4_in_H\<^sub>e e
    else hc1_in_H\<^sub>e e)"

fun tour_of_g'_map :: "('v1 uedge \<times> 'v1 \<times> nat) list \<Rightarrow> ('v1 uedge \<times> 'v1 \<times> nat) list" where
  "tour_of_g'_map [] = []"
| "tour_of_g'_map X' = concat (map hp_starting_at X') @ [hd X']"
  \<comment> \<open>Given a list of vertices \<open>X'\<close>, where each vertex marks the start of a Hamiltonian path, we 
  return a full tour.\<close>

lemma
  assumes "G1.ugraph_adj_map_invar G"
  shows "cost_of_path (c G) (tour_of_g'_map (g'_map_tour G T)) \<le> cost_of_path (c G) T"
  \<comment> \<open>The induced tour computed by the function \<open>g\<close> has lower cost compared to the original tour \<open>T\<close>.\<close>
  sorry (* TODO: tricky! *)

lemma
  obtains u where "G2.path_betw (f G) u (tour_of_g'_map (g'_map_tour G T)) u"
    sorry

lemma
  assumes "G2.is_hc (f G) T"
  shows "G2.is_hc (f G) (tour_of_g'_map (g'_map_tour G T))"
  \<comment> \<open>The induced tour computed by the function \<open>g\<close> is indeed a tour of the graph \<open>f G\<close>.\<close>
proof (intro G2.is_hcI)

  show "\<exists>u. G2.path_betw (f G) u (tour_of_g'_map (g'_map_tour G T)) u"
    sorry
    
  show "distinct (tl (tour_of_g'_map (g'_map_tour G T)))"
    sorry

  show "G2.vertices (f G) = set (tl (tour_of_g'_map (g'_map_tour G T)))"
    sorry
qed

end

section \<open>Properties of Reduction-Functions\<close>

context VC4_To_mTSP
begin

lemma f_is_complete: "is_complete (set_of_uedge ` G2.uedges (f G))"
  sorry

end

section \<open>Reduction Proofs\<close>

context VC4_To_mTSP
begin

lemma hc_from_vc:
  assumes "G1.is_vc G X"
  obtains T where "G2.is_hc (f G) T" "cost_of_path (c G) T = 15 * card (G1.uedges G) + card (set1 X)"
  sorry

lemma cost_of_mTSP:
  assumes opt_vc: "G1.is_min_vc G OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "G2.is_tsp (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 15 * card (G1.uedges G) + card (set1 OPT\<^sub>V\<^sub>C)"
proof -
  have "G1.is_vc G OPT\<^sub>V\<^sub>C"
    using assms by (elim G1.is_min_vcE)
  then obtain T where "G2.is_hc (f G) T" 
    "cost_of_path (c G) T = 15 * card (G1.uedges G) + card (set1 OPT\<^sub>V\<^sub>C)"
    by (elim hc_from_vc)
  moreover have "\<And>T. G2.is_hc (f G) T \<Longrightarrow> cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> cost_of_path (c G) T"
    using assms by (elim G2.is_tspE)
  ultimately show ?thesis
    by fastforce
qed

(* ----- 1st condition for a L-reduction ----- *)

lemma l_reduction1:
  assumes opt_vc: "G1.is_min_vc G OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "G2.is_tsp (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * card (set1 OPT\<^sub>V\<^sub>C)" (is "?c' OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> ?\<alpha> * ?c OPT\<^sub>V\<^sub>C")
  sorry (* TODO: use lemma VertexCover.vc_card_E_leq_max_degree *)

(* ----- 2nd condition for a L-reduction ----- *)

lemma
  assumes "G2.is_hc (f G) T"
  shows "G1.is_vc G (g G T)"
  sorry

lemma
  assumes "cost_of_path (c G) T \<le> 15 * card (G1.uedges G) + k"
  obtains k where "card (set1 (g G T)) \<le> k"
  sorry (* needed for proof of \<open>l_reduction2\<close> *)

lemma l_reduction2:
  assumes opt_vc: "G1.is_min_vc G OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "G2.is_tsp (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P" 
      and "G2.is_hc (f G) T"
  shows "\<bar> card (set1 (g G T)) - card (set1 OPT\<^sub>V\<^sub>C) \<bar> 
    \<le> 1 * \<bar> cost_of_path (c G) T - cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>"
  sorry

end

end