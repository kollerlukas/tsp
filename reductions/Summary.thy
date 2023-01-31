theory Summary
  imports VertexCover4ToMetricTravelingSalesman
begin

section \<open>Reduction Functions\<close>

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
  "g G T = fold_g1_uedges5 (insert1 o (map_edge_to_covering_vertex G T)) G set_empty1"

section \<open>Feasibility of Reduction Functions\<close>

lemma f_is_complete: 
  assumes "g1.ugraph_adj_map_invar G"
  shows "is_complete (set_of_uedge ` g2.uedges (f G))"
  \<comment> \<open>The graph \<open>f G\<close> is complete.\<close>
  sorry

lemma c_tri_inequality:
  assumes "x \<in> g2.vertices (f G)" "y \<in> g2.vertices (f G)" "z \<in> g2.vertices (f G)"
  shows "c G x z \<le> c G x y + c G y z"
  \<comment> \<open>The cost function \<open>c\<close> for the graph \<open>f G\<close> satisfies the triangle-inequality.\<close>
  sorry (* TODO *)

lemma g_is_vc:
  assumes "g1.ugraph_adj_map_invar G" and "g2.is_hc_Adj (f G) T"
  shows "g1.is_vc_Adj G (g G T)"
  \<comment> \<open>The function \<open>g\<close> always computes a vertex cover of the graph \<open>G\<close> (feasible solution).\<close>
  sorry

section \<open>Reduction Properties\<close>

lemma l_reduction1:
  assumes "g1.ugraph_adj_map_invar G" 
      and max_degree: "\<And>v. v \<in> g1.vertices G \<Longrightarrow> g1.degree_Adj G v \<le> enat 4"
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "g2.is_tsp_Adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * card (set1 OPT\<^sub>V\<^sub>C)" (is "?c' OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> ?\<alpha> * ?\<tau>_G")
  \<comment> \<open>First condition for a L-Reduction.\<close>
  sorry

lemma l_reduction2:
  assumes "g1.ugraph_adj_map_invar G"
      and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "g2.is_tsp_Adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P" 
      and "g2.is_hc_Adj (f G) T"
  shows "\<bar> card (set1 (g G T)) - card (set1 OPT\<^sub>V\<^sub>C) \<bar> 
    \<le> 1 * \<bar> cost_of_path (c G) T - cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>" (is "\<bar> card _ - ?\<tau>_G \<bar> \<le> _")
  \<comment> \<open>Second condition for a L-Reduction.\<close>
  sorry

end