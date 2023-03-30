theory VertexCover4ToMetricTravelingSalesman_AdjList                                                 
  imports VertexCover4ToMetricTravelingSalesman_Specs GraphAdjList
begin  

notation ugraph_adj_list.ugraph_adj_map_invar ("ugraph'_invar")
notation ugraph_adj_list.rep ("rep'_uedge")
notation ugraph_adj_list.neighborhood ("\<N>")

context ugraph_adj_map_by_linorder 
begin

\<comment> \<open>Compute representatives for induced graph.\<close>
fun rep_prod :: "('v uedge \<times> 'v \<times> nat) uedge \<Rightarrow> ('v uedge \<times> 'v \<times> nat) uedge" where
  "rep_prod (uEdge (uEdge u\<^sub>1 v\<^sub>1,w\<^sub>1,i\<^sub>1) (uEdge u\<^sub>2 v\<^sub>2,w\<^sub>2,i\<^sub>2)) = 
    (let e\<^sub>1 = (uEdge u\<^sub>1 v\<^sub>1,w\<^sub>1,i\<^sub>1); e\<^sub>2 = (uEdge u\<^sub>2 v\<^sub>2,w\<^sub>2,i\<^sub>2) in
    if u\<^sub>1 < u\<^sub>2 then uEdge e\<^sub>1 e\<^sub>2
    else if u\<^sub>2 < u\<^sub>1 then uEdge e\<^sub>2 e\<^sub>1
    else if v\<^sub>1 < v\<^sub>2 then uEdge e\<^sub>1 e\<^sub>2
    else if v\<^sub>2 < v\<^sub>1 then uEdge e\<^sub>2 e\<^sub>1
    else if w\<^sub>1 < w\<^sub>2 then uEdge e\<^sub>1 e\<^sub>2
    else if w\<^sub>2 < w\<^sub>1 then uEdge e\<^sub>2 e\<^sub>1
    else if i\<^sub>1 < i\<^sub>2 then uEdge e\<^sub>1 e\<^sub>2
    else if i\<^sub>2 < i\<^sub>1 then uEdge e\<^sub>2 e\<^sub>1
    else uEdge e\<^sub>1 e\<^sub>2)" (* TODO: is there a way of automizing this? *)

lemma rep_prod_is_rep_sym: "rep_prod (uEdge x y) = rep_prod (uEdge y x)" 
proof (cases x; cases y)
  fix e\<^sub>1 w\<^sub>1 i\<^sub>1 e\<^sub>2 w\<^sub>2 i\<^sub>2
  assume [simp]: "x = (e\<^sub>1,w\<^sub>1,i\<^sub>1)" and [simp]: "y = (e\<^sub>2,w\<^sub>2,i\<^sub>2)"
  show ?thesis
    by (cases e\<^sub>1; cases e\<^sub>2) (auto simp add: Let_def)
qed

lemma rep_prod_is_rep_cases: "rep_prod (uEdge x y) = uEdge x y \<or> rep_prod (uEdge x y) = uEdge y x"
proof (cases x; cases y)
  fix e\<^sub>1 w\<^sub>1 i\<^sub>1 e\<^sub>2 w\<^sub>2 i\<^sub>2
  assume [simp]: "x = (e\<^sub>1,w\<^sub>1,i\<^sub>1)" and [simp]: "y = (e\<^sub>2,w\<^sub>2,i\<^sub>2)"
  show ?thesis
    by (cases e\<^sub>1; cases e\<^sub>2) (auto simp add: Let_def)
qed

lemmas rep_prod_is_rep = rep_prod_is_rep_sym rep_prod_is_rep_cases

end

notation ugraph_adj_list.rep_prod ("rep'_uedge'_prod")

abbreviation "uedge \<equiv> \<lambda>u v. rep_uedge (uEdge u v)"

lemma inj_rep_uedge_uv: "inj_on (uedge u) X"
  by rule (auto split: if_splits)

fun edges_from where "edges_from (u,Nu) = map (uedge u) (filter (\<lambda>v. uEdge u v = uedge u v) Nu)"

fun uedges where "uedges G = concat (map edges_from G)"

lemma distinct_edges_from: "distinct Nu \<Longrightarrow> distinct (edges_from (u,Nu))"
  using inj_rep_uedge_uv by (auto simp add: distinct_map)

lemma isin_edges_from_elim: 
  assumes "x \<in> set (edges_from (u,Nu))"
  obtains v where "v \<in> set Nu" "x = uEdge u v" "x = uedge u v"
  using assms by fastforce

lemma isin_edges_from_intro: 
  assumes "v \<in> set Nu" "x = uEdge u v" "x = uedge u v" 
  shows "x \<in> set (edges_from (u,Nu))"
  using assms by fastforce

lemma disjoint_edges_from: 
  assumes "ugraph_invar G" "(u,Nu) \<in> set G" "(v,Nv) \<in> set G" "(u,Nu) \<noteq> (v,Nv)"
  shows "set (edges_from (u,Nu)) \<inter> set (edges_from (v,Nv)) = {}"
proof (rule ccontr)
  assume "set (edges_from (u,Nu)) \<inter> set (edges_from (v,Nv)) \<noteq> {}"
  then obtain w\<^sub>1 w\<^sub>2 where "uEdge u w\<^sub>1 = uEdge v w\<^sub>2"
    by (auto elim: isin_edges_from_elim)
  moreover have "u \<noteq> v"
    using assms lmap_unique_assoc by fastforce
  ultimately show "False"
    by auto
qed

lemma distinct_uedges_adj_list: 
  assumes "ugraph_invar G"
  shows "distinct (uedges G)"
  apply (subst uedges.simps)
  apply (rule distinct_concat_map)
proof -
  have "distinct (map fst G)"
    using assms by auto
  thus "distinct G"
    by (metis distinct_zipI1 zip_map_fst_snd)
  show "\<And>x. x \<in> set G \<Longrightarrow> distinct (edges_from x)" 
  proof -
    fix x
    assume "x \<in> set G"
    moreover obtain u Nu where [simp]: "x = (u,Nu)"
      by (cases x)
    ultimately have "\<N> G u = Nu"
      using assms isin_lmap_neighborhood by auto
    hence "distinct Nu"
      using assms by auto
    thus "distinct (edges_from x)"
      by (simp del: edges_from.simps) (intro distinct_edges_from)
  qed
  show "\<And>x y. x \<in> set G \<Longrightarrow> y \<in> set G \<Longrightarrow> x \<noteq> y \<Longrightarrow> set (edges_from x) \<inter> set (edges_from y) = {}"
  proof -
    fix x y
    assume "x \<in> set G" "y \<in> set G" "x \<noteq> y"
    moreover obtain u Nu v Nv where [simp]: "x = (u,Nu)" and [simp]: "y = (v,Nv)"
      by (cases x; cases y)
    ultimately show "set (edges_from x) \<inter> set (edges_from y) = {}"
      apply (simp del: edges_from.simps)
      apply (intro disjoint_edges_from)
      using assms by auto
  qed
qed

lemma uedges_rep_idem: "map rep_uedge (uedges G) = (uedges G)"
  by (induction G) (auto simp add: ugraph_adj_list.rep_idem simp del: ugraph_adj_list.rep.simps)
  
lemma set_uedges:
  assumes "ugraph_invar G"
  shows "set (uedges G) = ugraph_adj_list.uedges G"
proof
  show "set (uedges G) \<subseteq> ugraph_adj_list.uedges G"
  proof
    fix x
    assume "x \<in> set (uedges G)"
    then obtain u Nu where "(u,Nu) \<in> set G" "x \<in> set (edges_from (u,Nu))"
      by auto
    moreover then obtain v where "v \<in> set Nu" and [simp]: "x = uedge u v"
      by (elim isin_edges_from_elim)
    moreover have [simp]: "\<N> G u = Nu"
      using assms calculation isin_lmap_neighborhood by auto
    ultimately have "lset_isin (\<N> G u) v"
      using assms by (auto simp add: lset_isin simp del: lset_isin.simps)
    thus "x \<in> ugraph_adj_list.uedges G"
      unfolding ugraph_adj_list.uedges_def2 by auto
  qed
next
  show "ugraph_adj_list.uedges G \<subseteq> set (uedges G)"
  proof
    fix x
    assume "x \<in> ugraph_adj_list.uedges G"
    then obtain u v where [simp]: "x = uedge u v" and v_isin_Nu: "lset_isin (\<N> G u) v" (is "lset_isin ?Nu v")
      unfolding ugraph_adj_list.uedges_def2 by auto
    moreover hence u_isin_Nv: "lset_isin (\<N> G v) u" (is "lset_isin ?Nv u")
      using assms by auto
    ultimately consider "x = uEdge u v" | "x = uEdge v u"
      using ugraph_adj_list.is_rep by auto
    thus "x \<in> set (uedges G)"
    proof cases
      assume "x = uEdge u v"
      moreover have "v \<in> lset_set (\<N> G u)"
        using assms v_isin_Nu lset_isin by metis
      ultimately have "x \<in> set (edges_from (u,?Nu))"
        by (intro isin_edges_from_intro) simp+
      moreover have "lmap_lookup G u = Some ?Nu" 
        using v_isin_Nu by (intro ugraph_adj_list.lookup_non_empty_neighborhood)
      moreover hence "(u,?Nu) \<in> set G"
        using assms isin_lmap_lookup by metis
      ultimately show "x \<in> set (uedges G)"
        by force
    next
      assume "x = uEdge v u"
      moreover have "x = uedge v u"
        using ugraph_adj_list.is_rep by auto
      moreover have "u \<in> lset_set (\<N> G v)"
        using assms v_isin_Nu lset_isin by metis
      ultimately have "x \<in> set (edges_from (v,?Nv))"
        by (intro isin_edges_from_intro) simp+
      moreover have "lmap_lookup G v = Some ?Nv" 
        using u_isin_Nv by (intro ugraph_adj_list.lookup_non_empty_neighborhood)
      moreover hence "(v,?Nv) \<in> set G"
        using assms isin_lmap_lookup by metis
      ultimately show "x \<in> set (uedges G)"
        by force
    qed
  qed
qed

fun fold_uedges where
  "fold_uedges f G = fold f (uedges G)"

lemma fold_uedges:
  assumes "ugraph_invar G"
  obtains es where "distinct es" "map rep_uedge es = es" 
    "set es = ugraph_adj_list.uedges G" "fold_uedges f G a = fold f es a"
proof (rule that)
  let ?es="uedges G"
  show "distinct ?es"
    using assms by (intro distinct_uedges_adj_list)
  show "map rep_uedge ?es = ?es"
    using assms by (intro uedges_rep_idem)
  show "set ?es = ugraph_adj_list.uedges G"
    using assms by (intro set_uedges)
  show "fold_uedges f G a = fold f ?es a"
    by auto
qed

interpretation fold_uedges: ugraph_adj_map_fold_uedges
  lmap_empty lmap_update lmap_delete lmap_lookup lmap_invar lset_empty lset_insert lset_delete 
  lset_isin lset_set lset_invar lset_union lset_inter lset_diff
  rep_uedge fold_uedges
  apply unfold_locales 
  apply (elim fold_uedges)
  apply auto
  done

fun fold_vset where
  "fold_vset f X = fold f X"

lemma finite_lsets: "finite (lset_set X)"
  by auto

lemma fold_vset: 
  assumes "lset_invar X"
  obtains xs where "distinct xs" "set xs = lset_set X" "fold_vset f X a = fold f xs a"
  using assms by auto

interpretation fold_vset: ugraph_adj_map_fold_vset
  lmap_empty lmap_update lmap_delete lmap_lookup lmap_invar lset_empty lset_insert lset_delete 
  lset_isin lset_set lset_invar lset_union lset_inter lset_diff
  rep_uedge fold_vset
  apply unfold_locales
  using finite_lsets apply simp
  apply (elim fold_vset)
  apply auto
  done

interpretation lreduction: VC4_To_mTSP
  (* graph representation 1 *) lmap_empty lmap_update lmap_delete lmap_lookup lmap_invar lset_empty 
  lset_insert lset_delete lset_isin lset_set lset_invar lset_union lset_inter lset_diff rep_uedge
  (* graph representation 2 *) lmap_empty lmap_update lmap_delete lmap_lookup lmap_invar lset_empty 
  lset_insert lset_delete lset_isin lset_set lset_invar lset_union lset_inter lset_diff rep_uedge_prod
  fold_uedges fold_uedges fold_uedges fold_uedges fold_uedges
  fold_vset fold_vset fold_vset
  choose_edge
  apply unfold_locales
  apply (rule ugraph_adj_list.rep_prod_is_rep(1))
  apply (rule ugraph_adj_list.rep_prod_is_rep(2))
  apply (elim fold_uedges; blast)
  apply (elim fold_uedges; blast)
  apply (elim fold_uedges; blast)
  apply (elim fold_uedges; blast)
  using finite_lsets apply simp
  apply (elim fold_vset; blast)
  apply (elim fold_vset; blast)
  using finite_lsets apply simp
  apply (elim fold_vset; blast)
  apply (rule choose_edge) 
  apply simp
  apply simp
  done

\<comment> \<open>Functions\<close>
thm lreduction.f.simps
thm lreduction.c.simps
thm lreduction.g.simps

fun f_adjlist where
  "f_adjlist G = (
    let V = fold_uedges (lset_union o lreduction.vertices_of_He) G lset_empty;
        n = \<lambda>x. (if lset_isin V x then lset_delete x V else lset_empty) in 
    fold_vset (\<lambda>v. lmap_update v (n v)) V lmap_empty)"

lemma "f_adjlist = lreduction.f"
  unfolding f_adjlist.simps Let_def lreduction.f.simps lreduction.complete_graph.simps 
    lreduction.graph_of_vertices.simps lreduction.vertices_of_H.simps 
    lreduction.neighborhood_compl.simps by simp

\<comment> \<open>Feasibility\<close>
thm lreduction.f_is_complete
thm lreduction.c_tri_inequality
thm lreduction.g_is_vc

\<comment> \<open>Correctness\<close>
thm lreduction.l_reduction1
thm lreduction.l_reduction2

end