(* Author: Lukas Koller *)
theory DoubleTree
  imports Main MST TSP Eulerian
begin

section \<open>\textsc{DoubleTree} Approximation Algorithm for \textsc{mTSP}\<close>

text \<open>Compute a Hamiltonian Cycle of an Eulerian Tour.\<close>
fun comp_hc_of_et :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "comp_hc_of_et [] H = H"
| "comp_hc_of_et [v] H = v#H"
| "comp_hc_of_et (v#P) H = (if v \<in> set H then comp_hc_of_et P H else comp_hc_of_et P (v#H))"

lemma comp_hc_of_et_remdups_aux:
  assumes "distinct H" "length P > 0"
  shows "comp_hc_of_et P H = last P # remdups (rev (butlast P) @ H)"
  using assms
proof (induction P H rule: comp_hc_of_et.induct)
  case (3 u v P H)
  thus ?case by (fastforce simp: remdups_append)
qed (auto simp: distinct_remdups_id)

text \<open>This lemma is not needed. Just to show a different way of implementing \<open>comp_hc_of_et\<close> 
using \<open>remdups\<close>.\<close>
lemma comp_hc_of_et_remdups: 
  "comp_hc_of_et P [] = (if length P > 0 then last P#remdups (rev (butlast P)) else [])"
  using comp_hc_of_et_remdups_aux[of "[]" P] by auto

lemma hc_of_et_hd: "P \<noteq> [] \<Longrightarrow> last P = hd (comp_hc_of_et P H)"
  by (induction P H rule: comp_hc_of_et.induct) auto

lemma hc_of_et_last_aux: "H \<noteq> [] \<Longrightarrow> last H = last (comp_hc_of_et P H)"
  by (induction P H rule: comp_hc_of_et.induct) auto

lemma hc_of_et_last: "P \<noteq> [] \<Longrightarrow> hd P = last (comp_hc_of_et P [])"
proof (induction P rule: list012.induct)
  case (3 u v P)
  then show ?case 
    using hc_of_et_last_aux[of "[u]" "v#P"] by auto
qed auto

lemma hc_of_et_set_eq: "set P \<union> set H = set (comp_hc_of_et P H)"
  by (induction P H rule: comp_hc_of_et.induct) auto

lemma hc_of_et_non_nil: "P \<noteq> [] \<Longrightarrow> (comp_hc_of_et P H) \<noteq> []"
  by (induction P H rule: comp_hc_of_et.induct) auto

lemma hc_of_et_distinct: "distinct H \<Longrightarrow> distinct (tl (comp_hc_of_et P H))"
  by (induction P H rule: comp_hc_of_et.induct) (auto simp: Let_def distinct_tl)

lemma hc_of_et_vs:
  assumes "is_et X P" 
  shows "set (comp_hc_of_et P []) = mVs X"
proof
  show "set (comp_hc_of_et P []) \<subseteq> mVs X"
    using assms mem_path_Vs[of "set_mset X" P] is_etE[of X P]
          hc_of_et_set_eq[of P "[]"] by (auto simp: mpath_def2 mVs_def)
next
  show "mVs X \<subseteq> set (comp_hc_of_et P [])"
    unfolding mVs_def
  proof
    fix v
    assume "v \<in> Vs (set_mset X)"
    then obtain e where "e \<in># X" "v \<in> e"
      by (auto elim: vs_member_elim)
    moreover hence "e \<in># mset (edges_of_path P)"
      using assms is_etE[of X P] by auto
    ultimately show "v \<in> set (comp_hc_of_et P [])"
      using v_in_edge_in_path_gen[of e P v] hc_of_et_set_eq[of P] by auto
  qed
qed

lemma et_distinct_adj:
  assumes "mgraph_invar X" "is_et X P"
  shows "distinct_adj P"
proof -
  have "path (set_mset X) P"
    using assms is_etE by (auto simp: mpath_def2)
  thus ?thesis
    using assms path_distinct_adj by auto
qed     

lemma distinct_adj_tl_comp_hc_of_et:
  assumes "distinct_adj P" "distinct H"
  shows "distinct_adj (tl (comp_hc_of_et P H))"
  using assms by (induction P H rule: comp_hc_of_et.induct) 
    (auto simp: distinct_tl distinct_distinct_adj)

lemma hd_remdups_append:
  assumes "x = hd (remdups (xs@[x]))"
  shows "xs = [] \<or> xs = [x] \<or> \<not> distinct_adj xs"
  using assms by (induction xs) (auto split: if_splits simp: distinct_adj_Cons)

lemma hd_tl_comp_hc_of_et_not_distinct_adj:
  assumes "u = hd (tl (comp_hc_of_et (u#P@[u]) []))"
  shows "\<not> distinct_adj (u#P@[u])" (is "\<not> distinct_adj ?P")
proof -
  have "u = hd (remdups (rev P@[u]))"
    using assms by (auto simp: comp_hc_of_et_remdups[of ?P])
  hence "P = [] \<or> P = [u] \<or> \<not> distinct_adj P"
    using hd_remdups_append[of u "rev P"] by auto
  thus ?thesis
    by (elim disjE) (auto simp: distinct_adj_Cons distinct_adj_append_iff)
qed

lemma distinct_adj_last_neq_hd_tl:
  assumes "distinct_adj P" "length P > 1" "hd P = last P"
  shows "last P \<noteq> hd (tl (comp_hc_of_et P []))"
proof (rule ccontr; simp)
  assume "last P = hd (tl (comp_hc_of_et P []))"
  moreover obtain u P' where "P = u#P'@[u]"
    using assms
    by (metis append_butlast_last_id append_self_conv2 distinct_hd_last_neq distinct_singleton 
        dual_order.strict_trans length_greater_0_conv less_one list.collapse tl_append2)
    (* TODO: clean up! *)
  ultimately have "\<not> distinct_adj P"
    using hd_tl_comp_hc_of_et_not_distinct_adj[of u P'] by auto
  thus "False"
    using assms by auto
qed

lemma distinct_adj_comp_hc_of_et:
  assumes "distinct_adj P" "P \<noteq> [] \<Longrightarrow> hd P = last P"
  shows "distinct_adj (comp_hc_of_et P [])"
  using assms
proof (induction  P rule: list012.induct) (* induction just for case distinction *)
  case (3 u v P)
  moreover hence "last (u#v#P) \<noteq> hd (tl (comp_hc_of_et (u#v#P) []))"
    using distinct_adj_Cons[of u "v#P"] distinct_adj_last_neq_hd_tl[of "u#v#P"] by auto
  moreover have "distinct_adj (tl (comp_hc_of_et (u#v#P) []))"
    using distinct_distinct_adj[OF hc_of_et_distinct[of "[]" "u#v#P"]] by auto
  ultimately show ?case 
    using comp_hc_of_et_remdups[of "u#v#P"] by (auto simp: distinct_adj_Cons)  
qed auto

locale hc_of_et = 
  metric_graph_abs E c + 
  mst E c comp_mst + 
  eulerian comp_et for E :: "'a set set" and c comp_mst and comp_et :: "'a mgraph \<Rightarrow> 'a list"
begin

lemma hc_of_et_path:
  assumes "is_et X P" "set_mset X \<subseteq> E"
  shows "path E (comp_hc_of_et P [])" (is "path E ?H")
proof -
  have "set P \<subseteq> Vs E"
    using assms Vs_subset[of "set_mset X" E] is_etE[of X P]
    by (auto simp: mpath_def2 mem_path_Vs subsetI)
  hence "set ?H \<subseteq> Vs E"
    using hc_of_et_set_eq[of P "[]"] by auto
  moreover have "mgraph_invar X"
    using assms graph finite_subset[OF Vs_subset, of "set_mset X" E] by auto
  moreover have "distinct_adj (comp_hc_of_et P [])"
    using calculation assms et_distinct_adj distinct_adj_comp_hc_of_et by (fastforce simp: is_etE)
  ultimately show ?thesis
    unfolding mpath_def using path_complete_graph[of ?H] by auto
qed

lemma hc_of_et_cycle:
  assumes "P \<noteq> []" "is_et X P"
  shows "hd (comp_hc_of_et P []) = last (comp_hc_of_et P [])" (is "hd ?H = last ?H")
proof -
  have "hd ?H = last P"
    using assms hc_of_et_hd[of P "[]"] by auto
  also have "... = hd P"
    using assms by (auto simp: is_etE)
  also have "... = last ?H"
    using assms hc_of_et_last by auto
  finally show ?thesis .
qed

lemma hc_of_et_walk_betw:
  assumes "P \<noteq> []" "is_et X P" "set_mset X \<subseteq> E"
  obtains v where "walk_betw E v (comp_hc_of_et P []) v"
proof
  let ?H="comp_hc_of_et P []"
  let ?v="hd ?H"
  show "walk_betw E ?v ?H ?v"
  proof (rule nonempty_path_walk_between)
    show "path E ?H" "?H \<noteq> []" "hd ?H = ?v" "last ?H = ?v"
      using assms hc_of_et_path[of X P] hc_of_et_non_nil[of P "[]"] hc_of_et_cycle[of P X] by auto
  qed
qed

lemma hc_of_et_correct: 
  assumes "is_et X P" "mVs X = Vs E" "set_mset X \<subseteq> E"
  shows "is_hc (comp_hc_of_et P [])"
proof (cases "P = []")
  case True
  hence "X = {#}"
    using assms et_nil[of X] by auto
  hence "Vs E = {}"
    using assms by (auto simp: mVs_def Vs_def)
  hence "E = {}"
    using vs_member[of _ E] graph by fastforce
  then show ?thesis 
    using \<open>P = []\<close> hc_nil_iff by auto
next
  case False
  then obtain v where "comp_hc_of_et P [] \<noteq> []" "walk_betw E v (comp_hc_of_et P []) v"
    using assms hc_of_et_non_nil by (auto elim: hc_of_et_walk_betw[of P X])
  then show ?thesis
    apply (rule is_hcI_non_nil)
    using assms hc_of_et_walk_betw[of P X] hc_of_et_vs[of X P] hc_of_et_distinct[of "[]" P] 
          hc_of_et_cycle[of P X] by auto
qed

lemma cost_of_path_hc_of_et:
  assumes "set P \<union> set H \<subseteq> Vs E"
  shows "cost_of_path (comp_hc_of_et P H) \<le> cost_of_path (rev P @ H)"
  using assms
proof (induction P H rule: comp_hc_of_et.induct)
  case (3 u v P H)
  then show ?case 
    using cost_of_path_app_tri_ineq[of "rev (v#P)" H u] by auto
qed auto

lemma hc_of_et_reduces_cost: "set P \<subseteq> Vs E \<Longrightarrow> cost_of_path (comp_hc_of_et P []) \<le> cost_of_path P"
  using cost_of_path_hc_of_et[of P "[]"] cost_of_path_rev[of P] by auto

end

locale double_tree_algo = 
  metric_graph_abs E c + 
  mst E c comp_mst + 
  eulerian comp_et for E :: "'a set set" and c comp_mst and comp_et :: "'a mgraph \<Rightarrow> 'a list"
begin

definition double_tree where
  "double_tree = (
    let T = comp_mst c E;
        T\<^sub>2\<^sub>x = mset_set T + mset_set T;
        P = comp_et T\<^sub>2\<^sub>x in
        comp_hc_of_et P [])"

lemma T2x_eulerian:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T"
  shows "is_eulerian T\<^sub>2\<^sub>x"
  using assms[unfolded is_mst_def is_st_def] finite_E finite_subset[of T E]
        double_graph_eulerian[of T T\<^sub>2\<^sub>x] by auto

lemma T2x_vs:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T"
  shows "mVs T\<^sub>2\<^sub>x = Vs E"
  using assms[unfolded is_mst_def is_st_def] finite_subset[OF _ finite_E] by (auto simp: mVs_def) 

lemma T2x_edges:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T"
  shows "set_mset T\<^sub>2\<^sub>x \<subseteq> E"
  using assms[unfolded is_mst_def is_st_def] finite_subset[OF _ finite_E] by auto 

lemmas dt_correctness = T2x_eulerian[OF mst] T2x_vs[OF mst] T2x_edges[OF mst]

end

subsection \<open>Feasibility of \textsc{DoubleTree}\<close>

locale double_tree_algo_feasibility =
  hc_of_et +
  double_tree_algo
begin

lemma "is_hc (double_tree)" (is "is_hc ?H")
  apply (simp only: double_tree_def Let_def)
  apply (rule hc_of_et_correct, rule eulerian)
  using dt_correctness by auto

end

subsection \<open>Approximation of \textsc{DoubleTree}\<close>

locale double_tree_algo_approx =
  hc_of_et +
  double_tree_algo
begin

lemma cost_of_et:
  assumes "is_et T P" 
  shows "cost_of_path P = (\<Sum>e\<in>#T. c e)"
  using assms cost_of_path_sum[of P] et_edges[of T P] by auto

lemma et_not_single_v:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T" "is_et T\<^sub>2\<^sub>x P"
  shows "length P \<noteq> 1"
  using assms
proof (induction P rule: list012.induct) (* induction just for case distinction *)
  case (2 v)
  hence "T\<^sub>2\<^sub>x = {#}" "mpath T\<^sub>2\<^sub>x [v]"
    using is_etE[of T\<^sub>2\<^sub>x "[v]"] by auto
  hence "mVs T\<^sub>2\<^sub>x = {}" "v \<in> mVs T\<^sub>2\<^sub>x"
    unfolding mpath_def2 by (auto simp: mVs_def Vs_def)
  then show ?case by auto
qed auto

lemma hc_of_et_cost_le_dt:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T" "is_et T\<^sub>2\<^sub>x P"
  shows "cost_of_path (comp_hc_of_et P []) \<le> 2 * cost_of_st T"
proof -
  have "set P \<subseteq> Vs E"
    using assms et_vertices_len_neq_1[of T\<^sub>2\<^sub>x P, OF _ et_not_single_v] T2x_vs[of T T\<^sub>2\<^sub>x] by auto
  hence "cost_of_path (comp_hc_of_et P []) \<le> cost_of_path P"
    using hc_of_et_reduces_cost[of P] by auto
  also have "... = (\<Sum>e\<in>#T\<^sub>2\<^sub>x. c e)"
    using assms cost_of_et by auto
  also have "... = (\<Sum>e\<in>T. c e) + (\<Sum>e\<in>T. c e)"
    using assms by (simp add: sum_unfold_sum_mset)
  also have "... = 2 * (\<Sum>e\<in>T. c e)"
    using mult_2 by auto
  also have "... = 2 * cost_of_st T"
    by (auto simp: cost_of_st_def)
  finally show ?thesis .
qed

lemma dt_mst_approx:
  assumes "is_mst T"
  shows "cost_of_path double_tree \<le> 2 * cost_of_st T"
proof -
  let ?T="comp_mst c E"
  let ?T\<^sub>2\<^sub>x="mset_set ?T + mset_set ?T"
  let ?P="comp_et ?T\<^sub>2\<^sub>x"
  
  have "cost_of_path double_tree = cost_of_path (comp_hc_of_et ?P [])"
    unfolding double_tree_def by (auto simp: Let_def)
  also have "... \<le> 2 * cost_of_st ?T"
    using mst hc_of_et_cost_le_dt[of ?T ?T\<^sub>2\<^sub>x ?P] eulerian[OF T2x_eulerian, of ?T ?T\<^sub>2\<^sub>x] by auto
  also have "... = 2 * cost_of_st T"
    using assms mst_eq_cost[OF mst, of T] by auto
  finally show ?thesis .
qed

lemma hc_connected_component:
  assumes "is_hc H" "u = (tl H) ! i\<^sub>u" "i\<^sub>u < length (tl H)" "v = (tl H) ! i\<^sub>v" "i\<^sub>v < length (tl H)" 
          "i\<^sub>u < i\<^sub>v" 
  shows "u \<in> connected_component (set (edges_of_path (tl H))) v" 
    (is "u \<in> connected_component ?E' v")
proof -
  let ?P="drop (i\<^sub>u + 1) (take (i\<^sub>v + 2) H)"
  let ?P'="drop i\<^sub>u (take (i\<^sub>v + 1) (tl H))"
  have "?P = ?P'"
    using drop_tl[of "i\<^sub>u + 1" "take (i\<^sub>v + 2) H"] tl_take[of "i\<^sub>v + 2" H] by auto

  have "u = H ! (i\<^sub>u + 1)" "v = H ! (i\<^sub>v + 1)"
    using assms nth_tl[of _ H] by auto
  hence "walk_betw E u ?P v" "length ?P > 1"
    using assms hc_walk_betw1[of H "i\<^sub>u + 1" "i\<^sub>v + 1"] by auto
  hence "walk_betw (set (edges_of_path ?P')) u ?P' v"
    using assms \<open>?P = ?P'\<close> walk_on_edges_of_path[of E u ?P v] by auto
  hence "walk_betw ?E' u ?P' v"
    using edges_of_path_drop_take_subset[of i\<^sub>u "i\<^sub>v + 1" "tl H"] 
            walk_subset[of "set (edges_of_path ?P')" ?E'] by auto
  then show "u \<in> connected_component ?E' v"
    using walk_symmetric[of ?E' u _ v] by auto
qed

lemma tl_hc_connected:
  assumes "is_hc H"
  shows "is_connected (set (tl (edges_of_path H)))" (is "is_connected ?E'")
proof (rule is_connectedI)
  fix u v
  assume "u \<in> Vs ?E'" "v \<in> Vs ?E'"
  hence "u \<in> Vs (set (edges_of_path (tl H)))" "v \<in> Vs (set (edges_of_path (tl H)))"
    by (auto simp: edges_of_path_tl)
  hence "u \<in> set (tl H)" "v \<in> set (tl H)"
    using assms edges_of_path_Vs[of "tl H"] by auto
  then obtain i\<^sub>u i\<^sub>v where i\<^sub>u_i\<^sub>v_simps:"u = (tl H) ! i\<^sub>u" "i\<^sub>u < length (tl H)" 
    "v = (tl H) ! i\<^sub>v" "i\<^sub>v < length (tl H)"
    using set_conv_nth[of "tl H"] by auto

  have "i\<^sub>u = i\<^sub>v \<or> i\<^sub>u < i\<^sub>v \<or> i\<^sub>v < i\<^sub>u"
    by auto
  then show "u \<in> connected_component ?E' v"
  proof (elim disjE)
    assume "i\<^sub>u = i\<^sub>v"
    hence "u = v"
      using i\<^sub>u_i\<^sub>v_simps by auto
    then show "u \<in> connected_component ?E' v"
      using in_own_connected_component by auto
  next
    assume "i\<^sub>u < i\<^sub>v"
    then show "u \<in> connected_component ?E' v"
      using assms i\<^sub>u_i\<^sub>v_simps hc_connected_component by (auto simp: edges_of_path_tl)
  next
    assume "i\<^sub>v < i\<^sub>u"
    hence "v \<in> connected_component ?E' u"
      using assms i\<^sub>u_i\<^sub>v_simps hc_connected_component by (auto simp: edges_of_path_tl)
    then show "u \<in> connected_component ?E' v"
      using connected_components_member_sym[of v ?E' u] by auto
  qed
qed

lemma hc_degree_leq_2:
  assumes "is_hc H" "x \<in> set H"
  shows "degree (set (tl (edges_of_path H))) x \<le> 2"
  using assms i0_lb
proof (induction H rule: list0123.induct) (* induction just for case distinction *)
  case (4 u v w P)
  moreover hence "distinct (v#w#P)" "length (v#w#P) > 1"
    by (elim is_hc_nonnilE) auto
  moreover have "x \<in> set (v#w#P)"
    using calculation hc_vs_set[of "u#v#w#P"] is_hc_nonnilE[of "u#v#w#P"] by auto
  ultimately show ?case
    using degree_edges_of_path_leq_2[of "v#w#P"] by (auto simp: edges_of_path_tl)
qed auto

lemma degree_edges_of_path_hd_leq_1:
  assumes "distinct P"
  shows "degree (set (edges_of_path P)) (hd P) \<le> 1" (is "degree ?E\<^sub>P (hd P) \<le> 1")
  using assms
proof (induction P rule: list012.induct) (* induction just for case distinction *)
  case (3 u v P)
  then show ?case 
    using degree_edges_of_path_hd by fastforce
qed auto (* induction just for case distinction *)

lemma non_acyclic_path_not_distinct:
  assumes "path E P" "\<not> is_acyclic (set (edges_of_path P))" (is "\<not> is_acyclic ?E\<^sub>P")
  shows "\<not> distinct P"
proof
  assume "distinct P"

  have "?E\<^sub>P \<subseteq> E"
    using assms path_edges_subset by auto
  hence graph_E\<^sub>P: "graph_invar ?E\<^sub>P"
    using graph finite_subset[OF Vs_subset[of ?E\<^sub>P E]] by auto
  moreover obtain C where cycle_C: "is_cycle ?E\<^sub>P C"
    using assms by (auto elim: not_acyclicE)
  ultimately have "length C > 2"
    using cycle_length by auto
  hence "Vs (set (edges_of_path C)) \<noteq> {}" (is "Vs ?E\<^sub>C \<noteq> {}")
    using vs_edges_path_eq[of C] by (auto simp: set_empty[of C])
  then obtain e where "e \<in> ?E\<^sub>C"
    by (auto elim: vs_member_elim)
  moreover then obtain u v where "e = {u,v}"
    by (auto elim: v_in_edge_in_path_inj)
  ultimately have "{u,v} \<in> ?E\<^sub>C"
    by auto
  moreover have "?E\<^sub>C \<subseteq> ?E\<^sub>P"
    by (metis cycle_C cycle_edges_subset)
  moreover have "{u,v} \<in> ?E\<^sub>P"
    using calculation by auto
  moreover have "u \<in> set P" "v \<in> set P"
    using calculation v_in_edge_in_path_gen[of \<open>{u,v}\<close>] by auto
  moreover have "u \<noteq> v"
    using calculation graph_E\<^sub>P by auto
  moreover have "2 \<le> card (set P)"
    using calculation card_mono[of "set P" "{u,v}"] by auto
  ultimately have "length P > 1"
    using card_length[of P] by auto

  have "Vs ?E\<^sub>C = Vs ?E\<^sub>P \<or> Vs ?E\<^sub>C \<subset> Vs ?E\<^sub>P"
    using \<open>?E\<^sub>C \<subseteq> ?E\<^sub>P\<close>Vs_subset[of ?E\<^sub>C ?E\<^sub>P] by auto
  thus "False"
  proof (elim disjE)
    assume "Vs ?E\<^sub>C = Vs ?E\<^sub>P"
    moreover have "hd P \<in> hd (edges_of_path P)"
      using \<open>length P > 1\<close> hd_v_in_hd_e[of P] by auto
    moreover have "hd (edges_of_path P) \<in> ?E\<^sub>P"
      using \<open>length P > 1\<close> edges_of_path_length[of P] by (intro hd_in_set) auto
    moreover have "hd P \<in> Vs ?E\<^sub>P"
      using calculation by (auto intro: vs_member_intro)
    ultimately have "hd P \<in> Vs ?E\<^sub>C"
      by auto
    hence "hd P \<in> set C"
      using v_in_edge_in_path_gen by (fastforce elim: vs_member_elim)

    have "degree ?E\<^sub>P (hd P) \<le> 1"
      using \<open>distinct P\<close> degree_edges_of_path_hd_leq_1[of P] by auto
    moreover have "degree ?E\<^sub>P (hd P) \<ge> 2"
      using \<open>hd P \<in> set C\<close> cycle_degree[OF graph_E\<^sub>P cycle_C] by auto
    ultimately have  "enat 2 \<le> enat 1"
      by (metis numeral_eq_enat one_enat_def dual_order.trans)
    thus ?thesis
      using enat_ord_simps by auto
  next
    assume "Vs ?E\<^sub>C \<subset> Vs ?E\<^sub>P"
    moreover have "is_connected ?E\<^sub>P"
      using assms path_connected by auto
    ultimately obtain u v where "{u,v} \<in> ?E\<^sub>P" "u \<in> Vs ?E\<^sub>C" "v \<in> Vs ?E\<^sub>P - Vs ?E\<^sub>C"
      using \<open>Vs ?E\<^sub>C \<noteq> {}\<close> \<open>?E\<^sub>C \<subseteq> ?E\<^sub>P\<close> connected_bridge[of ?E\<^sub>P ?E\<^sub>C] by auto
    moreover hence "u \<in> set C" "v \<notin> Vs ?E\<^sub>C" "u \<in> set P"
      using vs_member_elim[of _ ?E\<^sub>C] v_in_edge_in_path_gen[of _ C] 
            v_in_edge_in_path_gen[of "{u,v}" P u] by auto
    moreover hence "{u,v} \<notin> ?E\<^sub>C"
      using v_in_edge_in_path[of v u C] insert_commute by auto
    moreover then obtain e\<^sub>1 e\<^sub>2 where "e\<^sub>1 \<noteq> e\<^sub>2" "e\<^sub>1 \<in> ?E\<^sub>C" "u \<in> e\<^sub>1" "e\<^sub>2 \<in> ?E\<^sub>C" "u \<in> e\<^sub>2"
      using cycle_C calculation cycle_edges_for_v[OF \<open>graph_invar ?E\<^sub>P\<close>, of C u] by auto
    moreover hence "e\<^sub>1 \<in> ?E\<^sub>P" "e\<^sub>1 \<noteq> {u,v}" "e\<^sub>2 \<in> ?E\<^sub>P" "e\<^sub>2 \<noteq> {u,v}"
      using \<open>?E\<^sub>C \<subseteq> ?E\<^sub>P\<close> calculation by auto
    moreover hence "{{u,v},e\<^sub>1,e\<^sub>2} \<subseteq> ?E\<^sub>P" "card' {{u,v},e\<^sub>1,e\<^sub>2} = 3"
      using calculation by auto
    moreover have "degree {{u,v},e\<^sub>1,e\<^sub>2} u = 3"
      unfolding degree_def using calculation by auto
    ultimately have "degree ?E\<^sub>P u \<ge> 3"
      using subset_edges_less_degree[of "{{u,v},e\<^sub>1,e\<^sub>2}" ?E\<^sub>P u] by auto
    hence "enat 3 \<le> enat 2"
      using degree_edges_of_path_leq_2[OF \<open>distinct P\<close> \<open>length P > 1\<close> \<open>u \<in> set P\<close>]
      by (metis numeral_eq_enat dual_order.trans) (* TODO: clean up \<open>enat\<close> stuff *)
    thus ?thesis
      using enat_ord_simps by auto
  qed
qed

lemma tl_hc_acyclic:
  assumes "is_hc H"
  shows "is_acyclic (set (tl (edges_of_path H)))" (is "is_acyclic ?E\<^sub>H")
proof (rule ccontr)
  assume "\<not> is_acyclic ?E\<^sub>H"
  moreover have "path E (tl H)"
    using assms is_hc_path tl_path_is_path by auto
  moreover have "distinct (tl H)"
    using assms by (auto elim: is_hc_nonnilE)
  ultimately show "False"
    using non_acyclic_path_not_distinct[of "tl H", OF \<open>path E (tl H)\<close>] 
    by (auto simp: edges_of_path_tl[of H])
qed

lemma tl_hc_Vs:
  assumes "is_hc H"
  shows "Vs E = Vs (set (tl (edges_of_path H)))" (is "Vs E = Vs ?E\<^sub>H'")
proof -
  have "Vs E = set (tl H)"
    using assms by (auto simp: is_hcE)
  also have "... = Vs (set (edges_of_path (tl H)))"
    apply (cases "H = []")
    using vs_member[of _ "{}"] apply fastforce
    using hc_non_nil_length_gr2[of H, OF assms] vs_edges_path_eq[of "tl H"] apply auto
    done
  also have "... = Vs ?E\<^sub>H'"
    by (auto simp: edges_of_path_tl[of H])
  finally show ?thesis .
qed

lemma tl_hc_tree:
  assumes "is_hc H"
  shows "is_tree (set (tl (edges_of_path H)))"
  using tl_hc_connected[OF assms] tl_hc_acyclic[OF assms] by (auto intro: is_treeI)

lemma tl_hc_st:
  assumes "is_hc H"
  shows "is_st (set (tl (edges_of_path H)))" (is "is_st ?E\<^sub>H'")
  using assms hc_edges_subset set_tl_subset[of "edges_of_path H"] tl_hc_Vs tl_hc_tree 
  by (intro is_stI) auto

lemma mst_mtsp_approx:
  assumes "is_mst T" "is_mtsp OPT"
  shows "cost_of_st T \<le> cost_of_path OPT"
  using assms
proof (cases OPT)
  case Nil
  hence "E = {}"
    using assms hc_nil_iff by (auto simp: is_mtspE is_tspE)
  hence "T = {}"
    using assms is_mstE is_stE by auto
  hence "cost_of_st T = 0"
    unfolding cost_of_st_def by auto
  then show ?thesis
    using cost_of_path_pos by auto
next
  case (Cons v OPT')
  let ?E'="edges_of_path OPT"
  let ?e="hd (edges_of_path OPT)"
  have "is_st (set (tl ?E'))"
    using assms tl_hc_st[of OPT] by (auto simp: is_mtspE is_tspE)
  hence "cost_of_st T \<le> cost_of_st (set (tl ?E'))"
    using assms by (auto elim: is_mstE)
  also have "... = (\<Sum>e\<in>set (tl ?E'). c e)"
    unfolding cost_of_st_def by auto
  also have "... \<le> (\<Sum>e\<in>set ?E'. c e)"
    using costs_ge_0 sum_mono2[of "set ?E'" "set (tl ?E')" c] by (auto simp: set_tl_subset)
  also have "... \<le> cost_of_path OPT"
    using cost_of_path_leq_sum[of OPT] by auto
  finally show ?thesis .
qed

lemma dt_approx:
  assumes "is_mtsp OPT"
  shows "cost_of_path double_tree \<le> 2 * cost_of_path OPT"
proof -
  have "cost_of_path double_tree \<le> 2 * cost_of_st (comp_mst c E)"
    using dt_mst_approx[OF mst] .
  also have "... \<le> 2 * cost_of_path OPT"
    using mst_mtsp_approx[OF mst assms] by (auto simp: mult_2_mono)
  finally show ?thesis .
qed

end

(* interpretation double_tree_algo 
  sorry *)

end