(* Author: Lukas Koller *)
theory DoubleTree
  imports Main 
    tsp.MinSpanningTree 
    tsp.TravelingSalesman 
    tsp.EulerianTour 
    "HOL-Hoare.Hoare_Logic"
begin

section \<open>DoubleTree Approximation Algorithm for Metric TSP\<close>

text \<open>Compute a Hamiltonian Cycle of an Eulerian Tour.\<close>
fun comp_hc_of_et :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "comp_hc_of_et [] H = H"
| "comp_hc_of_et [v] H = v#H"
| "comp_hc_of_et (v#P) H = (if v \<in> set H then comp_hc_of_et P H else comp_hc_of_et P (v#H))"

lemma comp_hc_of_et_tl_simps: 
  shows "P \<noteq> [] \<Longrightarrow> hd P \<in> set H \<Longrightarrow> tl P \<noteq> [] \<Longrightarrow> comp_hc_of_et P H = comp_hc_of_et (tl P) H"
  and  "P \<noteq> [] \<Longrightarrow> hd P \<notin> set H \<or> tl P = [] \<Longrightarrow> comp_hc_of_et P H = comp_hc_of_et (tl P) (hd P#H)"
  by (induction P arbitrary: H rule: list012.induct) auto

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
    using assms path_distinct_adj by (auto simp: mgraph_invar_def2)
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
  then consider "P = []" | "P = [u]" | "\<not> distinct_adj P"
    using hd_remdups_append[of u "rev P"] by auto
  thus ?thesis
    by cases (auto simp: distinct_adj_Cons distinct_adj_append_iff)
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
  eulerian comp_et for E :: "'a set set" and c and comp_et :: "'a mgraph \<Rightarrow> 'a list"
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
    using assms graph finite_subset[OF Vs_subset, of "set_mset X" E] 
    by (auto simp: mgraph_invar_def2)
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
  shows "is_hc E (comp_hc_of_et P [])"
proof (cases "P = []")
  assume "P = []"
  hence "X = {#}"
    using assms et_nil[of X] by auto
  hence "Vs E = {}"
    using assms by (auto simp: mVs_def Vs_def)
  hence "E = {}"
    using vs_member[of _ E] graph by fastforce
  then show ?thesis 
    using \<open>P = []\<close> hc_nil_iff by auto
next
  assume "P \<noteq> []"
  then obtain v where "comp_hc_of_et P [] \<noteq> []" "walk_betw E v (comp_hc_of_et P []) v"
    using assms hc_of_et_non_nil by (auto elim: hc_of_et_walk_betw[of P X])
  then show ?thesis
    apply (rule is_hcI_nonnil)
    using assms hc_of_et_walk_betw[of P X] hc_of_et_vs[of X P] hc_of_et_distinct[of "[]" P] 
          hc_of_et_cycle[of P X] by auto
qed

lemma cost_of_path_hc_of_et:
  assumes "set P \<union> set H \<subseteq> Vs E"
  shows "cost_of_path\<^sub>c (comp_hc_of_et P H) \<le> cost_of_path\<^sub>c (rev P @ H)"
  using assms
proof (induction P H rule: comp_hc_of_et.induct)
  case (3 u v P H)
  then show ?case 
    using cost_of_path_app_tri_ineq[of "rev (v#P)" H u] by auto
qed auto

lemma hc_of_et_reduces_cost: 
  "set P \<subseteq> Vs E \<Longrightarrow> cost_of_path\<^sub>c (comp_hc_of_et P []) \<le> cost_of_path\<^sub>c P"
  using cost_of_path_hc_of_et[of P "[]"] cost_of_path_rev[of P] by auto

end

locale double_tree_algo = 
  hc_of_et E c comp_et + 
  mst E c comp_mst 
  for E c comp_et comp_mst
begin

definition double_tree where
  "double_tree = (
    let T = comp_mst c E;
        T\<^sub>2\<^sub>x = mset_set T + mset_set T;
        P = comp_et T\<^sub>2\<^sub>x in
        comp_hc_of_et P [])"

lemma T2x_eulerian:
  assumes "is_mst E c T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T"
  shows "is_eulerian T\<^sub>2\<^sub>x"
  using assms[unfolded is_mst_def is_st_def] finite_E finite_subset[of T E]
        double_graph_eulerian[of T T\<^sub>2\<^sub>x] by auto

lemma T2x_vs:
  assumes "is_mst E c T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T"
  shows "mVs T\<^sub>2\<^sub>x = Vs E"
  using assms[unfolded is_mst_def is_st_def] finite_subset[OF _ finite_E] by (auto simp: mVs_def) 

lemma T2x_edges:
  assumes "is_mst E c T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T"
  shows "set_mset T\<^sub>2\<^sub>x \<subseteq> E"
  using assms[unfolded is_mst_def is_st_def] finite_subset[OF _ finite_E] by auto 

lemmas dt_correctness = T2x_eulerian[OF mst] T2x_vs[OF mst] T2x_edges[OF mst]

end

subsection \<open>Feasibility of the DoubleTree Algorithm\<close>

context double_tree_algo
begin

lemma dt_is_hc: "is_hc E (double_tree)"
  unfolding double_tree_def Let_def
  apply (rule hc_of_et_correct, rule eulerian)
  using dt_correctness[OF is_connected] by auto

end

subsection \<open>Approximation of the DoubleTree Algorithm\<close>

locale mtsp_opt = 
  metric_graph_abs E c for E :: "'a set set" and c +
  fixes OPT
  assumes opt: "is_mtsp OPT"
begin

lemma tl_hc_acyclic:
  assumes "is_hc E H"
  shows "is_acyclic (set (tl (edges_of_path H)))" (is "is_acyclic ?E\<^sub>H")
proof (rule ccontr)
  assume "\<not> is_acyclic ?E\<^sub>H"
  moreover have "path E (tl H)"
    using assms is_hc_path tl_path_is_path by auto
  moreover have "distinct (tl H)"
    using assms by (auto elim: is_hcE_nonnil)
  ultimately show "False"
    using non_acyclic_path_not_distinct[of "tl H", OF \<open>path E (tl H)\<close>] 
    by (auto simp: edges_of_path_tl[of H])
qed

lemma tl_hc_Vs:
  assumes "is_hc E H"
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

lemma hc_connected_component:
  assumes "is_hc E H" "u = (tl H) ! i\<^sub>u" "i\<^sub>u < length (tl H)" "v = (tl H) ! i\<^sub>v" "i\<^sub>v < length (tl H)" 
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
    using assms hc_walk_betw1[of E H "i\<^sub>u + 1" "i\<^sub>v + 1"] by auto
  hence "walk_betw (set (edges_of_path ?P')) u ?P' v"
    using assms \<open>?P = ?P'\<close> walk_on_edges_of_path[of E u ?P v] by auto
  hence "walk_betw ?E' u ?P' v"
    using edges_of_path_drop_take_subset[of i\<^sub>u "i\<^sub>v + 1" "tl H"] 
            walk_subset[of "set (edges_of_path ?P')" ?E'] by auto
  then show "u \<in> connected_component ?E' v"
    using walk_symmetric[of ?E' u _ v] by auto
qed

lemma tl_hc_connected:
  assumes "is_hc E H"
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

  consider "i\<^sub>u = i\<^sub>v" | "i\<^sub>u < i\<^sub>v" | "i\<^sub>v < i\<^sub>u"
    by linarith
  then show "u \<in> connected_component ?E' v"
  proof cases
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

lemma tl_hc_tree:
  assumes "is_hc E H"
  shows "is_tree (set (tl (edges_of_path H)))"
  using tl_hc_connected[OF assms] tl_hc_acyclic[OF assms] by (auto intro: is_treeI)

lemma tl_hc_st:
  assumes "is_hc E H"
  shows "is_st E (set (tl (edges_of_path H)))" (is "is_st E ?E\<^sub>H'")
  using assms hc_edges_subset set_tl_subset[of "edges_of_path H"] tl_hc_Vs tl_hc_tree 
  by (intro is_stI) auto

lemma mst_mtsp_approx:
  assumes "is_mst E c T"
  shows "cost_of_st\<^sub>c T \<le> cost_of_path\<^sub>c OPT"
  using assms
proof cases
  assume "OPT = []"
  hence "E = {}"
    using opt assms hc_nil_iff by (auto simp: is_tspE)
  hence "T = {}"
    using assms is_stE[OF is_mstE(1)] by auto
  hence "cost_of_st\<^sub>c T = 0"
    by auto
  then show ?thesis
    using cost_of_path_pos by auto
next
  assume "OPT \<noteq> []"
  let ?E'="edges_of_path OPT"
  let ?e="hd (edges_of_path OPT)"
  have "is_st E (set (tl ?E'))"
    using opt assms tl_hc_st[of OPT] by (auto simp: is_tspE)
  hence "cost_of_st\<^sub>c T \<le> cost_of_st\<^sub>c (set (tl ?E'))"
    using assms by (auto elim: is_mstE)
  also have "... \<le> sum c (set ?E')"
    using costs_ge_0 sum_mono2[of "set ?E'" "set (tl ?E')" c] by (auto simp: set_tl_subset)
  also have "... \<le> cost_of_path\<^sub>c OPT"
    using cost_of_path_leq_sum[of OPT] by auto
  finally show ?thesis .
qed

end

locale double_tree_algo_approx = double_tree_algo + mtsp_opt
begin

lemma cost_of_et:
  assumes "is_et T\<^sub>2 P" 
  shows "cost_of_path\<^sub>c P = \<Sum>\<^sub># (image_mset c T\<^sub>2)"
  using assms cost_of_path_sum[of c P] et_edges[of T\<^sub>2 P] by auto

lemma et_not_single_v:
  assumes "is_mst E c T" "is_et T\<^sub>2 P"
  shows "length P \<noteq> 1"
  using assms
proof (induction P rule: list012.induct) (* induction just for case distinction *)
  case (2 v)
  hence "T\<^sub>2 = {#}" "mpath T\<^sub>2 [v]"
    using is_etE[of T\<^sub>2 "[v]"] by auto
  hence "mVs T\<^sub>2 = {}" "v \<in> mVs T\<^sub>2"
    unfolding mpath_def2 by (auto simp: mVs_def Vs_def)
  then show ?case by auto
qed auto

lemma hc_of_et_cost_le_dt:
  assumes "is_mst E c T" "T\<^sub>2 = mset_set T + mset_set T" "is_et T\<^sub>2 P"
  shows "cost_of_path\<^sub>c (comp_hc_of_et P []) \<le> 2 * cost_of_st\<^sub>c T"
proof -
  have "set P \<subseteq> Vs E"
    using assms et_vertices_len_neq_1[of T\<^sub>2 P, OF _ et_not_single_v] T2x_vs[of T T\<^sub>2] by auto
  hence "cost_of_path\<^sub>c (comp_hc_of_et P []) \<le> cost_of_path\<^sub>c P"
    using hc_of_et_reduces_cost[of P] by auto
  also have "... = \<Sum>\<^sub># (image_mset c T\<^sub>2)"
    using assms cost_of_et by auto
  also have "... = sum c T + sum c T"
    using assms by (simp add: sum_unfold_sum_mset)
  also have "... = 2 * cost_of_st\<^sub>c T"
    using mult_2 by auto
  finally show ?thesis .
qed

lemma dt_mst_approx:
  assumes "is_mst E c T"
  shows "cost_of_path\<^sub>c double_tree \<le> 2 * cost_of_st\<^sub>c T"
proof -
  let ?T="comp_mst c E"
  let ?T\<^sub>2="mset_set ?T + mset_set ?T"
  let ?P="comp_et ?T\<^sub>2"
  
  have "cost_of_path\<^sub>c double_tree = cost_of_path\<^sub>c (comp_hc_of_et ?P [])"
    unfolding double_tree_def by (auto simp: Let_def)
  also have "... \<le> 2 * cost_of_st\<^sub>c ?T"
    using mst[OF is_connected] hc_of_et_cost_le_dt[of ?T ?T\<^sub>2 ?P] 
      eulerian[OF T2x_eulerian, of ?T ?T\<^sub>2] by auto
  also have "... = 2 * cost_of_st\<^sub>c T"
    using assms is_connected mst_eq_cost[OF mst] by auto
  finally show ?thesis .
qed

lemma dt_approx: "cost_of_path\<^sub>c double_tree \<le> 2 * cost_of_path\<^sub>c OPT"
proof -
  have "cost_of_path\<^sub>c double_tree \<le> 2 * cost_of_st\<^sub>c (comp_mst c E)"
    using is_connected dt_mst_approx[OF mst] by auto
  also have "... \<le> 2 * cost_of_path\<^sub>c OPT"
    using is_connected mst_mtsp_approx[OF mst] by (auto simp: mult_2_mono)
  finally show ?thesis .
qed

end

theorem dt_is_hc: 
  fixes E and c :: "'a set \<Rightarrow> 'b::{ordered_semiring_0,semiring_numeral}"
  assumes "graph_invar E" "is_complete E" "\<And>e. c e > 0"
      and tri_ineq: "\<And>u v w. u \<in> Vs E \<Longrightarrow> v \<in> Vs E \<Longrightarrow> w \<in> Vs E \<Longrightarrow> c {u,w} \<le> c {u,v} + c {v,w}"
      and mst: "\<And>E. is_connected E \<Longrightarrow> is_mst E c (comp_mst c E)"
      and eulerian: "\<And>E. is_eulerian E \<Longrightarrow> is_et E (comp_et E)"
  shows "is_hc E (double_tree_algo.double_tree E c comp_et comp_mst)"
  using assms by (intro double_tree_algo.dt_is_hc) unfold_locales

theorem dt_approx: 
  fixes E and c :: "'a set \<Rightarrow> 'b::{ordered_semiring_0,semiring_numeral}"
  defines "c' \<equiv> \<lambda>u v. c {u,v}"
  assumes "graph_invar E" "is_complete E" "\<And>e. c e > 0"
      and tri_ineq: "\<And>u v w. u \<in> Vs E \<Longrightarrow> v \<in> Vs E \<Longrightarrow> w \<in> Vs E \<Longrightarrow> c {u,w} \<le> c {u,v} + c {v,w}"
      and opt: "is_tsp E c OPT"
      and mst: "\<And>E. is_connected E \<Longrightarrow> is_mst E c (comp_mst c E)"
      and eulerian: "\<And>E. is_eulerian E \<Longrightarrow> is_et E (comp_et E)"
  shows "cost_of_path c' (double_tree_algo.double_tree E c comp_et comp_mst) \<le> 2 * cost_of_path c' OPT"
  unfolding c'_def using assms by (intro double_tree_algo_approx.dt_approx; unfold_locales) auto

lemma refine_double_tree:
  fixes E and c :: "'a set \<Rightarrow> 'b::{ordered_semiring_0,semiring_numeral}"
  defines "c' \<equiv> \<lambda>u v. c {u,v}"
  assumes "graph_invar E" "is_complete E" "\<And>e. c e > 0"
      and tri_ineq: "\<And>u v w. u \<in> Vs E \<Longrightarrow> v \<in> Vs E \<Longrightarrow> w \<in> Vs E \<Longrightarrow> c {u,w} \<le> c {u,v} + c {v,w}"
      and opt: "is_tsp E c OPT"
      and mst: "\<And>E. is_connected E \<Longrightarrow> is_mst E c (comp_mst c E)"
      and eulerian: "\<And>E. is_eulerian E \<Longrightarrow> is_et E (comp_et E)"
  shows "VARS T T\<^sub>2\<^sub>x v P P' H { True }
    T := comp_mst c E;
    T\<^sub>2\<^sub>x := mset_set T + mset_set T;
    P := comp_et T\<^sub>2\<^sub>x;
    P' := P;
    H := [];
    WHILE P' \<noteq> [] 
    INV { comp_hc_of_et P [] = comp_hc_of_et P' H 
      \<and> P = comp_et T\<^sub>2\<^sub>x 
      \<and> T\<^sub>2\<^sub>x = mset_set T + mset_set T 
      \<and> T = comp_mst c E 
    } DO
      v := hd P';
      P' := tl P';
      IF v \<in> set H \<and> P' \<noteq> [] THEN
        H := H
      ELSE
        H := v#H
      FI
    OD { is_hc E H \<and> cost_of_path c' H \<le> 2 * cost_of_path c' OPT }"
proof (vcg, goal_cases)
  case (1 T T\<^sub>2\<^sub>x v P P' H)
  then show ?case 
    by (auto simp: comp_hc_of_et_tl_simps)
next
  case (2 T T\<^sub>2\<^sub>x v P P' H)
  moreover hence "H = double_tree_algo.double_tree E c comp_et comp_mst"
    using assms 2 
    apply (subst double_tree_algo.double_tree_def) (* TODO: why do I need subst here?! *)
    apply unfold_locales 
    apply (auto simp: Let_def)
    done
  ultimately show ?case 
    using assms dt_is_hc[of E c comp_mst comp_et] dt_approx[of E c OPT comp_mst comp_et] by auto
qed

end