(* Author: Lukas Koller *)
theory DoubleTree
  imports Main MST TSP Eulerian
begin

section \<open>\textsc{DoubleTree} Approximation Algorithm for mTSP\<close>
                                                
locale double_tree_algo = 
  metric_graph_abs E c + 
  mst E c comp_mst + 
  eulerian comp_et for E :: "'a set set" and c comp_mst and comp_et :: "'a mgraph \<Rightarrow> 'a list"
begin

text \<open>Hamiltonian Cycle of Eulerian Tour\<close>
fun hc_of_et :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "hc_of_et [] H = H"
| "hc_of_et [v] H = v#H"
| "hc_of_et (v#P) H = (if v \<in> List.set H then hc_of_et P H else hc_of_et P (v#H))"

lemma hc_of_et_set_eq: "set P \<union> set H = set (hc_of_et P H)"
  by (induction P H rule: hc_of_et.induct) auto

lemma hc_of_et_non_nil: "P \<noteq> [] \<Longrightarrow> (hc_of_et P H) \<noteq> []"
  by (induction P H rule: hc_of_et.induct) auto

lemma hc_of_et_vs:
  assumes "is_et X P" 
  shows "set (hc_of_et P []) = mVs X"
proof
  show "set (hc_of_et P []) \<subseteq> mVs X"
    using assms[unfolded is_et_def mpath_def] mem_path_Vs[of "set_mset X" P] 
          hc_of_et_set_eq[of P "[]"] by (auto simp: mVs_def)
next
  show "mVs X \<subseteq> set (hc_of_et P [])"
    unfolding mVs_def
  proof
    fix v
    assume "v \<in> Vs (set_mset X)"
    then obtain e where "e \<in># X" "v \<in> e"
      by (auto elim: vs_member_elim)
    then have "e \<in># mset (edges_of_path P)"
      using assms[unfolded is_et_def] by auto
    then show "v \<in> set (hc_of_et P [])"
      using \<open>v \<in> e\<close> v_in_edge_in_path_gen[of e P v] hc_of_et_set_eq[of P] by auto
  qed
qed

lemma hc_of_et_path:
  assumes "is_et X P" "set_mset X \<subseteq> E"
  shows "path E (hc_of_et P [])" (is "path E ?H")
proof -
  have "set P \<subseteq> Vs E"
    using assms[unfolded is_et_def mpath_def] Vs_subset[of "set_mset X" E] 
    by (auto simp: mem_path_Vs subsetI)
  then have "set ?H \<subseteq> Vs E"
    using hc_of_et_set_eq[of P "[]"] by auto
  then show ?thesis
    unfolding mpath_def using path_complete_graph[of ?H] by auto
qed

lemma hc_of_et_distinct: "distinct H \<Longrightarrow> distinct (tl (hc_of_et P H))"
  by (induction P H rule: hc_of_et.induct) (auto simp: Let_def distinct_tl)

lemma hc_of_et_last_aux: "H \<noteq> [] \<Longrightarrow> last H = last (hc_of_et P H)"
  by (induction P H rule: hc_of_et.induct) auto

lemma hc_of_et_last: "P \<noteq> [] \<Longrightarrow> hd P = last (hc_of_et P [])"
  using hc_of_et_last_aux by (induction P rule: a.induct) auto

lemma hc_of_et_hd: "P \<noteq> [] \<Longrightarrow> last P = hd (hc_of_et P H)"
  by (induction P H rule: hc_of_et.induct) auto

lemma hc_of_et_cycle:
  assumes "P \<noteq> []" "is_et X P"
  shows "hd (hc_of_et P []) = last (hc_of_et P [])" (is "hd ?H = last ?H")
proof -
  have "hd ?H = last P"
    using assms hc_of_et_hd[of P "[]"] by auto
  also have "... = hd P"
    using assms[unfolded is_et_def] by auto
  also have "... = last ?H"
    using assms hc_of_et_last by auto
  finally show ?thesis .
qed

lemma hc_of_et_walk_betw:
  assumes "P \<noteq> []" "is_et X P" "set_mset X \<subseteq> E"
  shows "\<exists>v. walk_betw E v (hc_of_et P []) v" (is "\<exists>v. walk_betw E v ?H v")
proof
  let ?v="hd ?H"
  show "walk_betw E ?v ?H ?v"
  proof (rule nonempty_path_walk_between)
    show "path E ?H" "?H \<noteq> []" "hd ?H = ?v" "last ?H = ?v"
      using assms hc_of_et_path[of X P] hc_of_et_non_nil[of P "[]"] hc_of_et_cycle[of P X] by auto
  qed
qed

lemma hc_of_et_correct: 
  assumes "is_et X P" "mVs X = Vs E" "set_mset X \<subseteq> E"
  shows "is_hc (hc_of_et P [])"
proof (cases "P = []")
  case True
  then have "X = {#}"
    using assms et_nil[of X] by auto
  then have "Vs E = {}"
    using assms by (auto simp: mVs_def Vs_def)
  have "E = {}"
    using vs_member[of _ E] \<open>Vs E = {}\<close> graph by fastforce
  then show ?thesis 
    using \<open>P = []\<close> hc_nil_iff by auto
next
  case False
  then show ?thesis 
    unfolding is_hc_def
    using assms hc_of_et_walk_betw[of P X] hc_of_et_vs[of X P] hc_of_et_distinct[of "[]" P] 
          hc_of_et_cycle[of P X] by auto
qed

fun double_tree :: "unit \<Rightarrow> 'a list" where
  "double_tree () = (
    let T = comp_mst c E;
        T\<^sub>2\<^sub>x = mset_set T + mset_set T;
        P = comp_et T\<^sub>2\<^sub>x in
        hc_of_et P [])"

text \<open>Feasibility of \textsc{DoubleTree}\<close>

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

lemma "is_hc (double_tree ())" (is "is_hc ?H")
  apply (simp only: double_tree.simps Let_def)
  apply (rule hc_of_et_correct, rule eulerian)
  using dt_correctness by auto

text \<open>Approximation of \textsc{DoubleTree}\<close>

lemma cost_of_path_hc_of_et:
  assumes "set P \<union> set H \<subseteq> Vs E"
  shows "cost_of_path (hc_of_et P H) \<le> cost_of_path (rev P @ H)"
  using assms
proof (induction P H rule: hc_of_et.induct)
  case (3 u v P H)
  then show ?case 
    using cost_of_path_app_tri_ineq[of "rev (v#P)" H u] by auto
qed auto

lemma hc_of_et_reduces_cost: "set P \<subseteq> Vs E \<Longrightarrow> cost_of_path (hc_of_et P []) \<le> cost_of_path P"
  using cost_of_path_hc_of_et[of P "[]"] cost_of_path_rev[of P] by auto

lemma cost_of_et:
  assumes "is_et T P" 
  shows "cost_of_path P = (\<Sum>e\<in>#T. c e)"
  using assms cost_of_path_sum[of P] et_edges[of T P] by auto

lemma et_not_single_v:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T" "is_et T\<^sub>2\<^sub>x P"
  shows "length P \<noteq> 1"
  using assms
proof (induction P rule: a.induct) (* induction just for case distinction *)
  case (2 v)
  then have "T\<^sub>2\<^sub>x = {#}" "mpath T\<^sub>2\<^sub>x [v]"
    unfolding is_et_def by auto
  then have "mVs T\<^sub>2\<^sub>x = {}" "v \<in> mVs T\<^sub>2\<^sub>x"
    unfolding mpath_def by (auto simp: mVs_def Vs_def)
  then show ?case by auto
qed auto

lemma hc_of_et_cost_le_dt:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T" "is_et T\<^sub>2\<^sub>x P"
  shows "cost_of_path (hc_of_et P []) \<le> 2 * cost_of_st T"
proof -
  have "set P \<subseteq> Vs E"
    using assms et_vertices[of T\<^sub>2\<^sub>x P, OF _ et_not_single_v] T2x_vs[of T T\<^sub>2\<^sub>x] by auto
  then have "cost_of_path (hc_of_et P []) \<le> cost_of_path P"
    using hc_of_et_reduces_cost[of P] by auto
  also have "... = (\<Sum>e\<in>#T\<^sub>2\<^sub>x. c e)"
    using assms cost_of_et by auto
  also have "... = (\<Sum>e\<in>T. c e) + (\<Sum>e\<in>T. c e)"
    using assms by (simp add: sum_unfold_sum_mset)
  also have "... = 2 * (\<Sum>e\<in>T. c e)"
    sorry
  also have "... = 2 * cost_of_st T"
    by (auto simp: cost_of_st_def)
  finally show ?thesis .
qed

lemma dt_mst_approx:
  assumes "is_mst T"
  shows "cost_of_path (double_tree ()) \<le> 2 * cost_of_st T"
proof -
  let ?T="comp_mst c E"
  let ?T\<^sub>2\<^sub>x="mset_set ?T + mset_set ?T"
  let ?P="comp_et ?T\<^sub>2\<^sub>x"
  
  have "cost_of_path (double_tree ()) = cost_of_path (hc_of_et ?P [])"
    by (auto simp: Let_def)
  also have "... \<le> 2 * cost_of_st ?T"
    using mst hc_of_et_cost_le_dt[of ?T ?T\<^sub>2\<^sub>x ?P] eulerian[OF T2x_eulerian, of ?T ?T\<^sub>2\<^sub>x] by auto
  also have "... = 2 * cost_of_st T"
    using assms mst_eq_cost[OF mst, of T] by auto
  finally show ?thesis .
qed

lemma st_of_hc_connected:
  assumes "is_hc H" "E' = set (edges_of_path H)" "e \<in> E'"
  shows "is_connected (E' - {e})"
  sorry

lemma st_of_hc_acyclic:
  assumes "is_hc H" "E' = set (edges_of_path H)" "e \<in> E'"
  shows "is_acyclic (E' - {e})"
  sorry

lemma st_of_hc_tree:
  assumes "is_hc H" "E' = set (edges_of_path H)" "e \<in> E'"
  shows "is_tree (E' - {e})"
  unfolding is_tree_def
  using assms st_of_hc_connected[of H E' e] st_of_hc_acyclic[of H E' e] by auto

lemma st_of_hc:
  assumes "is_hc H" "E' = set (edges_of_path H)" "e \<in> E'"
  shows "is_st (E' - {e})"
  unfolding is_st_def
  using assms st_of_hc_tree[of H E' e]
  sorry

lemma mst_mtsp_approx:
  assumes "is_mst T" "is_mtsp OPT"
  shows "cost_of_st T \<le> cost_of_path OPT"
proof (cases "OPT = []")
  case True
  then have "E = {}"
    using assms[unfolded is_mtsp_def is_tsp_def] hc_nil_iff by auto
  then have "T = {}"
    using assms[unfolded is_mst_def is_st_def] by auto
  then have "cost_of_st T = 0"
    unfolding cost_of_st_def by auto
  then show ?thesis
    using cost_of_path_pos by auto
next
  let ?E'="set (edges_of_path OPT)"
  case False
  then have "?E' \<noteq> {}"
    using assms[unfolded is_mtsp_def is_tsp_def] hc_edges_nil[of OPT] by auto
  then obtain e where "e \<in> ?E'"
    by fastforce
  then have "is_st (?E' - {e})"
    using assms[unfolded is_mtsp_def is_tsp_def] st_of_hc[of OPT ?E' e] by auto
  then have "cost_of_st T \<le> cost_of_st (?E' - {e})"
    using assms[unfolded is_mst_def] by auto
  also have "... = (\<Sum>e\<in>(?E' - {e}). c e)"
    unfolding cost_of_st_def by auto
  also have "... \<le> (\<Sum>e\<in>(?E' - {e}). c e) + c e"
    using costs_ge_0 by (auto simp: add.commute add_increasing)
  also have "... = (\<Sum>e\<in>?E'. c e)"
    using sum.union_disjoint[of "?E' - {e}" "{e}" c] insert_Diff[OF \<open>e \<in> ?E'\<close>] by auto
  also have "... \<le> cost_of_path OPT"
    using cost_of_path_leq_sum[of OPT] by auto
  finally show ?thesis .
qed

lemma dt_approx:
  assumes "is_mtsp OPT"
  shows "cost_of_path (double_tree ()) \<le> 2 * cost_of_path OPT"
proof -
  have "cost_of_path (double_tree ()) \<le> 2 * cost_of_st (comp_mst c E)"
    using dt_mst_approx[OF mst] .
  also have "... \<le> 2 * cost_of_path OPT"
    using mst_mtsp_approx[OF mst assms] sorry
  finally show ?thesis .
qed

end

lemma "a \<le> b \<Longrightarrow> 2 * a \<le> 2 * b"
  sorry (* TODO: ask Mohammad *)

end