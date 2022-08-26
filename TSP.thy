(* Author: Lukas Koller *)
theory TSP
  imports Main CompleteGraph WeightedGraph "HOL-Library.Multiset"
begin

context graph_abs
begin

text \<open>Hamiltonian cycle\<close>
definition "is_hc H \<equiv> path E H \<and> set H = Vs E \<and> distinct (tl H) \<and> hd H = last H"

lemma hc_nil_iff: "E = {} \<longleftrightarrow> is_hc []"
proof -
  have "E = {} \<longleftrightarrow> path E [] \<and> set [] = Vs E"
    unfolding Vs_def using graph by force
  also have "... \<longleftrightarrow> is_hc []"
    unfolding is_hc_def by (simp add: hd_Nil_eq_last)
  finally show ?thesis .
qed

lemma hc_nil_iff2: 
  assumes "is_hc H" 
  shows "E = {} \<longleftrightarrow> H = []"
proof 
  assume "E = {}"
  then have "{} = Vs E"
    unfolding Vs_def by auto
  also have "... = set H"
    using assms[unfolded is_hc_def] by auto
  finally show "H = []"
    by auto
next
  assume "H = []"
  then show "E = {}"
    using assms hc_nil_iff by blast
qed

lemma card_vertices_ge2:
  assumes "E \<noteq> {}" 
  shows "card (Vs E) \<ge> 2"
proof -
  obtain u v where "{u,v} \<in> E" "u \<noteq> v"
    using assms graph by force
  then have "{u,v} \<subseteq> Vs E"
    unfolding Vs_def by blast
  then show ?thesis
    using \<open>{u,v} \<in> E\<close> by (metis card_2_iff card_mono graph)
qed

lemma hc_non_nil_length_ge2:
  assumes "is_hc H" "H \<noteq> []"
  shows "length H \<ge> 2"
proof (rule ccontr)
  assume "\<not> length H \<ge> 2"

  have "card (Vs E) = card (set H)"
    using assms[unfolded is_hc_def] by auto
  also have "... < 2"
    using \<open>\<not> length H \<ge> 2\<close> card_length[of H] by linarith
  finally show "False"
    using assms hc_nil_iff2[of H] card_vertices_ge2 by auto
qed

lemma edges_of_path_nil: 
  assumes "edges_of_path H = []" 
  shows "H = [] \<or> (\<exists>v. H = [v])"
  using assms by (induction H rule: edges_of_path.induct) auto

lemma hc_edges_nil: 
  assumes "is_hc H" "edges_of_path H = []" 
  shows "H = []"
  using assms edges_of_path_nil hc_non_nil_length_ge2 by force

lemma hc_distinct_edges:
  assumes "is_hc H"
  shows "distinct (edges_of_path H)"
  sorry

end

context pos_w_graph_abs
begin

fun cost_of_path where
  "cost_of_path [] = 0"
| "cost_of_path [v] = 0"
| "cost_of_path (u#v#P) = c {u,v} + cost_of_path (v#P)"

lemma cost_of_path_pos: "cost_of_path P \<ge> 0"
  by (induction P rule: cost_of_path.induct) (auto simp: costs_ge_0)

lemma cost_of_path_le: "cost_of_path P \<le> cost_of_path (v#P)"
  by (induction P arbitrary: v rule: cost_of_path.induct) (auto simp: costs_ge_0 add_increasing)

lemma cost_of_path_sum: "cost_of_path P = (\<Sum>e \<in># mset (edges_of_path P). c e)"
  by (induction P rule: cost_of_path.induct) auto

lemma cost_of_path_distinct_sum: 
  assumes "distinct (edges_of_path P)" 
  shows "cost_of_path P = (\<Sum>e \<in> set (edges_of_path P). c e)"
  using assms cost_of_path_sum[of P] mset_set_set[of "edges_of_path P"] 
  by (simp add: sum_unfold_sum_mset)

lemma cost_of_path_app: "cost_of_path (P @ [u,v]) = c {u,v} + cost_of_path (P @ [u])"
  by (induction P rule: cost_of_path.induct) (auto simp: add.assoc add.commute add.left_commute)

lemma cost_of_path_rev: "cost_of_path P = cost_of_path (rev P)"
proof (induction P rule: cost_of_path.induct)
  case (3 u v P)
  then have "cost_of_path (u#v#P) = c {u,v} + cost_of_path (rev P @ [v])"
    using "3.IH" by auto
  also have "... = cost_of_path (rev (u#v#P))"
    using cost_of_path_app[of "rev P" v u] by (auto simp: insert_commute)
  finally show ?case .
qed auto

text \<open>Traveling-Salesman Problem\<close>
definition "is_tsp P \<equiv> is_hc P \<and> (\<forall>P'. is_hc P' \<longrightarrow> cost_of_path P \<le> cost_of_path P')"

end

locale metric_graph_abs = 
  compl_graph_abs E + 
  pos_w_graph_abs E c for E c +
  assumes tri_ineq: "u\<in>Vs E \<Longrightarrow> v\<in>Vs E \<Longrightarrow> w\<in>Vs E \<Longrightarrow> c {u,w} \<le> c {u,v} + c {v,w}"
begin

lemma cost_of_path_cons_tri_ineq:
  assumes "set P \<union> {u,v} \<subseteq> Vs E"
  shows "cost_of_path (u#P) \<le> cost_of_path (u#v#P)"
  using assms
proof (induction P)
  case (Cons w P)
  then have "cost_of_path (u#w#P) \<le> c {u,v} + c {v,w} + cost_of_path (w#P)"
    using tri_ineq by (auto simp: add_right_mono)
  also have "... = cost_of_path (u#v#w#P)"
    by (auto simp: add.assoc)
  finally show ?case .
qed (auto simp: costs_ge_0)

lemma cost_of_path_app_tri_ineq:
  assumes "set P\<^sub>1 \<union> set P\<^sub>2 \<union> {w} \<subseteq> Vs E" 
  shows "cost_of_path (P\<^sub>1 @ P\<^sub>2) \<le> cost_of_path (P\<^sub>1 @ w#P\<^sub>2)"
  using assms cost_of_path_le cost_of_path_cons_tri_ineq 
  by (induction P\<^sub>1 rule: a.induct) (auto simp: add_left_mono)

text \<open>metric Traveling-Salesman\<close>
definition "is_mtsp P \<equiv> is_tsp P"

end

end