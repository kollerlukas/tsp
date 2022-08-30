(* Author: Lukas Koller *)
theory TSP
  imports Main CompleteGraph WeightedGraph "HOL-Library.Multiset"
begin

context graph_abs
begin

text \<open>Hamiltonian cycle\<close>
definition "is_hc H \<equiv> (H \<noteq> [] \<longrightarrow> (\<exists>v. walk_betw E v H v)) \<and> set H = Vs E \<and> distinct (tl H)"

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

lemma path_drop:
  assumes "path E P"
  shows "path E (drop i P)"
  using assms path_suff[of E "take i P" "drop i P"] append_take_drop_id[of i P] by auto

lemma path_take:
  assumes "path E P"
  shows "path E (take i P)"
  using assms path_pref[of E "take i P" "drop i P"] append_take_drop_id[of i P] by auto

lemma hc_walk_betw1:
  assumes "is_hc H" "i\<^sub>u < i\<^sub>v" "i\<^sub>v < length H"
  shows "walk_betw E (H ! i\<^sub>u) (drop i\<^sub>u (take (i\<^sub>v+1) H)) (H ! i\<^sub>v)" (is "walk_betw E ?u ?P ?v")
proof (rule nonempty_path_walk_between)
  show "path E ?P"
    using assms[unfolded is_hc_def walk_betw_def] path_drop[OF path_take, of H i\<^sub>u "i\<^sub>v+1"] by auto

  have "length ?P = i\<^sub>v-i\<^sub>u+1"
    using assms length_take[of i\<^sub>v H] length_drop[of i\<^sub>u "take (i\<^sub>v+1) H"] by auto 
  then show "?P \<noteq> []"
    using assms length_0_conv[of ?P] by auto

  show "hd ?P = ?u"
    using assms hd_drop_conv_nth[of i\<^sub>u "take (i\<^sub>v+1) H"] nth_take[of i\<^sub>u "i\<^sub>v+1" H] by auto

  show "last ?P = ?v"
    using assms last_drop[of i\<^sub>u "take (i\<^sub>v+1) H"] last_conv_nth[of "take (i\<^sub>v+1) H"] 
      nth_take[of i\<^sub>v "i\<^sub>v+1" H] by force
qed

lemma hc_walk_betw2: (* TODO *)
  assumes "is_hc H" "i\<^sub>u < i\<^sub>v" "i\<^sub>v < length H"
  shows "walk_betw E (H ! i\<^sub>u) (rev (tl (take i\<^sub>u H)) @ rev (drop i\<^sub>v H)) (H ! i\<^sub>v)" (is "walk_betw E ?u (?P1 @ ?P2) ?v")
proof (rule nonempty_path_walk_between)
  let ?P ="?P1 @ ?P2"

  have "hd ?P2 = last H"
    sorry
  
  have "last ?P1 = hd (tl H)" "hd ?P2 = hd H"
    sorry

  have "?P1 \<noteq> [] \<Longrightarrow> ?P2 \<noteq> [] \<Longrightarrow> {last ?P1,hd ?P2} \<in> E"
    using assms[unfolded is_hc_def walk_betw_def] sorry

  have "path E ?P1" "path E ?P2"
    using assms[unfolded is_hc_def walk_betw_def] 
      rev_path_is_path[OF tl_path_is_path[OF path_take], of H i\<^sub>u]
      rev_path_is_path[OF path_drop, of H i\<^sub>v] by auto
  then show "path E ?P"
    using path_append[of E ?P1 ?P2]
    sorry

  show "?P \<noteq> []"
    sorry

  show "hd ?P = ?u"
    sorry

  show "last ?P = ?v"
    sorry
qed

lemma hc_edge_distinct_paths:
  assumes "is_hc H" "u \<in> Vs E" "v \<in> Vs E"
  obtains P\<^sub>1 P\<^sub>2 where "walk_betw E u P\<^sub>1 v" "walk_betw E u P\<^sub>2 v" 
    "set (edges_of_path P\<^sub>1) \<inter> set (edges_of_path P\<^sub>2) = {}"
  using hc_walk_betw1 hc_walk_betw2
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
  shows "(\<Sum>e \<in> set (edges_of_path P). c e) = cost_of_path P"
  using assms cost_of_path_sum[of P] mset_set_set[of "edges_of_path P"] 
  by (simp add: sum_unfold_sum_mset)

lemma "(\<Sum>e \<in> set A. c e) \<le> (\<Sum>e \<in># mset A. c e)"
  sorry

lemma cost_of_path_leq_sum: "(\<Sum>e \<in> set (edges_of_path P). c e) \<le> cost_of_path P"
  using cost_of_path_sum[of P] sum_unfold_sum_mset
  sorry (* TODO: ask Mohammad *)

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