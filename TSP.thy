(* Author: Lukas Koller *)
theory TSP
  imports Main Misc CompleteGraph WeightedGraph MST "HOL-Library.Multiset"
begin

context graph_abs
begin

text \<open>Hamiltonian cycle\<close>
definition "is_hc H \<equiv> (H \<noteq> [] \<longrightarrow> (\<exists>v. walk_betw E v H v)) \<and> set (tl H) = Vs E \<and> distinct (tl H)"
(* TODO: Definition with \<open>is_cycle\<close> *)

lemma is_hcE:
  assumes "is_hc H"
  shows "H \<noteq> [] \<Longrightarrow> (\<exists>v. walk_betw E v H v)" "Vs E = set (tl H)" "distinct (tl H)"
  using assms[unfolded is_hc_def] by auto

lemma is_hc_nilE:
  assumes "is_hc []"
  shows "Vs E = {}"
  using assms[unfolded is_hc_def] by auto

lemma is_hc_nonnilE:
  assumes "is_hc H" "H \<noteq> []"
  obtains v where "walk_betw E v H v" "set (tl H) = Vs E" "distinct (tl H)"
  using assms[unfolded is_hc_def] by auto

lemma is_hc_path: "is_hc H \<Longrightarrow> path E H"
  by (cases H) (auto intro: path.intros elim: is_hc_nonnilE)

lemma walk_betw_vv_set_tl_eq: 
  assumes "H \<noteq> []" "walk_betw E v H v" "set H = Vs E" 
  shows "set (tl H) = Vs E"
proof -
  have "E \<noteq> {}"
    using assms by (auto simp: Vs_def)
  then have "2 \<le> length H"
    using assms card_vertices_ge2 card_length[of H] by auto
  then have "hd H \<in> set (tl H)"
    using assms[unfolded walk_betw_def] last_in_set_tl[of H] by auto
  then have "set (tl H) = set H"
    using hd_Cons_tl[OF \<open>H \<noteq> []\<close>] insert_absorb[of "hd H" "set (tl H)"] set_simps by metis
  also have "... = Vs E"
    using assms by (auto elim: is_hc_nonnilE) 
  finally show ?thesis .
qed

lemma is_hcI_non_nil: 
  "H \<noteq> [] \<Longrightarrow> walk_betw E v H v \<Longrightarrow> set H = Vs E \<Longrightarrow> distinct (tl H) \<Longrightarrow> is_hc H"
  unfolding is_hc_def using walk_betw_vv_set_tl_eq by auto

lemma is_hcI_nil: 
  "Vs E = {} \<Longrightarrow> is_hc []"
  unfolding is_hc_def by auto

lemma hc_nil_iff: "E = {} \<longleftrightarrow> is_hc []"
proof -
  have "E = {} \<longleftrightarrow> path E [] \<and> set [] = Vs E"
    unfolding Vs_def using graph by force
  also have "... \<longleftrightarrow> is_hc []"
    by (auto intro: is_hcI_nil simp: is_hc_nilE)
  finally show ?thesis .
qed

lemma hc_vs_set:
  assumes "is_hc H"
  shows "set H = Vs E"
proof (cases "H = []")
  case True
  then show ?thesis 
    using assms by (auto simp: is_hc_nilE)
next
  case False
  then have "hd H \<in> set (tl H)"
    using assms[unfolded is_hc_def walk_betw_def] by (metis hd_in_set mem_path_Vs)
  then have "set H = set (tl H)"
    using hd_Cons_tl[OF \<open>H \<noteq> []\<close>] insert_absorb[of "hd H" "set (tl H)"] set_simps by metis
  also have "... = Vs E"
    using assms \<open>H \<noteq> []\<close> by (auto elim: is_hc_nonnilE[of H])
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
    using assms hc_vs_set by auto
  finally show "H = []"
    by auto
next
  assume "H = []"
  then show "E = {}"
    using assms hc_nil_iff by blast
qed

lemma hc_non_nil_length_gr2:
  assumes "is_hc H" "H \<noteq> []"
  shows "length H > 2"
proof (rule ccontr)
  assume "\<not> length H > 2"
  then have "card (Vs E) < 2"
    using assms card_length[of "tl H"] by (auto simp: is_hcE)
  then show "False"
    using assms hc_nil_iff2[of H] card_vertices_ge2 by auto
qed

lemma hc_edges_nil: 
  assumes "is_hc H" "edges_of_path H = []" 
  shows "H = []"
  using assms edges_of_path_nil hc_non_nil_length_gr2 by force

lemma hc_length:
  assumes "is_hc H" "H \<noteq> []"
  shows "length H = card (Vs E) + 1"
proof -
  have "length H = 1 + length (tl H)"
    using assms hd_Cons_tl[of H] by auto
  also have "... = card (Vs E) + 1"
    using assms distinct_card[of "tl H"] by (auto elim: is_hc_nonnilE)
  finally show ?thesis .
qed

lemma hc_edges_length:
  assumes "is_hc H"
  shows "length (edges_of_path H) = card (Vs E)"
  using assms
proof (induction H)
  case Nil
  then show ?case 
    using hc_nil_iff2[of "[]"] by (simp add: Vs_def)
next
  case (Cons v H)
  then show ?case 
    using hc_length[of "v#H"] edges_of_path_length[of "v#H"] by (simp add: Vs_def)
qed

lemma hc_edges_subset: 
  assumes "is_hc H"
  shows "set (edges_of_path H) \<subseteq> E"
proof (cases "H = []")
  case False
  then obtain v where "walk_betw E v H v"
    using assms by (auto elim: is_hc_nonnilE)
  then show ?thesis
    using walk_edges_subset by fastforce
qed auto

lemma hc_walk_betw1:
  assumes "is_hc H" "i\<^sub>u < i\<^sub>v" "i\<^sub>v < length H"
  shows "walk_betw E (H ! i\<^sub>u) (drop i\<^sub>u (take (i\<^sub>v+1) H)) (H ! i\<^sub>v)" (is "walk_betw E ?u ?P ?v")
proof -
  have "path E H"
    using assms by (auto elim: is_hc_nonnilE walk_between_nonempty_path)
  moreover hence "set (edges_of_path H) \<subseteq> E"
    using path_edges_subset by auto
  ultimately show ?thesis
    using assms walk_subset[OF _ walk_of_path[of E H i\<^sub>u i\<^sub>v]] by auto
qed

lemma is_hc_def2: "is_hc H \<longleftrightarrow> (H \<noteq> [] \<longrightarrow> is_cycle E H) \<and> set (tl H) = Vs E \<and> distinct (tl H)"
  oops (* Does not hold! counterexample: graph with 2 vertices *)

end

context pos_w_graph_abs
begin

text \<open>Traveling-Salesman Problem\<close>
definition "is_tsp P \<equiv> is_hc P \<and> (\<forall>P'. is_hc P' \<longrightarrow> cost_of_path P \<le> cost_of_path P')"

lemma is_tspE:
  assumes "is_tsp P"
  shows "is_hc P" "\<And>P'. is_hc P' \<Longrightarrow> cost_of_path P \<le> cost_of_path P'"
  using assms[unfolded is_tsp_def] by auto

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
  by (induction P\<^sub>1 rule: list012.induct) (auto simp: add_left_mono)

text \<open>metric Traveling-Salesman\<close>
definition "is_mtsp P \<equiv> is_tsp P"

lemma is_mtspE:
  assumes "is_mtsp P"
  shows "is_tsp P"
  using assms[unfolded is_mtsp_def] by auto

end

end