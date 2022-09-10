(* Author: Lukas Koller *)
theory TSP
  imports Main CompleteGraph WeightedGraph MST "HOL-Library.Multiset"
begin

context graph_abs
begin

lemma path_subset_singleton:
  assumes "path X [v]" "v \<in> Vs X'"
  shows "path X' [v]"
  using assms by (auto intro: path.intros)

lemma path_subset:
  assumes "path X P" "set (edges_of_path P) \<subseteq> X'" "set P \<subseteq> Vs X'"
  shows "path X' P"
  using assms by (induction P rule: path.induct) (auto intro: path.intros)

lemma walk_superset:
  assumes "walk_betw X u P v" "set (edges_of_path P) \<subseteq> X'" "set P \<subseteq> Vs X'"
  shows "walk_betw X' u P v"
  using assms path_subset unfolding walk_betw_def by blast 

lemma path_Vs_subset: 
  assumes "path X P" 
  shows "set P \<subseteq> Vs X"
  using assms mem_path_Vs[of X] by blast

lemma vs_edges_path_eq:
  assumes "length P \<noteq> 1"
  shows "set P = Vs (set (edges_of_path P))"
  using assms
proof (induction P rule: edges_of_path.induct)
  case (3 u v P)
  show ?case 
  proof 
    show "set (u#v#P) \<subseteq> Vs (set (edges_of_path (u#v#P)))" (is "set (u#v#P) \<subseteq> Vs ?E'")
    proof
      fix w
      assume "w \<in> set (u#v#P)"
      then obtain e where "e \<in> set (edges_of_path (u#v#P))" "w \<in> e"
        using path_vertex_has_edge[of "u#v#P" w] by auto
      then show "w \<in> Vs ?E'"
        by (intro vs_member_intro)
    qed
  next
    show "Vs (set (edges_of_path (u#v#P))) \<subseteq> set (u#v#P)"
      using edges_of_path_Vs[of "u#v#P"] by auto
  qed
qed (auto simp: Vs_def)

lemma walk_on_edges_of_path:
  assumes "walk_betw X u P v" "length P \<noteq> 1"
  shows "walk_betw (set (edges_of_path P)) u P v"
proof (rule walk_superset)
  show "walk_betw X u P v"
    using assms by auto
  show "set (edges_of_path P) \<subseteq> set (edges_of_path P)"
    by auto
  show "set P \<subseteq> Vs (set (edges_of_path P)) "
    using assms vs_edges_path_eq by auto
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

text \<open>Hamiltonian cycle\<close>
definition "is_hc H \<equiv> (H \<noteq> [] \<longrightarrow> (\<exists>v. walk_betw E v H v)) \<and> set (tl H) = Vs E \<and> distinct (tl H)"
(* TODO: Definition with \<open>is_cycle\<close> *)

lemma is_hc_def2: "is_hc H \<longleftrightarrow> (H \<noteq> [] \<longrightarrow> is_cycle E H) \<and> set (tl H) = Vs E \<and> distinct (tl H)"
proof
  assume "is_hc H"
  moreover then have "H \<noteq> [] \<longrightarrow> is_cycle E H"
    unfolding is_hc_def using cycle_length[OF graph] is_cycleI simple_pathI2 sorry
  ultimately show "(H \<noteq> [] \<longrightarrow> is_cycle E H) \<and> set (tl H) = Vs E \<and> distinct (tl H)"
    by (auto simp: is_hc_def)
next
  assume "(H \<noteq> [] \<longrightarrow> is_cycle E H) \<and> set (tl H) = Vs E \<and> distinct (tl H)"
  then show "is_hc H"
    unfolding is_hc_def by (auto elim: is_cycleE)
qed

thm cycle_length[OF graph]

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

lemma last_in_set_tl: "2 \<le> length xs \<Longrightarrow> last xs \<in> set (tl xs)"
  by (induction xs) auto

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

lemma edges_of_path_nil: 
  assumes "edges_of_path H = []" 
  shows "H = [] \<or> (\<exists>v. H = [v])"
  using assms by (induction H rule: edges_of_path.induct) auto

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

lemma walk_edges_subset: "walk_betw E u P v \<Longrightarrow> set (edges_of_path P) \<subseteq> E"
  using walk_between_nonempty_path[of E u P v] path_edges_subset by auto

lemma hc_edges_subset: 
  assumes "is_hc H"
  shows "set (edges_of_path H) \<subseteq> E"
proof (cases "H = []")
  case False
  then obtain v where "walk_betw E v H v"
    using assms by (auto elim: is_hc_nonnilE)
  then show ?thesis
    using walk_edges_subset by auto
qed auto

lemma hc_walk_betw1:
  assumes "is_hc H" "i\<^sub>u < i\<^sub>v" "i\<^sub>v < length H"
  shows "walk_betw E (H ! i\<^sub>u) (drop i\<^sub>u (take (i\<^sub>v+1) H)) (H ! i\<^sub>v)" (is "walk_betw E ?u ?P ?v")
proof (rule nonempty_path_walk_between)
  show "path E ?P"
    using assms path_drop[OF path_take, of E H i\<^sub>u "i\<^sub>v+1"] 
    by (cases H) (auto elim: is_hc_nonnilE simp: walk_between_nonempty_path)
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