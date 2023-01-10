(* Author: Lukas Koller *)
theory MinWeightMatching
  imports Main tsp.Misc tsp.WeightedGraph tsp.CompleteGraph
begin

definition "is_perf_match E M \<equiv> M \<subseteq> E \<and> matching M \<and> Vs M = Vs E"

lemma is_perf_matchI:
  assumes "M \<subseteq> E" "matching M" "Vs M = Vs E"
  shows "is_perf_match E M"
  using assms by (auto simp: is_perf_match_def)

lemma is_perf_matchI2:
  assumes "M \<subseteq> E" "\<And>u. u \<in> Vs E \<Longrightarrow> \<exists>!e \<in> M. u \<in> e"
  shows "is_perf_match E M"
proof -
  have "Vs M = Vs E"
    using assms
  proof (intro equalityI)
    show "Vs E \<subseteq> Vs M"
    proof
      fix v
      assume "v \<in> Vs E"
      then obtain e where "e \<in> M" "v \<in> e"
        using assms by meson
      thus "v \<in> Vs M"
        by (auto intro: vs_member_intro)
    qed
  qed (auto simp: Vs_subset)
  moreover hence "matching M"
    unfolding matching_def2 using assms by auto
  ultimately show ?thesis
    using assms by (intro is_perf_matchI)
qed

lemma is_perf_matchE:
  assumes "is_perf_match E M"
  shows "M \<subseteq> E" "matching M" "Vs M = Vs E"
  using assms[unfolded is_perf_match_def] by auto

lemma extend_perf_match:
  assumes "is_perf_match E M" "u \<notin> Vs E" "v \<notin> Vs E" "{{u,v}} \<union> E \<subseteq> E'" "Vs E' = Vs E \<union> {u,v}"
  shows "is_perf_match E' ({{u,v}} \<union> M)"
proof (rule is_perf_matchI2)
  have "M \<subseteq> E"
    using assms by (auto simp: is_perf_matchE)
  thus "{{u,v}} \<union> M \<subseteq> E'"
    using assms by auto

  show "\<And>w. w \<in> Vs E' \<Longrightarrow> \<exists>!e \<in> {{u,v}} \<union> M. w \<in> e"
  proof -
    fix w
    assume "w \<in> Vs E'"
    then consider "w \<in> {u,v}" | "w \<in> Vs E - {u,v}"
      using assms by auto
    thus "\<exists>!e \<in> {{u,v}} \<union> M. w \<in> e"
    proof cases
      assume "w \<in> {u,v}"
      moreover hence "\<exists>!e \<in> {{u,v}}. w \<in> e"
        by auto
      moreover have "w \<notin> Vs M"
        using assms calculation by (auto simp: is_perf_matchE)
      moreover hence "\<forall>e \<in> M. w \<notin> e"
        using vs_member[of w M] by auto
      ultimately show "\<exists>!e \<in> {{u,v}} \<union> M. w \<in> e"
        by auto
    next
      assume "w \<in> Vs E - {u,v}"
      moreover hence "w \<in> Vs M" "matching M"
        using assms by (auto simp: is_perf_matchE)
      moreover hence "\<exists>!e \<in> M. w \<in> e"
        by (auto simp: matching_def2)
      ultimately show "\<exists>!e \<in> {{u,v}} \<union> M. w \<in> e"
        by auto 
    qed
  qed
qed

lemma restr_graph_compl': 
  "graph_invar E \<Longrightarrow> is_complete E \<Longrightarrow> V \<subseteq> Vs E \<Longrightarrow> is_complete {e \<in> E. e \<subseteq> V}" 
  by (intro restr_compl_graph_abs.E\<^sub>V_complete) unfold_locales (* TODO: clean up lemma!? *)

lemma restr_graph_Vs':
  "graph_invar E \<Longrightarrow> is_complete E \<Longrightarrow> V \<subseteq> Vs E \<Longrightarrow> card V \<noteq> 1 \<Longrightarrow> Vs {e \<in> E. e \<subseteq> V} = V"
  by (intro restr_compl_graph_abs.Vs_E\<^sub>V_eq_V) unfold_locales (* TODO: clean up lemma!? *)

context compl_graph_abs
begin

lemma perf_match_exists: 
  assumes "even (card (Vs E))"
  obtains M where "is_perf_match E M"
proof -
  have "finite (Vs E)" "even (card (Vs E))"
    using graph assms finite_subset[OF Vs_subset] by auto
  thus ?thesis
    using assms graph complete (* restr_graph_compl restr_graph_Vs *) that
  proof (induction "Vs E" arbitrary: E thesis rule: finite_even_induct)
    case empty
    moreover hence "E = {}"
      by (intro Vs_emptyE) auto
    moreover hence "is_perf_match E {}"
      by (auto intro: is_perf_matchI simp: matching_def)
    ultimately show ?case by auto
  next
    case (insert2 u v V)
    have "even (card V)"
      apply (rule finite_even_cardI)
      using insert2 by auto
    moreover have "V \<subseteq> Vs E"
      using insert2 by auto
    moreover hence "V = Vs {e \<in> E. e \<subseteq> V}" (is "V = Vs ?E'")
      using insert2 calculation by (intro restr_graph_Vs'[symmetric]) auto
    moreover have "even (card (Vs ?E'))" 
      using calculation by auto
    moreover have "graph_invar ?E'" 
      apply (rule graph_subset)
      using insert2 by auto
    moreover have "is_complete ?E'"
      using insert2 calculation by (intro restr_graph_compl') 
    ultimately obtain M where "is_perf_match ?E' M"
      using is_completeE[of ?E'] by (elim insert2.hyps(5))
    moreover have "u \<notin> Vs ?E'" "v \<notin> Vs ?E'" "Vs E = Vs ?E' \<union> {u,v}"
      using insert2 by (auto simp: \<open>V = Vs {e \<in> E. e \<subseteq> V}\<close>[symmetric])
    moreover have "u \<in> Vs E" "v \<in> Vs E"
      using insert2 by auto
    moreover hence "{u,v} \<in> E"
      using insert2 by (intro is_completeE)
    moreover hence "{{u,v}} \<union> ?E' \<subseteq> E"
      by auto
    ultimately have "is_perf_match E ({{u,v}} \<union> M)"
      by (intro extend_perf_match)
    thus ?case
      using insert2 by auto
  qed
qed

end

context restr_compl_graph_abs
begin

lemma perf_match_exists: 
  assumes "even (card (Vs E\<^sub>V))"
  obtains M where "is_perf_match E\<^sub>V M"
  apply (rule compl_graph_abs.perf_match_exists[of E\<^sub>V])
  apply unfold_locales
  using graph_E\<^sub>V E\<^sub>V_complete assms that by auto (* TODO: clean up lemma!? *)

end

context compl_graph_abs
begin

lemma restr_perf_match_exists: 
  assumes "V \<subseteq> Vs E" "even (card (Vs {e \<in> E. e \<subseteq> V}))"
  obtains M where "is_perf_match {e \<in> E. e \<subseteq> V} M"
  apply (rule restr_compl_graph_abs.perf_match_exists)
  apply unfold_locales
  using assms that by auto (* TODO: clean up lemma!? *)

end

abbreviation "cost_of_match c M \<equiv> sum c M"

context w_graph_abs
begin

abbreviation "cost_of_match\<^sub>c M \<equiv> sum c M"

end

context pos_w_graph_abs
begin

lemma cost_of_match_sum: "cost_of_match\<^sub>c (set M) \<le> \<Sum>\<^sub># (image_mset c (mset M))"
proof (induction M)
  case (Cons e M)
  thus ?case 
    by (cases "e \<in> set M") (auto simp: add_left_mono insert_absorb add_increasing costs_ge_0)
qed auto

end

definition "is_min_match E c M \<equiv> 
  is_perf_match E M \<and> (\<forall>M'. is_perf_match E M' \<longrightarrow> cost_of_match c M \<le> cost_of_match c M')"

lemma is_min_matchE:
  assumes "is_min_match E c M"
  shows "is_perf_match E M" "\<And>M'. is_perf_match E M' \<Longrightarrow> cost_of_match c M \<le> cost_of_match c M'"
  using assms[unfolded is_min_match_def] by auto

lemma is_min_matchE2:
  assumes "is_min_match E c M"
  shows "M \<subseteq> E" "matching M" "Vs M = Vs E" 
    "\<And>M'. is_perf_match E M' \<Longrightarrow> cost_of_match c M \<le> cost_of_match c M'"
  using is_min_matchE[OF assms] is_perf_matchE[of E M] by auto 

locale min_weight_matching =
  w_graph_abs E c for E :: "'a set set" and c +
  fixes comp_match
  assumes match: "\<And>E. (\<exists>M. is_perf_match E M) \<Longrightarrow> is_min_match E c (comp_match E c)"

end