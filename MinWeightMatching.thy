(* Author: Lukas Koller *)
theory MinWeightMatching
  imports Main WeightedGraph CompleteGraph
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

lemmas restr_graph_compl' = restr_compl_graph_abs.E\<^sub>V_complete[unfolded
    graph_abs_def
    compl_graph_abs_def compl_graph_abs_axioms_def
    restr_compl_graph_abs_def restr_compl_graph_abs_axioms_def 
    restr_graph_abs_def] (* TODO: clean up lemma!? *)

lemmas restr_graph_Vs' = restr_compl_graph_abs.Vs_E\<^sub>V_eq_V[unfolded
    graph_abs_def
    compl_graph_abs_def compl_graph_abs_axioms_def
    restr_compl_graph_abs_def restr_compl_graph_abs_axioms_def 
    restr_graph_abs_def] (* TODO: clean up lemma!? *)

context compl_graph_abs
begin

lemma perf_match_exists: 
  assumes "even (card (Vs E))"
  obtains M where "is_perf_match E M"
proof -
  have "finite_even (Vs E)"
    using graph assms finite_subset[OF Vs_subset] by (auto intro: finite_evenI2)
  thus ?thesis
    using that assms graph complete (* restr_graph_compl restr_graph_Vs[symmetric] *)
  proof (induction "Vs E" arbitrary: E thesis rule: finite_even.induct)
    case fe_empty
    moreover hence "E = {}"
      by (intro Vs_emptyE) auto
    moreover hence "is_perf_match E {}"
      by (auto intro: is_perf_matchI simp: matching_def)
    ultimately show ?case by auto
  next
    case (fe_insert2 V u v)
    moreover hence "V \<subseteq> Vs E"
      by (auto simp: finite_even_def2)
    moreover hence "card V \<noteq> 1"
      using fe_insert2 by (auto simp: finite_even_def2)
    moreover have "V = Vs {e \<in> E. e \<subseteq> V}" (is "V = Vs ?E'")
      using calculation by (intro restr_graph_Vs'[symmetric]) auto
    moreover hence "even (card (Vs ?E'))"
      using calculation by (auto simp: finite_even_def2)
    moreover have "?E' \<subseteq> E" "graph_invar ?E'"
      using calculation graph_subset[of E ?E'] by auto
    moreover have "is_complete ?E'"
      using calculation by (intro restr_graph_compl') auto
    moreover obtain M where "is_perf_match ?E' M"
      using calculation by blast
    moreover have "u \<in> Vs E" "v \<in> Vs E"
      using calculation by auto
    moreover hence "{{u,v}} \<union> ?E' \<subseteq> E"
      using calculation by auto
    ultimately have "is_perf_match E ({{u,v}} \<union> M)"
      by (intro extend_perf_match[of ?E' M]) auto
    thus ?case 
      using fe_insert2 by auto
  qed
qed

end

context restr_compl_graph_abs
begin

lemma perf_match_exists: 
  assumes "even (card (Vs E\<^sub>V))"
  obtains M where "is_perf_match E\<^sub>V M"
  using assms E\<^sub>V_graph E\<^sub>V_complete
    compl_graph_abs.perf_match_exists[unfolded 
      graph_abs_def 
      compl_graph_abs_def compl_graph_abs_axioms_def, of E\<^sub>V]
  by fastforce (* TODO: clean up lemma!? *)

end

context compl_graph_abs
begin

lemma restr_perf_match_exists: 
  assumes "V \<subseteq> Vs E" "even (card (Vs {e \<in> E. e \<subseteq> V}))"
  obtains M where "is_perf_match {e \<in> E. e \<subseteq> V} M"
  using assms graph complete 
    restr_compl_graph_abs.perf_match_exists[unfolded
      graph_abs_def
      compl_graph_abs_def compl_graph_abs_axioms_def
      restr_compl_graph_abs_def restr_compl_graph_abs_axioms_def 
      restr_graph_abs_def, of E V] 
  by fastforce (* TODO: clean up lemma!? *)

end

context w_graph_abs
begin

abbreviation "cost_of_match M \<equiv> sum c M"

end

context pos_w_graph_abs
begin

lemma cost_of_match_sum: "cost_of_match (set M) \<le> \<Sum>\<^sub># (image_mset c (mset M))"
proof (induction M)
  case (Cons e M)
  thus ?case 
    by (cases "e \<in> set M") (auto simp: add_left_mono insert_absorb add_increasing costs_ge_0)
qed auto

end

definition "is_min_match E c M \<equiv> 
  is_perf_match E M \<and> (\<forall>M'. is_perf_match E M' \<longrightarrow> sum c M \<le> sum c M')"

lemma is_min_matchE:
  assumes "is_min_match E c M"
  shows "is_perf_match E M" "\<And>M'. is_perf_match E M' \<Longrightarrow> sum c M \<le> sum c M'"
  using assms[unfolded is_min_match_def] by auto

lemma is_min_matchE2:
  assumes "is_min_match E c M"
  shows "M \<subseteq> E" "matching M" "Vs M = Vs E" "\<And>M'. is_perf_match E M' \<Longrightarrow> sum c M \<le> sum c M'"
  using is_min_matchE[OF assms] is_perf_matchE[of E M] by auto 

locale min_weight_matching =
  w_graph_abs E c for E :: "'a set set" and c +
  fixes comp_match
  assumes match: "\<And>E. (\<exists>M. is_perf_match E M) \<Longrightarrow> is_min_match E c (comp_match E c)"

end