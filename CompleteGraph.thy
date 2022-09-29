(* Author: Lukas Koller *)
theory CompleteGraph
  imports Main Misc MinWeightMatching "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

abbreviation "is_complete E \<equiv> (\<forall>u v. u \<in> Vs E \<and> v \<in> Vs E \<and> u \<noteq> v \<longrightarrow> {u,v} \<in> E)"

locale compl_graph_abs = 
  graph_abs E for E +
  assumes complete: "is_complete E"
begin

text \<open>In a complete graph any sequence of nodes is a path.\<close>
lemma path_complete_graph: 
  assumes "distinct_adj P" (* assumption: consecutive nodes are not equal! *)  
      and "set P \<subseteq> Vs E" 
  shows "path E P" 
  using assms complete 
proof (induction P rule: list012.induct)
  case (3 u v P)
  moreover hence "{u,v} \<in> E"
    using complete by auto
  moreover have "path E (v#P)"
    using calculation by (auto simp: distinct_adj_ConsD)
  ultimately show ?case 
    by (auto intro: path.intros)
qed auto

end

lemma restricted_graph_complete:
  fixes V E
  defines "E\<^sub>V \<equiv> {e \<in> E. e \<subseteq> V}"
  assumes "is_complete E"
  shows "is_complete E\<^sub>V"
proof (rule allI impI)+
  fix u v
  assume "u \<in> Vs E\<^sub>V \<and> v \<in> Vs E\<^sub>V \<and> u \<noteq> v"
  moreover hence "u \<in> Vs E" "v \<in> Vs E"
    using Vs_subset[of E\<^sub>V E] by (auto simp: E\<^sub>V_def)
  moreover have "{u,v} \<in> E"
    using assms calculation by auto
  moreover have "u \<in> V" 
    using calculation Vs_subset_restricted_graph by (fastforce simp: E\<^sub>V_def)
  moreover have "v \<in> V"
    using calculation Vs_subset_restricted_graph by (fastforce simp: E\<^sub>V_def)
  ultimately show "{u,v} \<in> E\<^sub>V"
    by (auto simp: E\<^sub>V_def)
qed

lemma Vs_restricted_complete_graph:
  fixes V E
  defines "E\<^sub>V \<equiv> {e \<in> E. e \<subseteq> V}"
  assumes "is_complete E" "card V \<noteq> 1" "V \<subseteq> Vs E"
  shows "Vs E\<^sub>V = V"
  using assms
proof (intro equalityI)
  show "V \<subseteq> Vs E\<^sub>V"
  proof (cases "V = {}")
    case False
    show ?thesis
    proof
      fix v
      assume "v \<in> V"
      moreover then obtain u where "u \<in> V - {v}"
        using assms False
        by (metis is_singletonI' is_singleton_altdef member_remove remove_def) (* TODO: clean up *)
      moreover have "v \<in> Vs E" "u \<in> Vs E" "u \<noteq> v"
        using assms calculation by auto
      moreover hence "{u,v} \<in> E"
        using assms by auto
      ultimately have "{u,v} \<in> E\<^sub>V"
        using assms by auto
      thus "v \<in> Vs E\<^sub>V"
        by (auto intro: vs_member_intro)
    qed
  qed auto
qed (auto simp: Vs_subset_restricted_graph)

lemma perf_match_exists: 
  assumes graph: "graph_invar E" 
      and complete: "is_complete E"
      and "even (card (Vs E))"
  shows "\<exists>M. is_perf_match E M"
proof -
  have "finite_even (Vs E)"
    using assms finite_subset[OF Vs_subset] by (auto intro: finite_evenI2)
  thus ?thesis
    using assms
  proof (induction "Vs E" arbitrary: E rule: finite_even.induct)
    case fe_empty
    moreover hence "E = {}"
      using Vs_nilE by blast
    moreover hence "is_perf_match E {}"
      by (auto intro: is_perf_matchI simp: matching_def)
    ultimately show ?case by auto
  next
    case (fe_insert2 V u v)
    moreover hence "card V \<noteq> 1" "V \<subseteq> Vs E"
      by (auto simp: finite_even_def2)
    moreover hence "V = Vs {e \<in> E. e \<subseteq> V}" (is "V = Vs ?E'")
      using calculation Vs_restricted_complete_graph[of E V] by auto
    moreover hence "even (card (Vs ?E'))"
      using calculation by (auto simp: finite_even_def2)
    moreover have "?E' \<subseteq> E" "graph_invar ?E'"
      using calculation graph_subset[of E ?E'] by auto
    moreover have "is_complete ?E'"
      using calculation restricted_graph_complete[of E V] by auto
    moreover obtain M where "is_perf_match ?E' M"
      using calculation by fastforce
    moreover have "u \<in> Vs E" "v \<in> Vs E"
      using calculation by auto
    moreover hence "{{u,v}} \<union> ?E' \<subseteq> E"
      using calculation by auto
    ultimately have "is_perf_match E ({{u,v}} \<union> M)"
      by (intro extend_perf_match[of ?E' M]) auto
    thus ?case by auto
  qed
qed

end