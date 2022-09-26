(* Author: Lukas Koller *)
theory CompleteGraph
  imports Main Misc MinWeightMatching "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

locale compl_graph_abs = 
  graph_abs E for E +
  assumes complete: "u \<in> Vs E \<Longrightarrow> v \<in> Vs E \<Longrightarrow> u \<noteq> v \<Longrightarrow> {u,v} \<in> E"
begin

text \<open>In a complete graph any sequence of nodes is a path.\<close>
lemma path_complete_graph: 
  assumes "distinct_adj P" (* assumption: consecutive nodes are not equal! *)  "set P \<subseteq> Vs E" 
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

lemma perf_match_exists: 
  assumes graph: "graph_invar E" 
      and complete: "\<And>u v. u \<in> Vs E \<Longrightarrow> v \<in> Vs E \<Longrightarrow> u \<noteq> v \<Longrightarrow> {u,v} \<in> E"
      and "even (card (Vs E))"
  shows "\<exists>M. is_perf_match E M"
proof -
  have "finite_even (Vs E)"
    using assms finite_subset[OF Vs_subset] by (auto intro: finite_evenI2)
  thus ?thesis
    using assms
  proof (induction "Vs E" arbitrary: E rule: finite_even.induct)
    case 1
    moreover hence "E = {}"
      using Vs_nilE by blast
    moreover hence "is_perf_match E {}"
      by (auto intro: is_perf_matchI simp: matching_def)
    ultimately show ?case by auto
  next
    case (2 V u v)
    let ?E'="{e \<in> E. u \<notin> e \<and> v \<notin> e}"
    have "V = Vs ?E'"
      sorry
    moreover hence "even (card (Vs ?E'))"
      sorry
    moreover have "?E' \<subseteq> E"
      using "2.prems" by auto
    ultimately obtain M where "is_perf_match ?E' M"
      using 2 graph_subset sorry
    moreover have "{u,v} \<in> E"
      sorry
    ultimately have "is_perf_match E ({{u,v}} \<union> M)"
      sorry
    thus ?case by auto
  qed
qed

end