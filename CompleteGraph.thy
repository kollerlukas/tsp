(* Author: Lukas Koller *)
theory CompleteGraph
  imports Main Misc "berge/Berge"
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
    assume "V \<noteq> {}"
    show ?thesis
    proof
      fix v
      assume "v \<in> V"
      moreover then obtain u where "u \<in> V - {v}"
        using assms \<open>V \<noteq> {}\<close>
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

end