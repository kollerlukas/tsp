(* Author: Lukas Koller *)
theory CompleteGraph
  imports Main Misc "berge/Berge"
begin

definition "is_complete E \<equiv> (\<forall>u v. u \<in> Vs E \<and> v \<in> Vs E \<and> u \<noteq> v \<longrightarrow> {u,v} \<in> E)"

lemma is_completeI: "(\<And>u v. u \<in> Vs E \<Longrightarrow> v \<in> Vs E \<Longrightarrow> u \<noteq> v \<Longrightarrow> {u,v} \<in> E) \<Longrightarrow> is_complete E"
  unfolding is_complete_def by auto

lemma is_completeE: "is_complete E \<Longrightarrow> u \<in> Vs E \<Longrightarrow> v \<in> Vs E \<Longrightarrow> u \<noteq> v \<Longrightarrow> {u,v} \<in> E"
  unfolding is_complete_def by auto

locale compl_graph_abs = 
  graph_abs E for E +
  assumes complete: "is_complete E"
begin

lemma edge_in_E_intro: "u \<in> Vs E \<Longrightarrow> v \<in> Vs E \<Longrightarrow> u \<noteq> v \<Longrightarrow> {u,v} \<in> E"
  using complete[unfolded is_complete_def] by auto

text \<open>In a complete graph any sequence of nodes is a path.\<close>
lemma path_complete_graph: 
  assumes "distinct_adj P" (* assumption: consecutive nodes are not equal! *)  
      and "set P \<subseteq> Vs E" 
  shows "path E P" 
  using assms complete 
proof (induction P rule: list012.induct)
  case (3 u v P)
  moreover hence "{u,v} \<in> E"
    by (auto intro: edge_in_E_intro)
  moreover have "path E (v#P)"
    using calculation by (auto simp: distinct_adj_ConsD)
  ultimately show ?case 
    by (auto intro: path.intros)
qed auto

lemma prepend_path_by_vertex:
  assumes "path E P" "w \<in> Vs E" "P \<noteq> [] \<Longrightarrow> hd P \<noteq> w"
  shows "path E (w#P)"
proof cases
  assume "P = []"
  thus ?thesis
    using assms by (auto intro: path.intros)
next
  assume "P \<noteq> []"
  moreover hence "hd P \<noteq> w"
    using assms by auto
  moreover have "hd P \<in> Vs E"
    using assms calculation by (intro mem_path_Vs) auto
  ultimately have "{w,hd P} \<in> E"
    using assms by (auto intro: edge_in_E_intro)
  hence "path E ([w] @ P)"
    using assms by (intro path_append) auto
  thus ?thesis
    by auto
qed

lemma extend_path_by_vertex:
  assumes "path E P" "v \<in> Vs E" "P \<noteq> [] \<Longrightarrow> last P \<noteq> v"
  shows "path E (P @ [v])"
proof cases
  assume "P = []"
  thus ?thesis
    using assms by (auto intro: path.intros)
next
  assume "P \<noteq> []"
  moreover hence "last P \<noteq> v"
    using assms by auto
  moreover have "last P \<in> Vs E"
    using assms calculation by (intro mem_path_Vs) auto
  ultimately have "{last P,v} \<in> E"
    using assms by (auto intro: edge_in_E_intro)
  thus ?thesis
    using assms by (auto intro: path_append path.intros)
qed

lemma distinct_path_through_vertices:
  assumes "V \<subseteq> Vs E"
  obtains P where "path E P" "distinct P" "set P = V"
  using finite_vertices[OF assms(1)] assms
proof -
  obtain P where "set P = V" "distinct P"
    using finite_vertices[OF assms(1)] finite_distinct_list by auto
  moreover hence "path E P"
    using assms by (auto intro: path_complete_graph simp: distinct_distinct_adj)
  ultimately show ?thesis
    using that by auto
qed

lemma extend_path_by_edge_last_neq:
  assumes "path E P" "{u,v} \<in> E" "P \<noteq> [] \<Longrightarrow> last P \<noteq> u"
  shows "path E (P @ [u,v])"
proof cases
  assume "P = []"
  thus ?thesis
    using assms by (auto intro: edge_is_path)
next
  assume "P \<noteq> []"
  moreover hence "last P \<in> Vs E"
    using assms path_Vs_subset[of E P] by auto
  moreover have "u \<in> Vs E"
    using assms by (auto intro: vs_member_intro)
  moreover hence "{last P,u} \<in> E"
    using assms calculation by (auto intro: edge_in_E_intro)
  moreover have "path E [u,v]"
    using assms by (auto intro: edge_is_path)
  ultimately show ?thesis
    using assms by (auto intro: path_append)
qed

lemma extend_path_by_edge:
  assumes "path E P" "e \<in> E"
  obtains u v where "e = {u,v}" "path E (P @ [u,v])"
proof -
  obtain u v where [simp]: "e = {u,v}" "u \<noteq> v"
    using assms graph by auto
  then consider "P = []" "{u,v} \<in> E" | "last P \<noteq> u" "{u,v} \<in> E" | "last P \<noteq> v" "{v,u} \<in> E"
    using assms by (fastforce simp: insert_commute)
  thus ?thesis
    using assms that by cases (intro that, auto intro: extend_path_by_edge_last_neq)
qed

end

locale restr_compl_graph_abs =
  compl_graph_abs E +
  restr_graph_abs E V for V and E +
  assumes V_subset: "V \<subseteq> Vs E"
begin

lemma E\<^sub>V_complete: "is_complete E\<^sub>V"
proof (rule is_completeI)
  fix u v
  assume "u \<in> Vs E\<^sub>V" "v \<in> Vs E\<^sub>V" "u \<noteq> v"
  moreover hence "u \<in> Vs E" "v \<in> Vs E"
    using Vs_subset[of E\<^sub>V E] by (auto simp: E\<^sub>V_def)
  moreover have "{u,v} \<in> E"
    using calculation by (auto intro: edge_in_E_intro)
  moreover have "u \<in> V" 
    using calculation Vs_subset_restr_graph by (fastforce simp: E\<^sub>V_def)
  moreover have "v \<in> V"
    using calculation Vs_subset_restr_graph by (fastforce simp: E\<^sub>V_def)
  ultimately show "{u,v} \<in> E\<^sub>V"
    by (auto simp: E\<^sub>V_def)
qed

lemma edge_in_E\<^sub>V_intro: "u \<in> Vs E\<^sub>V \<Longrightarrow> v \<in> Vs E\<^sub>V \<Longrightarrow> u \<noteq> v \<Longrightarrow> {u,v} \<in> E\<^sub>V"
  using E\<^sub>V_complete[unfolded is_complete_def] by auto

lemma Vs_E\<^sub>V_eq_V:
  assumes "card V \<noteq> 1"
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
        using V_subset assms calculation by auto
      moreover hence "{u,v} \<in> E"
        using assms by (auto intro: edge_in_E_intro)
      ultimately have "{u,v} \<in> E\<^sub>V"
        unfolding E\<^sub>V_def using assms by auto
      thus "v \<in> Vs E\<^sub>V"
        by (auto intro: vs_member_intro)
    qed
  qed auto
qed (auto simp: Vs_subset_restr_graph)

lemma path_on_E\<^sub>V:
  assumes "card V \<noteq> 1"
      and "path E P" "set P \<subseteq> V"
  shows "path E\<^sub>V P"
proof (rule subset_path)
  show "path E P"
    using assms by auto
  show "set (edges_of_path P) \<subseteq> E\<^sub>V"
  proof
    fix e
    assume "e \<in> set (edges_of_path P)"
    moreover hence "e \<in> E"
      using assms calculation path_edges_subset by blast
    moreover have "e \<subseteq> V"
      using assms calculation edge_of_path_subset_of_vpath by blast
    ultimately show "e \<in> E\<^sub>V"
      unfolding E\<^sub>V_def by auto
  qed
  have "Vs E\<^sub>V = V"
    using assms by (intro Vs_E\<^sub>V_eq_V) auto  
  thus "set P \<subseteq> Vs E\<^sub>V"
    using assms by auto
qed

(* lemma last_short_cut:
  assumes "set P \<subseteq> Vs E\<^sub>V" "w \<in> Vs E\<^sub>V"
  shows "last (short_cut E\<^sub>V (P @ [w])) = w"
  using assms E\<^sub>V_complete
proof (induction P rule: list012.induct)
  case (3 u v P)
  thus ?case
  proof cases
    assume "{u,v} \<in> E\<^sub>V"
    thus ?case
      using 3 short_cut_nonnil by force
  qed auto
qed auto *)

lemma last_short_cut:
  assumes "u \<in> Vs E\<^sub>V" "w \<in> Vs E\<^sub>V"
  shows "last (short_cut E\<^sub>V (u#P @ [w])) = w"
  using assms edge_in_E\<^sub>V_intro
proof (induction "u#P" arbitrary: u P rule: short_cut.induct)
  case (3 E\<^sub>V u v P)
  thus ?case
  proof cases
    assume "{u,v} \<in> E\<^sub>V"
    moreover hence "v \<in> Vs E\<^sub>V"
      by (auto intro: edges_are_Vs)
    ultimately show ?case
      using 3 last_short_cut_simp[of u E\<^sub>V] by auto 
  qed auto
qed auto

lemma last_short_cut2:
  assumes "P \<noteq> []" "hd P \<in> Vs E\<^sub>V" "last P \<in> Vs E\<^sub>V"
  shows "last (short_cut E\<^sub>V P) = last P"
  using assms last_short_cut
proof -
  consider u where "P = [u]" | u w P' where "P = u#P' @ [w]"
    using assms by (metis neq_Nil_conv rev_exhaust)
  thus ?thesis
    using assms last_short_cut by cases auto
qed

lemma short_cut_path:
  assumes "path E (u#P)" "u \<in> Vs E\<^sub>V" "card V \<noteq> 1"
  shows "path E\<^sub>V (short_cut E\<^sub>V (u#P))"
proof (intro path_intro2)
  show "set (edges_of_path (short_cut E\<^sub>V (u#P))) \<subseteq> E\<^sub>V"
    by (intro short_cut_edges)
  show "set (short_cut E\<^sub>V (u#P)) \<subseteq> Vs E\<^sub>V"
    using assms by (intro short_cut_Vs_subset) auto
qed

lemma set_short_cut: 
  assumes "u \<in> Vs E\<^sub>V"
  shows "set (short_cut E\<^sub>V (u#P)) = (set (u#P) \<inter> Vs E\<^sub>V) \<union> {u}"
  using assms edge_in_E\<^sub>V_intro
proof (induction "u#P" arbitrary: u P rule: short_cut.induct)
  case (3 E\<^sub>V u v P)
  thus ?case 
  proof cases
    assume "{u,v} \<in> E\<^sub>V"
    moreover hence "v \<in> Vs E\<^sub>V"
      by (auto simp: edges_are_Vs)
    ultimately show ?thesis
      using 3 by auto
  next
    assume "{u,v} \<notin> E\<^sub>V"
    then consider "u = v" | "v \<notin> Vs E\<^sub>V"
      using "3.prems" by auto
    thus ?case
      using 3 \<open>{u,v} \<notin> E\<^sub>V\<close> by cases auto
  qed
qed auto

lemma short_cut_Vs_superset:
  assumes "u \<in> Vs E\<^sub>V" "Vs E\<^sub>V \<subseteq> set (u#P)"
  shows "Vs E\<^sub>V \<subseteq> set (short_cut E\<^sub>V (u#P))"
  using assms set_short_cut[of u P] by auto

end

context compl_graph_abs                                   
begin

lemma restr_graph_compl: "V \<subseteq> Vs E \<Longrightarrow> is_complete {e \<in> E. e \<subseteq> V}"
  by (intro restr_compl_graph_abs.E\<^sub>V_complete) unfold_locales

lemma restr_graph_Vs: "V \<subseteq> Vs E \<Longrightarrow> card V \<noteq> 1 \<Longrightarrow> Vs {e \<in> E. e \<subseteq> V} = V"
  by (intro restr_compl_graph_abs.Vs_E\<^sub>V_eq_V) unfold_locales

end

end