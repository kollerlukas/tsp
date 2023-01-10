(* Author: Lukas Koller *)
theory EulerianTour
  imports Main tsp.Misc tsp.MultiGraph (* "../misc/Select" *)
begin

text \<open>A graph is eulerian iff all vertices have even degree.\<close>
definition "is_eulerian E \<equiv> (\<forall>v \<in> mVs E. even' (mdegree E v))"

lemma is_eulerianI: "(\<And>v. v \<in> mVs E \<Longrightarrow> even' (mdegree E v)) \<Longrightarrow> is_eulerian E"
  unfolding is_eulerian_def by auto

text \<open>Definition of a Eulerian tour on multigraphs.\<close>
definition "is_et E T \<equiv> mpath E T \<and> hd T = last T \<and> E = mset (edges_of_path T)"

lemma is_etE:
  assumes "is_et E T"
  shows "mpath E T" "hd T = last T" "E = mset (edges_of_path T)"
  using assms[unfolded is_et_def] by auto

lemma et_nil: "is_et E [] \<Longrightarrow> E = {#}"
  unfolding is_et_def by auto

lemma et_nil1: "is_et E [v] \<Longrightarrow> E = {#}"
  unfolding is_et_def by auto

lemma et_edges: 
  assumes "is_et E T" 
  shows "E = mset (edges_of_path T)"
  using assms by (auto elim: is_etE)

lemma et_length_neq_1_2:
  assumes "mgraph_invar E" "is_et E T"
  shows "length T \<noteq> 1" "length T \<noteq> 2"
proof -
  show "length T \<noteq> 1"
  proof (rule ccontr; simp only: not_not)
    assume "length T = 1"
    moreover then obtain v where "T = [v]"
      using list_hd_singleton by fastforce
    moreover hence "v \<in> mVs E"
      using assms mem_mpath_mVs[of E T] by (auto simp: is_etE)
    moreover then obtain e where "e \<in># E" "v \<in> e"
      by (auto elim: mVs_memberE)
    moreover have "E = {#}"
      using assms calculation et_nil1 by auto
    ultimately show "False"
      by auto
  qed

  show "length T \<noteq> 2"
  proof (rule ccontr; simp only: not_not)
    assume "length T = 2"
    moreover then obtain u v where "T = [u,v]"
      using list_hd_singleton by (metis Suc_1 length_Suc_conv)
    moreover hence "u = v"
      using assms is_etE by fastforce
    moreover have "{u,v} \<in># E"
      using assms calculation mpath_edges_subset[of E T] by (auto simp: is_etE)
    moreover hence "u \<noteq> v"
      using assms by auto
    ultimately show "False"
      by auto
  qed
qed

lemma et_vertices_len_neq_1: 
  assumes "is_et E T" "length T \<noteq> 1" (* there is no Eulerian Tour with length 1 *)
  shows "set T = mVs E"
  using assms
proof (induction T rule: edges_of_path.induct)
  case 1
  then show ?case 
    using et_nil[of E] by (auto simp: mVs_def Vs_def)
next
  case (3 u v T)
  show ?case
  proof 
    show "set (u#v#T) \<subseteq> mVs E"
    proof
      fix w
      assume "w \<in> set (u#v#T)"
      hence "2 \<le> length (u#v#T)"
        by auto
      then obtain e where "e \<in> set (edges_of_path (u#v#T))" "w \<in> e"
        using path_vertex_has_edge[of "u#v#T" w, OF _ \<open>w \<in> set (u#v#T)\<close>] by auto
      hence "e \<in># E"
        using "3.prems"[unfolded is_et_def] by auto
      then show "w \<in> mVs E"
        unfolding mVs_def Vs_def using \<open>w \<in> e\<close> by auto
    qed
  next
    show "mVs E \<subseteq> set (u#v#T)"
    proof
      fix w
      assume "w \<in> mVs E"
      then obtain e where "e \<in># E" "w \<in> e"
        unfolding mVs_def using vs_member by metis
      hence "e \<in> set (edges_of_path (u#v#T))"
        using "3.prems"[unfolded is_et_def] by auto
      then show "w \<in> set (u#v#T)"
        using v_in_edge_in_path_gen[of e "u#v#T", OF _ \<open>w \<in> e\<close>] by auto
    qed
  qed
qed auto

lemma double_graph_degree:
  assumes "E\<^sub>2\<^sub>x = mset_set E + mset_set E" "v \<in> mVs E\<^sub>2\<^sub>x"
  shows "mdegree E\<^sub>2\<^sub>x v = 2 * degree E v"
proof -
  have "mdegree E\<^sub>2\<^sub>x v = mdegree (mset_set E) v + mdegree (mset_set E) v"
    using assms mdegree_add by auto
  also have "... = 2 * degree E v"
    using mdegree_eq_degree[of E v] by (auto simp: semiring_numeral_class.mult_2)
  finally show ?thesis .
qed

lemma double_graph_eulerian:
  assumes "finite E" "E\<^sub>2\<^sub>x = mset_set E + mset_set E"
  shows "is_eulerian E\<^sub>2\<^sub>x"
proof (rule is_eulerianI)
  fix v
  assume "v \<in> mVs E\<^sub>2\<^sub>x"
  then show "even' (mdegree E\<^sub>2\<^sub>x v)"
    using assms non_inf_degr[of E v] double_graph_degree[of E\<^sub>2\<^sub>x E v] 
          even_enat_mult2[of "degree E v"] by auto
qed

locale eulerian =
  fixes comp_et :: "'a mgraph \<Rightarrow> 'a list"
  assumes eulerian: "\<And>E. is_eulerian E \<Longrightarrow> is_et E (comp_et E)"

(* TODO: implement algorithm to compute Eulerian Tour? *)

end