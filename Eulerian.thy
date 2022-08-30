theory Eulerian
  imports Main MultiGraph Select
begin

text \<open>even predicate for \<open>enat\<close>.\<close>
fun even' :: "enat \<Rightarrow> bool" where
  "even' \<infinity> = False"
| "even' i = even i"

lemma even_2x: "i \<noteq> \<infinity> \<Longrightarrow> even' (2 * i)"
  using dvdI sorry

text \<open>A graph is eulerian iff all vertices have even degree.\<close>
definition "is_eulerian E \<equiv> (\<forall>v \<in> mVs E. even' (mdegree E v))"

lemma is_eulerianI: "(\<And>v. v \<in> mVs E \<Longrightarrow> even' (mdegree E v)) \<Longrightarrow> is_eulerian E"
  unfolding is_eulerian_def by auto

definition "is_et E T \<equiv> mpath E T \<and> hd T = last T \<and> E = mset (edges_of_path T)"

lemma edges_of_path_nil:
  assumes "edges_of_path T = []"
  shows "T = [] \<or> (\<exists>v. T = [v])"
  using assms by (induction T rule: edges_of_path.induct) auto

lemma et_nil: "is_et E [] \<Longrightarrow> E = {#}"
  unfolding is_et_def by auto

lemma double_graph_degree:
  assumes "E\<^sub>2\<^sub>x = mset_set E + mset_set E" "v \<in> mVs E\<^sub>2\<^sub>x"
  shows "mdegree E\<^sub>2\<^sub>x v = 2 * degree E v"
  sorry

lemma non_inf_degr: "finite E \<Longrightarrow> degree E v \<noteq> \<infinity>"
  unfolding degree_def2 by auto

lemma et_edges: 
  assumes "is_et E T" 
  shows "E = mset (edges_of_path T)" (is "E = ?E(T)")
  using assms[unfolded is_et_def] by auto

lemma et_vertices: 
  assumes "is_et E T" "length T \<noteq> 1" (* there is not Eulerian Tour with length 1 *)
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
      then have "2 \<le> length (u#v#T)"
        by auto
      then obtain e where "e \<in> set (edges_of_path (u#v#T))" "w \<in> e"
        using path_vertex_has_edge[of "u#v#T" w, OF _ \<open>w \<in> set (u#v#T)\<close>] by auto
      then have "e \<in># E"
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
      then have "e \<in> set (edges_of_path (u#v#T))"
        using "3.prems"[unfolded is_et_def] by auto
      then show "w \<in> set (u#v#T)"
        using v_in_edge_in_path_gen[of e "u#v#T", OF _ \<open>w \<in> e\<close>] by auto
    qed
  qed
qed auto

lemma double_graph_eulerian:
  assumes "finite E" "E\<^sub>2\<^sub>x = mset_set E + mset_set E"
  shows "is_eulerian E\<^sub>2\<^sub>x"
proof (rule is_eulerianI)
  fix v
  assume "v \<in> mVs E\<^sub>2\<^sub>x"
  then show "even' (mdegree E\<^sub>2\<^sub>x v)"
    using assms non_inf_degr[of E v] double_graph_degree[of E\<^sub>2\<^sub>x E v] 
          even_2x[of "degree E v"] by auto
qed

locale eulerian =
  fixes comp_et :: "'a mgraph \<Rightarrow> 'a list"
  assumes eulerian: "is_eulerian E \<Longrightarrow> is_et E (comp_et E)"

end