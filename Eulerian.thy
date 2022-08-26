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

definition "is_et E T \<equiv> mpath E T \<and> hd T = last T \<and> 
  (\<forall>e\<in>#E. \<exists>!i. i < length (edges_of_path T) \<and> e = (edges_of_path T) ! i)"

lemma et_nil_iff:
  assumes "is_et E T"
  shows "T = [] \<longleftrightarrow> E = {#}"
  using assms sorry

lemma double_graph_degree:
  assumes "E\<^sub>2\<^sub>x = mset_set E + mset_set E" "v \<in> mVs E\<^sub>2\<^sub>x"
  shows "mdegree E\<^sub>2\<^sub>x v = 2 * degree E v"
  sorry

lemma non_inf_degr: "finite E \<Longrightarrow> degree E v \<noteq> \<infinity>"
  unfolding degree_def2 by auto

lemma et_edges: 
  assumes "is_et E T" 
  shows "E = mset (edges_of_path T)"
  sorry

lemma et_vertices: 
  assumes "is_et E T" 
  shows "set T = mVs E"
  sorry

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