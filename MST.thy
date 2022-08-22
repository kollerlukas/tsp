theory MST
  imports "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

context graph_abs
begin

section \<open>Definitions\<close>

text \<open>Connected Graph\<close>
definition "is_connected G \<equiv> \<forall>u\<in>Vs G.\<forall>v\<in>Vs G. u\<in>connected_component G v"

text \<open>Acyclic Graph\<close>
definition "is_acyclic G \<equiv> \<forall>P P'. path G P \<and> path G P' \<and> hd P = hd P' \<and> last P  = last P' \<longrightarrow> P = P'"

text \<open>Tree\<close>
definition "is_tree T \<equiv> is_connected T \<and> is_acyclic T"

text \<open>Spanning Tree\<close>
definition "is_st T \<equiv> T \<subseteq> E \<and> Vs E = Vs T \<and> is_tree T"

section \<open>Minimum Spanning Tree\<close>

definition "is_mst c T \<equiv> is_st T \<and> (\<forall>T'. is_st T' \<longrightarrow> (\<Sum>e\<in>T. c e) \<le> (\<Sum>e\<in>T'. c e))"

lemma finite_mst: 
  assumes "is_mst c T" 
  shows "finite T"
  using assms finite_subset finite_E unfolding is_mst_def is_st_def by auto

subsection \<open>Kruskal's Algorithm\<close>

fun kruskal :: "('a set \<Rightarrow> int) \<Rightarrow> 'a set set" where
  "kruskal c = (let Es = sorted_key_list_of_set c E; 
    f = \<lambda>T e. if is_acyclic (T \<union> {e}) then T \<union> {e} else T in 
    foldl f {} Es)"

lemma foldl_is_acyclic:
  assumes "is_acyclic T" "f = (\<lambda>T e. if is_acyclic (T \<union> {e}) then T \<union> {e} else T)"
  shows "is_acyclic (foldl f T Es)"
  using assms by (induction Es arbitrary: T) auto

lemma empty_path: 
  assumes "path {} P" 
  shows "P = []"
  using assms by (induction rule: path.induct) (auto simp: Vs_def)

lemma empty_is_acyclic: 
  shows "is_acyclic {}"
  unfolding is_acyclic_def using empty_path by blast

lemma kruskal_is_acyclic: 
  shows "is_acyclic (kruskal c)"
  using foldl_is_acyclic empty_is_acyclic by auto 

lemma kruskal_is_connected:
  assumes "is_connected E" 
  shows "is_connected (kruskal c)" (is "is_connected ?T")
proof (rule ccontr)
  assume "\<not>is_connected ?T"
  then obtain u v where "u\<in>Vs ?T" "v\<in>Vs ?T" "u\<notin>connected_component ?T v"
    unfolding is_connected_def by auto
  let ?uv="{{u',v'} | u' v'. {u',v'}\<in>E \<and> u'\<in>connected_component E u \<and> v'\<in>connected_component E v}"
  have "?uv \<noteq> {}"
    using assms unfolding is_connected_def sorry
  then obtain e where "e\<in>?uv" "\<forall>e'\<in>?uv. c e \<le> c e'"
    sorry

  

  show "False"
    sorry
qed

lemma "is_st (kruskal c)"
  sorry (* need characterizations of MST *)

lemma "is_mst c (kruskal c)"
  sorry

end

end