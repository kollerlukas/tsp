(* Author: Lukas Koller *)
theory MST
  imports Main "Prim_Dijkstra_Simple.Undirected_Graph" WeightedGraph (* default graph defintions from Berge? *)
begin

(* ask Mohammad: use Prim_Dijkstra_Simple definitions for trees, etc. or new defintions with equiv.-proofs? *)

text \<open>Connected Graph\<close>
definition "is_connected E \<equiv> \<forall>u\<in>Vs E.\<forall>v\<in>Vs E. u \<in> connected_component E v"

lemma is_connectedI: "(\<And>u v. u\<in>Vs E \<Longrightarrow> v\<in>Vs E \<Longrightarrow> u \<in> connected_component E v) \<Longrightarrow> is_connected E"
  unfolding is_connected_def by auto

text \<open>Acyclic Graph\<close>
definition "is_acyclic E \<equiv> \<forall>u v P P'. walk_betw E u P v \<and> walk_betw E u P' v \<longrightarrow> P = P'"

text \<open>Tree\<close>
definition "is_tree T \<equiv> is_connected T \<and> is_acyclic T"

lemma is_tree2: "is_tree T \<longleftrightarrow> card T = card (Vs T) - 1 \<and> is_connected T"
proof
  assume "is_tree T"
  show "card T = card (Vs T) - 1 \<and> is_connected T"
    sorry
next
  assume "card T = card (Vs T) - 1 \<and> is_connected T"
  show "is_tree T"
    sorry
qed

context graph_abs
begin

text \<open>Convert to graph from \<open>Prim_Dijkstra_Simple\<close>.\<close>
abbreviation "G \<equiv> Undirected_Graph.graph (Vs E) {(u,v)| u v. {u,v}\<in>E}"

lemma "is_connected E \<longleftrightarrow> Undirected_Graph.connected G"
  sorry

lemma "is_tree T \<longleftrightarrow> tree G"
  sorry

text \<open>Spanning Tree\<close>
definition "is_st T \<equiv> T \<subseteq> E \<and> Vs E = Vs T \<and> is_tree T"

end

context w_graph_abs
begin

definition "cost_of_st T \<equiv> (\<Sum>e\<in>T. c e)"

text \<open>Minimum Spanning Tree\<close>
definition "is_mst T \<equiv> is_st T \<and> (\<forall>T'. is_st T' \<longrightarrow> cost_of_st T \<le> cost_of_st T')"

lemma mst_eq_cost:
  assumes "is_mst T\<^sub>1" "is_mst T\<^sub>2"
  shows "cost_of_st T\<^sub>1 = cost_of_st T\<^sub>2"
  using assms[unfolded is_mst_def] by fastforce

end

locale mst = w_graph_abs E c for E c +
  fixes comp_mst
  assumes mst: "is_mst (comp_mst c E)"

(* TODO: use Prim_Dijkstra_Simple *)

(* interpretation mst
  sorry *)

end