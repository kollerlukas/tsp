(* Author: Lukas Koller *)
theory MST
  imports Main WeightedGraph (* "Prim_Dijkstra_Simple.Prim_Impl" *)
begin

text \<open>Connected Graph\<close>
definition "is_connected E \<equiv> \<forall>u\<in>Vs E.\<forall>v\<in>Vs E. u\<in>connected_component E v"

text \<open>Acyclic Graph\<close>
definition "is_acyclic E \<equiv> \<forall>P P'. path E P \<and> path E P' \<and> hd P = hd P' \<and> last P  = last P' \<longrightarrow> P = P'"

text \<open>Tree\<close>
definition "is_tree T \<equiv> is_connected T \<and> is_acyclic T"

context graph_abs
begin

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