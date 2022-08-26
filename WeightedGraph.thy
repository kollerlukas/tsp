(* Author: Lukas Koller *)
theory WeightedGraph
  imports Main "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

text \<open>Weighted Graph\<close>
locale w_graph_abs = 
  graph_abs E for E :: "'a set set" +
  fixes c :: "'a set \<Rightarrow> 'b::{ordered_semiring_0,times,numeral}" (* which types *)
  assumes "e \<in> E \<Longrightarrow> c e = c e"

text \<open>Weighted Graph with psotive weights\<close>
locale pos_w_graph_abs = 
  w_graph_abs E c for E c +
  assumes costs_positive: "c e > 0"
begin                            

lemma costs_ge_0: "c e \<ge> 0"
  using costs_positive by (simp add: order_less_imp_le)

lemma "c e + c e = (1 + 1) * c e" (* for testing... *)
  sorry

end

end