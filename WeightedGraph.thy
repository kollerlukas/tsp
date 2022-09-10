(* Author: Lukas Koller *)
theory WeightedGraph
  imports Main "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

text \<open>Weighted Graph\<close>
locale w_graph_abs = 
  graph_abs E for E :: "'a set set" +
  fixes c :: "'a set \<Rightarrow> 'b::{ordered_semiring_0,times,numeral,monoid_mult}"

text \<open>Weighted Graph with positive weights\<close>
locale pos_w_graph_abs = 
  w_graph_abs E c for E c +
  assumes costs_positive: "c e > 0"
begin                            

lemma costs_ge_0: "c e \<ge> 0"
  using costs_positive by (simp add: order_less_imp_le)

lemma mult_2: "(x::'b) + x = 2 * x"
  using mult_1 distrib_right[symmetric, of 1 x 1] by auto

lemma mult_2_mono: "(x::'b) \<le> y \<Longrightarrow> 2 * x \<le> 2 * y"
  using mult_2[symmetric] add_mono_thms_linordered_semiring(1) by fastforce

end

end