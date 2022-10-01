(* Author: Lukas Koller *)
theory WeightedGraph
  imports Main Misc "HOL-Library.Multiset"
begin

text \<open>Weighted Graph\<close>
locale w_graph_abs = 
  graph_abs E for E :: "'a set set" +
  fixes c :: "'a set \<Rightarrow> 'b::{ordered_semiring_0,semiring_numeral}"

text \<open>Weighted Graph with positive weights\<close>
locale pos_w_graph_abs = 
  w_graph_abs E c for E c +
  assumes costs_positive: "c e > 0"
begin                            

lemma costs_ge_0: "c e \<ge> 0"
  using costs_positive by (simp add: order_less_imp_le)

lemma sum_costs_pos: "sum c A \<ge> 0"
  using costs_ge_0 by (simp add: sum_nonneg)

lemma sum_union_leq:
  assumes "finite A" "finite B"
  shows "sum c (A \<union> B) \<le> sum c A + sum c B"
proof -
  have "sum c (A \<union> B) \<le> sum c (A \<union> B) + sum c (A \<inter> B)"
    using sum_costs_pos add_increasing2 by auto
  also have "...  = sum c A + sum c B"
    using assms sum.union_inter by auto
  finally show ?thesis .
qed

fun cost_of_path where
  "cost_of_path [] = 0"
| "cost_of_path [v] = 0"
| "cost_of_path (u#v#P) = c {u,v} + cost_of_path (v#P)"

lemma cost_of_path_pos: "cost_of_path P \<ge> 0"
  by (induction P rule: cost_of_path.induct) (auto simp: costs_ge_0)

lemma cost_of_path_le: "cost_of_path P \<le> cost_of_path (v#P)"
  by (induction P arbitrary: v rule: cost_of_path.induct) (auto simp: costs_ge_0 add_increasing)

lemma cost_of_path_sum: "cost_of_path P = (\<Sum>e \<in># mset (edges_of_path P). c e)"
  by (induction P rule: cost_of_path.induct) auto

lemma cost_of_path_distinct_sum: 
  assumes "distinct (edges_of_path P)" 
  shows "(\<Sum>e \<in> set (edges_of_path P). c e) = cost_of_path P"
  using assms cost_of_path_sum[of P] mset_set_set[of "edges_of_path P"] 
  by (simp add: sum_unfold_sum_mset)

lemma cost_of_path_leq_sum: "(\<Sum>e \<in> set (edges_of_path P). c e) \<le> cost_of_path P"
proof (induction P rule: cost_of_path.induct)
  case (3 u v P)
  have "sum c (set (edges_of_path (u#v#P))) \<le> c {u,v} + sum c (set (edges_of_path (v#P)))"
    using sum_union_leq[of "{{u,v}}" "set (edges_of_path (v#P))"] by auto
  also have "... \<le> cost_of_path (u#v#P)"
    using "3.IH" by (auto simp: add_left_mono)
  finally show ?case .
qed auto

lemma cost_of_path_app: "cost_of_path (P @ [u,v]) = c {u,v} + cost_of_path (P @ [u])"
  by (induction P rule: cost_of_path.induct) (auto simp: add.assoc add.commute add.left_commute)

lemma cost_of_path_rev: "cost_of_path P = cost_of_path (rev P)"
proof (induction P rule: cost_of_path.induct)
  case (3 u v P)
  then have "cost_of_path (u#v#P) = c {u,v} + cost_of_path (rev P @ [v])"
    using "3.IH" by auto
  also have "... = cost_of_path (rev (u#v#P))"
    using cost_of_path_app[of "rev P" v u] by (auto simp: insert_commute)
  finally show ?case .
qed auto

end

end