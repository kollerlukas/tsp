(* Author: Lukas Koller *)
theory MinWeightMatching
  imports Main WeightedGraph
begin

definition "is_perf_match E M \<equiv> matching M \<and> Vs M = Vs E"

definition "is_min_w_match E c M \<equiv> 
  is_perf_match E M \<and> (\<forall>M'. is_perf_match E M' \<longrightarrow> sum c M \<le> sum c M')"

locale min_weight_matching =
  w_graph_abs E c for E :: "'a set set" and c +
  fixes comp_match
  assumes "(\<exists>M. is_perf_match E M) \<Longrightarrow> is_min_w_match E c (comp_match E c)"

end