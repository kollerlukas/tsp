(* Author: Lukas Koller *)
theory TravelingSalesman
  imports Main tsp.Misc tsp.CompleteGraph tsp.WeightedGraph tsp.HamiltonianCycle
begin

section \<open>Traveling-Salesman Problem (\textsc{TSP})\<close>
definition "is_tsp E c P \<equiv> is_hc E P \<and> (\<forall>P'. is_hc E P' \<longrightarrow> cost_of_path c P \<le> cost_of_path c P')"

lemma is_tspE:
  assumes "is_tsp E c P"
  shows "is_hc E P" "\<And>P'. is_hc E P' \<Longrightarrow> cost_of_path c P \<le> cost_of_path c P'"
  using assms[unfolded is_tsp_def] by auto

lemma is_tsp_nilE:
  assumes "is_tsp E c P" "P = []"
  shows "Vs E = {}"
  using assms[unfolded is_tsp_def is_hc_def] by auto

lemma is_tsp_nonnilE:
  assumes "is_tsp E c P" "P \<noteq> []"
  obtains v where "walk_betw E v P v" "Vs E = set (tl P)" "distinct (tl P)" 
    "\<And>P'. is_hc E P' \<Longrightarrow> cost_of_path c P \<le> cost_of_path c P'"
  using assms[unfolded is_tsp_def] by (auto simp: is_hc_def)

context metric_graph_abs
begin

section \<open>Metric Traveling-Salesman (\textsc{mTSP})\<close>

text \<open>Metric Traveling-Salesman is the Traveling-Salesman Problem on complete and metric graphs.\<close>
abbreviation "is_mtsp P \<equiv> is_tsp E (\<lambda>u v. c {u,v}) P"

end

end