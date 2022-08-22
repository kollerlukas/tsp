theory TSP
  imports Main CompleteGraph
begin

context graph_abs
begin

text \<open>Hamiltonian cycle\<close>
definition "is_hc H \<equiv> path E H \<and> set H = Vs E \<and> distinct (tl H) \<and> hd H = last H"

fun cost_of_path where
  "cost_of_path c [] = 0"
| "cost_of_path c [v] = 0"
| "cost_of_path c (u#v#P) = c {u,v} + cost_of_path c (v#P)"

text \<open>Traveling-Salesman\<close>
definition "is_tsp c P \<equiv> graph_invar E \<and> (\<forall>e\<in>E. c e > 0) \<and> is_hc P 
  \<and> (\<forall>P'. is_hc P' \<longrightarrow> cost_of_path c P \<le> cost_of_path c P')"

end

context graph_abs_compl
begin

text \<open>metric Traveling-Salesman\<close>
definition "is_mtsp c P \<equiv> is_tsp c P"

end

end