theory TSP
  imports Main CompleteGraph
begin

context graph_abs
begin

text \<open>Hamiltonian cycle\<close>
definition "is_hc H \<equiv> path E H \<and> set H = Vs E \<and> distinct (tl H) \<and> hd H = last H"

lemma hc_nil_iff: "E = {} \<longleftrightarrow> is_hc []"
proof -
  have "E = {} \<longleftrightarrow> path E [] \<and> set [] = Vs E"
    unfolding Vs_def using graph by force
  also have "... \<longleftrightarrow> is_hc []"
    unfolding is_hc_def by (simp add: hd_Nil_eq_last)
  finally show ?thesis .
qed

fun cost_of_path :: "('a set \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "cost_of_path c [] = 0"
| "cost_of_path c [v] = 0"
| "cost_of_path c (u#v#P) = c {u,v} + cost_of_path c (v#P)"

lemma cost_of_path_sum: "cost_of_path c P = (\<Sum>e\<in>set (edges_of_path P). c e)"
  apply (induction P rule: cost_of_path.induct)
  apply auto
  sorry


text \<open>Traveling-Salesman\<close>
definition "is_tsp (c::'a set \<Rightarrow> nat) P \<equiv> graph_invar E \<and> (\<forall>e\<in>E. c e > 0) \<and> is_hc P 
  \<and> (\<forall>P'. is_hc P' \<longrightarrow> cost_of_path c P \<le> cost_of_path c P')"

end

context graph_abs_compl
begin

text \<open>metric Traveling-Salesman\<close>
definition "is_mtsp (c::'a set \<Rightarrow> nat) P \<equiv> 
  is_tsp c P \<and> (\<forall>u\<in>Vs E.\<forall>v\<in>Vs E.\<forall>w\<in>Vs E. c {u,w} \<le> c {u,v} + c {v,w})"

end

end