(* Author: Lukas Koller *)
theory CompleteGraph
  imports Main Misc "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

locale compl_graph_abs = 
  graph_abs E for E +
  assumes complete: "u\<in>Vs E \<Longrightarrow> v\<in>Vs E \<Longrightarrow> {u,v}\<in>E"
begin

text \<open>In a complete graph any sequence of nodes is a path.\<close>
lemma path_complete_graph: "set P \<subseteq> Vs E \<Longrightarrow> path E P"
  using complete by (induction P rule: list012.induct) auto

end

end