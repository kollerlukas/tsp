theory CompleteGraph
  imports Main "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

(* function just for the induction schema *)
fun a where
  "a E [] = undefined"
| "a E [v] = undefined"
| "a E (v#P) = a E P"

text \<open>In a complete graph any sequence of nodes is a path.\<close>
lemma path_in_complete_graph:
  assumes "\<forall>u\<in>Vs E.\<forall>v\<in>Vs E. {u,v}\<in>E" "set P \<subseteq> Vs E"
  shows "path E P"
  using assms by (induction E P rule: a.induct) auto

locale graph_abs_compl =
  graph_abs +
  assumes complete: "\<forall>u\<in>Vs E.\<forall>v\<in>Vs E. {u,v}\<in>E"
begin

lemmas complete_path = path_in_complete_graph[OF complete]

end

end