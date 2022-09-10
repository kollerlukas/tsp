(* Author: Lukas Koller *)
theory CompleteGraph
  imports Main "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

(* function just for the induction schema *)
fun list012 where
  "list012 [] = undefined"
| "list012 [v] = undefined"
| "list012 (u#v#P) = list012 (v#P)"

(* function just for the induction schema *)
fun list0123 where
  "list0123 [] = undefined"
| "list0123 [v] = undefined"
| "list0123 [u,v] = undefined"
| "list0123 (u#v#w#P) = list0123 (v#w#P)"

(* function just for the induction schema *)
fun list01234 where
  "list01234 [] = undefined"
| "list01234 [v] = undefined"
| "list01234 [u,v] = undefined"
| "list01234 [u,v,w] = undefined"
| "list01234 (u#v#w#x#P) = list01234 (v#w#x#P)"

locale compl_graph_abs = 
  graph_abs E for E +
  assumes complete: "u\<in>Vs E \<Longrightarrow> v\<in>Vs E \<Longrightarrow> {u,v}\<in>E"
begin

text \<open>In a complete graph any sequence of nodes is a path.\<close>
lemma path_complete_graph: "set P \<subseteq> Vs E \<Longrightarrow> path E P"
  using complete by (induction P rule: list012.induct) auto

end

end