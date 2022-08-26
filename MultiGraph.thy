theory MultiGraph
  imports Main "HOL-Library.Multiset" "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

type_synonym 'a mgraph = "'a set multiset"

definition "mgraph_rel E\<^sub>1 E\<^sub>2 \<equiv> (set_mset E\<^sub>1 = set_mset E\<^sub>2)"

quotient_type 'a graph = "'a mgraph" / mgraph_rel
  morphisms Rep_graph Abs_graph
proof (rule equivpI)
  show "reflp mgraph_rel" by (auto simp: reflp_def mgraph_rel_def)
  show "symp mgraph_rel" by (auto simp: symp_def mgraph_rel_def)
  show "transp mgraph_rel" by (auto simp: transp_def mgraph_rel_def)
qed

locale mgraph_def =
  fixes E :: "'a set multiset"

abbreviation "mgraph_invar E \<equiv> graph_invar (set_mset E)"

locale mgraph_abs = mgraph_def +
  assumes mgraph: "mgraph_invar E"

definition "mVs E = Vs (set_mset E)"

definition "mpath E P \<equiv> path (set_mset E) P"

definition "mdegree (E::'a mgraph) v \<equiv> undefined" (* TODO *)

end