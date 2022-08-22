theory CompleteGraph
  imports Main "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

locale graph_abs_compl =
  graph_abs +
  assumes complete: "\<forall>u\<in>Vs E.\<forall>v\<in>Vs E. {u,v}\<in>E"
begin

end

end