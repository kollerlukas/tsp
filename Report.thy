(*<*)
theory Report
  imports Main 
    "graphs/WeightedGraph"
    "graphs/CompleteGraph"
    "problems/MinWeightMatching"
    "problems/MinSpanningTree"
    "problems/EulerianTour"
    "problems/TravelingSalesman"
    "algorithms/DoubleTree"
    "algorithms/ChristofidesSerdyukov"
    "graphs/GraphAdjList"
    "graphs/GraphAdjMap_Specs"
    "reductions/VertexCover4ToMetricTravelingSalesman_Specs"
    "reductions/FindHamiltonianPath"
    "reductions/VertexCover4ToMetricTravelingSalesman_AdjList"

    "HOL-Library.OptionalSugar"
begin
declare [[show_question_marks = false]]
(*>*)

section \<open>Introduction\<close>

text \<open>The \textsc{Traveling-Salesman Problem} (\textsc{TSP}) is a well known optimization problem. 
The \textsc{TSP} describes the problem of finding a tour with minimum total weight in a given 
weighted undirected graph s.t. every vertex of the graph is visited exactly once. The \textsc{TSP} 
has many applications in different areas, such as planning and scheduling @{cite "brumitt_stentz_1996"}, 
logistics @{cite "ratliff_rosenthal_1983"}, and designing printed circuit boards @{cite "groetschel_et_al_1991"}.

The \textsc{TSP} is \textsc{NP}-hard @{cite "korte_vygen_2018"}. This means, that unless 
$\textsc{P}=\textsc{NP}$, the \textsc{TSP} cannot be solved in polynomial time. When dealing with 
\textsc{NP}-hard optimization problems, a typical strategy is to approximate the optimal solution with 
an approximation algorithm @{cite "vazirani_2010"}. An approximation algorithm is a polynomial time 
algorithm that returns a bounded approximate solution. The approximation ratio gives a bound on the 
distance between the approximate solution and the optimal solution. Ideally, the approximation ratio 
is a constant factor. An approximation algorithm essentially trades the optimality of the returned 
solution for a polynomial running time. 
Unfortunately, there are bad news for the \textsc{TSP}: there is no constant-factor approximation 
algorithm for the \textsc{TSP} @{cite "sahni_gonzalez_1976"}. 

The \textsc{Metric TSP} is a simplifies the \textsc{TSP} by making the following two assumptions:
\begin{enumerate*}[label=(\roman*)]
  \item the given graph is complete and 
  \item the edge-weights satisfy the triangle-inequality.
\end{enumerate*}
The \textsc{Metric TSP} is still \textsc{NP}-hard @{cite "sahni_gonzalez_1976"}.

This report describes the formalization of parts of the section 21.1, \textit{Approximation Algorithms 
for the TSP} from @{cite "korte_vygen_2018"}.
\begin{enumerate}
  \item I have formalized and verified two approximation algorithms, \textsc{DoubleTree} and 
    \textsc{Christofides-Serdyukov}, for \textsc{Metric TSP}.
  \item I have formalized an L-reduction from the \textsc{Minimum Vertex Cover Problem} with maximum 
    degree of 4 (\textsc{VCP4}) to the \textsc{Metric TSP}, which proves the \textsc{MaxSNP}-hardness 
    of the \textsc{Metric TSP}.
\end{enumerate}

The \textsc{MaxSNP}-hardness of a problem proves the non-existence of an approximation scheme @{cite "papadimitriou_yannakakis_1991"}.
An approximation scheme is an approximation algorithm that takes an additional parameter \<open>\<epsilon> > 0\<close>
and has an approximation ratio of \<open>1 + \<epsilon>\<close> for minimization and \<open>1 - \<epsilon>\<close> for maximization problems. 
\textsc{MaxSNP} is a complexity class that contains graph-theoretical optimization problems. For any 
problem in \textsc{MaxSNP} there is a constant-factor approximation algorithm @{cite "papadimitriou_yannakakis_1991"}.
A linear reduction (L-reduction) is special type of reduction for optimization problems @{cite "papadimitriou_yannakakis_1991"}, 
that is used to prove the \textsc{MaxSNP}-hardness of problems. A problem is called 
\textsc{MaxSNP}-hard if every problem in \textsc{MaxSNP} L-reduces to it.

All of my formalizations are done within the interactive theorem prover Isabelle/HOL @{cite "nipkow_wenzel_paulson_2002"}.
My formalizations can be found on GitHub: \url{https://github.com/kollerlukas/tsp}.\<close>

(* ----- *)

section \<open>Related Work\<close>

text \<open>With an approximation ratio of $\frac{3}{2}$, the \textsc{Christofides-Serdyukov} algorithm 
@{cite "christofides_1976" and "serdyukov_1978"} is the best known approximation algorithm for the 
\textsc{Metric TSP} @{cite "korte_vygen_2018"}. Recently, @{cite "karlin_et_al_2021"} have developed a 
randomized approximation algorithm for the \textsc{Metric TSP} which (in expectation) achieves a 
slightly better approximation ratio than the \textsc{Christofides-Serdyukov} algorithm.

In @{cite "essmann_et_al_2020"} 6 different approximation algorithms are formalized and verified in 
Isabelle/HOL. I have followed their formalization approaches and formalized the \textsc{DoubleTree} 
and the \textsc{Christofides-Serdyukov} algorithm in similar fashion.

In @{cite "wimmer_2021"} polynomial time reductions are formalized in Isabelle/HOL. To formally reason 
about running times of functions a computational model for the programming language is required. 
Therefore, @{cite "wimmer_2021"} have developed the imperative language \texttt{IMP-} which provides 
a computational model to reason about the running times of function implemented in \texttt{IMP-}.\<close>

section \<open>Fundamentals and Definitions\<close>

text \<open>I build on the formalization of graphs by @{cite "abdulaziz_2020"}, which is developed for a 
formalization of Berge's theorem @{cite "berge_1954"}. 
An undirected graph is formalized as a finite set of edges. An edge is represented by a doubleton set. 

@{abbrev[display] graph_invar}

The locale @{locale graph_abs} fixes an instance \<open>E\<close> of a graph that satisfies the invariant 
@{const graph_invar}. The graph formalization by @{cite "abdulaziz_2020"} provides definitions for 
the following concepts.
\begin{itemize}
  \item Vertices of a graph: @{const Vs}
  \item Paths: @{const path}, @{const walk_betw}, and @{const edges_of_path}
  \item Degree of vertices: @{const degree}
  \item Connected components: @{const connected_component}
  \item Matchings: @{const matching}
\end{itemize}
 
The approximation algorithms and the L-reduction use many graph-related concepts that are not 
defined in @{cite "abdulaziz_2020"}, such as weighted graphs, minimum spanning-tree, or 
Hamiltonian cycle. This section describes the formalization of graph-related concepts that are the 
necessary for the formalization of the \textsc{DoubleTree} and \textsc{Christofides-Serdyukov} 
approximation algorithms as well as the L-reduction. Most of the definitions are straightforward, 
therefore only important formalization choices are highlighted.

All of the graph-related definitions are defined in theories which are located in the 
@{path "./graphs"}- or @{path "./problems"}-directory.

Many simple results and lemmas are formalized in the theory @{file "./misc/Misc.thy"} which is 
located in the directory @{path "./misc"}.\<close>

subsection \<open>Connected Graphs\<close>

text \<open>A graph is connected if all vertices are contained in the same connected component. 

@{thm[display] is_connected_def}\<close>

subsection \<open>Weighted Graphs\<close>

text \<open>The locale @{locale w_graph_abs} fixes an instance of a graph \<open>E\<close> and edge weights \<open>c\<close>.

The locale @{locale pos_w_graph_abs} extends the locale @{locale w_graph_abs} with the 
assumption that all edge weights are positive.\<close>
(* (*<*)
context pos_w_graph_abs
begin
(*>*)
text \<open>The locale @{locale pos_w_graph_abs} extends the locale @{locale w_graph_abs} with the 
assumption that all edge weights are positive.

@{thm[display] costs_positive}\<close>
(*<*)
end
(*>*) *)
text \<open>The function \<open>cost_of_path\<^sub>c\<close> computes the cost of a given path with the edge weights \<open>c\<close>.\<close>

subsection \<open>Complete Graphs\<close>

text \<open>A graph is complete if there exists an edge between every two vertices.

@{thm[display] is_complete_def}
                          
The locale @{locale compl_graph_abs} fixes an instance of a complete graph \<open>E\<close>.\<close>
(*<*)
context compl_graph_abs
begin
(*>*)
text \<open>In a complete graph, any sequence of vertices s.t. no two consecutive vertices are equal is a path.

@{lemma[display] "is_complete E \<Longrightarrow> distinct_adj P \<Longrightarrow> set P \<subseteq> Vs E \<Longrightarrow> path E P" by (rule path_complete_graph)}\<close>
(*<*)
end
(*>*)
(* text \<open>The locale @{const restr_compl_graph_abs} additionally fixes a subgraph of the instance \<open>E\<close>.\<close>*)
(*<*)
context metric_graph_abs
begin
(*>*)
text\<open>The locale @{locale metric_graph_abs} extends the locales @{locale compl_graph_abs} and 
@{locale pos_w_graph_abs} and assumes that the edge weights \<open>c\<close> satisfy the triangle-inequality. 
Within such a graph any intermediate vertex on a path can be removed to obtain a shorter path. 
Given a set of vertices \<open>X\<close> and a path \<open>P\<close>, the function @{const short_cut} removes all vertices 
along the path \<open>P\<close> that are not contained \<open>X\<close>. The resulting path has a less total weight.

@{thm[display] cost_of_path_short_cut_tri_ineq[where E\<^sub>V="X"]}\<close>
(*<*)
end
(*>*)

subsection \<open>Acyclic Graphs\<close>

text \<open>A path is a simple if no edge is used twice.

@{thm[display] is_simple_def}

A cycle is a path s.t. 
\begin{enumerate*}[label=(\roman*)]
  \item the first and last vertex are the same,
  \item the path is simple, and
  \item the path uses at least one edge.
\end{enumerate*}

@{thm[display] is_cycle_def}

A graph is acyclic if it does not contain a cycle.

@{thm[display] is_acyclic_def}\<close>
(*<*)
context graph_abs
begin
(*>*)
text \<open>A vertex that is contained in a cycle has a degree of at least 2.

@{thm[display] cycle_degree}\<close>
(*<*)
end
(*>*)

subsection \<open>Trees\<close>

text \<open>A tree is a graph that is 
\begin{enumerate*}[label=(\roman*)]
  \item connected,
  \item acyclic.
\end{enumerate*}

@{thm[display] is_tree_def}

A spanning tree of a graph is a subgraph s.t.
\begin{enumerate*}[label=(\roman*)]
  \item it is a tree and
  \item it contains every vertex.
\end{enumerate*}

@{thm[display] is_st_def}\<close>

(*<*)
context w_graph_abs
begin
(*>*)
text\<open>A minimum spanning tree (MST) is a spanning tree with minimum total weight. The function 
@{const cost_of_st\<^sub>c} computes the total weight of a given spanning tree with the edge weights \<open>c\<close>.

@{lemma[display,source] "is_mst E c T \<equiv> is_st E T \<and> (\<forall>T'. is_st E T' \<longrightarrow> cost_of_st\<^sub>c T \<le> cost_of_st\<^sub>c T')" by (rule is_mst_def)}\<close>
(* @{thm[display] is_mst_def} *)
(*<*)
end
(*>*)

text \<open>The locale @{locale mst} assumes the existence of an algorithm (denoted by \<open>comp_mst\<close>) to 
compute a MST for a given graph.\<close>

subsection \<open>Hamiltonian Cycles\<close>

text \<open>A Hamiltonian cycle is a non-empty tour in a graph that visits every vertex exactly once.

@{lemma[display,source] "is_hc E H \<equiv> 
  (H \<noteq> [] \<longrightarrow> (\<exists>v. walk_betw E v H v)) \<and> set (tl H) = Vs E \<and> distinct (tl H)" by (rule is_hc_def)}

With this formalization, a Hamiltonian cycle is not necessarily a cycle. The graph that only contains 
one edge \<open>e={u,v}\<close> has the Hamiltonian cycle \<open>u,v,u\<close> which is not a cycle. The path is not a simple, 
because the edge \<open>e\<close> is used twice.\<close>

subsection \<open>Traveling-Salesman Problem\<close>

text \<open>A solution to the \textsc{TSP} is a Hamiltonian cycle with minimum total weight.\<close>
(*<*)
context w_graph_abs
begin
(*>*)
text\<open>@{lemma[display,source] "is_tsp E c P \<equiv> 
  is_hc E P \<and> (\<forall>P'. is_hc E P' \<longrightarrow> cost_of_path\<^sub>c P \<le> cost_of_path\<^sub>c P')" by (rule is_tsp_def)}\<close>
(* @{thm[display] is_tsp_def} *)
(*<*)
end
(*>*)

subsection \<open>Multi-Graphs\<close>

text \<open>A multigraph is formalized as a multiset of edges. The theory @{file "./graphs/MultiGraph.thy"} 
contains unfinished attempts for encoding a multigraph with a regular graph.\<close>

subsection \<open>Eulerian Tours\<close>

text \<open>A graph is eulerian if every vertex has even degree. The \textsc{DoubleTree} and the 
\textsc{Christofides-Serdyukov} algorithm use eulerian multigraphs, thus the predicate 
@{const is_eulerian} is defined for multigraphs. The function @{const mdegree} returns the degree of 
a vertex in a multigraph. @{const mVs} return the set of vertices of a multigraph.

@{thm[display] is_eulerian_def}

A Eulerian tour is a path that uses every edge of a given graph exactly once. @{const mpath} is the 
predicate for a path in a multigraph.

@{thm[display] is_et_def}

The locale @{locale eulerian} fixes an algorithm (denoted by \<open>comp_et\<close>) to compute a Eulerian tour 
for a given multi-graph.\<close>

subsection \<open>Perfect Matchings\<close>

text \<open>A perfect matching is a matching that contains every vertex.

@{thm[display] is_perf_match_def}\<close>
(*<*)
context w_graph_abs
begin
(*>*)
text \<open>A minimum-weight perfect matching is a perfect matching with minimum total weight.

@{lemma[display] "is_min_match E c M \<equiv> 
  is_perf_match E M \<and> (\<forall>M'. is_perf_match E M' \<longrightarrow> cost_of_match c M \<le> cost_of_match c M')" by (rule is_min_match_def)}\<close>
(*<*)
end
(*>*)
text \<open>The locale @{locale min_weight_matching} fixes an algorithm (denoted by \<open>comp_match\<close>) to 
compute a minimum-weight perfect matching for a given graph.\<close>

subsection \<open>Vertex Cover\<close>

text \<open>A vertex cover is a subset of edges that contains at least one endpoint of every edge.

@{thm[display] is_vc_def}

A minimum vertex cover is a vertex cover with minimum cardinality.

@{thm[display] is_min_vc_def}\<close>
(*<*)
context graph_abs
begin
(*>*)
text \<open>If the degree of every vertex in a graph \<open>E\<close> is bounded by a constant \<open>k\<close>, then the number of 
edges in \<open>E\<close> is upper-bounded by \<open>k\<close>-times the cardinality of a vertex cover.

@{thm[display] card_E_leq_max_degree_card_vc}\<close>
(*<*)
end
(*>*)

(* ----- *)

section \<open>Approximating the \textsc{Metric TSP}\<close>

text \<open>This section describes the formalization of the \textsc{DoubleTree} and the 
\textsc{Christofides-Serdyukov} approximation algorithms for \textsc{Metric TSP}. Both 
algorithms are quite similar 
and depend on the following proposition @{cite \<open>Lemma 21.3\<close> "korte_vygen_2018"}:

Let the graph \<open>E\<close> with edge weights \<open>c\<close> be an instance of the \textsc{Metric TSP}. Given a connected 
Eulerian graph \<open>E'\<close> that spans the vertices of the graph \<open>E\<close>, we can compute (in polynomial time) a 
Hamiltonian cycle for \<open>E\<close> with total weight of at most the total weight of all edges in \<open>E'\<close>. 

The proof for this proposition is constructive: first compute a Eulerian tour \<open>P\<close> for the Eulerian 
graph \<open>E'\<close>. The tour \<open>P\<close> visits every vertex of \<open>E\<close> at least once, because the Eulerian graph \<open>E'\<close> 
spans the vertices of \<open>E\<close>. Next, the duplicate vertices in the tour \<open>P\<close> are removed to 
obtain the desired Hamiltonian cycle for the graph \<open>E\<close> ("shortcutting"). The edge weights \<open>c\<close> 
satisfy the triangle-inequality (by assumption), thus the total weight of the resulting 
Hamiltonian cycle is at most the total weight of the Eulerian tour \<open>P\<close>, which is exactly the total 
weight of all edges in the Eulerian graph \<open>E'\<close>.

The construction for this proposition is formalized with the function @{const comp_hc_of_et}. Given 
a Eulerian tour for \<open>E'\<close>, the function @{const comp_hc_of_et} computes a Hamiltonian cycle for \<open>E\<close>. 
The locale @{locale hc_of_et} (see theory @{file "./algorithms/DoubleTree.thy"}) extends the locales 
@{locale metric_graph_abs} and @{locale eulerian} and thus assumes the necessary assumptions for the 
input graph \<open>E\<close>. The second argument to the function @{const comp_hc_of_et} is an accumulator.\<close>
(*<*)
context hc_of_et
begin
(*>*)
text \<open>We assume the multigraph \<open>E'\<close> spans the vertices of the graph \<open>E\<close> and only contains edges (maybe 
multiple instance of an edge) of the graph \<open>E\<close>.

@{thm[display] hc_of_et_correct[where X="E'",no_vars]}

The following lemma shows that the total weight of the Hamiltonian cycle returned by the function 
@{const comp_hc_of_et} is bounded by the total weight of the edges of the Eulerian tour \<open>P\<close>.
                         
@{thm[display] hc_of_et_reduces_cost [no_vars]}\<close>
(*<*)
end
(*>*)

text \<open>With the proposition @{cite \<open>Lemma 21.3\<close> "korte_vygen_2018"} the task of approximating 
\textsc{Metric TSP} boils down to constructing a Eulerian graph that spans the vertices of the graph \<open>E\<close>. 
The total weight of the edges of the Eulerian graph directly bounds the total weight of the approximate 
solution, and thus directly influcences the approximation-ratio.

Both approximation algorithms, \textsc{DoubleTree} and \textsc{Christofides-Serdyukov}, first 
compute a MST \<open>T\<close> of the input graph \<open>E\<close>. Then edges are added to the MST \<open>T\<close> to construct a 
Eulerian graph that spans the vertices of the graph \<open>E\<close>.

The \textsc{DoubleTree} algorithm constructs a Eulerian graph by simply doubling every edge of the 
MST \<open>T\<close>. In this multigraph every vertex has even degree and thus this multi-graph is a Eulerian 
graph. The total weight of any Hamiltonian cycle is at least the the total weight of \<open>T\<close>. Thus, the 
total weight of the Hamiltonian cycle produced by the \textsc{DoubleTree} algorithm is at most 
2-times the total weight of the optimal Hamiltonian cycle. Therefore, the 
\textsc{DoubleTree} algorithm is a 2-approximation algorithm for the \textsc{Metric TSP}.

On the other hand, the \textsc{Christofides-Serdyukov} algorithm computes a minimum perfect-matching 
\<open>M\<close> between the vertices that have odd-degree in \<open>T\<close>. The union of \<open>M\<close> and the MST \<open>T\<close> is a 
Eulerian graph. The total weight of \<open>M\<close> is at most half the total weight of the optimal Hamiltonian 
cycle. Therefore, the \textsc{Christofides-Serdyukov} algorithm is a $\frac{3}{2}$-approximation 
algorithm for the \textsc{Metric TSP}.

The polynomial running time of both the \textsc{DoubleTree} and \textsc{Christofides-Serdyukov} are 
easy to see and thus explicit proofs are omitted.\<close>

subsection \<open>Formalizing the \textsc{DoubleTree} Algorithm\<close>

text \<open>The \textsc{DoubleTree} algorithm consists of three main steps.
\begin{enumerate}
  \item Compute a MST \<open>T\<close> of the input graph \<open>E\<close>.
  \item Compute a Eulerian tour \<open>P\<close> of the doubled MST \<open>T + T\<close>.
  \item Remove duplicate vertices in \<open>P\<close> by short-cutting (see @{const comp_hc_of_et}).
\end{enumerate}
Thus, the \textsc{DoubleTree} algorithm depends to two algorithms:
\begin{enumerate}
  \item an algorithm to compute a MST, e.g. Prim's algorithm @{cite "lammich_nipkow_2019"}, and
  \item an algorithm to compute a Eulerian tour in an Eulerian multigraph, e.g. Eulers's algorithm @{cite "korte_vygen_2018"}.
\end{enumerate}
For the formalization of the \textsc{DoubleTree} algorithm the existence of an algorithm for both of 
these problems is assumed. The locale @{locale double_tree_algo} extends the locales 
@{locale hc_of_et} and @{locale mst} and thus assumes the existence of the required algorithms. 
The existence of a function \<open>comp_et\<close> to compute an Eulerian tour is already is assumed by the 
locale @{locale hc_of_et}. The function \<open>comp_mst\<close> denotes the assumed function to compute a MST.\<close>
(*<*)
context double_tree_algo
begin
(*>*)
text \<open>@{lemma[display,source] "double_tree = (
    let T = comp_mst c E;
        T\<^sub>2\<^sub>x = mset_set T + mset_set T;
        P = comp_et T\<^sub>2\<^sub>x in
        comp_hc_of_et P [])" by (rule double_tree_def)}

For the defined \textsc{DoubleTree} algorithm two properties need to be proven:
\begin{enumerate*}[label=(\roman*)]
  \item the feasibility, and
  \item the approximation ratio.
\end{enumerate*}
The formalization of these proofs is straightforward. The following lemma proves the feasibility 
of the \textsc{DoubleTree} algorithm. The path returned by the \textsc{DoubleTree} algorithm is 
indeed a Hamiltonian cycle for the graph \<open>E\<close>.

@{thm[display] dt_is_hc [no_vars]}\<close>
(*<*)
end
context double_tree_algo_approx
begin                
(*>*)
text\<open>The following lemma shows that the approximation ratio of the \textsc{DoubleTree} algorithm is 2. 
\<open>OPT\<close> denotes the optimal tour for the graph \<open>E\<close>.

@{thm[display] dt_approx [no_vars]}\<close>
(*<*)
end
locale dt_hoare_display = double_tree_algo_approx E c comp_et comp_mst for E c comp_et comp_mst + 
  assumes opt: "is_mtsp OPT"
begin

lemma dt_hoare_display: "VARS T T\<^sub>2\<^sub>x v P P' H { True }
    T := comp_mst c E;
    T\<^sub>2\<^sub>x := mset_set T + mset_set T;
    P := comp_et T\<^sub>2\<^sub>x;
    P' := P;
    H := [];
    WHILE P' \<noteq> [] 
    INV { comp_hc_of_et P [] = comp_hc_of_et P' H 
      \<and> P = comp_et T\<^sub>2\<^sub>x 
      \<and> T\<^sub>2\<^sub>x = mset_set T + mset_set T 
      \<and> T = comp_mst c E 
    } DO
      v := hd P';
      P' := tl P';
      IF v \<in> set H \<and> P' \<noteq> [] THEN
        H := H
      ELSE
        H := v#H
      FI
    OD { is_hc E H \<and> cost_of_path\<^sub>c H \<le> 2 * cost_of_path\<^sub>c OPT }"
  apply (rule refine_double_tree)
  apply unfold_locales
  apply (simp add: graph)
  apply (simp add: complete)
  apply (simp add: costs_positive)
  apply (simp add: tri_ineq)
  apply (simp add: opt)
  apply (simp add: mst)
  apply (simp add: eulerian)
  done
(*>*)
text\<open>Finally, the definition of the \textsc{DoubleTree} algorithm is refined to a \texttt{WHILE}-program 
using Hoare Logic.

@{lemma[display,source] "VARS T T\<^sub>2\<^sub>x v P P' H 
  { True }
    T := comp_mst c E;
    T\<^sub>2\<^sub>x := mset_set T + mset_set T;
    P := comp_et T\<^sub>2\<^sub>x;
    P' := P;
    H := [];
    WHILE P' \<noteq> [] 
    INV { comp_hc_of_et P [] = comp_hc_of_et P' H 
      \<and> P = comp_et T\<^sub>2\<^sub>x 
      \<and> T\<^sub>2\<^sub>x = mset_set T + mset_set T 
      \<and> T = comp_mst c E 
    } DO
      v := hd P';
      P' := tl P';
      IF v \<in> set H \<and> P' \<noteq> [] THEN
        H := H
      ELSE
        H := v#H
      FI
    OD 
  { is_hc E H \<and> cost_of_path\<^sub>c H \<le> 2 * cost_of_path\<^sub>c OPT }" by (rule dt_hoare_display)}\<close>
(*<*)
end
(*>*)

(* ----- *)

subsection \<open>Formalizing the \textsc{Christofides-Serdyukov} Algorithm\<close>

text \<open>The \textsc{Christofides-Serdyukov} algorithm is similar to the \textsc{DoubleTree}, and 
consists of the following steps.
\begin{enumerate}
  \item Compute a MST \<open>T\<close> of the input graph \<open>E\<close>.
  \item Compute a minimum perfect-matching \<open>M\<close> between the vertices that have odd degree in \<open>T\<close>.
  \item Compute a Eulerian tour \<open>P\<close> of the union of the MST and the perfect-matching \<open>J = T + M\<close>.
  \item Remove duplicate vertices in \<open>P\<close> by short-cutting (see @{const comp_hc_of_et}).
\end{enumerate}
Hence, the \textsc{Christofides-Serdyukov} algorithm depends on 3 algorithms: the 2 algorithms the 
\textsc{DoubleTree} algorithm dependes on, as well as an algorithm to compute a minimum 
perfect-matching, e.g. Edmond's Blossom algorithm @{cite edmonds_1965}.

The \textsc{Christofides-Serdyukov} algorithm is formalized in a similar fashion to the 
\textsc{DoubleTree} algorithm. The locale @{locale christofides_serdyukov_algo} extends the locale 
@{locale double_tree_algo} and adds the assumption for the existence of an algorithm to compute a 
minimum perfect-matching. The function \<open>comp_match\<close> computes a minimum perfect-matching for a given 
graph. The definition of the \textsc{Christofides-Serdyukov} algorithm in the 
locale @{locale christofides_serdyukov_algo} is straightforward.\<close>
(*<*)
context christofides_serdyukov_algo
begin
(*>*)
text \<open>@{lemma[display,source] "christofides_serdyukov = (
    let T = comp_mst c E;
        W = {v \<in> Vs T. \<not> even' (degree T v)};
        M = comp_match ({e \<in> E. e \<subseteq> W}) c;
        J = mset_set T + mset_set M;
        P = comp_et J in
        comp_hc_of_et P [])" by (rule christofides_serdyukov_def)}

The feasibility of the \textsc{Christofides-Serdyukov} algorithm is proven by the following lemma. 
The path returned by the \textsc{Christofides-Serdyukov} algorithm is indeed a Hamiltonian cycle.\<close>
(*<*)
end
context christofides_serdyukov_algo_feasibility
begin
(*>*)
text \<open>@{thm[display] cs_is_hc [no_vars]}\<close>
(*<*)
end
context christofides_serdyukov_algo_approx
begin
(*>*)
text \<open>The following lemma shows that the approximation ratio of the \textsc{Christofides-Serdyukov} 
algorithm is $\frac{3}{2}$. \<open>OPT\<close> denotes the optimal tour for the graph \<open>E\<close>.

@{thm[display] cs_approx [no_vars]}\<close>
(*<*)
end
context christofides_serdyukov_algo_approx
begin

lemma cs_hoare_display: "VARS T W M J v P P' H { True }
    T := comp_mst c E;
    W := {v \<in> Vs T. \<not> even' (degree T v)};
    M := comp_match ({e \<in> E. e \<subseteq> W}) c;
    J := mset_set T + mset_set M;
    P := comp_et J;
    P' := P;
    H := [];
    WHILE P' \<noteq> [] 
    INV { comp_hc_of_et P [] = comp_hc_of_et P' H 
      \<and> P = comp_et J 
      \<and> J = mset_set T + mset_set M 
      \<and> M = comp_match ({e \<in> E. e \<subseteq> W}) c 
      \<and> W = {v \<in> Vs T. \<not> even' (degree T v)} 
      \<and> T = comp_mst c E 
    } DO
      v := hd P';
      P' := tl P';
      IF v \<in> set H \<and> P' \<noteq> [] THEN
        H := H
      ELSE
        H := v#H
      FI
    OD { is_hc E H \<and> 2 * cost_of_path\<^sub>c H \<le> 3 * cost_of_path\<^sub>c OPT }"
  apply (rule refine_christofides_serdyukov)
  apply unfold_locales
  apply (simp add: mst)
  apply (simp add: eulerian)
  apply (simp add: match)
  apply (simp add: opt)
  
  done
(*>*)
text\<open>Like the \textsc{DoubleTree} algorithm, the definition of the \textsc{Christofides-Serdyukov} 
algorithm is refined to a \texttt{WHILE}-program using Hoare Logic.

@{lemma[display,source] "VARS T W M J v P P' H 
  { True }
    T := comp_mst c E;
    W := {v \<in> Vs T. \<not> even' (degree T v)};
    M := comp_match ({e \<in> E. e \<subseteq> W}) c;
    J := mset_set T + mset_set M;
    P := comp_et J;
    P' := P;
    H := [];
    WHILE P' \<noteq> [] 
    INV { comp_hc_of_et P [] = comp_hc_of_et P' H 
      \<and> P = comp_et J 
      \<and> J = mset_set T + mset_set M 
      \<and> M = comp_match ({e \<in> E. e \<subseteq> W}) c 
      \<and> W = {v \<in> Vs T. \<not> even' (degree T v)} 
      \<and> T = comp_mst c E 
    } DO
      v := hd P';
      P' := tl P';
      IF v \<in> set H \<and> P' \<noteq> [] THEN
        H := H
      ELSE
        H := v#H
      FI
    OD 
  { is_hc E H \<and> 2 * cost_of_path\<^sub>c H \<le> 3 * cost_of_path\<^sub>c OPT }" by (rule cs_hoare_display)}\<close>
(*<*)
end
(*>*)

(* ----- *)
 
section \<open>L-Reduction from \textsc{VCP4} to \textsc{Metric TSP}\<close>

(*<*)
context VCP4_To_mTSP
begin
(*>*)

text \<open>This section describes the formalization of an L-Reduction from the 
\textsc{Minimum Vertex Cover Problem}, with maximum degree of 4 (\textsc{VCP4}), to the \textsc{Metric TSP}. 
The formalization is based of an L-reduction proof by @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"}.

The \textsc{Minimum Vertex Cover Problem} describes the optimization problem of finding
a vertex-cover with minimum cardinality for a given graph. A vertex-cover is subset of vertices 
that contains at least one end-point of every edge. The \textsc{VCP4} is the restriction of the 
\textsc{Minimum Vertex Cover Problem} to input graphs where the degree of every vertex is bounded by 4.
The bounded degree is only needed to prove the linear inequalities that are required for the L-reduction. 
The \textsc{VCP4} is known to be \textsc{MaxSNP}-hard @{cite \<open>Theorem 16.46\<close> "korte_vygen_2018"}.

First, I define what an L-reduction is.
Let \<open>A\<close> and \<open>B\<close> be optimization problems with cost functions \<open>c\<^sub>A\<close> and \<open>c\<^sub>B\<close>. The cost of the optimal
solution for an instance of an optimization problem is denoted by \<open>OPT(\<cdot>)\<close>.
An L-reduction (linear reduction) consists of a pair of functions \<open>f\<close> and \<open>g\<close> and two positive constants
\<open>\<alpha>,\<beta> > 0\<close> s.t for every instance \<open>x\<^sub>A\<close> of \<open>A\<close>
\begin{enumerate}[label=(\roman*)]
  \item \<open>f x\<^sub>A\<close> is an instance of \<open>B\<close> and \<open>OPT (f x\<^sub>A) \<le> \<alpha>(OPT x\<^sub>A)\<close>, and 
  \item for any feasible solution \<open>y\<^sub>B\<close> of \<open>f x\<^sub>A\<close>, \<open>g x\<^sub>A y\<^sub>B\<close> is a feasible solution of \<open>x\<^sub>A\<close> s.t.
    \<open>\<bar>((c\<^sub>A x\<^sub>A (g x\<^sub>A y\<^sub>B)) - OPT x\<^sub>A\<bar> \<le> \<bar>(c\<^sub>A (f x\<^sub>A) y\<^sub>B) - OPT (f x\<^sub>A)\<bar>\<close>.
\end{enumerate}

The second linear inequality essentially ensures the following: given an optimal solution for \<open>f x\<^sub>A\<close>
the function \<open>g\<close> has to construct an optimal solution for \<open>x\<^sub>A\<close>.

We L-reduce the \textsc{VCP4} to the \textsc{Metric TSP} by defining the functions \<open>f\<close> and \<open>g\<close> and 
proving their required properties.
The function \<open>f\<close> maps an instance of the \textsc{VCP4} to an instance of the \textsc{Metric TSP}. 
An instance of the \textsc{VCP4} consists of a  graph where the degree of every vertex is at most 4.
To construct an instance of the \textsc{Metric TSP}, we need to construct a complete graph with edge 
weights s.t. the edge weights satisfy the triangle-inequality.

\begin{figure}
  \centering
  \begin{tikzpicture}
    \pic[scale=2.0] (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};
  \end{tikzpicture}
  \caption{Subgraph \<open>H\<^sub>e\<close> for an edge \<open>e:={u,v}\<close>. Each corner vertex of \<open>H\<^sub>e\<close> corresponds to an endpoint of \<open>e\<close>.}\label{fig:He}
\end{figure}

The function \<open>f\<close> is defined by the following construction.
Let \<open>G\<close> be an instance of the \textsc{VCP4}, and let \<open>H:=f G\<close> denote the graph that is construct from 
\<open>G\<close> by the function \<open>f\<close>. For each edge \<open>e\<close> of \<open>G\<close>, a subgraph \<open>H\<^sub>e\<close> is added to \<open>H\<close> (see Figure~\ref{fig:He}). 
The function \<open>f\<close> computes the complete graph over all the subgraphs \<open>H\<^sub>e\<close> (one for every edge \<open>e\<close> of the graph \<open>G\<close>). 
The subgraph \<open>H\<^sub>e\<close> consists of 12 vertices that are arranged in a 4-by-3 lattice structure. 
Each corner vertex of subgraph \<open>H\<^sub>e\<close> corresponds to an endpoint of the edge \<open>e\<close>. The subgraph \<open>H\<^sub>e\<close> 
has the special property that there is no Hamiltonian path for \<open>H\<^sub>e\<close> that starts and ends at corner 
vertices of \<open>H\<^sub>e\<close> that correspond to different endpoints of the edge \<open>e\<close>. E.g. there is no Hamiltonian 
path for the subgraph \<open>H\<^sub>e\<close> that starts at the top-left corner vertex and ends at the bottom-right 
corner vertex. Therefore, the start- and end-vertex of a Hamiltonian path for a subgraph \<open>H\<^sub>e\<close> can 
only correspond to the one endpoint of the edge \<open>e\<close>. This property is used to encode a vertex cover 
of \<open>G\<close> in a Hamiltonian cycle of \<open>H\<close>. The subgraph \<open>H\<^sub>e\<close> admits 3 types of Hamiltonian paths 
(see Figure~\ref{fig:Hamiltonian-paths-He}). 

\begin{figure}
  \centering
  \begin{subfigure}[b]{0.3\textwidth}
    \centering
    \begin{tikzpicture}
      \pic[scale=1.5] (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};

      \draw[hpEdge] 
        (uv-u1) -- (uv-u3) -- (uv-v2) -- (uv-u5) -- (uv-v6) 
          -- (uv-u4) -- (uv-v5) -- (uv-u6) -- (uv-v4) -- (uv-v1) 
          -- (uv-v3) -- (uv-u2);

      \node[hpEndpoint] at (uv-u1) {};
      \node[hpEndpoint] at (uv-u2) {};
    \end{tikzpicture}
    \caption{}\label{fig:Hamiltonian-paths-He1}         
  \end{subfigure}
  \hfill
  \begin{subfigure}[b]{0.3\textwidth}
    \centering
    \begin{tikzpicture}
      \pic[scale=1.5] (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};

      \draw[hpEdge] 
        (uv-u1) -- (uv-u3) -- (uv-v2) -- (uv-u5) -- (uv-v6) 
          -- (uv-u4) -- (uv-v5) -- (uv-u2) -- (uv-v3) -- (uv-v1) 
          -- (uv-v4) -- (uv-u6);

      \node[hpEndpoint] at (uv-u1) {};
      \node[hpEndpoint] at (uv-u6) {};
    \end{tikzpicture}
    \caption{}\label{fig:Hamiltonian-paths-He2}
  \end{subfigure}
  \hfill
  \begin{subfigure}[b]{0.3\textwidth}
  \centering
    \begin{tikzpicture}
      \pic[scale=1.5] (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};

      \draw[hpEdge] 
        (uv-v6) -- (uv-u5)-- (uv-v2) -- (uv-u3) -- (uv-u1) 
          -- (uv-u4) -- (uv-v5) -- (uv-u2) -- (uv-v3) -- (uv-v1) 
          -- (uv-v4) -- (uv-u6);

      \node[hpEndpoint] at (uv-v6) {};
      \node[hpEndpoint] at (uv-u6) {};
    \end{tikzpicture}
    \caption{}\label{fig:Hamiltonian-paths-He3}
  \end{subfigure}
  \caption{This figure shows the different types Hamiltonian paths for the subgraphs \<open>H\<^sub>e\<close> for an 
    edge \<open>e:={u,v}\<close>.}\label{fig:Hamiltonian-paths-He}
\end{figure}

Next, I describe the edge weights of the graph \<open>H\<close>. The graph \<open>H\<close> is complete, thus there is an edge 
between every pair of vertices of \<open>H\<close>. Every vertex of \<open>H\<close> belongs to a subgraph \<open>H\<^sub>e\<close>. We distinguish 
between 3 types of edges.
\begin{enumerate}[label=(\roman*)]
  \item An edge that connects two vertices which both belong to the same subgraph \<open>H\<^sub>e\<close> has the weight 
    equal to the distance of the vertices in the subgraph \<open>H\<^sub>e\<close>.
  \item An edge that connects two corner vertices of different subgraphs \<open>H\<^sub>e\<close> and \<open>H\<^sub>f\<close> (\<open>e \<noteq> f\<close>) but 
    both vertices correspond to the same endpoint has the weight of 4.
  \item All remaining edges have the weight of 5.
\end{enumerate} 
The proof that the edge weights satisfy the traingle-inequality requires a long and tedious case 
distinction and thus is omitted.

Next, I describe the definition of the function \<open>g\<close>.
The function \<open>g\<close> maps a Hamiltonian cycle \<open>T\<close> in \<open>H\<close> to a vertex cover \<open>X\<close> of \<open>G\<close>. 
By the construction of \<open>H\<close>, the Hamiltonian cycle \<open>T\<close> may be 
composed of only Hamiltonian paths for the subgraphs \<open>H\<^sub>e\<close>. In this case, for each edge \<open>e\<close> of \<open>G\<close> 
the covering vertex of \<open>e\<close> is identified by looking at the Hamiltonian path for the subgraph \<open>H\<^sub>e\<close> 
that is contained in \<open>T\<close>. The Hamiltonian path of the subgraph \<open>H\<^sub>e\<close> can only 
correspond to one endpoint of the edge \<open>e\<close>. This endpoint is selected as the covering vertex for 
the edge \<open>e\<close>. If the Hamiltonian cycle \<open>T\<close> does not contain a Hamiltonian path for every subgraph \<open>H\<^sub>e\<close>, 
a Hamiltonian cycle \<open>T'\<close> for \<open>H\<close> is constructed. The Hamiltonian cycle \<open>T'\<close> contains a Hamiltonian 
path for every subgraph \<open>H\<^sub>e\<close> and the total cost of \<open>T'\<close> is at most the total cost of \<open>T\<close>. The 
Hamiltonian cycle \<open>T'\<close> is constructed by carefully replacing parts of \<open>T\<close> with a Hamiltonian path 
for a subgraph \<open>H\<^sub>e\<close>.\<close>

subsection \<open>Formalizing the L-Reduction\<close>

text \<open>The functions \<open>f\<close> and \<open>g\<close> are required to be computable in polynomial time. The locale 
@{locale ugraph_adj_map} provides an abstract adjacency map which serves as a graph representation 
that allows for the implementation of executable function on graphs. The locale @{locale ugraph_adj_map} 
can be instantiated with an implementation for sets (locale @{locale Set2}) and maps (locale @{locale Map}) 
to obtain executable functions on graphs. The necessary graph-related definitions are redefined for 
the adjencecy-map representation of graphs (see theory @{file "./graphs/GraphAdjMap_Specs.thy"}). 
The definitions for the adjencecy-map representation of graphs are denoted by the postfix \<open>-Adj\<close>.\<close>
(*<*)
end
context ugraph_adj_map
begin
(*>*)
text \<open>The set of undirected edges of a graph which is represented by an adjacency map is returned 
by the function @{const[names_short] uedges}. A linear order on the vertices is used to identify 
different instances of the same undirected edge.\<close>
(*<*)
end
context VCP4_To_mTSP
begin
(*>*)
text \<open>The L-reduction itself is formalized in the locale @{locale VCP4_To_mTSP} that depends on two 
executable adjacency-maps (locale @{locale ugraph_adj_map}), one for each of the graphs \<open>G\<close> and \<open>H\<close> 
which are denoted by \<open>g1\<close> and \<open>g2\<close>. The locale @{locale VCP4_To_mTSP} also assumes functions that 
provide \texttt{fold}-operations for the graphs. The reduction functions \<open>f\<close> and \<open>g\<close> are defined in 
the locale @{locale VCP4_To_mTSP} using the assumed \texttt{fold}-operations and some auxiliary functions. 
The theory @{file "reductions/VertexCover4ToMetricTravelingSalesman_AdjList.thy"} instantiates the 
locale @{locale VCP4_To_mTSP} with an implementation of an adjacency list to obtain executable functions.

The vertices of the subgraphs \<open>H\<^sub>e\<close> are represented by a tuple \<open>(e,u,i)\<close> where \<open>u\<close> is an endpoint of 
the edge \<open>e\<close> and \<open>i \<in> {1..6}\<close> is an index. The Figure~\ref{fig:He-formalization} shows the 
formalization of a subgraph \<open>H\<^sub>e\<close>. The vertices of the subgraph \<open>H\<^sub>e\<close> have to be named such that the 
subgraph is symmetric (\<open>H\<^sub>{\<^sub>u\<^sub>,\<^sub>v\<^sub>}=H\<^sub>{\<^sub>v\<^sub>,\<^sub>u\<^sub>}\<close>). 

\begin{figure}
  \centering
  \begin{tikzpicture}
    \pic[scale=2.5] (uv) at (0,0) {He-labeled={e}{u}{v}};
  \end{tikzpicture}
  \caption{Formalization of the subgraph \<open>H\<^sub>e\<close> for an edge \<open>e:={u,v}\<close>.}\label{fig:He-formalization}
\end{figure}

The function \<open>f\<close> uses the auxiliary function @{const[names_short] complete_graph} which constructs 
the complete graph for a given set of vertices. The function @{const[names_short] vertices_of_H} 
computes all the vertices of the graph \<open>H\<close>.

@{thm[display,names_short] f.simps}

The edge weights are formalized by the function \<open>c\<close>, which maps two vertices to an integer. 
The definition of the function \<open>c\<close> uses a couple of auxiliary functions to distinguish different cases of edges. 
To simplify things, the case for two vertices that are neighbours in subgraph \<open>H\<^sub>e\<close> (weight 1) is handled separately. 
The function @{const is_edge_in_He} checks if there is a subgraph \<open>H\<^sub>e\<close> in \<open>H\<close> where the two 
given vertices are connected by an edge. The function @{const are_vertices_in_He} checks if there is 
a subgraph \<open>H\<^sub>e\<close> in \<open>H\<close> that contains both given vertices. The function @{const min_dist_in_He} computes 
the distance between two vertices in a subgraph \<open>H\<^sub>e\<close>. The function \<open>rep1\<close> is required to compare the undirected edges.

@{thm[display,mode=IfThen] c.simps}

The function \<open>g\<close> depends on two functions @{const shorten_tour} and @{const vc_of_tour}. The 
function @{const shorten_tour} modifies a Hamiltonian cycle s.t. the resulting tour has less total weight 
and the cycle contains a Hamiltonian path for every subgraph \<open>H\<^sub>e\<close>. The function @{const vc_of_tour} 
computes a vertex cover for \<open>G\<close> given a Hamiltonian cycle that contains a Hamiltonian path for every 
subgraph \<open>H\<^sub>e\<close>.

@{thm[display] g.simps}

Given a tour \<open>T\<close> of \<open>H\<close>, the function @{const shorten_tour} iteratively (for each edge \<open>e\<close> of \<open>G\<close>) 
removes all vertices of the subgraph \<open>H\<^sub>e\<close> from the tour \<open>T\<close> and appends a Hamiltonian path for the 
subgraph \<open>H\<^sub>e\<close>. This replacement is done regardless of whether the tour \<open>T\<close> already contains a 
Hamiltonian path for the subgraph \<open>H\<^sub>e\<close>. This simplifies definitions and proofs by avoiding extra case 
distinctions. The appended Hamiltonian path for the subgraph \<open>H\<^sub>e\<close> is carefully chosen such that the 
resulting tour has less total weight. The function @{const shorten_tour} formalizes property (b) from 
the L-reduction proof in @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"}.

Contrary, the function \<open>g\<close> described by @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} only replaces parts 
of the tour \<open>T\<close> with a Hamiltonian path for a subgraph \<open>H\<^sub>e\<close> when the tour \<open>T\<close> does not already contain 
a Hamiltonian path for the subgraph \<open>H\<^sub>e\<close>. Thus, the resulting tour may contain Hamiltonian paths for 
the subgraphs \<open>H\<^sub>e\<close> that do not start or end at corner vertices of the subgraph \<open>H\<^sub>e\<close>. Therefore, the 
construction of the vertex cover for \<open>G\<close> from the modified tour \<open>T'\<close> requires an extra case 
distinction to handle the different types of Hamiltonian paths for the subgraphs \<open>H\<^sub>e\<close> (see Figure~\ref{fig:Hamiltonian-paths-He}). 
@{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} does not make the required case distinction in the 
definition of the function \<open>g\<close>. The types \ref{fig:Hamiltonian-paths-He2} and \ref{fig:Hamiltonian-paths-He3} 
of Hamiltonian paths for the subgraph \<open>H\<^sub>e\<close> from Figure~\ref{fig:Hamiltonian-paths-He} are not covered.
On the other hand, the function @{const shorten_tour} explicitly handles these cases.\<close>

subsection \<open>Proofs for the L-Reduction\<close>

text \<open>The locale @{locale VCP4_To_mTSP} contains the proofs for the feasibility of the reduction 
functions and the linear inequalities required for a L-reduction.\<close>
(*<*)
end
locale fixed_adj_map_G = VCP4_To_mTSP +
  fixes G OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4 X
  assumes G_assms: "g1.ugraph_adj_map_invar G" "card (g1.uedges G) > 1"
  and opt_mtsp: "g2.is_tsp_Adj (f G) (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4" "set_invar1 OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4" "card1 OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4 > 1"
  and max_degree: "\<And>v. v \<in> g1.vertices G \<Longrightarrow> g1.degree_Adj G v \<le> enat 4"
  and invar_X: "card1 X > 1" "set_invar1 X"
begin
lemma f_is_complete_display: "g2.is_complete_Adj (f G)"
  using G_assms(1) by (rule f_is_complete)

lemma g_is_vc_display: "g2.is_hc_Adj (f G) T \<Longrightarrow> g1.is_vc_Adj G (g G T)"
  using G_assms by (rule g_is_vc)

(*>*)
text \<open>The function \<open>f\<close> constructs a complete graph.

@{thm[display] f_is_complete_display}
                             
Given Hamiltonian cycle \<open>T\<close>, the function \<open>g\<close> selects, for each edge \<open>e\<close> of \<open>G\<close>, an endpoint
to be included in the result. Thus, the function \<open>g\<close> computes a vertex cover for \<open>G\<close> given a 
Hamiltonian cycle for \<open>H\<close>.

@{thm[display] g_is_vc_display}\<close>
(*<*)
end
context fixed_adj_map_G
begin

lemma hp_of_vc_display:
  shows "g1.is_vc_Adj G X \<Longrightarrow> 
    \<exists>T. g2.is_hc_Adj (f G) T \<and> cost_of_path (c G) T \<le> 15 * int (card (g1.uedges G)) + card1 X"
  using invar_X hp_of_vc[OF G_assms] by blast

(*>*)
text \<open>Next, I describe the proofs for the linear inequalities that are required for the L-reduction. 
The following two lemmas formalize two important properties that are needed for the proofs of the 
linear inequalities.

We prove an upper-bound for the total cost of the optimal Hamiltonian cycle for the graph \<open>H\<close>. This 
lemma corresponds to the property (a) that is used by the L-reduction proof in @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"}. 
Let \<open>OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P\<close> be an optimal Hamiltonian cycle for \<open>H\<close> and let \<open>OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4\<close> be an optimal vertex cover for \<open>G\<close>.

@{thm[display] (concl) cost_of_opt_mTSP[where OPT\<^sub>V\<^sub>C="OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4"]}

Intuitively, using the optimal vertex cover \<open>OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4\<close> for \<open>G\<close>, a Hamiltonian cycle \<open>T\<close> for \<open>H\<close> is constructed. 
The total cost of \<open>T\<close> is at least the total cost of the optimal Hamiltonian cycle \<open>OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P\<close>. The 
Hamiltonian cycle \<open>T\<close> traverses each subgraph \<open>H\<^sub>e\<close> with the Hamiltonian path that starts and ends at 
the corner vertices that correspond to the covering vertex of \<open>e\<close> in the vertex cover \<open>OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4\<close>. Each 
Hamiltonian path for a subgraph \<open>H\<^sub>e\<close> has a total cost of 11. We now need to add @{term "card (g1.uedges G)"} many
edges to connect the start- and end-vertices of the Hamiltonian paths to form a Hamiltonian cycle for \<open>H\<close>. 
We pick as many edges with weight 4 ("cheaper" edges) as possible. For the remaining connections we 
use "expensive" edges with weight 5. It turns out we can select at most @{term "(card (g1.uedges G) - card1 OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4)"} 
many edges of weight 4. Thus, the total weight of the constructed Hamiltonian cycle \<open>T\<close> is at most 
@{term "11 * card (g1.uedges G) + 4 * (card (g1.uedges G) - card1 OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4) + 5 * card1 OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4 = 15 * card (g1.uedges G) + card1 OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4"}.
Essentially, the number of "expensive" edges in the Hamiltonian cycle \<open>T\<close> for \<open>H\<close> corresponds to the 
cardinality of the vertex cover for \<open>G\<close>. The generalization of this construction for an arbitrary 
vertex cover is formalized by the following lemma. 

@{thm[display] hp_of_vc_display}\<close>
(*<*)
end
context fixed_adj_map_G
begin

lemma card_g_leq_k_display: 
  "g2.is_hc_Adj (f G) T \<Longrightarrow> \<exists>k. card1 (g G T) \<le> k \<and> 15 * int (card (g1.uedges G)) + k \<le> cost_of_path (c G) T"
  using card_g_leq_k[OF G_assms opt_vc] by blast
(*>*)
text \<open>Another property that is required for the proof of the linear inequalities of the L-reduction 
is an upper-bound for the cardinality of the vertex cover that is constructed by the function \<open>g\<close>.
This lemma corresponds to the property (c) that is used by the L-reduction proof in @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"}.

@{thm[display] card_g_leq_k_display}

The cardinality of the vertex cover that is constructed by the function \<open>g\<close> can be at most 
the number "expensive" edges in a Hamiltonian cycle \<open>T\<close> of \<open>H\<close>. This follows from the fact that any 
two edges \<open>e\<close> and \<open>f\<close> in \<open>G\<close> (\<open>e \<noteq> f\<close>), where the subgraphs \<open>H\<^sub>e\<close> and \<open>H\<^sub>f\<close> are connected by a "cheap" 
edge in \<open>T\<close>, are covered by the same endpoint. Thus, there can only be distinct covering vertices if 
two subgraphs are connected by an "expensive" edge.\<close>
(*<*)
lemma l_reduction1_display: "cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * card1 OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4"
  using G_assms opt_vc(3) max_degree opt_vc(1,2) opt_mtsp by (rule l_reduction1)

lemma l_reduction2_display:
  "g2.is_hc_Adj (f G) T \<Longrightarrow> 
    \<bar> card1 (g G T) - card1 OPT\<^sub>V\<^sub>C\<^sub>P\<^sub>4 \<bar> \<le> 1 * \<bar> cost_of_path (c G) T - cost_of_path (c G) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>" 
  using G_assms opt_vc opt_mtsp by (rule l_reduction2)
(*>*)
text \<open>With the lemmas proved above, we prove the linear inequalities required for the L-reduction. 
The first linear inequality is formalized by the following lemma.

@{thm[display] l_reduction1_display}

By assumption, the degree of every vertex in \<open>G\<close> is at most 4. Thus, the number of edges of \<open>G\<close> is 
bounded by 4-times the cardinality of any vertex cover of \<open>G\<close>. The first inequality is a consequence 
of the upper-bound on the total cost of the optimal Hamiltonian cycle \<open>OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P\<close> for \<open>H\<close> and the 
upper-bound of the number of edges of \<open>G\<close>.

The following lemma formalizes the second linear inequality for the L-reduction.

@{thm[display] l_reduction2_display}

The second inequality follows from the upper-bound for the cardinality of the vertex cover that is 
constructed by the function \<open>g\<close> and the upper-bound for the total cost of the optimal Hamiltonian 
cycle \<open>OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P\<close>.\<close>
(*<*)
end
context VCP4_To_mTSP
begin
(*>*)

subsection \<open>Flaws and Unfinished Business\<close>

text \<open>In this section, I describe two flaws in the L-reduction proof by @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} 
that I discovered during the formalization. I also go over the parts of my formalization that are not 
finished.

The L-reduction proof that is presented in @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} is incomplete. 
During the formalization of the L-reduction I have discovered two flaws in the proof by @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"}.
\begin{enumerate}[label=(\roman*)]
  \item {The proof by @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} fails if the optimal vertex cover 
    of \<open>G\<close> has a cardinality of 1. In this case, some of the auxiliary lemmas used in @{cite "korte_vygen_2018"} 
    do not hold. In particular the upper-bound for optimal Hamiltonian cycle for \<open>H\<close> does not hold. 
    The construction for the L-reduction still works in this case, but the proofs for this case need 
    to be considered separately. I circumvent this problem by explicitly excluding this case through 
    an additional assumption. Formalizing the proof for this case should be straightforward and just 
    a matter of adapting the necessary lemmas.}
  \item {The proof for @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} does not cover every case, when 
    identifying the covering vertices for \<open>G\<close> from a Hamiltonian cycle \<open>T\<close> for \<open>H\<close>. There are 
    different types Hamiltonian paths for the subgraphs \<open>H\<^sub>e\<close> that do not start or end at corner 
    vertices of the subgraph \<open>H\<^sub>e\<close>. @{cite "korte_vygen_2018"} only describe how to identify a covering 
    vertex if the Hamiltonian path starts and ends at a corner vertex of the subgraph \<open>H\<^sub>e\<close>. For some 
    Hamiltonian paths that do not start or end at corners of the subgraph \<open>H\<^sub>e\<close>, it is not 
    immediately clear which covering vertex to choose. I have solved this issue by extending the 
    definition of the function \<open>g\<close>. The definition of the function \<open>g\<close> described in @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} 
    only replaces parts of the tour \<open>T\<close> with a Hamiltonian path for a subgraph \<open>H\<^sub>e\<close> when the tour \<open>T\<close> 
    does not already contain a Hamiltonian path for the subgraph \<open>H\<^sub>e\<close>. Thus, the resulting tour may 
    contain Hamiltonian paths for the subgraphs \<open>H\<^sub>e\<close> that do not start or end at corner vertices of 
    the subgraph \<open>H\<^sub>e\<close>. Therefore, the construction of the vertex cover for \<open>G\<close> from the modified tour 
    \<open>T'\<close> would require an extra case distinction to handle the different types of Hamiltonian paths 
    for the subgraphs \<open>H\<^sub>e\<close> (see Figure~\ref{fig:Hamiltonian-paths-He}). @{cite"korte_vygen_2018"} 
    does not make the required case distinction in the definition of the function \<open>g\<close>. The types of 
    Hamiltonian paths for the subgraph \<open>H\<^sub>e\<close> depicted in the Figures~\ref{fig:Hamiltonian-paths-He2} 
    and \ref{fig:Hamiltonian-paths-He3} are not covered. 
    
    @{cite"korte_vygen_2018"} cite a proof by @{cite "papadimitriou_yannakakis_1993"}. The proof by 
    @{cite "papadimitriou_yannakakis_1993"} use a similar construction to prove the \textsc{MaxSNP}-harness 
    of a restricted version of the \textsc{Metric TSP}, where the values of the edge weights are 
    restricted to only 1 or 2. Because of the restricted edge weights the proof by @{cite "papadimitriou_yannakakis_1993"}
    does not have this issue.

    On the other hand, I defined the function \<open>g\<close> using the function @{const shorten_tour} which 
    explicitly handles these cases.}
\end{enumerate}

There are two aspects that make my formalization of the L-reduction incomplete. Firstly, I have not 
finished the proof that the subgraph \<open>H\<^sub>e\<close> only admits three types of Hamiltonian paths 
(see Figure~\ref{fig:Hamiltonian-paths-He}). The lemma is stated in the theory @{file "reductions/VertexCover4ToMetricTravelingSalesman_Specs.thy"}.
The theory @{file "./reductions/FindHamiltonianPath.thy"} contains an instantiation this lemma for 
with an executable graph representation. By exhaustive search, the instantiated lemma is proven. This 
result needs to be transferred to the reduction proof. At the moment I am not sure what the best and 
way to do this is. I have also attempted another way to prove this. I tried, by coming up with a 
clever naming of the vertices of the subgraph \<open>H\<^sub>e\<close> to prove that there is no Hamiltonian path that 
start and ends at vertices on opposing sides of the subgraph. Unfortunately, I did not have success 
with this approch.

Secondly, I have not formally proven the polynomial running times of the functions \<open>f\<close> and \<open>g\<close>. To 
formally reason about running times a formal computational model is required. The imperative language 
\texttt{IMP-} provides such a computational model. \texttt{IMP-} was developed as part of a formalization 
of polynomial time reduction @{cite "wimmer_2021"}. A possible approach to prove the polynomial 
running times of the functions \<open>f\<close> and \<open>g\<close>, is to refine instantiations of their definitions (with 
implementations for the locales @{locale Map} and @{locale Set2}) to \texttt{IMP-}. With the computational 
model provided by \texttt{IMP-}, we can prove the running times of the refined reduction functions.\<close>
(*<*)
end
(*>*)

(* ----- *)
 
section \<open>Future Work and Conclusion\<close>

text \<open>In this work, I describe my formalization of parts of the section 21.1, 
\textit{Approximation Algorithms for the TSP} from @{cite "korte_vygen_2018"}.
\begin{itemize}
  \item I have formalized and formally verified two approximation algorithms for \textsc{Metric TSP}: the 
    \textsc{DoubleTree} and the \textsc{Christofides-Serdyukov} algorithm.
  \item I have formalized an L-reduction from \textsc{VCP4} to \textsc{Metric TSP}, which proves the 
    \textsc{MaxSNP}-hardness of \textsc{Metric TSP}.
\end{itemize}

I have formalized a significant amount of graph-related concepts.

I present an approach to formalize of the L-reductions in Isabelle/HOL. 

With the formalization and formal verification of the \textsc{DoubleTree} and the 
\textsc{Christofides-Serdyukov} algorithm I have continued the work of @{cite "essmann_et_al_2020"} 
in formalizing approximation algorithms in Isabelle/HOL.

Future work includes proving the existence of the necessary algorithms for the \textsc{DoubleTree} 
and \textsc{Christofides-Serdyukov} algorithm. Algorithms for the following problems is need to be 
formalized: MST, minimum perfect matching, and Eulerian tour. There is already 
an existing formalization of Prim's algorithm @{cite "lammich_nipkow_2019"}, an algorithm that 
computes a MST. In the theory @{file "./adaptors/BergePrimAdaptor.thy"}, I have started (but not 
finished) to implement an adaptor to formalization by @{cite "lammich_nipkow_2019"}. Suitable 
algorithms for the other problems are e.g. Edmonds' Blossom algorithm @{cite "edmonds_1965"} for 
minimum perfect matching and Euler's algorithm @{cite "korte_vygen_2018"} for Eulerian tour.

Furthermore, the Eulerian graphs that are constructed for the \textsc{DoubleTree} and 
\textsc{Christofides-Serdyukov} algorithm might be multigraphs. Therefore, the formalization of 
multigraphs is required. In the theory @{file "./graphs/MultiGraph.thy"}, I have started (but not 
finished) to formalize an encoding of multigraphs with simple graphs.

For the L-reduction it is required to prove the polynomial running time of reduction functions \<open>f\<close> 
and \<open>g\<close>. Moreover, the proof that the subgraph \<open>H\<^sub>e\<close> only admits certain Hamiltonian paths has to be 
finished.
\<close>

(*<*)
end
(*>*)