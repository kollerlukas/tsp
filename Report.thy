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

text \<open>The \textsc{Traveling-Salesman Problem} (\textsc{TSP}) is a well known 
optimization problem. The \textsc{TSP} describes the problem of finding a tour with minimum total 
weight in a given weighted graph s.t. every vertex of the graph is visited exactly once. The 
\textsc{TSP} has many applications in different areas, e.g. planning and scheduling @{cite "brumitt_stentz_1996"}, 
logistics @{cite "ratliff_rosenthal_1983"}, designing printed circuit boards @{cite "groetschel_et_al_1991"}, etc..

The \textsc{TSP} is \textsc{NP}-hard @{cite "korte_vygen_2018"}. This means, that unless 
$\textsc{P}=\textsc{NP}$, the \textsc{TSP} cannot be solved in polynomial time. When 
dealing with optimization problems, a typical strategy is to approximate the optimal solution with 
an approximation algorithm. An approximation algorithm is a polynomial time algorithm that returns a 
bounded approximate solution. An approximation algorithm essentially trades the optimality of the 
returned solution for polynomial running time. Ideally, the distance between the approximate 
solution and the optimal solution can be bounded by a constant factor.
Unfortunately, there is no constant-factor approximation algorithm for the \textsc{TSP} @{cite "korte_vygen_2018"}. 

The \textsc{Metric TSP} is a simplifies the \textsc{TSP} by making the following two assumptions:
\begin{enumerate*}[label=(\roman*)]
  \item the given graph is complete and 
  \item the edge-weights satisfy the triangle-inequality.
\end{enumerate*}
The \textsc{Metric TSP} is still \textsc{NP}-hard @{cite "korte_vygen_2018"}.

This report describes the formalization of parts of the section 21.1, \textit{Approximation Algorithms for the TSP} from
@{cite "korte_vygen_2018"}.
\begin{enumerate}
  \item I have formalized and verified two approximation algorithms, \textsc{DoubleTree} and 
    \textsc{Christofides-Serdyukov}, for \textsc{Metric TSP}. The \textsc{Christofides-Serdyukov} 
    @{cite "christofides_1976" and "serdyukov_1978"} algorithm is the best known approximation 
    algorithm for the \textsc{Metric TSP} @{cite "korte_vygen_2018"}.
  \item I have formalized a L-reduction from the \textsc{Minimum Vertex Cover Problem} with maximum 
    degree of 4 to the \textsc{Metric TSP}, which proves the \textsc{MaxSNP}-hardness of the 
    \textsc{Metric TSP}.
\end{enumerate}

The \textsc{MaxSNP}-hardness of a problem proves the non-existence of an approximation scheme @{cite "papadimitriou_yannakakis_1991"}.
An approximation scheme is an approximation algorithm that takes an additional parameter $\epsilon >0$ based on which the approximate solution is bounded.
\textsc{MaxSNP} is a complexity class that contains graph-theoretical optimization problems. For any 
problem in \textsc{MaxSNP} there is a constant-factor approximation algorithm @{cite "papadimitriou_yannakakis_1991"}.
A linear reduction (L-reduction) is special type of reduction for optimization problems @{cite "papadimitriou_yannakakis_1991"}. 
A problem is called \textsc{MaxSNP}-hard if every problem in \textsc{MaxSNP} L-reduces to it.
\<close>

(* ----- *)

section \<open>Related Work\<close>

text \<open>

@{cite essmann_et_al_2020} have formalized different approximation algorithms in Isabelle/HOL.

{\color{red} Reductions in Isabelle?}

{\color{red} Refinement to IMP-.}\<close>

section \<open>Fundamentals and Definitions\<close>

text \<open>I build on the exiting formalization of Berge's theorem by {\color{red} Mohammad 
Abdulaziz (citation?)}. An undirected graph is formalized as a finite set of edges. An edge is 
represented by a doubleton set. 

@{abbrev[display] graph_invar}

The locale @{locale graph_abs} fixes an instance \<open>E\<close> of a graph that satisfies the invariant 
@{const graph_invar}. The graph formalization by {\color{red} Mohammad Abdulaziz (citation?)} 
provides definitions for the following concepts.
\begin{itemize}
  \item Vertices of a graph: @{const Vs}
  \item Paths: @{const path}, @{const walk_betw}, and @{const edges_of_path}
  \item Degree of vertices: @{const degree}
  \item Connected components: @{const connected_component}
  \item Matchings: @{const matching}
\end{itemize}
 
The approximation algorithms and the L-reduction use many graph-related concepts that are not 
defined in the formalization of Berge's theorem by {\color{red} Mohammad Abdulaziz (citation?)}, 
e.g. weighted edges, minimum spanning-tree, Hamiltonian cycle, etc..

This section describes the formalization of graph-related concepts that are the necessary for 
the formalization of the \textsc{DoubleTree} and \textsc{Christofides-Serdyukov} approximation 
algorithms as well as the L-reduction. Most of the definitions are straightforward, thus only 
important formalization choices are highlighted.

All of the graph-related definitions are defined in theories which are located in 
the @{path "./graphs"}- or @{path "./problems"}-directory.

Many simple results and lemmas are formalized in the theory @{file "./misc/Misc.thy"} which is located in 
the directory @{path "./misc"}.\<close>

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

(* ----- *)

section \<open>Approximating the \textsc{Metric TSP}\<close>

text \<open>This section describes the formalization of the \textsc{DoubleTree} and the 
\textsc{Christofides-Serdyukov} approximation algorithms for \textsc{Metric TSP}. Both 
algorithms are quite similar 
and depend on the following proposition (Lemma 21.3, @{cite "korte_vygen_2018"}):

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

text \<open>With the proposition (Lemma 21.3 @{cite "korte_vygen_2018"}) the task of approximating 
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
algorithm for the \textsc{Metric TSP}.\<close>

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

For the defined \textsc{DoubleTree} algorithm we prove two properties:
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
context VC4_To_mTSP
begin
(*>*)

text \<open>This section describes the formalization of an L-Reduction from the 
\textsc{Minimum Vertex Cover Problem}, with maximum degree of 4 (\textsc{VCP4}), to the \textsc{Metric TSP}. 
The formalization is based of an L-reduction proof that is presented in @{cite "korte_vygen_2018"} 
(Theorem 21.1).

The \textsc{Minimum Vertex Cover Problem} describes the optimization problem of finding
a vertex-cover with minimum cardinality for a given graph. A vertex-cover is subset of vertices 
that contains at least one end-point of every edge. The \textsc{VCP4} is the restriction of the 
\textsc{Minimum Vertex Cover Problem} to input graphs where every vertex has a degree of at most 4.
The bounded degree is only needed to prove the linear inequalities required by the L-reduction.

We now define what an L-reduction is.
Let \<open>A\<close> and \<open>B\<close> be optimization problems with cost functions \<open>c\<^sub>A\<close> and \<open>c\<^sub>B\<close>. The cost of the optimal
solution for an instance of an optimization problem is denoted by \<open>OPT(\<cdot>)\<close>.
An L-reduction (linear reduction) consists of a pair of functions \<open>f\<close> and \<open>g\<close> and two constants
\<open>\<alpha>,\<beta> > 0\<close> s.t for every instance \<open>x\<^sub>A\<close> of \<open>A\<close>
\begin{enumerate}[label=(\roman*)]
  \item \<open>f x\<^sub>A\<close> is an instance of \<open>B\<close> and \<open>OPT(f x\<^sub>A) \<le> \<alpha>OPT(x\<^sub>A)\<close>, and 
  \item for any feasible solution \<open>y\<^sub>B\<close> of \<open>f x\<^sub>A\<close>, \<open>g x\<^sub>A y\<^sub>B\<close> is a feasible solution of \<open>x\<^sub>A\<close> s.t.
    \<open>|(c\<^sub>A x\<^sub>A (g x\<^sub>A y\<^sub>B)) - OPT(x\<^sub>A)| \<le> | (c\<^sub>A (f x\<^sub>A) y\<^sub>B) - OPT(f x\<^sub>A)|\<close>.
\end{enumerate}

The second linear inequality essentially ensures the following: given an optimal solution for \<open>f x\<^sub>A\<close> 
the function \<open>g\<close> has to construct an optimal solution for \<open>x\<^sub>A\<close>. 

We L-reduce the \textsc{VCP4} to the \textsc{Metric TSP} by defining the functions \<open>f\<close> and \<open>g\<close> and 
proving their required properties.
The function \<open>f\<close> maps an instance of the \textsc{VCP4} to an instance of the \textsc{Metric TSP}. 
An instance of the \textsc{VCP4} consists of a  graph where the degree of every vertex is at most 4.
To construct an instance of the 
\textsc{Metric TSP} we need to construct a complete graph with edge weights s.t. the edge weights 
satisfy the triangle-inequality.

We describe the function \<open>f\<close> with the following construction.
Let \<open>G\<close> be an instance of the \textsc{VCP4}, and we denote the constructed graph with \<open>H:=f G\<close>.
For each edge \<open>e\<close> of \<open>G\<close> we add a subgraph \<open>H\<^sub>e\<close> to \<open>H\<close> (see figure~\ref{fig:He}). The graph \<open>H\<close> 
is the complete graph over all the vertices of the subgraphs \<open>H\<^sub>e\<close> (one for every edge \<open>e\<close> of the graph \<open>G\<close>). 
The subgraph \<open>H\<^sub>e\<close> consists of 12 vertices that are arranged in a 4-by-3 lattice structure. 
Each corner vertex of each subgraph \<open>H\<^sub>e\<close> corresponds to an endpoint of the edge \<open>e\<close>.

\begin{figure}
  \centering
  \begin{tikzpicture}
    \pic[scale=2.0] (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};
  \end{tikzpicture}
  \caption{Subgraph \<open>H\<^sub>e\<close> for an edge \<open>e:={u,v}\<close>. For each corner vertex the corresponding endpoint is labeled.}\label{fig:He}
\end{figure}

Each subgraph \<open>H\<^sub>e\<close> has the special property that there is no Hamiltonian path 
for \<open>H\<^sub>e\<close> that starts and ends at corner vertices of \<open>H\<^sub>e\<close> that correspond to different 
endpoints of the edge \<open>e\<close>. Therefore, the start- and end-vertex of a Hamiltonian path for a 
subgraph \<open>H\<^sub>e\<close> can only correspond to the same endpoint of the edge \<open>e\<close>. This property is used to 
encode a vertex cover of \<open>G\<close> in a Hamiltonian cycle of \<open>H\<close>.

The subgraph \<open>H\<^sub>e\<close> admits 3 types of Hamiltonian paths (see figure~\ref{fig:Hamiltonian-paths-He}).

\begin{figure}
  \centering
  \begin{minipage}{.3\textwidth}
    \centering
    \begin{tikzpicture}[transform shape,scale=1.0]
      \pic (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};

      \draw[hpEdge] 
        (uv-u1) -- (uv-u3) -- (uv-v2) -- (uv-u5) -- (uv-v6) 
          -- (uv-u4) -- (uv-v5) -- (uv-u6) -- (uv-v4) -- (uv-v1) 
          -- (uv-v3) -- (uv-u2);

      \node[hpEndpoint] at (uv-u1) {};
      \node[hpEndpoint] at (uv-u2) {};
    \end{tikzpicture}
    \caption{}\label{fig:Hamiltonian-paths-He1}
  \end{minipage}%
  \begin{minipage}{.3\textwidth}
    \centering
    \begin{tikzpicture}[transform shape,scale=1.0]
      \pic (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};

      \draw[hpEdge] 
        (uv-u1) -- (uv-u3) -- (uv-v2) -- (uv-u5) -- (uv-v6) 
          -- (uv-u4) -- (uv-v5) -- (uv-u2) -- (uv-v3) -- (uv-v1) 
          -- (uv-v4) -- (uv-u6);

      \node[hpEndpoint] at (uv-u1) {};
      \node[hpEndpoint] at (uv-u6) {};
    \end{tikzpicture}
    \caption{}\label{fig:Hamiltonian-paths-He2}
  \end{minipage}%
  \begin{minipage}{.3\textwidth}
    \centering
    \begin{tikzpicture}[transform shape,scale=1.0]
      \pic (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};

      \draw[hpEdge] 
        (uv-v6) -- (uv-u5)-- (uv-v2) -- (uv-u3) -- (uv-u1) 
          -- (uv-u4) -- (uv-v5) -- (uv-u2) -- (uv-v3) -- (uv-v1) 
          -- (uv-v4) -- (uv-u6);

      \node[hpEndpoint] at (uv-v6) {};
      \node[hpEndpoint] at (uv-u6) {};
    \end{tikzpicture}
    \caption{}\label{fig:Hamiltonian-paths-He3}
  \end{minipage}
  \caption{This figure shows the different types Hamiltonian paths for the subgraphs \<open>H\<^sub>e\<close> for an 
    edge \<open>e:={u,v}\<close>.}\label{fig:Hamiltonian-paths-He}
\end{figure}

Next, we describe the edge weights of the graph \<open>H\<close>. The graph \<open>H\<close> is complete, thus we have edges 
between every pair of vertices of \<open>H\<close>. Every vertex of \<open>H\<close> belongs to a subgraph \<open>H\<^sub>e\<close>. We distinguish 
3 types of edges to describe the edge weights:
\begin{enumerate*}[label=(\roman*)]
  \item an edge that connects two vertices which both belong to the same subgraph \<open>H\<^sub>e\<close> has the weight 
    equal to the distance of the vertices in the subgraph \<open>H\<^sub>e\<close>,
  \item an edge that connects two corner vertices of different subgraphs \<open>H\<^sub>e\<close> and \<open>H\<^sub>f\<close> (\<open>e \<noteq> f\<close>) but 
    both vertices correspond to the same endpoint has the weight of 4,
  \item all remaining edges have the weight of 5.
\end{enumerate*}

The proof that the edge weights satisfy the traingle-inequality is omitted.

Next, we describe the definition of the function \<open>g\<close>.
The function \<open>g\<close> maps a Hamiltonian cycle \<open>T\<close> in \<open>H\<close> to a vertex cover \<open>X\<close> of \<open>G\<close>. 
By the construction of \<open>H\<close>, the Hamiltonian cycle \<open>T\<close> may be 
composed of only Hamiltonian paths for the subgraphs \<open>H\<^sub>e\<close>. In this case, for each edge \<open>e\<close> of \<open>G\<close> 
we identify the covering vertex of \<open>e\<close> by looking at the Hamiltonian path of the subgraph \<open>H\<^sub>e\<close> 
that is contained in \<open>T\<close>. The Hamiltonian path of the subgraph \<open>H\<^sub>e\<close> can only 
correspond to one endpoint of the edge \<open>e\<close>. This endpoint is selected as the covering vertex for 
the edge \<open>e\<close>. If the Hamiltonian cycle \<open>T\<close> does not contain a Hamiltonian path for every subgraph \<open>H\<^sub>e\<close>, 
we construct a Hamiltonian cycle \<open>T'\<close> for \<open>H\<close> s.t. \<open>T'\<close> contains a Hamiltonian path for every \<open>H\<^sub>e\<close> 
and the cost of \<open>T'\<close> is at most the cost of \<open>T\<close>. The Hamiltonian cycle \<open>T'\<close> is constructed by 
iteratively replacing parts of the Hamiltonian cycle \<open>T\<close> with a Hamiltonian path for a 
subgraph \<open>H\<^sub>e\<close>.

The functions \<open>f\<close> and \<open>g\<close> have to be computable (in polynomial time) functions. Therefore, the locale 
@{locale ugraph_adj_map} provides an abstract adjacency map, which can be instantiated to obtain 
executable functions on graphs.

The L-reduction itself is formalized in the locale @{locale VC4_To_mTSP} that depends on two 
executable adjacency-maps (@{locale ugraph_adj_map}), one for each of the graphs \<open>G\<close> and \<open>H\<close> (denoted by \<open>g1\<close> and \<open>g2\<close>). 
The locale @{locale VC4_To_mTSP} also assumes appropriate \texttt{fold}-functions for the graphs.
The necessary graph-related definitions are redefined for the adjencecy-map representation of graphs. 
The definitions for the adjencecy-map representation of graphs are denoted by the postfix \<open>-Adj\<close>.

The reduction functions \<open>f\<close> and \<open>g\<close> are defined in the locale @{locale VC4_To_mTSP} using the assumed 
\texttt{fold}-functions and some auxiliary functions. The function \<open>f\<close> uses the auxiliary function 
@{const[names_short] complete_graph} to construct the complete graph for a given set of vertices. 
The function @{const[names_short] vertices_of_H} computes all the vertices of the graph \<open>H\<close>. The 
vertices of the subgraphs \<open>H\<^sub>e\<close> are represented by a tuple \<open>(e,u,i)\<close> where \<open>u\<close> is an endpoint of the 
edge \<open>e\<close> and \<open>i \<in> {1..6}\<close> is an index. 

\begin{figure}
  \centering
  \begin{tikzpicture}
    \pic[scale=2.5] (uv) at (0,0) {He-labeled={e}{u}{v}};
  \end{tikzpicture}
  \caption{Formalization of the subgraph \<open>H\<^sub>e\<close> for an edge \<open>e:={u,v}\<close>.}\label{fig:He}
\end{figure}

The naming of the vertices of the subgraph \<open>H\<^sub>e\<close> has to be symmetric s.t. \<open>H\<^sub>{\<^sub>u\<^sub>,\<^sub>v\<^sub>}=H\<^sub>{\<^sub>v\<^sub>,\<^sub>u\<^sub>}\<close>. I attempted to encode more information with the naming, but I failed.

@{thm[display,names_short] vertices_of_H.simps}

@{thm[display,names_short] f.simps}

The edge weights are formalized by the function \<open>c\<close>, which maps two vertices to an integer. 
The definition of the function \<open>c\<close> uses a couple of auxiliary functions to identify the different cases. 
To simplify things, the case for two vertices that are neighbours in subgraph \<open>H\<^sub>e\<close> (weight 1). 
The function @{const is_edge_in_He} checks if there is a subgraph \<open>H\<^sub>e\<close> in \<open>H\<close> where the two 
given vertices are connected by an edge. The function @{const are_vertices_in_He} checks if there is 
a subgraph \<open>H\<^sub>e\<close> in \<open>H\<close> that contains both given vertices. The function @{const min_dist_in_He} computes 
the distance between two vertices in a subgraph \<open>H\<^sub>e\<close>. 

@{thm[display,mode=IfThen] c.simps}

The function \<open>g\<close> depends on two functions @{const shorten_tour} and @{const vc_of_tour}. The 
function @{const shorten_tour} modifies a Hamiltonian cycle s.t. the resulting has less total weight 
and the cycle contains a Hamiltonian path for every subgraph \<open>H\<^sub>e\<close>. The function @{const vc_of_tour} 
computes a vertex cover for \<open>G\<close> given a Hamiltonian cycle that contains a Hamiltonian path for every 
subgraph \<open>H\<^sub>e\<close>.

@{thm[display] g.simps}

Given a tour \<open>T\<close> of \<open>H\<close>, the function @{const shorten_tour} iteratively (for each edge \<open>e\<close> of \<open>G\<close>) 
removes all vertices of the subgraph \<open>H\<^sub>e\<close> from the tour \<open>T\<close> and appends a Hamiltonian path for the 
subgraph \<open>H\<^sub>e\<close>. This replacement is done regardless of whether the tour \<open>T\<close> already contains a 
Hamiltonian path for the subgraph \<open>H\<^sub>e\<close>. The appended Hamiltonian path for the subgraph \<open>H\<^sub>e\<close> is 
carefully chosen such that the resulting tour has less total weight. On the other hand, the function 
\<open>g\<close> descibed by @{cite "korte_vygen_2018"} only inserts a Hamiltonian paths when the tour \<open>T\<close> does 
not already contain a Hamiltonian path for the subgraph \<open>H\<^sub>e\<close>. 

The main reason for this decision is that, by always inserting a Hamiltonian path we make sure that 
the resulting tour only contains Hamiltonian paths that start and end at a corner vertex of a subgraph \<open>H\<^sub>e\<close>. 
This simplifies the formalization. The resulting tour is represented with a sequence of starting-vertices 
instead of a path in the graph \<open>H\<close>. This simplifies the definitions and proofs, e.g. definition for @{const vc_of_tour}.
Furthermore, all the cases for the different possible Hamiltonian paths for the subgraphs \<open>H\<^sub>e\<close> 
(see figure~\ref{fig:Hamiltonian-paths-He}) are handled explicitly. The cases where the tour \<open>T\<close> 
contains a Hamiltonian path for a subgraph \<open>H\<^sub>e\<close> of type \ref{fig:Hamiltonian-paths-He2} or \ref{fig:Hamiltonian-paths-He3} from figure~\ref{fig:Hamiltonian-paths-He} 
are not covered by the proof of @{cite "korte_vygen_2018"}.

The locale @{locale VC4_To_mTSP} also contains the proofs for the feasibility of the reduction functions 
and the linear inequalities required for a L-reduction.

@{thm[display] f_is_complete}

@{thm[display] g_is_vc}

@{thm[display] l_reduction1}

@{thm[display] l_reduction2}

{\color{red} proof intuition}

The following lemmas are important lemmas when proving the linear inequalities.

@{thm[display] cost_of_opt_mTSP}

@{thm[display] card_g_leq_k}

The following lemma describes a case distinction on the different possible Hamiltonian paths that 
are admitted by the substructures \<open>H\<^sub>e\<close>. 

@{thm[display] hamiltonian_paths_with_cost_11}

This lemma is not proven in my formalization because I am unsure about the best way to prove this 
lemma. In the theory @{file "./reductions/FindHamiltonianPath.thy"} I have started to prove this lemma for an 
instantiation of the graph representations. This result needs to be transfered into the reduction 
proof. At the moment I am not sure what the best and way to do this is. 
\<close>

text \<open>The L-reduction proof that is presented in @{cite "korte_vygen_2018"} is incomplete. 
\begin{enumerate}[label=(\roman*)]
  \item {The proof fails if the optimal vertex cover of \<open>G\<close> has a cardinality of 1. In this case, 
    some of the auxiliary lemmas used in @{cite "korte_vygen_2018"} do not hold. The construction of 
    the L-reduction still works in this case, but for the proof this case needs to be considered 
    separately. For now I have only excluded this case through assumptions.}
  \item {The proof is missing multiple cases, when identifying the covering vertices. There are 
    different Hamiltonian paths for the substructures \<open>H\<^sub>e\<close> that do not start or end at corners of 
    the substructures \<open>H\<^sub>e\<close>. @{cite "korte_vygen_2018"} only describe how to identify a covering 
    vertex if the Hamiltonian path starts and ends at a corner of the substructures \<open>H\<^sub>e\<close>. For some 
    Hamiltonian path that do not start or end at corners of the substructures \<open>H\<^sub>e\<close>, it is not 
    immediately clear which covering vertex to choose. I have solved this issue by extending the 
    definition of the function \<open>g\<close>. {\color{red} compare to @{cite "papadimitriou_yannakakis_1993"}}}
\end{enumerate}
\<close>

(*<*)
end
(*>*)

(* ----- *)
 
section \<open>Future Work and Conclusion\<close>

text \<open>For my Interdisciplinary Project, I have formalized parts of the section 21.1, 
\textit{Approximation Algorithms for the TSP} from @{cite "korte_vygen_2018"}.
\begin{itemize}
  \item I have formally verified two approximation algorithms for \textsc{Metric TSP}: the 
    \textsc{DoubleTree} and the \textsc{Christofides-Serdyukov} algorithm.
  \item I have formalized a L-reduction to \textsc{Metric TSP}, which proves the 
    \textsc{MaxSNP}-hardness of \textsc{Metric TSP}.
\end{itemize}

Future work includes:

\begin{itemize}
  \item The Eulerian graphs that are constructed for the \textsc{DoubleTree} and 
    \textsc{Christofides-Serdyukov} algorithm might be multi-graphs. In the theory 
      @{file "./graphs/MultiGraph.thy"}, I have started formalizing an encoding of multi-graphs with simple 
      graphs. This formalization needs to be finished.
  \item Prove the existence of the necessary algorithms for the \textsc{DoubleTree} and 
    \textsc{Christofides-Serdyukov} algorithm.
    \begin{itemize}
      \item Write an adapter to the existing formalization of Prim's algorithm @{cite "lammich_nipkow_2019"}.
      \item Formalize and verify algorithms for minimum perfect matching @{cite "edmonds_1965"} and Eulerian tour @{cite "korte_vygen_2018"}.
    \end{itemize}
  \item Prove the polynomial running time of reduction functions $f$ and $g$.
    \begin{itemize}
      \item To prove the running time one needs to assume a computational model. \texttt{IMP-} 
        provides a computational model. Thus, a way to prove the polynomial time-complexity of the 
        functions \<open>f\<close> and \<open>g\<close> it to refine the functions to \texttt{IMP-} and prove the running 
        time of the refined definitions.
      \end{itemize}
\end{itemize}
\<close>

(*<*)

end

(*>*)