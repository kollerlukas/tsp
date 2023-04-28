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
    "reductions/VertexCover4ToMetricTravelingSalesman_AdjList"
begin

section \<open>Introduction\<close>

text \<open>The \textsc{Traveling-Salesman Problem} (\textsc{TSP}) is one of the most studied 
$\mathcal{NP}$-complete optimization problems (* TODO: citation *). \textsc{TSP} describes the 
optimization problem of finding a Hamiltonian cycle with minimal total weight in a given 
graph. A Hamiltonian cycle is a cycle in a graph that visits every vertex exactly once.

Unless $\mathcal{P}=\mathcal{NP}$, $\mathcal{NP}$-hard cannot be solved in polynomial time. When 
dealing with optimization problems, a typical strategy is to relax the optimality condition for 
a solution and by accepting approximate solutions. An approximation algorithm is a polynomial time 
algorithm that returns a bounded approximate solution. Ideally, the approximate solution can be 
bounded by a constant factor.

What is a approximation algorithm?

See: Verified approximation algorithms @{cite "essmann_et_al_2020"}

Unfortunately, there is no constant-factor-approximation algorithm for the general \textsc{TSP} 
@{cite "korte_vygen_2018"}. 

Therefore, a less general version of the \textsc{TSP} is considered. In this work we consider the 
\textsc{Metric TSP}. The \textsc{Metric TSP} specializes the \textsc{TSP} by assuming that the given 
graph is complete and the edge-weights satisfy the triangle-inequality. These assumption are 
satisfies most of the time when solving real-world instances of \textsc{TSP}, e.g. finding the 
shortest tour that connects certain cities on a map.

The goal of this work is to formalize parts of the 21\textsuperscript{st} chapter,
\textit{The Traveling-Salesman Problem}, of the book @{cite "korte_vygen_2018"}. My work can be 
split into three section: \begin{enumerate}
  \item The formalization of the necessary graph-related defintions,
  \item The formalization and correctness proofs for two approximation algorithms, 
    \textsc{DoubleTree} and \textsc{Christofides-Serdyukov},
  \item The formalization of a L-reduction from the \textsc{Vertex Cover Problem} to 
    the \textsc{Metric TSP} which proves the $\mathcal{MaxSNP}$-hardness of the \textsc{Metric TSP}.
\end{enumerate}

The \textsc{Christofides-Serdyukov} is the best known approximation algorithm for 
\textsc{Metric TSP} @{cite "korte_vygen_2018"}.

{\color{red} What is $\mathcal{MaxSNP}$?}
\<close>

(* ----- *)

section \<open>Related Work\<close>

text \<open>

An approximation algorithm is a polynomial-time algorithm for an optimization problem that 
returns an approximate solution. The \textit{approximation ratio} bounds the distance between the
approximate solution and the optimal solution.

@{cite essmann_et_al_2020} have formalized different approximation algorithms in Isabelle/HOL.

{\color{red} Reductions in Isabelle?}

{\color{red} Refinement to IMP-.}
\<close>

section \<open>Fundamentals and Definitions\<close>

text \<open>I build on the exiting formalization of Berge's theorem by {\color{red} Mohammad 
Abdulaziz (citation?)}. An undirected graph is formalized as a finite set of edges, where each edge 
is represented by a doubleton set. 

@{const graph_invar}
 
The approximation algorithms and the L-reduction use many graph-related concepts that are not 
defined in the formalization of Berge's theorem by {\color{red} Mohammad Abdulaziz (citation?)}, 
e.g. weighted edges, minimum spanning-tree, Hamiltonian cycle, etc..

In this section, I will go the formalization of graph-related concepts that are the necessary for 
the formalization of the \textsc{DoubleTree} and \textsc{Christofides-Serdyukov} approximation 
algorithms as well as the L-reduction. Because most of the definitions are straightforward I will 
only highlight specific important formalzation choices.

All of these definitions are in {\color{red} ".thy"}-files, which are located in the {\color{red} "./graphs"}- or {\color{red} "./problems"}
-directory.\<close>

subsection \<open>Connected Graphs\<close>

text \<open>A graph is connected if any pair of vertices is contained in the same connected component.\<close>
thm is_connected_def
            
thm connected_bridge

subsection \<open>Weighted Graphs\<close>

text \<open>Graph with edge weights. Locale @{const w_graph_abs}}\<close>

text \<open>Weighted graph with only positive edges weights. Locale @{const pos_w_graph_abs}\<close>

subsection \<open>Complete Graphs\<close>

text \<open>A graph is complete if there exists an edges for any pair of vertices that are not equal.\<close>
thm is_complete_def

text \<open>Complete graph locale @{const compl_graph_abs}\<close>

text \<open>A locale that fixes a subgraph of a complete graph. Locale @{const restr_compl_graph_abs}\<close>

text \<open>Complete graph with triangle inequality. @{const metric_graph_abs}\<close>

thm metric_graph_abs.cost_of_path_short_cut_tri_ineq

text \<open>In a complete graph, any sequence of vertices s.t. no two consecutive vertices are equal 
(@{const distinct_adj}) is a path.\<close>
thm compl_graph_abs.path_complete_graph

subsection \<open>Acyclic Graphs\<close>

text \<open>A path is a simple if no edge is used twice.\<close>
thm is_simple_def


text \<open>I have defined a cycle in a graph to be a vertex-path where the first and last element are the same.\<close>

text \<open>A cycle is a path s.t. (i) it starts and ends at the same node, (ii) it is simple, and 
(iii) it uses at least one edge.\<close>
thm is_cycle_def

text \<open>A vertex that is contained in a cycle has a degree greater-equal to 2.\<close>
thm graph_abs.cycle_degree

text \<open>A graph is acyclic if no cycle is contained in the graph.\<close>
thm is_acyclic_def

subsection \<open>Trees\<close>

text \<open>A tree is a graph that is (i) connected and (ii) acyclic.\<close>
thm is_tree_def

subsection \<open>Spanning Trees\<close>

text \<open>A spanning tree is a subgraph s.t. (i) it is a tree and (ii) it contains every vertex.\<close>
thm is_st_def

subsection \<open>Minimum Spanning Trees\<close>

text \<open>A minimum spanning tree is a spanning tree with minimum weight.\<close>
thm is_mst_def

text \<open>A locale that a minimum spanning. Locale @{const mst}}\<close>

subsection \<open>Hamiltonian Cycles\<close>

thm is_hc_def

subsection \<open>Traveling-Salesman Problem\<close>

thm is_tsp_def

text \<open>For the \textsc{Metric TSP} a locale \<open>metric_graph_abs\<close> which assumes the necessary properties 
about the input graph (completeness and trinagle-inequality) is used.\<close>

term metric_graph_abs.is_mtsp

subsection \<open>Multi-Graphs\<close>

(* TODO: finish encoding of a multi-graph in a regular graph. *)

subsection \<open>Eulerian Tours\<close>

thm is_eulerian_def

text \<open>Locale that fixes an algorithm that computes a Eulerian tour for a given multi-graph.
  Locale @{const eulerian}\<close>

(* TODO: implement and verify an algorithm for Eulerian Tour *)

text \<open>Eulerian Tour on a Multi-Graph.\<close>
thm is_et_def

subsection \<open>Perfect Matchings\<close>

thm is_perf_match_def

subsection \<open>Minimum-Weight Perfect Matchings\<close>

thm is_min_match_def

text \<open>Locale that fixes an algorithm that computes a minimum-weight perfect matching for a given 
graph. Locale @{const min_weight_matching}\<close>

text \<open>Every complete graph with an even number of vertices has a perfect matching.\<close>
thm compl_graph_abs.perf_match_exists

(* ----- *)

section \<open>Approximating the \textsc{Metric TSP}\<close>

text \<open>In this section, I will go over my formalization of the \textsc{DoubleTree} and the 
\textsc{Christofides-Serdyukov} approximation algorithms for \textsc{Metric TSP}. Both approximation 
algorithms, \textsc{DoubleTree} and \textsc{Christofides-Serdyukov}, are
depend on the following proposition (Lemma 21.3 @{cite "korte_vygen_2018"}):
Let graph \<open>G\<close> with edge weights \<open>c\<close> be an instance of the \textsc{Metric TSP}. Given a connected 
Eulerian graph \<open>G'\<close> that spans the vertices of the graph \<open>G\<close>, we can compute (in polynomial time) a 
Hamiltonian cycle for \<open>G\<close> with total weight of at most the total of all edges 
in \<open>G'\<close>. 

The proof for this proposition is constructive: first a Eulerian tour \<open>P\<close> is computed in the
graph \<open>G'\<close>. The tour \<open>P\<close> visits every vertex of \<open>G\<close> at least once, because the Eulerian graph \<open>G'\<close> 
spans the vertices of \<open>G\<close>. For the next step, duplicate vertices in the tour \<open>P\<close> are removed to 
obtain the desired Hamiltonian cycle for the graph \<open>G\<close> ("shortcutting"). The edge weights \<open>c\<close> 
satisfy the triangle-inequality (by assumption), thus the total weight of the resulting 
Hamiltonian cycle is at most the total weight of the Eulerian tour \<open>P\<close>, which is the total weight 
of the edges of the Eulerian graph \<open>G'\<close>.

This construction for this proposition is formalized by the function @{const comp_hc_of_et}.
The locale @{locale hc_of_et} provides the necessary assumption on the input graph \<open>G\<close>. The lemmas 
@{thm hc_of_et.hc_of_et_correct} and @{thm hc_of_et.cost_of_path_hc_of_et} prove the correctness.

Using the proposition (Lemma 21.3 @{cite "korte_vygen_2018"}), an approximation algorithm for the 
\textsc{Metric TSP} is derived by simply constructing a Eulerian graph that spans the vertices 
of the graph \<open>G\<close>. By minimizing the total weight of the edges of the Eulerian graph one directly 
reduces the approximation ratio of the resulting approximation algorithm.

Both approximation algorithms, \textsc{DoubleTree} and \textsc{Christofides-Serdyukov}, first 
compute a minimum spanning-tree \<open>T\<close> of \<open>G\<close> and add edges to \<open>T\<close> to construct a Eulerian graph that
spans the vertices of the graph \<open>G\<close>. By the proposition (Lemma 21.3 @{cite "korte_vygen_2018"}), we 
can then compute (in polynomial time) a Hamiltonian cycle in \<open>G\<close> with a total weight that is bounded 
by the total weight of \<open>T\<close> and the added edges.

The \textsc{DoubleTree} algorithm constructs a Eulerian graph by computing the multi-graph which 
contains every edge of \<open>T\<close> twice. In this multigraph every vertex has even degree and thus this 
multi-graph is a Eulerian graph. The total weight of any Hamiltonian cycle is at least the the total 
weight of \<open>T\<close>. Thus, the total weight of the Hamiltonian cycle produced by the \textsc{DoubleTree} 
algorithm is bounded by 2-times the total weight of the optimal Hamiltonian cycle. Therefore, the 
\textsc{DoubleTree} algorithm is a 2-approximation algorithm for the \textsc{Metric TSP}.

On the other hand, the \textsc{Christofides-Serdyukov} algorithm computes a minimum perfect-matching 
\<open>M\<close> between the vertices that have odd-degree in \<open>T\<close>. The union of \<open>M\<close> and \<open>T\<close> is a Eulerian graph. 
The total weight of \<open>M\<close> is at most half the total weight of the optimal Hamiltonian cycle. Therefore, 
the \textsc{Christofides-Serdyukov} algorithm is a 1.5-approximation algorithm for the 
\textsc{Metric TSP}.\<close>

subsection \<open>Formalizing the \textsc{DoubleTree} Approximation Algorithm\<close>

text \<open>The \textsc{DoubleTree} algorithm consists of three main steps:
\begin{enumerate}
  \item compute a minimum spanning-tree \<open>T\<close> of the input graph \<open>G\<close>,
  \item compute a Eulerian tour \<open>P\<close> of the doubled minimum spanning-tree \<open>T + T\<close>,
  \item and remove duplicate vertices in \<open>P\<close> by short-cutting.
\end{enumerate}
Thus, the \textsc{DoubleTree} algorithm depends to two algorithms:
\begin{enumerate}
  \item an algorithm to compute a minimum spanning-tree, e.g. Prim's algorithm 
    @{cite "lammich_nipkow_2019"}, and
  \item an algorithm to compute a Eulerian tour in an Eulerian graph, e.g. Fleury's algorithm 
    {\color{red} TODO: add citation}.
\end{enumerate}
For the formalization of the \textsc{DoubleTree} algorithm the existence of an algorithm for both of 
these problems is assumed. The assumptions are both captured in the locale @{locale hc_of_et}.
Further, to simplify matters the locale fixes a graph \<open>E\<close> with edge weights \<open>c\<close> and add the 
assumptions for an instance of \textsc{Metric TSP} (@{locale metric_graph_abs}.
Defining the \textsc{DoubleTree} algorithm in the locale @{locale double_tree_algo} is 
straightforward.

@{const double_tree_algo.double_tree}

For the defined \textsc{DoubleTree} algorithm we prove two properties: 
\begin{enumerate}
  \item the feasibility, and
  \item the approximation factor.
\end{enumerate}
The formalization of the proofs for the feasibility and approximation ratio of the 
\textsc{DoubleTree} algorithm is straightforward. 
The lemma @{thm dt_is_hc} proves the feasibility and the lemma @{thm dt_approx} proves the 
approximation ratio.

Finally, the definition of the \textsc{DoubleTree} algorithm is refined to IMP using Hoare Logic 
@{thm refine_double_tree} {\color{red} TODO: add citation}.\<close>

(* ----- *)

subsection \<open>Formalizing the \textsc{Christofides-Serdyukov} Approximation Algorithm\<close>

text \<open>The \textsc{Christofides-Serdyukov} algorithm is similar to the \textsc{DoubleTree}, and 
consists of the following steps:
\begin{enumerate}
  \item compute a minimum spanning-tree \<open>T\<close> of the input graph \<open>G\<close>,
  \item compute a minimum perfect-matching \<open>M\<close> between the vertices that have odd degree in \<open>T\<close>,
  \item compute a Eulerian tour \<open>P\<close> of the union of the minimum spanning-tree and the perfect-matching \<open>T + M\<close>,
  \item and remove duplicate vertices in \<open>P\<close> by short-cutting.
\end{enumerate}
Therefore, the \textsc{Christofides-Serdyukov} algorithm depends on the algorithm the 
\textsc{DoubleTree} algorithm depended on as well as an algorithm to compute a minimum 
perfect-matching, e.g. Edmond's Blossom algorithm @{cite edmonds_1965} {\color{red} TODO: check if correct?}.

The \textsc{Christofides-Serdyukov} algorithm is formalized in a similar fashion to the 
\textsc{DoubleTree} algorithm. The locale @{locale christofides_serdyukov_algo} extends the locale 
@{locale double_tree_algo} and adds the assumption for the existence of an algorithm to compute a 
minimum perfect-matching. The definition of the \textsc{Christofides-Serdyukov} algorithm in the 
locale @{locale christofides_serdyukov_algo} is straightforward.

@{const christofides_serdyukov_algo.christofides_serdyukov}

The feasibility and approximation ratio of the \textsc{Christofides-Serdyukov} algorithm are proven 
by the lemmas @{thm cs_is_hc} and @{thm cs_approx}. The formalization of these proofs is 
straightforward.

Like the \textsc{DoubleTree} algorithm, the definition of the \textsc{Christofides-Serdyukov} 
algorithm is refined to IMP using Hoare Logic @{thm refine_christofides_serdyukov} {\color{red} TODO: add citation}.
\<close>

(* ----- *)
 
section \<open>L-Reduction from \textsc{Minimum Vertex Cover Problem} to \textsc{Metric TSP}\<close>

text \<open>In this section, I describe the formalization of a L-Reduction from the 
\textsc{Minimum Vertex Cover Problem} to the \textsc{Metric TSP}, which is presented in 
@{cite "korte_vygen_2018"}.

The \textsc{Minimum Vertex Cover Problem} describes the optimization problem of finding
a vertex-cover with minimum cardinality. A vertex-cover is subset of vertices that contains
at least one end-point of the edge.

Let \<open>A\<close> and \<open>B\<close> be optimization problems with cost functions \<open>c\<^sub>A\<close> and \<open>c\<^sub>B\<close>. The cost of the optimal
solution for an optimization problem is denoted by \<open>OPT(\<cdot>)\<close>.
An L-reduction (linear reduction) consists of a pair of functions \<open>f\<close> and \<open>g\<close> and two constants
\<open>\<alpha>,\<beta> > 0\<close> s.t for every instance \<open>x\<^sub>A\<close> of \<open>A\<close>
\begin{enumerate}[(i)]
  \item \<open>f x\<^sub>A\<close> is an instance of \<open>B\<close> and \<open>OPT(f x\<^sub>A) \<le> OPT(x\<^sub>A)\<close>, and 
  \item for any feasible solution \<open>y\<^sub>B\<close> of \<open>f x\<^sub>A\<close>, \<open>g x\<^sub>A y\<^sub>B\<close> is a feasible solution of \<open>x\<^sub>A\<close> s.t.
    \<open>|(c\<^sub>A x\<^sub>A (g x\<^sub>A y\<^sub>B)) - OPT(x\<^sub>A)| \<le> | (c\<^sub>A (f x\<^sub>A) y\<^sub>B) - OPT(f x\<^sub>A)|\<close>.
\end{enumerate}

We L-reduce the \textsc{Minimum Vertex Cover Problem}, with maximum degree of 4, to the \textsc{Metric TSP}. 

Therefore, we need to define the two functions \<open>f\<close> and \<open>g\<close> required for the L-reduction.
For the function \<open>f\<close>, given an instance of the \textsc{Minimum Vertex Cover Problem}, we need to 
construct an instance of the \textsc{Metric TSP}. An instance of the 
\textsc{Minimum Vertex Cover Problem} consists of an arbitrary graph, and the task is to decide 
for each edge which endpoint is the \textit{covering} vertex. A \textit{covering} vertex is included
in the vertex cover. To construct an instance of the \textsc{Metric TSP} we need to construct a 
complete graph with edge weight s.t. the edge weights satisfy the triangle-inequality.

Let \<open>G\<close> be an instance of the \textsc{Minimum Vertex Cover Problem}, and let \<open>H := f G\<close>.
For each edge of \<open>G\<close> we add a substructure \<open>H\<^sub>e\<close> to \<open>H\<close>. There are different Hamiltonian paths
in \<open>H\<^sub>e\<close>. A Hamiltonian cycle in \<open>H\<close> can be composed of Hamiltonian paths for each \<open>H\<^sub>e\<close>.
Depending on which Hamiltonian path in \<open>H\<^sub>e\<close> is chosen we pick an endpoint to be the 
\textit{covering} for the edge \<open>e\<close>. If a Hamiltonian cycle \<open>T\<close> in \<open>H\<close> does not contain a Hamiltonian 
path for every \<open>H\<^sub>e\<close> we can construct a Hamiltonian cycle \<open>T'\<close> in \<open>H\<close> s.t. \<open>T'\<close> contains a Hamiltonian 
path for every \<open>H\<^sub>e\<close> and the cost of \<open>T'\<close> is at most the cost of \<open>T\<close>.

The L-reduction is formalized in the locale @{locale VC4_To_mTSP} that depends on two executable 
adjacency-maps for the graphs \<open>G\<close> and \<open>H\<close> as well as appropriate fold-functions for the graphs.

The locale @{locale ugraph_adj_map}

reference locale 

The functions \<open>f\<close> and \<open>g\<close> are defined in .
\<close>

text \<open>Prove that Metric Traveling-Salesman is MAX-SNP hard.\<close>

(* ----- *)
 
section \<open>Future Work and Conclusion\<close>

text \<open>\begin{enumerate}
  \item implement algorithm for computing a Eulerian tour (Fleury's Algorithm)
  \item connect with implementaion of algrothim for MST (Prim's Algorithm)
  \item prove complexity of reduction function, e.g. refine reduction functions to IMP-.
  \item ... 
\end{enumerate}\<close>

(* TODO *)

end