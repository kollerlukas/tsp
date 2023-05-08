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

text \<open>The \textsc{Traveling-Salesman Problem} (\textsc{TSP}) is one of the most studied 
$\textsc{NP}$-complete optimization problems. \textsc{TSP} describes the 
optimization problem of finding a Hamiltonian cycle with minimal total weight in a given 
graph. A Hamiltonian cycle is a cycle in a graph that visits every vertex exactly once.

Unless $\textsc{P}=\textsc{NP}$, $\textsc{NP}$-hard cannot be solved in polynomial time. When 
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

I have formalized parts of the section 21.1, \textit{Approximation Algorithms for the TSP} from 
@{cite "korte_vygen_2018"}.
\begin{enumerate}
  \item I have formalized and verified two approximation algorithms, \textsc{DoubleTree} and 
    \textsc{Christofides-Serdyukov}, for \textsc{Metric TSP}.
  \item I have formalized a L-reduction from the \textsc{Minimum Vertex Cover Problem} with maximum 
    degree of 4 to the \textsc{Metric TSP}, which proves the $\textsc{MaxSNP}$-hardness of the 
    \textsc{Metric TSP}.
\end{enumerate}

The \textsc{Christofides-Serdyukov} is the best known approximation algorithm for 
\textsc{Metric TSP} @{cite "korte_vygen_2018"}.

{\color{red} What is $\textsc{MaxSNP}$?}
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

All of these definitions are in \texttt{.thy}-files, which are located in the @{path "./graphs"}- or @{path "./problems"}
-directory.\<close>

subsection \<open>Connected Graphs\<close>

text \<open>A graph is connected if any pair of vertices is contained in the same connected component.\<close>
thm is_connected_def
            
thm connected_bridge

subsection \<open>Weighted Graphs\<close>

text \<open>Graph with edge weights. Locale @{const w_graph_abs}\<close>

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

text \<open>A locale that a minimum spanning. Locale @{const mst}\<close>

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
\textsc{Christofides-Serdyukov} approximation algorithms for \textsc{Metric TSP}. The 
\textsc{Christofides-Serdyukov} @{cite "christofides_1976" and "serdyukov_1978"} algorithm is the 
best known approximation algorithm for the \textsc{Metric TSP} @{cite "korte_vygen_2018"}. Both 
algorithms, the \textsc{DoubleTree} and \textsc{Christofides-Serdyukov} algorithm, are quite similar 
and depend on the following proposition (Lemma 21.3 @{cite "korte_vygen_2018"}):
Let the graph \<open>G\<close> with edge weights \<open>c\<close> be an instance of the \textsc{Metric TSP}. Given a connected 
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
The locale @{locale hc_of_et} provides the necessary assumption on the input graph \<open>G\<close>. The 
following lemmas prove the correctness.

@{thm[display] hc_of_et.hc_of_et_correct [no_vars]} 

@{thm[display] hc_of_et.cost_of_path_hc_of_et [no_vars]}

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
  \item an algorithm to compute a Eulerian tour in an Eulerian graph, e.g. Eulers's algorithm @{cite "korte_vygen_2018"}..
\end{enumerate}
For the formalization of the \textsc{DoubleTree} algorithm the existence of an algorithm for both of 
these problems is assumed. The assumptions are both captured in the locale @{locale hc_of_et}.
Further, to simplify matters the locale fixes a graph \<open>E\<close> with edge weights \<open>c\<close> and add the 
assumptions for an instance of \textsc{Metric TSP} (@{locale metric_graph_abs}.
Defining the \textsc{DoubleTree} algorithm in the locale @{locale double_tree_algo} is 
straightforward.\<close>
(*<*)
context double_tree_algo
begin
(*>*)
text \<open>
@{thm[display] double_tree_def}
\<close>
(*<*)
end
(*>*)
text\<open>For the defined \textsc{DoubleTree} algorithm we prove two properties: 
\begin{enumerate*}[label=(\roman*)]
  \item the feasibility, and
  \item the approximation factor.
\end{enumerate*}
The formalization of the proofs for the feasibility and approximation ratio of the 
\textsc{DoubleTree} algorithm is straightforward. 
The following lemmas prove the feasibility and the approximation ratio of the \textsc{DoubleTree} algorithm.

@{thm[display] dt_is_hc}

@{thm[display] dt_approx} 

Finally, the definition of the \textsc{DoubleTree} algorithm is refined to a \texttt{WHILE}-program 
using Hoare Logic.

@{thm[display] refine_double_tree}

\<close>

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
locale @{locale christofides_serdyukov_algo} is straightforward.\<close>
(*<*)
context christofides_serdyukov_algo
begin
(*>*)
text \<open>
@{thm[display] christofides_serdyukov_def}
\<close>
(*<*)
end
(*>*)
text\<open>
The feasibility and approximation ratio of the \textsc{Christofides-Serdyukov} algorithm are proven 
by the following lemmas. The formalization of their proofs is straightforward.\<close>
(*<*)
context christofides_serdyukov_algo_feasibility
begin
(*>*)
text \<open>
@{thm[display] cs_is_hc}
\<close>
(*<*)
end

context christofides_serdyukov_algo_approx
begin
(*>*)
text \<open>
@{thm[display] cs_approx}
\<close>
(*<*)
end
(*>*)
text\<open>
Like the \textsc{DoubleTree} algorithm, the definition of the \textsc{Christofides-Serdyukov} 
algorithm is refined to a \texttt{WHILE}-program using Hoare Logic. 

@{thm[display] refine_christofides_serdyukov}
\<close>

(* ----- *)
 
section \<open>L-Reduction from \textsc{Minimum Vertex Cover Problem} to \textsc{Metric TSP}\<close>

(*<*)
context VC4_To_mTSP
begin
(*>*)

text \<open>In this section, I describe the formalization of a L-Reduction from the 
\textsc{Minimum Vertex Cover Problem}, with maximum degree of 4 (\textsc{VCP4}), to the \textsc{Metric TSP}, which 
is presented in @{cite "korte_vygen_2018"}.

The \textsc{Minimum Vertex Cover Problem} describes the optimization problem of finding
a vertex-cover with minimum cardinality for a given graph. A vertex-cover is subset of vertices 
that contains at least one end-point of every edge. The \textsc{VCP4} is the restriction of the 
\textsc{Minimum Vertex Cover Problem} to input graphs where every vertex has a degree of at most 4.

Let \<open>A\<close> and \<open>B\<close> be optimization problems with cost functions \<open>c\<^sub>A\<close> and \<open>c\<^sub>B\<close>. The cost of the optimal
solution for an optimization problem is denoted by \<open>OPT(\<cdot>)\<close>.
An L-reduction (linear reduction) consists of a pair of functions \<open>f\<close> and \<open>g\<close> and two constants
\<open>\<alpha>,\<beta> > 0\<close> s.t for every instance \<open>x\<^sub>A\<close> of \<open>A\<close>
\begin{enumerate}[label=(\roman*)]
  \item \<open>f x\<^sub>A\<close> is an instance of \<open>B\<close> and \<open>OPT(f x\<^sub>A) \<le> OPT(x\<^sub>A)\<close>, and 
  \item for any feasible solution \<open>y\<^sub>B\<close> of \<open>f x\<^sub>A\<close>, \<open>g x\<^sub>A y\<^sub>B\<close> is a feasible solution of \<open>x\<^sub>A\<close> s.t.
    \<open>|(c\<^sub>A x\<^sub>A (g x\<^sub>A y\<^sub>B)) - OPT(x\<^sub>A)| \<le> | (c\<^sub>A (f x\<^sub>A) y\<^sub>B) - OPT(f x\<^sub>A)|\<close>.
\end{enumerate}

We L-reduce the \textsc{VCP4} to the \textsc{Metric TSP}. 

To describe an L-reduction, the definition of two functions \<open>f\<close> and \<open>g\<close> is required.
For the function \<open>f\<close>, we are given an instance of the \textsc{VCP4} and we need to 
construct an instance of the \textsc{Metric TSP}. An instance of the \textsc{VCP4} consists of an 
arbitrary graph where the degree of any vertex is at most 4. To construct an instance of the 
\textsc{Metric TSP} we need to construct a complete graph with edge weights s.t. the edge weights 
satisfy the triangle-inequality.

The function \<open>f\<close> is described by the following construction.
Let \<open>G\<close> be an instance of the \textsc{VCP4}, and let \<open>H:=f G\<close>.
For each edge \<open>e\<close> of \<open>G\<close> we add a substructure \<open>H\<^sub>e\<close> to \<open>H\<close> (see figure~\ref{fig:He}). The graph \<open>H\<close> 
is the complete graph over the vertices of the substructures \<open>H\<^sub>e\<close>. The substructure \<open>H\<^sub>e\<close> consists of 
12 vertices that are arranged in a 4-by-3 lattice structure. Each corner vertex corresponds 
to an endpoint of the edge \<open>e\<close>.

\begin{figure}
  \centering
  \begin{tikzpicture}[scale=2.0]
    \pic (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};
  \end{tikzpicture}
  \caption{Substructure \<open>H\<^sub>e\<close> for an edge \<open>e:={u,v}\<close>.}\label{fig:He}
\end{figure}

The substructure \<open>H\<^sub>e\<close> for the edge \<open>e\<close> has the special property that there is no Hamiltonian path 
in \<open>H\<^sub>e\<close> that starts and ends at corner-vertices of the substructure that correspond to different 
endpoints of the edge \<open>e\<close>. Therefore, the start- and end-vertex of a Hamiltonian path for the 
substructure \<open>H\<^sub>e\<close> can only correspond to one endpoint of the edge \<open>e\<close>. This property is used to 
encode a vertex cover of \<open>G\<close> in a Hamiltonian cycle of \<open>H\<close>.

The substructure \<open>H\<^sub>e\<close> admits 3 types of Hamiltonian paths (see figure~\ref{fig:Hamiltonian_paths_He}).

\begin{figure}
  \centering
  \begin{minipage}{.3\textwidth}
    \centering
    \begin{tikzpicture}[scale=2.0]
      \pic (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};

      \draw[hpEdge] 
        (uv-u1) -- (uv-u3) -- (uv-v2) -- (uv-u5) -- (uv-v6) 
          -- (uv-u4) -- (uv-v5) -- (uv-u6) -- (uv-v4) -- (uv-v1) 
          -- (uv-v3) -- (uv-u2);

      \node[hpEndpoint] at (uv-u1) {};
      \node[hpEndpoint] at (uv-u2) {};
    \end{tikzpicture}
  \end{minipage}%
  \begin{minipage}{.3\textwidth}
    \centering
    \begin{tikzpicture}[scale=2.0]
      \pic (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};

      \draw[hpEdge] 
        (uv-u1) -- (uv-u3) -- (uv-v2) -- (uv-u5) -- (uv-v6) 
          -- (uv-u4) -- (uv-v5) -- (uv-u2) -- (uv-v3) -- (uv-v1) 
          -- (uv-v4) -- (uv-u6);

      \node[hpEndpoint] at (uv-u1) {};
      \node[hpEndpoint] at (uv-u6) {};
    \end{tikzpicture}
  \end{minipage}%
  \begin{minipage}{.3\textwidth}
    \centering
    \begin{tikzpicture}[scale=2.0]
      \pic (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};

      \draw[hpEdge] 
        (uv-v6) -- (uv-u5)-- (uv-v2) -- (uv-u3) -- (uv-u1) 
          -- (uv-u4) -- (uv-v5) -- (uv-u2) -- (uv-v3) -- (uv-v1) 
          -- (uv-v4) -- (uv-u6);

      \node[hpEndpoint] at (uv-v6) {};
      \node[hpEndpoint] at (uv-u6) {};
    \end{tikzpicture}
  \end{minipage}
  \caption{This figure shows the different types Hamiltonian paths for the substructure \<open>H\<^sub>e\<close> for an 
    edge \<open>e:={u,v}\<close>. All three Hamiltonian paths correspond to the endpoint \<open>u\<close>.}\label{fig:Hamiltonian_paths_He}
\end{figure}

Next, I describe the edge weights of the graph \<open>H\<close>.
The weight of an edge between vertices of the same substructure \<open>H\<^sub>e\<close> is simply the distance of the 
vertices within the substructure \<open>H\<^sub>e\<close>. An edge that connects two corners of two different 
substructures \<open>H\<^sub>e\<close> and \<open>H\<^sub>f\<close> (\<open>e \<noteq> f\<close>), where both corners are on the side of their substructure that 
corresponds to the same vertex have weight 4. All remaining edges have weight 5. The proof that the 
edge weights satisfy the traingle-inequality is omitted.

For the function \<open>g\<close> we need to construct a feasible solution for \<open>G\<close> given a feasible solution for 
\<open>H\<close>, which is an arbitrary Hamiltonian cycle \<open>T\<close> in \<open>H\<close>. A Hamiltonian cycle \<open>T\<close> in \<open>H\<close> may be 
composed of only Hamiltonian paths for the substructures \<open>H\<^sub>e\<close>. In this case, for each edge \<open>e\<close> of \<open>G\<close> 
we look at the Hamiltonian path of \<open>H\<^sub>e\<close> that is contained in \<open>T\<close>: the Hamiltonian path can only 
correspond to one endpoint of the edge \<open>e\<close>. We select this endpoint to be the covering vertex for 
the edge \<open>e\<close>. If a Hamiltonian cycle \<open>T\<close> in \<open>H\<close> does not contain a Hamiltonian path for every \<open>H\<^sub>e\<close>, 
we construct a Hamiltonian cycle \<open>T'\<close> in \<open>H\<close> s.t. \<open>T'\<close> contains a Hamiltonian path for every \<open>H\<^sub>e\<close> 
and the cost of \<open>T'\<close> is at most the cost of \<open>T\<close>. The Hamiltonian cycle \<open>T'\<close> is constructed by 
iteratively replacing parts of the current Hamiltonian cycle with a Hamiltonian path for a 
substructure \<open>H\<^sub>e\<close>.

The functions \<open>f\<close> and \<open>g\<close> have to be computable (in polynomial time) functions. Therefore, the locale 
@{locale ugraph_adj_map} provides an abstract adjacency map, which can be instantiated to obtain 
executable functions on graphs.

The L-reduction itself is formalized in the locale @{locale VC4_To_mTSP} that depends on two 
executable adjacency-maps (@{locale ugraph_adj_map}), one for each of the graphs \<open>G\<close> and \<open>H\<close>. 
The locale @{locale VC4_To_mTSP} additionally assumes appropriate \texttt{fold}-functions for the graphs.

The reduction functions \<open>f\<close> and \<open>g\<close> are defined in the @{locale VC4_To_mTSP} using the assumed 
\texttt{fold}-functions and some auxiliary functions.

@{thm[display] f.simps}

@{thm[display] c.simps}

@{thm[display] g.simps}

Please note, that my definition of the function \<open>g\<close> is a little different compared to the definition 
by @{cite "korte_vygen_2018"}. In @{cite "korte_vygen_2018"}, the function \<open>g\<close> only inserts a 
Hamiltonian path for a substructure \<open>H\<^sub>e\<close> if the current Hamiltonian cycle does not contain a 
Hamiltonian path for \<open>H\<^sub>e\<close>. Thus, resulting Hamiltonian cycle may contain arbitrary 
Hamiltonian paths for the substructures \<open>H\<^sub>e\<close>. There are Hamiltonian path for the substructures \<open>H\<^sub>e\<close> 
that do not start or end at a corner. This makes identifying the covering vertex for an edge more 
difficult. On the other hand, my definition of the function \<open>g\<close> makes sure that the resulting 
Hamiltonian cycle only consists of Hamiltonian paths for the substructures \<open>H\<^sub>e\<close> that start and end 
at the corners of the substructures \<open>H\<^sub>e\<close>. Therefore, identifying the covering vertex is simplified.

The locale @{locale VC4_To_mTSP} also contains the proofs for the feasibility of the reduction functions 
and the linear inequalities required for a L-reduction.

@{thm[display] f_is_complete}

@{thm[display] g_is_vc}

@{thm[display] l_reduction1}

@{thm[display] l_reduction2}

The following lemmas are important lemmas when proving the linear inequalities.

@{thm[display] cost_of_opt_mTSP}

@{thm[display] card_g_leq_k}

The following lemma describes a case distinction on the different possible Hamiltonian paths that 
are admitted by the substructures \<open>H\<^sub>e\<close>. 

@{thm[display] hamiltonian_paths_with_cost_11}

This lemma is not proven in my formalization because I am unsure about the best way to prove this 
lemma. In the theory @{theory tsp.FindHamiltonianPath} I have started to prove this lemma for an 
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
    definition of the function \<open>g\<close>.}
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
      @{theory tsp.MultiGraph}, I have started formalizing an encoding of multi-graphs with simple 
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