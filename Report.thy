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

{\color{red} Refinement to IMP-.}
\<close>

section \<open>Fundamentals and Definitions\<close>

text \<open>I build on the exiting formalization of Berge's theorem by {\color{red} Mohammad 
Abdulaziz (citation?)}. An undirected graph is formalized as a finite set of edges, where each edge 
is represented by a doubleton set. 

@{abbrev[display] graph_invar}
 
The approximation algorithms and the L-reduction use many graph-related concepts that are not 
defined in the formalization of Berge's theorem by {\color{red} Mohammad Abdulaziz (citation?)}, 
e.g. weighted edges, minimum spanning-tree, Hamiltonian cycle, etc..

In this section, I will go the formalization of graph-related concepts that are the necessary for 
the formalization of the \textsc{DoubleTree} and \textsc{Christofides-Serdyukov} approximation 
algorithms as well as the L-reduction. Because most of the definitions are straightforward I will 
only highlight specific important formalization choices.

All of these definitions are in \texttt{.thy}-files, which are located in the @{path "./graphs"}- 
or @{path "./problems"}-directory.

Many simple results and lemmas are formalized in the theory @{theory tsp.Misc} which is located in 
the directory @{path "./misc"}.
\<close>

subsection \<open>Connected Graphs\<close>

text \<open>A graph is connected if any pair of vertices is contained in the same connected component.

@{thm[display] is_connected_def}
\<close>

subsection \<open>Weighted Graphs\<close>

text \<open>The locale @{locale w_graph_abs} fixes an instance of a graph \<open>E\<close> and edge weights \<open>c\<close>.

The locale @{locale pos_w_graph_abs} assumes the edge weights \<open>c\<close> to be positive.
\<close>

subsection \<open>Complete Graphs\<close>

text \<open>A graph is complete if there exists an edge for any pair of vertices that are not equal.

@{thm[display] is_complete_def}

The locale @{locale compl_graph_abs} fixes an instance of a complete graph \<open>E\<close>.

In a complete graph, any sequence of vertices s.t. no two consecutive vertices are equal is a path.

@{thm[display] compl_graph_abs.path_complete_graph}

The locale @{const restr_compl_graph_abs} additionally fixes a subgraph of the instance \<open>E\<close>.

The locale @{locale metric_graph_abs} fixes an instance of a complete graph \<open>E\<close> and assumes that the 
edge weights \<open>c\<close> are positive and satisfy the triangle-inequality. A consequence of these assumption 
is that any path can be short-cutted.

@{thm[display] metric_graph_abs.cost_of_path_short_cut_tri_ineq}
\<close>                             

subsection \<open>Acyclic Graphs\<close>

text \<open>A path is a simple if no edge is used twice.

@{thm[display] is_simple_def}

A cycle in a graph is a vertex-path where the first and last element are the same.

A cycle is a vertex-path s.t. 
\begin{enumerate*}[label=(\roman*)]
  \item the first and last vertex are the same,
  \item the path is simple, and
  \item the path uses at least one edge.
\end{enumerate*}

@{thm[display] is_cycle_def}

A graph is acyclic if it does not contain a cycle.

@{thm[display] is_acyclic_def}
                     
A vertex that is contained in a cycle has a degree greater-equal to 2.

@{thm[display] graph_abs.cycle_degree}
\<close>

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

@{thm[display] is_st_def}

A minimum spanning tree is a spanning tree with minimum total weight.

@{thm[display] is_mst_def}

The locale @{locale mst} assumes the existence of an algorithm to compute a minimum spanning tree.
\<close>

subsection \<open>Hamiltonian Cycles\<close>

text \<open>A Hamiltonian cycle is a tour in a graph that visits every vertex exactly once.

@{thm[display] is_hc_def}

With this formalization, a Hamiltonian cycle is not necessarily a cycle. If a graph only contains 
one edge \<open>e={u,v}\<close> then \<open>[u,v,u]\<close> is a Hamiltonian cycle but not a cycle because it is not a simple 
path. The edge \<open>e\<close> is used twice.
\<close>

subsection \<open>Traveling-Salesman Problem\<close>

text \<open>A solution to the \textsc{TSP} is a Hamiltonian cycle with minimum total weight.

@{thm[display] is_tsp_def}
\<close>

subsection \<open>Multi-Graphs\<close>

text \<open>I have started to formalize an encoding of a multi-graph with a regular graph. My attempts 
be found in the theory @{theory tsp.MultiGraph}.\<close>

subsection \<open>Eulerian Tours\<close>

text \<open>A graph is eulerian if every vertex has even degree.

@{thm[display] is_eulerian_def}

A Eulerian tour is a path that uses every edge of a given graph exactly once.

@{thm[display] is_et_def}

The locale @{locale eulerian} fixes an algorithm to compute a Eulerian tour for a given multi-graph.
\<close>

subsection \<open>Perfect Matchings\<close>

text \<open>The existing graph formalization {\color{red} by Mohammad Abdulaziz} already contains 
formalization of matchings. A perfect matching is a matching that contains every vertex.

@{thm[display] is_perf_match_def} 

A minimum-weight perfect matching is a perfect matching with minimum total weight.

@{thm[display] is_min_match_def} 

The locale @{locale min_weight_matching} fixes an algorithm to compute a minimum-weight perfect 
matching for a given graph. 
\<close>

(* ----- *)

section \<open>Approximating the \textsc{Metric TSP}\<close>

text \<open>This section describes the formalization of the \textsc{DoubleTree} and the 
\textsc{Christofides-Serdyukov} approximation algorithms for \textsc{Metric TSP}. Both 
algorithms are quite similar 
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
assumptions for an instance of \textsc{Metric TSP} (@{locale metric_graph_abs}).
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

text \<open>This section describes the formalization of a L-Reduction from the 
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
The necessary graph-related definitions are redefined for the adjencecy-map representation of graphs. 
The definitions for the adjencecy-map representation of graphs are denoted by the postfix \<open>-Adj\<close>.

The reduction functions \<open>f\<close> and \<open>g\<close> are defined in the locale @{locale VC4_To_mTSP} using the assumed 
\texttt{fold}-functions and some auxiliary functions. The function \<open>f\<close> uses the auxiliary function 
@{const[names_short] complete_graph} to construct the complete graph for a given set of vertices.

@{thm[display,names_short] f.simps}

The function \<open>c\<close> uses a couple of auxiliary functions to check different cases for the two given 
vertices. The function @{const is_edge_in_He} checks if there is a substructure \<open>H\<^sub>e\<close> where the two 
given vertices are connected by an edge. The function @{const are_vertices_in_He} checks if there is 
a substructure \<open>H\<^sub>e\<close> that contains both given vertices. The function @{const min_dist_in_He} computes 
the length of the shortest path in a substructure \<open>H\<^sub>e\<close> that connects the two given vertices. 

@{thm[display] c.simps}

The function \<open>g\<close> depends on two functions @{const shorten_tour} and @{const vc_of_tour}. The 
function @{const shorten_tour} modifies a Hamiltonian cycle s.t. the resulting has less total weight 
and the cycle contains a Hamiltonian path for every substructure \<open>H\<^sub>e\<close>. The function @{const vc_of_tour} 
computes a vertex cover for \<open>G\<close> given a Hamiltonian cycle that contains a Hamiltonian path for every 
substructure \<open>H\<^sub>e\<close>.

@{thm[display] g.simps}

Please note, that this definition of the function \<open>g\<close> is a little different compared to the definition 
by @{cite "korte_vygen_2018"}. In @{cite "korte_vygen_2018"}, the function \<open>g\<close> only inserts a 
Hamiltonian path for a substructure \<open>H\<^sub>e\<close> if the current Hamiltonian cycle does not contain a 
Hamiltonian path for \<open>H\<^sub>e\<close>. Thus, resulting Hamiltonian cycle may contain arbitrary 
Hamiltonian paths for the substructures \<open>H\<^sub>e\<close>. There are Hamiltonian path for the substructures \<open>H\<^sub>e\<close> 
that do not start or end at a corner. This makes identifying the covering vertex for an edge more 
difficult. On the other hand, my definition of the function \<open>g\<close> makes sure that the resulting 
Hamiltonian cycle only consists of Hamiltonian paths for the substructures \<open>H\<^sub>e\<close> that start and end 
at the corners of the substructures \<open>H\<^sub>e\<close>. Therefore, identifying the covering vertex is simplified.
Figure \ref{fig:Hamiltonian_paths_He} depicts the different types of Hamiltonian paths in the substructure \<open>H\<^sub>e\<close>.

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