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

text \<open>The \textsc{Traveling-Salesman Problem} (\textsc{TSP}) is a well-known optimization problem 
that describes the task of finding a tour among the vertices of a given weighted and 
undirected graph s.t. the tour has minimum total weight and every vertex of the graph is visited 
exactly once. The \textsc{TSP} has many applications in different areas, such as planning and 
scheduling @{cite "brumitt_stentz_1996"}, logistics @{cite "ratliff_rosenthal_1983"}, and designing 
printed circuit boards @{cite "groetschel_et_al_1991"}.

The \textsc{TSP} is \textsc{NP}-hard @{cite \<open>Theorem 15.43\<close> "korte_vygen_2018"}. This means, that unless 
$\textsc{P}=\textsc{NP}$, the \textsc{TSP} cannot be solved in polynomial time. When dealing with 
\textsc{NP}-hard optimization problems, a typical strategy is to approximate the optimal solution 
with an approximation algorithm. An approximation algorithm @{cite "vazirani_2010"} is a polynomial 
time algorithm that returns a bounded approximate solution. An approximation algorithm with an 
approximation ratio of \<open>\<alpha>\<close> is guaranteed to return an approximate solution that in the worst case 
has a total cost of \<open>\<alpha>OPT\<close>, where \<open>OPT\<close> is the total cost of the optimal solution. Ideally, the 
approximation ratio is a constant factor. An approximation algorithm essentially trades the 
optimality of the returned solution for a polynomial running time. Unfortunately, there is bad news 
for the \textsc{TSP}: there is no constant-factor approximation algorithm for the \textsc{TSP} 
@{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"}. 

Thus, in this work, I only consider the \textsc{Metric TSP}. The \textsc{Metric TSP} is a subcase 
of the \textsc{TSP} which makes the following two assumptions:
\begin{enumerate*}[label=(\roman*)]
  \item the given graph is complete and 
  \item the edge weights satisfy the triangle inequality.
\end{enumerate*}
The \textsc{Metric TSP} is still \textsc{NP}-hard @{cite \<open>Theorem 21.2\<close> "korte_vygen_2018"}.

In this work, I present my formalization of parts of section 21.1, \textit{Approximation Algorithms 
for the TSP}, from @{cite "korte_vygen_2018"}.
\begin{enumerate}
  \item I formalize and formally verify two approximation algorithms, \textsc{DoubleTree} and 
    \textsc{Christofides-Serdyukov}, for the \textsc{Metric TSP}.
  \item I formalize an L-reduction from the \textsc{Minimum Vertex Cover Problem} with maximum 
    degree of 4 (\textsc{VCP4}) to the \textsc{Metric TSP}, which proves the \textsc{MaxSNP}-hardness 
    of the \textsc{Metric TSP}.
\end{enumerate}

Unless $\textsc{P}=\textsc{NP}$, the \textsc{MaxSNP}-hardness of a problem proves the non-existence 
of an approximation scheme @{cite \<open>Corollary 16.40\<close> "korte_vygen_2018"}. An approximation scheme 
takes a parameter \<open>\<epsilon> > 0\<close> and produces an approximation algorithm with an approximation ratio of 
\mbox{\<open>(1 + \<epsilon>)\<close>} for minimization and \mbox{\<open>(1 - \<epsilon>)\<close>} for maximization problems. \textsc{MaxSNP} is a complexity 
class that contains graph-theoretical optimization problems. For any problem in \textsc{MaxSNP} 
there is a constant-factor approximation algorithm @{cite \<open>Theorem 1\<close> "papadimitriou_yannakakis_1991"}. 
A linear reduction (L-reduction) @{cite "papadimitriou_yannakakis_1991"} is a special type of 
reduction for optimization problems, that is used to prove the \textsc{MaxSNP}-hardness of problems. 
A problem is called \textsc{MaxSNP}-hard if every problem in \textsc{MaxSNP} L-reduces to it. The 
\textsc{VCP4} is known to be \textsc{MaxSNP}-hard @{cite \<open>Theorem 16.46\<close> "korte_vygen_2018"}.

Moreover, to get started with the project and to familiarize myself with the existing formalization 
of undirected graphs by \citeauthor{abdulaziz_2020} @{cite "abdulaziz_2020"}, I have formalized a 
proof by \citeauthor{korte_vygen_2018} @{cite \<open>Proposition 11.1\<close> "korte_vygen_2018"} which shows 
the equivalence of the maximum weight matching problem (\textsc{Maximum Matching Problem}) and the 
minimum weight perfect matching problem (\textsc{Minimum Matching Problem}).

All of my formalizations are done with the interactive theorem prover Isabelle/HOL 
@{cite "nipkow_wenzel_paulson_2002"}. My formalizations can be found on GitHub: 
\url{https://github.com/kollerlukas/tsp}.\<close>

section \<open>Related Work\<close>

text \<open>The \textsc{Christofides-Serdyukov} algorithm @{cite "christofides_1976" and "serdyukov_1978"} 
has an approximation ratio of $\frac{3}{2}$, and thus is the best known approximation algorithm for 
the \textsc{Metric TSP} @{cite "korte_vygen_2018"}. Recently, a randomized approximation algorithm 
for the \textsc{Metric TSP} was proposed, which (in expectation) achieves a slightly better 
approximation ratio than the \textsc{Christofides-Serdyukov} algorithm @{cite "karlin_et_al_2021"}.

A couple of different approximation algorithms are already formalized and verified in Isabelle/HOL 
@{cite "essmann_et_al_2020"}. I continue the work of \citeauthor{essmann_et_al_2020} 
@{cite "essmann_et_al_2020"} by formalizing and verifying the \textsc{DoubleTree} and the 
\textsc{Christofides-Serdyukov} approximation algorithms. Similar to \citeauthor{essmann_et_al_2020}, 
I give implementations for both of the formalized approximation algorithms with an imperative 
\texttt{WHILE}-program.

\citeauthor{wimmer_2021} @{cite "wimmer_2021"} formalized polynomial time reductions in Isabelle/HOL. 
To formally reason about the running times of functions, a computational model for the programming 
language is required. Therefore, \citeauthor{wimmer_2021} has developed the imperative language 
\texttt{IMP-} which provides a computational model to reason about the running times of functions 
implemented in \texttt{IMP-}. To my knowledge, there are no previous attempts to formalize an 
L-reduction in Isabelle/HOL.

{\sloppy \citeauthor{vazirani_2010} @{cite "vazirani_2010"} defines a \textit{gap-introducing} reduction 
which is a reduction from the satisfiability problem (\textsc{SAT}) to an optimization problem. A 
\textit{gap-preserving} reduction is a reduction between optimization problems. The combination of a 
gap-introducing and gap-preserving reduction can be used to prove the inapproximability of an 
optimization problem. Gap-preserving reductions are weaker than L-reductions @{cite "vazirani_2010"}.\par}\<close>

section \<open>Fundamentals and Definitions\<close>

text \<open>I build on the formalization of graphs by \citeauthor{abdulaziz_2020} @{cite "abdulaziz_2020"}, 
which is developed for a formalization of Berge's theorem @{cite "berge_1954"}. 
An undirected graph is represented by a finite set of edges. An edge is represented by a doubleton 
set. The following invariant characterizes a well-formed graph.

@{abbrev[display] graph_invar}

The locale @{locale graph_abs} fixes an instance of a graph \<open>E\<close> that satisfies the invariant 
@{const graph_invar}. The graph formalization by @{cite "abdulaziz_2020"} provides definitions for 
the following concepts.
\begin{itemize}
  \item @{const Vs} returns the set of vertices of a graph.
  \item A path is represented with a list of vertices and is characterized by the predicate 
    @{const path}. A walk (@{const walk_betw}) is a path between two specific vertices. The function 
    @{const edges_of_path} returns the list of edges of a given path.
  \item @{const degree} returns the degree of a vertex in a graph.
  \item @{const connected_component} returns the connected component of a vertex in a graph.
  \item A matching is a graph where no two edges are incident to the same vertex. The predicate 
    @{const matching} characterizes matchings.
\end{itemize}
 
The approximation algorithms and the L-reduction use many graph-related concepts that are not 
defined in @{cite "abdulaziz_2020"}, such as weighted graphs, minimum spanning trees, or 
Hamiltonian cycles. This section describes the formalization of the necessary graph-related concepts. 
Most of the definitions are straightforward, therefore only important formalization choices are 
highlighted.

All of the graph-related definitions are defined in theories that are located in the 
@{path "./graphs"}- or @{path "./problems"}-directory. Many simple results and lemmas are formalized 
in the theory @{file "./misc/Misc.thy"} which is located in the directory @{path "./misc"}.\<close>

subsection \<open>Connected Graphs\<close>

text \<open>A graph \<open>E\<close> is connected if any two vertices are contained in the same connected component. 
@{thm[display] is_connected_def}\<close>

subsection \<open>Weighted Graphs\<close>

text \<open>The locale @{locale w_graph_abs} fixes an instance of a graph \<open>E\<close> and edge weights \<open>c\<close>. The 
locale @{locale pos_w_graph_abs} extends the locale @{locale w_graph_abs} with the assumption that 
all edge weights are positive.\<close>
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

text \<open>A graph \<open>E\<close> is complete if there exists an edge between every two vertices.

@{thm[display] is_complete_def}
                          
The locale @{locale compl_graph_abs} fixes an instance of a complete graph \<open>E\<close>.\<close>
(*<*)
context compl_graph_abs
begin
(*>*)
text \<open>In a complete graph \<open>E\<close>, any sequence of vertices \<open>P\<close> s.t. no two consecutive vertices are 
equal (@{const distinct_adj}) is a path.

\begin{lemma}
  @{lemma[display] "is_complete E \<Longrightarrow> distinct_adj P \<Longrightarrow> set P \<subseteq> Vs E \<Longrightarrow> path E P" by (rule path_complete_graph)}
\end{lemma}\<close>
(*<*)
end
(*>*)
(* text \<open>The locale @{const restr_compl_graph_abs} additionally fixes a subgraph of the instance \<open>E\<close>.\<close>*)
(*<*)
context metric_graph_abs
begin
(*>*)
text\<open>{\sloppy The locale @{locale metric_graph_abs} extends the locales @{locale compl_graph_abs} and 
@{locale pos_w_graph_abs} and assumes that the edge weights \<open>c\<close> satisfy the triangle inequality. 
Within such a graph any intermediate vertex along a path can be removed to obtain a shorter path. 
Given a set of vertices \<open>X\<close> and a path \<open>P\<close>, the function @{const short_cut} removes all vertices 
along the path \<open>P\<close> that are not contained in \<open>X\<close>. The following lemma proves that the resulting path 
has less total weight.\par}

\begin{lemma}
  @{thm[display] cost_of_path_short_cut_tri_ineq[where E\<^sub>V="X"]}
\end{lemma}\<close>
(*<*)
end
(*>*)

subsection \<open>Acyclic Graphs\<close>

text \<open>A path \<open>P\<close> is simple if the path does not traverse an edge twice. This definition is in 
accordance to @{cite "lammich_nipkow_2019"}.

@{thm[display] is_simple_def}

A cycle \<open>C\<close> is a walk s.t. 
\begin{enumerate*}[label=(\roman*)]
  \item the first and last vertex are the same,
  \item the path is simple, and
  \item the walk uses at least one edge.
\end{enumerate*}

@{thm[display] is_cycle_def}

A graph \<open>E\<close> is acyclic if it does not contain a cycle.

@{thm[display] is_acyclic_def}\<close>
(*<*)
context graph_abs
begin
(*>*)
text \<open>The following lemma proves the fact that a vertex \<open>v\<close> that is contained in a cycle \<open>C\<close> has a 
degree of at least 2.

\begin{lemma}
  @{thm[display] cycle_degree}
\end{lemma}\<close>
(*<*)
end
(*>*)

subsection \<open>Trees\<close>

text \<open>A tree \<open>T\<close> is a graph that is 
\begin{enumerate*}[label=(\roman*)]
  \item connected, and
  \item acyclic.
\end{enumerate*}

@{thm[display] is_tree_def}

A spanning tree \<open>T\<close> of a graph \<open>E\<close> is a subgraph s.t.
\begin{enumerate*}[label=(\roman*)]
  \item \<open>T\<close> is a tree and
  \item \<open>T\<close> contains every vertex of \<open>E\<close>.
\end{enumerate*}

@{thm[display] is_st_def}\<close>
(*<*)
context w_graph_abs
begin
(*>*)
text\<open>A minimum spanning tree (MST) \<open>T\<close> is a spanning tree with minimum total weight.

@{lemma[display,source,mode=latex_sum] "is_mst E c T \<equiv> is_st E T \<and> (\<forall>T'. is_st E T' \<longrightarrow> (\<Sum>e\<in>T. c e) \<le> (\<Sum>e\<in>T'. c e))" by (rule is_mst_def)}\<close>
(* @{thm[display] is_mst_def} *)
(*<*)
end
(*>*)
text \<open>The locale @{locale mst} assumes the existence of an algorithm (denoted by \<open>comp_mst\<close>) that 
computes a MST for a given connected graph. This locale can be instantiated with a formalization of 
a suitable algorithm e.g. the formalization of Prim's algorithm by \citeauthor{lammich_nipkow_2019} 
@{cite "lammich_nipkow_2019"}. Given a connected graph, Prim's algorithm @{cite "jarnik_1930" and "prim_1957"} 
computes a MST. In the theory @{file "./adaptors/BergePrimAdaptor.thy"}, I have started (but not 
finished) to implement an adaptor between my formalization and the formalization by \citeauthor{lammich_nipkow_2019}. 
The adaptor already connects both formalizations for undirected graphs and proves the equivalence of 
the required definitions, e.g. definitions for MST. The only missing piece is to prove that the 
instantiated function for Prim's algorithm indeed computes a MST. This should be straightforward 
given the equivalences of the required definitions are already proven.\<close>

subsection \<open>Hamiltonian Cycles\<close>

text \<open>A Hamiltonian cycle \<open>H\<close> is a cycle in a graph \<open>E\<close> that visits every vertex exactly 
once. Sometimes a Hamiltonian cycle is called a tour of a graph.

@{lemma[display,source] "is_hc E H \<equiv> 
  (H \<noteq> [] \<longrightarrow> (\<exists>v. walk_betw E v H v)) \<and> set (tl H) = Vs E \<and> distinct (tl H)" by (rule is_hc_def)}

{\sloppy With this formalization, a Hamiltonian cycle is not necessarily a cycle (@{const is_cycle}). 
The graph that only contains one edge \<open>e={u,v}\<close> has the Hamiltonian cycle \<open>u,v,u\<close> which is not a 
simple path.\par}\<close>

subsection \<open>Traveling-Salesman Problem\<close>

(*<*)
context w_graph_abs
begin
(*>*)
text\<open>The optimal solution \<open>H\<close> to the \textsc{TSP} is a Hamiltonian cycle for the graph \<open>E\<close> with 
minimum total weight.

@{lemma[display,source] "is_tsp E c H \<equiv> is_hc E H
  \<and> (\<forall>H'. is_hc E H' \<longrightarrow> cost_of_path\<^sub>c H \<le> cost_of_path\<^sub>c H')" by (rule is_tsp_def)}\<close>
(*<*)
end
(*>*)

subsection \<open>Multi-Graphs\<close>

text \<open>A multigraph is formalized as a multiset of edges. The theory @{file "./graphs/MultiGraph.thy"} 
contains unfinished attempts for encoding a multigraph with a simple graph.\<close>

subsection \<open>Eulerian Tours\<close>

text \<open>A graph \<open>E\<close> is Eulerian if every vertex has even degree. The \textsc{DoubleTree} and the 
\textsc{Christofides-Serdyukov} algorithm need the concept of Eulerian multigraphs, thus the predicate 
@{const is_eulerian} is defined for multigraphs. The function \mbox{@{const mdegree}} returns the 
degree of a vertex in a multigraph. @{const mVs} returns the set of vertices of a multigraph.

@{thm[display] is_eulerian_def}

An Eulerian tour \<open>P\<close> is a path that uses every edge of a given graph \<open>E\<close> exactly once. The predicate 
@{const mpath} characterizes a path in a multigraph.

@{thm[display] is_et_def[where T="P"]}

The locale @{locale eulerian} fixes an algorithm (denoted by \<open>comp_et\<close>) that computes an Eulerian 
tour for a given multigraph. This locale could be instantiated with a formalization of Eulers's 
algorithm @{cite "korte_vygen_2018"}.\<close>

subsection \<open>Weighted Matchings and Perfect Matchings\<close>

text \<open>A subgraph \<open>M\<close> is a maximum weight matching for a graph \<open>E\<close> with edge weights \<open>c\<close> if \<open>M\<close> is a 
matching and the total weight of \<open>M\<close> is maximum.

@{lemma[display,source] "is_max_match E c M \<equiv> M \<subseteq> E \<and> matching M 
  \<and> (\<forall>M'. M' \<subseteq> E \<and> matching M' \<longrightarrow> (\<Sum>e\<in>M'. c e) \<le> (\<Sum>e\<in>M. c e))" by (auto simp add: is_max_match_def)}

A subgraph \<open>M\<close> is a perfect matching for a graph \<open>E\<close> if \<open>M\<close> contains every vertex of \<open>E\<close>.

@{thm[display] is_perf_match_def}\<close>
(*<*)
context w_graph_abs
begin
(*>*)
text \<open>A minimum weight perfect matching \<open>M\<close> is a perfect matching with minimum total weight.

@{lemma[display,source] "is_min_match E c M \<equiv> is_perf_match E M 
  \<and> (\<forall>M'. is_perf_match E M' \<longrightarrow> (\<Sum>e\<in>M. c e) \<le> (\<Sum>e\<in>M'. c e))" by (rule is_min_match_def)}\<close>
(*<*)
end
(*>*)
text \<open>The locale @{locale min_weight_matching} fixes an algorithm (denoted by \<open>comp_match\<close>) that 
computes a minimum weight perfect matching for a given graph. For an instantiation of this locale a 
formalization a suitable algorithm is required, e.g. the algorithm described in chapter 11 by 
\citeauthor{korte_vygen_2018} @{cite "korte_vygen_2018"}.\<close>

subsection \<open>Vertex Cover\<close>

text \<open>A vertex cover \<open>X\<close> is a subset of the vertices of a graph \<open>E\<close> s.t. every edge of \<open>E\<close> is 
incident to at least one vertex in \<open>X\<close> .

@{thm[display] is_vc_def}

A minimum vertex cover is a vertex cover with minimum cardinality.

@{thm[display] is_min_vc_def}\<close>
(*<*)
context graph_abs
begin

lemma card_E_leq_max_degree_card_vc_display: 
  "(\<forall>v \<in> Vs E. degree E v \<le> enat k) \<Longrightarrow> is_vc E X \<Longrightarrow> card E \<le> k * card X"
  using card_E_leq_max_degree_card_vc by blast
(*>*)
text \<open>If the degree of every vertex in a graph \<open>E\<close> is bounded by a constant \<open>k\<close>, then the number of 
edges of \<open>E\<close> is at most \<open>k\<close>-times the cardinality of any vertex cover \<open>X\<close> for \<open>E\<close>.

\begin{lemma}\label{lemma:max_degree_bound}
  @{thm[display] card_E_leq_max_degree_card_vc_display}
\end{lemma}\<close>
(*<*)
end
(*>*)

section \<open>Equivalence of the Maximum Weight Matching Problem and the Minimum Weight Perfect Matching Problem\<close>

text \<open>In this section, I go over my formalization of @{cite \<open>Proposition 11.1\<close> "korte_vygen_2018"} 
which shows the equivalence of the \textsc{Maximum Matching Problem} and the 
\textsc{Minimum Matching Problem}.

Similar to the formalization of polynomial time reductions by \citeauthor{wimmer_2021} 
@{cite "wimmer_2021"}, a problem \<open>P\<close> consists of a predicate \<open>is_sol\<close> that characterizes the 
solutions to instances of the problem. The function \<open>is_sol\<close> takes a problem instance and a potential
solution as arguments.

@{datatype[display] prob}

I define the two matching problems: the \textsc{Maximum Matching Problem} and the
\textsc{Minimum Matching Problem}. For a well-formed graph \<open>E\<close> with edge weights \<open>c\<close>, a solution to 
the \textsc{Maximum Matching Problem} is a maximum weight matching (@{const is_max_match}).

@{abbrev[display] P\<^sub>m\<^sub>a\<^sub>x}

If a given well-formed graph \<open>E\<close> with edge weights \<open>c\<close> admits a perfect matching, then a solution to 
the \textsc{Minimum Matching Problem} is a minimum weight perfect matching (@{const is_min_match}). 
Otherwise, the solution is \<open>None\<close>.

@{abbrev[display] P\<^sub>m\<^sub>i\<^sub>n}

If a function \<open>f\<close> returns a solution to every instance of a problem \<open>P\<close>, then the function \<open>f\<close> 
solves the problem \<open>P\<close>. The predicate @{const solves} characterizes functions that solve a 
particular problem.

@{lemma[display] "solves P f \<equiv> \<forall>a. is_sol P a (f a)" by (auto simp add: solves_def)}

Given a function \<open>g\<close> that solves the \textsc{Maximum Matching Problem} we want to solve the 
\textsc{Minimum Matching Problem}. Let \<open>E\<close> be an undirected graph with edge weights \<open>c\<close>. We change 
the edge weights of each edge as follows.

\begin{equation*}
  \text{\<open>c' e = 1 + (\<Sum>e\<in>E. \<bar>c e\<bar>) - c e\<close>}
\end{equation*}

A maximum weight matching for the graph \<open>E\<close> with edge weights \<open>c'\<close> is a minimum weight perfect 
matching for the graph \<open>E\<close> with edge weights \<open>c\<close>. The function \<open>f\<^sub>1\<close> solves the problem \<open>P\<^sub>m\<^sub>i\<^sub>n\<close> and 
takes as an argument a function \<open>g\<close> that solves the problem \<open>P\<^sub>m\<^sub>a\<^sub>x\<close>.

@{lemma[display] "f\<^sub>1 g (E,c) \<equiv> 
  let M = g (E,\<lambda>e. 1 + (\<Sum>e\<in>E. \<bar>c e\<bar>) - c e) in if Vs M = Vs E then Some M else None" by (auto simp add: f\<^sub>1_def)}

Given a function \<open>g\<close> that solves the \textsc{Minimum Matching Problem} we want to solve the 
\textsc{Maximum Matching Problem}. Let \<open>E\<close> be an undirected graph with edge weights \<open>c\<close>. We 
construct a graph \<open>H\<close> by doubling the graph \<open>E\<close> and adding an edge to connect each two copies of the 
same vertex. The function \<open>E\<^sub>H E\<close> construct this graph.

@{lemma[display] "E\<^sub>H E \<equiv> 
  {{(v,i),(w,i)} |v w i. {v,w} \<in> E \<and> i\<in>{1,2}} \<union> {{(v,1),(v,2)} |v. v \<in> Vs E}" by (auto simp add: E\<^sub>H_def)}

The function \<open>c\<^sub>H\<close> defines the edge weights for the constructed graph \<open>H\<close>. The cost of an edge in the 
first copy is its negative original weight. All other edges have no cost.

@{lemma[display] "c\<^sub>H (E,c) e \<equiv> if fst ` e \<in> E \<and> snd ` e = {1::int} then -c (fst ` e) else 0" by (auto simp add: c\<^sub>H_def)}

With the function \<open>g\<close>, we compute a minimum weight perfect matching \<open>M\<close> for the graph \<open>H\<close> with edge 
weights \<open>c\<^sub>H\<close>. The matching \<open>M\<close> is a maximum weight matching for the graph \<open>E\<close> with edge weights \<open>c\<close>. 
The function \<open>f\<^sub>2\<close> solves the problem \<open>P\<^sub>m\<^sub>a\<^sub>x\<close> and takes as an argument a function \<open>g\<close> that solves the 
problem \<open>P\<^sub>m\<^sub>i\<^sub>n\<close>.

@{lemma[display] "f\<^sub>2 g (E,c) \<equiv> case g (E\<^sub>H E,c\<^sub>H (E,c)) of 
  Some M \<Rightarrow> {{v,w} |v w. {(v,(1::nat)),(w,1)} \<in> M}" by (auto simp add: f\<^sub>2_def)}

The main results of the formalization of @{cite \<open>Proposition 11.1\<close> "korte_vygen_2018"} are the 
following two theorems.

\begin{theorem}
  @{thm[display] P\<^sub>m\<^sub>a\<^sub>x_leq_P\<^sub>m\<^sub>i\<^sub>n}
\end{theorem}

\begin{theorem}
  @{thm[display] P\<^sub>m\<^sub>i\<^sub>n_leq_P\<^sub>m\<^sub>a\<^sub>x}
\end{theorem}\<close>

section \<open>Approximaton Algorithms for the \textsc{Metric TSP}\<close>

text \<open>{\sloppy This section describes the formalization of the \textsc{DoubleTree} and the 
\textsc{Christofides-Serdyukov} approximation algorithms for the \textsc{Metric TSP}. Both 
algorithms are quite similar and depend on the following lemma.\par}

\begin{lemma}[{@{cite \<open>Lemma 21.3\<close> "korte_vygen_2018"}}]\label{lemma:comp_hc_of_et}
Let the graph \<open>E\<close> with edge weights \<open>c\<close> be an instance of the \textsc{Metric TSP}. Given a connected 
Eulerian graph \<open>E'\<close> that has the same vertices as the graph \<open>E\<close>, we can compute (in polynomial time) a 
Hamiltonian cycle for \<open>E\<close> with a total weight of at most the total weight of all edges in \<open>E'\<close>.
\end{lemma}
\begin{proof}
The proof is constructive: first compute an Eulerian tour \<open>P\<close> for the Eulerian 
graph \<open>E'\<close>. The tour \<open>P\<close> visits every vertex of \<open>E\<close> at least once, because the Eulerian graph \<open>E'\<close> 
spans the vertices of \<open>E\<close>. Next, the duplicate vertices in the tour \<open>P\<close> are removed to 
obtain the desired Hamiltonian cycle for the graph \<open>E\<close> ("shortcutting"). By assumption, the edge 
weights \<open>c\<close> satisfy the triangle inequality, and thus the total weight of the resulting 
Hamiltonian cycle is at most the total weight of the Eulerian tour \<open>P\<close>, which is exactly the total 
weight of all edges in the Eulerian graph \<open>E'\<close>.
\end{proof}

{\sloppy The construction for Lemma~\ref{lemma:comp_hc_of_et} is formalized with the function 
@{const comp_hc_of_et}. Given an Eulerian tour \<open>P\<close> for \<open>E'\<close>, the function @{const comp_hc_of_et} computes 
a Hamiltonian cycle for \<open>E\<close>. The second argument to the function @{const comp_hc_of_et} is an 
accumulator.\par}\<close>
(*<*)
lemma comp_hc_of_et_simps_display:
  "comp_hc_of_et [] H = H"
  "comp_hc_of_et [u] H = u#H"
  "comp_hc_of_et (u#v#P) H = (if u \<in> set H then comp_hc_of_et (v#P) H else comp_hc_of_et (v#P) (u#H))"
  by (rule comp_hc_of_et.simps)+
(*>*)
text \<open>
@{thm[display] comp_hc_of_et_simps_display}

The function @{const comp_hc_of_et} can be restated using the function @{const remdups} which 
removes duplicates from a list.

@{thm[display] comp_hc_of_et_remdups}\<close>
(*<*)
text \<open>The locale @{locale hc_of_et} extends the locales @{locale metric_graph_abs} and 
@{locale eulerian} and thus assumes the necessary assumptions for the input graph \<open>E\<close>.\<close>
context hc_of_et
begin
(*>*)
text \<open>It is assumed that the multigraph \<open>E'\<close> has the same vertices as the graph \<open>E\<close> and only 
contains edges (maybe multiple instances of an edge) of the graph \<open>E\<close>. Then, the function 
@{const comp_hc_of_et} computes a Hamiltonian cycle for \<open>E\<close>.

\begin{lemma}
  @{lemma[display,source] "is_et E' P \<and> mVs E' = Vs E \<and> set_mset E' \<subseteq> E 
    \<Longrightarrow> is_hc E (comp_hc_of_et P [])" by (auto simp add: hc_of_et_correct)}
\end{lemma}

The following lemma shows that the total weight of the Hamiltonian cycle returned by the function 
@{const comp_hc_of_et} is at most the total weight of the Eulerian tour \<open>P\<close>.
      
\begin{lemma}                   
  @{lemma[display,source] "set P \<subseteq> Vs E 
    \<Longrightarrow> cost_of_path\<^sub>c (comp_hc_of_et P []) \<le> cost_of_path\<^sub>c P" by (rule hc_of_et_reduces_cost)}
\end{lemma}\<close>
(*<*)
end
(*>*)

text \<open>With Lemma~\ref{lemma:comp_hc_of_et}, the task of approximating the \textsc{Metric TSP} boils 
down to constructing an Eulerian graph that spans the vertices of the graph \<open>E\<close>. The total weight 
of the edges of the Eulerian graph directly bounds the total weight of the approximate solution, 
and thus directly affects the approximation-ratio.

{\sloppy Both approximation algorithms, \textsc{DoubleTree} and \textsc{Christofides-Serdyukov}, 
first compute a MST \<open>T\<close> for the graph \<open>E\<close>. Then, edges are added to the MST \<open>T\<close> to construct a 
Eulerian multigraph \<open>E'\<close> that has the same vertices as the graph \<open>E\<close>. The function 
@{const comp_hc_of_et} is then applied to \<open>E'\<close> to obtain a Hamiltonian cycle for \<open>E\<close>.\par}

The polynomial running time of both the \textsc{DoubleTree} and \textsc{Christofides-Serdyukov} are
easy to see and thus explicit proofs are omitted.\<close>

subsection \<open>Formalizing the \textsc{DoubleTree} Algorithm\<close>

text \<open>The \textsc{DoubleTree} algorithm constructs an Eulerian graph by simply doubling every edge 
of a MST \<open>T\<close> for the input graph \<open>E\<close>. Thus, the \textsc{DoubleTree} algorithm consists of three 
steps.
\begin{enumerate}
  \item Compute a MST \<open>T\<close> for the input graph \<open>E\<close>.
  \item Compute an Eulerian tour \<open>P\<close> for the doubled MST \<open>T + T\<close>.
  \item Remove duplicate vertices in \<open>P\<close> by short-cutting (see @{const comp_hc_of_et}).
\end{enumerate}
Thus, the \textsc{DoubleTree} algorithm depends on two algorithms:
\begin{enumerate}
  \item an algorithm to compute a MST and
  \item an algorithm to compute an Eulerian tour in an Eulerian multigraph.
\end{enumerate}
For the formalization of the \textsc{DoubleTree} algorithm the existence of an algorithm for both of 
these problems is assumed. The function \<open>comp_mst\<close> denotes the assumed algorithm to compute a MST, 
and the function \<open>comp_et\<close> denotes the assumed algorithm to compute an Eulerian tour.\<close>
(*<*)
text \<open>The locale @{locale double_tree_algo} extends the locales 
@{locale hc_of_et} and @{locale mst} and thus assumes the existence of the required algorithms. 
The existence of a function \<open>comp_et\<close> to compute an Eulerian tour is already assumed by the 
locale @{locale hc_of_et}.\<close>
context double_tree_algo
begin
(*>*)
text \<open>@{lemma[display,source] "double_tree = (
    let T = comp_mst c E;
        T\<^sub>2\<^sub>x = mset_set T + mset_set T;
        P = comp_et T\<^sub>2\<^sub>x in
          comp_hc_of_et P [])" by (rule double_tree_def)}

For the defined \textsc{DoubleTree} algorithm two properties are proven:
\begin{enumerate*}[label=(\roman*)]
  \item the feasibility, and
  \item the approximation ratio.
\end{enumerate*}
The formalization of these proofs is straightforward. The following lemma proves the feasibility 
of the \textsc{DoubleTree} algorithm. The path returned by the \textsc{DoubleTree} algorithm is 
indeed a Hamiltonian cycle for the graph \<open>E\<close>.

\begin{theorem}
  @{thm[display] dt_is_hc [no_vars]}
\end{theorem}\<close>
(*<*)
end
locale dt_hoare_display = double_tree_algo_approx E c comp_et comp_mst 
  for E and c :: "'a set \<Rightarrow> nat" and comp_et comp_mst + 
  assumes opt: "is_mtsp OPT"
begin
(*>*)
text\<open>The following theorem shows that the approximation ratio of the \textsc{DoubleTree} algorithm is 2. 
The optimal tour for the graph \<open>E\<close> is denoted with \<open>OPT\<close>.

\begin{theorem}
  @{thm[display] dt_approx[no_vars]}
\end{theorem}

The total weight of any Hamiltonian cycle is at least the total weight of the MST \<open>T\<close>. Thus, the 
total weight of the Hamiltonian cycle produced by the \textsc{DoubleTree} algorithm is at most 
double the total weight of the optimal Hamiltonian cycle. Therefore, the 
\textsc{DoubleTree} algorithm is a 2-approximation algorithm for the \textsc{Metric TSP}.\<close>
(*<*)
lemma dt_hoare_display: "VARS T T\<^sub>2 v P P' H { (\<forall>E c. is_connected E \<longrightarrow> is_mst E c (comp_mst c E)) 
      \<and> (\<forall>E. is_eulerian E \<longrightarrow> is_et E (comp_et E)) }
    T := comp_mst c E;
    T\<^sub>2 := mset_set T + mset_set T;
    P := comp_et T\<^sub>2;
    P' := P;
    H := [];
    WHILE P' \<noteq> [] 
    INV { comp_hc_of_et P [] = comp_hc_of_et P' H 
      \<and> P = comp_et T\<^sub>2 
      \<and> T\<^sub>2 = mset_set T + mset_set T 
      \<and> T = comp_mst c E 
      \<and> (\<forall>E c. is_connected E \<longrightarrow> is_mst E c (comp_mst c E)) 
      \<and> (\<forall>E. is_eulerian E \<longrightarrow> is_et E (comp_et E))
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
  done
(*>*)
text\<open>Finally, the definition of the \textsc{DoubleTree} algorithm is refined to a 
\texttt{WHILE}-program using Hoare Logic.

@{lemma[display] "VARS T T\<^sub>2 v P P' H { (\<forall>E c. is_connected E \<longrightarrow> is_mst E c (comp_mst c E)) 
      \<and> (\<forall>E. is_eulerian E \<longrightarrow> is_et E (comp_et E)) }
    T := comp_mst c E;
    T\<^sub>2 := mset_set T + mset_set T;
    P := comp_et T\<^sub>2;
    P' := P;
    H := [];
    WHILE P' \<noteq> [] INV { comp_hc_of_et P [] = comp_hc_of_et P' H 
      \<and> P = comp_et T\<^sub>2
      \<and> T\<^sub>2 = mset_set T + mset_set T 
      \<and> T = comp_mst c E 
      \<and> (\<forall>E c. is_connected E \<longrightarrow> is_mst E c (comp_mst c E)) 
      \<and> (\<forall>E. is_eulerian E \<longrightarrow> is_et E (comp_et E)) } 
    DO
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

text \<open>The \textsc{Christofides-Serdyukov} algorithm is similar to the \textsc{DoubleTree}. Instead 
of doubling a MST \<open>T\<close> for the input graph \<open>E\<close>, the \textsc{Christofides-Serdyukov} algorithm 
computes a minimum perfect matching \<open>M\<close> between the vertices that have odd degree in \<open>T\<close>. The union 
of the matching \<open>M\<close> and the MST \<open>T\<close> is a Eulerian multigraph. Therefore, the 
\textsc{Christofides-Serdyukov} algorithm consists of the following steps.
\begin{enumerate}
  \item Compute a MST \<open>T\<close> for the input graph \<open>E\<close>.
  \item Compute a minimum perfect matching \<open>M\<close> between the vertices that have odd degree in \<open>T\<close>.
  \item Compute a Eulerian tour \<open>P\<close> for the union of the MST and the perfect matching \<open>J = T + M\<close>.
  \item Remove duplicate vertices in \<open>P\<close> by short-cutting (see @{const comp_hc_of_et}).
\end{enumerate}
Hence, the \textsc{Christofides-Serdyukov} algorithm depends on three algorithms: the algorithms the 
\textsc{DoubleTree} algorithm already depends on, as well as an algorithm to compute a minimum 
perfect matching.

The \textsc{Christofides-Serdyukov} algorithm is formalized similarly to the 
\textsc{DoubleTree} algorithm. The function \<open>comp_match\<close> denotes an assumed algorithm that computes 
a minimum perfect matching for a given graph.\<close>
(*<*)
text \<open>The locale @{locale christofides_serdyukov_algo} extends the locale 
@{locale double_tree_algo} and adds the assumption for the existence of an algorithm to compute a 
minimum perfect matching. The function \<open>comp_match\<close> computes a minimum perfect matching for a given 
graph. The definition of the \textsc{Christofides-Serdyukov} algorithm in the 
locale @{locale christofides_serdyukov_algo} is straightforward.\<close>
context christofides_serdyukov_algo
begin
(*>*)
text \<open>@{lemma[display,source] "christofides_serdyukov = (
    let T = comp_mst c E;
        W = {v \<in> Vs T. \<not> even' (degree T v)};
        M = comp_match ({e \<in> E. e \<subseteq> W}) c;
        J = mset_set T + mset_set M;
        P = comp_et J in
          comp_hc_of_et P [])" by (rule christofides_serdyukov_def)}\<close>
(*<*)
end
context christofides_serdyukov_algo_feasibility
begin
(*>*)
text \<open>The feasibility of the \textsc{Christofides-Serdyukov} algorithm is proven by the following lemma. 
The path returned by the \textsc{Christofides-Serdyukov} algorithm is indeed a Hamiltonian cycle.

\begin{theorem}
  @{thm[display] cs_is_hc [no_vars]}
\end{theorem}\<close>
(*<*)
end
locale christofides_serdyukov_hoare_display = 
  christofides_serdyukov_algo_approx _ _ _ _ _  OPT E c comp_mst comp_et comp_match
  for OPT E and c :: "'a set \<Rightarrow> nat" and comp_et comp_mst comp_match
begin
(*>*)
text \<open>{\sloppy The following theorem shows that the approximation ratio of the \textsc{Christofides-Serdyukov} 
algorithm is $\frac{3}{2}$. The optimal tour for the graph \<open>E\<close> is denoted with \<open>OPT\<close>.\par}

\begin{theorem}
  @{thm[display] cs_approx [no_vars]}
\end{theorem}

Let \<open>T\<close> be a MST for the input graph \<open>E\<close> and let \<open>W\<close> denote the vertices with odd degree in the MST 
\<open>T\<close>. The total weight of the Hamiltonian cycle that is computed by the \textsc{Christofides-Serdyukov} 
algorithm has at most the total weight of the MST \<open>T\<close> plus the total weight of the minimum weight 
perfect matching \<open>M\<close> between the vertices \<open>W\<close>. The total weight of the matching \<open>M\<close> is at most half 
the total weight of the optimal Hamiltonian cycle. The number of vertices in \<open>W\<close> is even, thus the 
edges of any Hamiltonian cycle for the vertices \<open>W\<close> can be split into two perfect matchings 
\<open>M\<^sub>1\<close> and \<open>M\<^sub>2\<close>. Therefore, the total weight of the minimum weight perfect matching \<open>M\<close> is at most 
half the total weight of a optimal Hamiltonian cycle for the vertices \<open>W\<close> which is at most the total 
weight of the optimal Hamiltonian cycle for the input graph \<open>E\<close>. Therefore, the 
\textsc{Christofides-Serdyukov} algorithm is a $\frac{3}{2}$-approximation algorithm for the 
\textsc{Metric TSP}.\<close>
(*<*)
lemma cs_hoare_display: "VARS T W M J v P P' H { (\<forall>E c. is_connected E \<longrightarrow> is_mst E c (comp_mst c E)) 
      \<and> (\<forall>E. is_eulerian E \<longrightarrow> is_et E (comp_et E))
      \<and> (\<forall>E c. (\<exists>M. is_perf_match E M) \<longrightarrow> is_min_match E c (comp_match E c)) }
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
      \<and> (\<forall>E c. is_connected E \<longrightarrow> is_mst E c (comp_mst c E)) 
      \<and> (\<forall>E. is_eulerian E \<longrightarrow> is_et E (comp_et E))
      \<and> (\<forall>E c. (\<exists>M. is_perf_match E M) \<longrightarrow> is_min_match E c (comp_match E c))
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
  (* apply (simp add: mst)
  apply (simp add: eulerian)
  apply (simp add: match) *)
  apply (simp add: opt)
  done
(*>*)
text\<open>{\sloppy Like the \textsc{DoubleTree} algorithm, the definition of the \textsc{Christofides-Serdyukov} 
algorithm is refined to a \texttt{WHILE}-program using Hoare Logic.\par}
@{lemma[display] "VARS T W M J v P P' H { (\<forall>E c. is_connected E \<longrightarrow> is_mst E c (comp_mst c E)) 
      \<and> (\<forall>E. is_eulerian E \<longrightarrow> is_et E (comp_et E))
      \<and> (\<forall>E c. (\<exists>M. is_perf_match E M) \<longrightarrow> is_min_match E c (comp_match E c)) }
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
      \<and> (\<forall>E c. is_connected E \<longrightarrow> is_mst E c (comp_mst c E)) 
      \<and> (\<forall>E. is_eulerian E \<longrightarrow> is_et E (comp_et E))
      \<and> (\<forall>E c. (\<exists>M. is_perf_match E M) \<longrightarrow> is_min_match E c (comp_match E c))
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
 
section \<open>L-Reduction from \textsc{VCP4} to \textsc{Metric TSP}\<close>
(*<*)
context VCP4_To_mTSP
begin
(*>*)

text \<open>This section describes the formalization of an L-Reduction from the 
\textsc{Minimum Vertex Cover Problem}, with maximum degree of 4 (\textsc{VCP4}), to the \textsc{Metric TSP}. 
The formalization is based on an L-reduction proof by @{cite \<open>Theorem 21.6\<close> "korte_vygen_2018"}.

The \textsc{Minimum Vertex Cover Problem} describes the optimization problem of finding
a vertex cover with minimum cardinality for a given graph. The \textsc{VCP4} is the restriction of the 
\textsc{Minimum Vertex Cover Problem} to input graphs where the degree of every vertex is bounded by 4.
The bounded degree is only needed to prove the linear inequalities that are required for the L-reduction. 
The \textsc{VCP4} is known to be \textsc{MaxSNP}-hard @{cite \<open>Theorem 16.46\<close> "korte_vygen_2018"}.

First, I define what an L-reduction is.
Let \<open>A\<close> and \<open>B\<close> be optimization problems with cost functions \<open>c\<^sub>A\<close> and \<open>c\<^sub>B\<close>. The cost of the optimal
solution for an instance of an optimization problem is denoted by \<open>OPT(\<cdot>)\<close>.
An L-reduction (linear reduction) consists of a pair of functions \<open>f\<close> and \<open>g\<close> (both computable in 
polynomial time) and two positive constants \<open>\<alpha>,\<beta> > 0\<close> s.t. for every instance \<open>x\<^sub>A\<close> of \<open>A\<close>
\begin{enumerate}[label=(\roman*)]
  \item \<open>f x\<^sub>A\<close> is an instance of \<open>B\<close> s.t. 
    
    @{theory_text "OPT (f x\<^sub>A) \<le> \<alpha>(OPT x\<^sub>A)"}, and
  \item and for any feasible solution \<open>y\<^sub>B\<close> of \<open>f x\<^sub>A\<close>, \<open>g x\<^sub>A y\<^sub>B\<close> is a feasible solution of \<open>x\<^sub>A\<close> s.t.
    
    @{theory_text "\<bar>(c\<^sub>A x\<^sub>A (g x\<^sub>A y\<^sub>B)) - OPT x\<^sub>A\<bar> \<le> \<beta>\<bar>(c\<^sub>B (f x\<^sub>A) y\<^sub>B) - OPT (f x\<^sub>A)\<bar>"}.
\end{enumerate}

The second linear inequality essentially ensures the following: given an optimal solution for \<open>f x\<^sub>A\<close>
the function \<open>g\<close> has to construct an optimal solution for \<open>x\<^sub>A\<close>.

The \textsc{VCP4} is L-reduced to the \textsc{Metric TSP} by defining the functions \<open>f\<close> and \<open>g\<close> and 
proving the feasibility of the functions and the required inequalities.
The function \<open>f\<close> maps an instance of the \textsc{VCP4} to an instance of the \textsc{Metric TSP}. 
An instance of the \textsc{VCP4} consists of a  graph where the degree of every vertex is at most 4.
To construct an instance of the \textsc{Metric TSP}, we construct a complete graph with edge weights 
s.t. the edge weights satisfy the triangle inequality.

\begin{figure}
  \centering
  \begin{tikzpicture}
    \pic[scale=2.0] (uv) at (0,0) {He={$\mathstrut u$}{$\mathstrut v$}};
  \end{tikzpicture}
  \caption{Subgraph \<open>H\<^sub>e\<close> for an edge \<open>e:={u,v}\<close>. Each corner vertex of \<open>H\<^sub>e\<close> corresponds to a vertex of \<open>e\<close>.}\label{fig:He}
\end{figure}

The function \<open>f\<close> is defined by the following construction.
Let \<open>G\<close> be an instance of the \textsc{VCP4}, and let \<open>H:=f G\<close>. For each edge \<open>e\<close> of \<open>G\<close>, a subgraph 
\<open>H\<^sub>e\<close> is added to \<open>H\<close> (see Figure~\ref{fig:He}). The function \<open>f\<close> computes the complete graph over 
all the subgraphs \<open>H\<^sub>e\<close> (one for every edge \<open>e\<close> of the graph \<open>G\<close>). Figure~\ref{fig:l-reduction-graph-H} 
illustrates this construction. A subgraph \<open>H\<^sub>e\<close> consists of 12 vertices that are arranged in a 4-by-3 
lattice. Each corner vertex of a subgraph \<open>H\<^sub>e\<close> corresponds to a vertex of the edge \<open>e\<close>. Moreover, a 
subgraph \<open>H\<^sub>e\<close> has the special property that there is no Hamiltonian path for \<open>H\<^sub>e\<close> that starts and 
ends at corner vertices of \<open>H\<^sub>e\<close> that correspond to different vertices of the edge \<open>e\<close>. E.g. there is 
no Hamiltonian path for the subgraph \<open>H\<^sub>e\<close> that starts at the top-left corner vertex and ends at the 
bottom-right corner vertex. Therefore, the start- and end-vertex of a Hamiltonian path for a 
subgraph \<open>H\<^sub>e\<close> can only correspond to the one vertex of the edge \<open>e\<close>. This property is used to encode 
a vertex cover of \<open>G\<close> with a Hamiltonian cycle of \<open>H\<close>. The subgraph \<open>H\<^sub>e\<close> admits 3 types of 
Hamiltonian paths (see Figure~\ref{fig:Hamiltonian-paths-He}).

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
  \caption{There are three different types of Hamiltonian paths for a subgraph \<open>H\<^sub>e\<close> for an edge \<open>e:={u,v}\<close>. 
  Each corner vertex is labeled with its corresponding vertex of the edge \<open>e\<close>.}\label{fig:Hamiltonian-paths-He}
\end{figure}

Next, I describe the edge weights of the graph \<open>H\<close>. The graph \<open>H\<close> is complete, thus there is an edge 
between every pair of vertices of \<open>H\<close>. Every vertex of \<open>H\<close> belongs to exactly one subgraph \<open>H\<^sub>e\<close>. We 
distinguish between 3 types of edges.
\begin{enumerate}[label=(\roman*)]
  \item An edge that connects two vertices that both belong to the same subgraph \<open>H\<^sub>e\<close> has a weight 
    equal to the distance of the vertices in the subgraph \<open>H\<^sub>e\<close>.
  \item An edge that connects two corner vertices of different subgraphs \<open>H\<^sub>e\<close> and \<open>H\<^sub>f\<close> (\<open>e \<noteq> f\<close>) but 
    both of the vertices correspond to the same vertices \<open>v\<close> of the graph \<open>G\<close> has a weight of 4.
  \item All remaining edges have a weight of 5.
\end{enumerate} 
The edge weights satisfy the triangle inequality because the edge weights can be seen as a metric 
completion of the graph \<open>H\<close> restricted to the edges that have weight 1 or 4.

\begin{figure}
  \centering
  \begin{tikzpicture}[label distance=0mm, scale=1]
    \node[graphNode] (u) at (0,\HeWidth+\HeHeight+\HeMargin) {};
    \node[graphNode,right = of u] (v) {};
    \node[graphNode,below = of u] (w) {};
    \node[graphNode,right = of w] (x) {};
    \path[-] (u) edge (v);
    \path[-] (v) edge (w);
    \path[-] (v) edge (x);
    \path[-] (w) edge (x);

    \path[|->,thick] (2.5,\HeWidth+\HeHeight+\HeMargin-0.5) edge node[label={above:$\mathstrut f$}] {} (3.5,\HeWidth+\HeHeight+\HeMargin-0.5);
  
    \pic (wx) at (5,0) {He={}{}};
    \pic[rotate=-90] (vx) at (5+\HeWidth+\HeMargin,\HeWidth+\HeHeight+\HeMargin) {He={}{}};
    \pic[rotate=45] (wv) at (5+0.146*\HeWidth,\HeMargin+0.146*\HeWidth+\HeHeight) {He={}{}};
    \pic (uv) at (5+-\HeMargin,1.146*\HeWidth+\HeHeight+3*\HeMargin) {He={}{}};

    \begin{scope}[on background layer]
      \draw (uv-v1) edge[edge4] (wv-v1);
      \draw (uv-v1) edge[edge4] (wv-v2);
      \draw (uv-v2) edge[edge4] (wv-v1);
      \draw (uv-v2) edge[edge4] (wv-v2);

      \draw (uv-v1) edge[edge4] (vx-u1);
      \draw (uv-v1) edge[edge4] (vx-u2);
      \draw (uv-v2) edge[edge4] (vx-u1);
      \draw (uv-v2) edge[edge4] (vx-u2);

      \draw (wv-v1) edge[edge4] (vx-u1);
      \draw (wv-v1) edge[edge4] (vx-u2);
      \draw (wv-v2) edge[edge4] (vx-u1);
      \draw (wv-v2) edge[edge4] (vx-u2);

      \draw (wx-u1) edge[edge4] (wv-u1);
      \draw (wx-u1) edge[edge4] (wv-u2);
      \draw (wx-u2) edge[edge4] (wv-u1);
      \draw (wx-u2) edge[edge4] (wv-u2);

      \draw (vx-v1) edge[edge4] (wx-v1);
      \draw (vx-v1) edge[edge4] (wx-v2);
      \draw (vx-v2) edge[edge4] (wx-v1);
      \draw (vx-v2) edge[edge4] (wx-v2);
    \end{scope}
  \end{tikzpicture}
  \caption{Depicted is the construction of the graph \<open>H:=f G\<close> from the graph \<open>G\<close>. The graph 
  \<open>H\<close> is complete, but only the edges with weight 1 or 4 are shown.}\label{fig:l-reduction-graph-H}
\end{figure}

Next, I describe the definition of the function \<open>g\<close>.
The function \<open>g\<close> maps a Hamiltonian cycle \<open>T\<close> in \<open>H\<close> to a vertex cover \<open>X\<close> of \<open>G\<close>. 
By the construction of \<open>H\<close>, the Hamiltonian cycle \<open>T\<close> may be 
composed of only Hamiltonian paths for the subgraphs \<open>H\<^sub>e\<close>. In this case, for each edge \<open>e\<close> of \<open>G\<close> 
the covering vertex of \<open>e\<close> is identified by looking at the Hamiltonian path for the subgraph \<open>H\<^sub>e\<close> 
that is contained in \<open>T\<close>. The Hamiltonian path of the subgraph \<open>H\<^sub>e\<close> can only 
correspond to one vertex of the edge \<open>e\<close>. This vertex is selected as the covering vertex for 
the edge \<open>e\<close>. If the Hamiltonian cycle \<open>T\<close> does not contain a Hamiltonian path for every subgraph \<open>H\<^sub>e\<close>, 
a Hamiltonian cycle \<open>T'\<close> for \<open>H\<close> is constructed. The Hamiltonian cycle \<open>T'\<close> contains a Hamiltonian 
path for every subgraph \<open>H\<^sub>e\<close> and the total cost of \<open>T'\<close> is at most the total cost of \<open>T\<close>. The 
Hamiltonian cycle \<open>T'\<close> is constructed by carefully replacing parts of \<open>T\<close> with a Hamiltonian path 
for a subgraph \<open>H\<^sub>e\<close>.\<close>

subsection \<open>Formalizing the L-Reduction\<close>

text \<open>The locale @{locale ugraph_adj_map} provides an abstract adjacency map that serves as a graph 
representation that allows for the implementation of executable functions on graphs. The locale 
@{locale ugraph_adj_map} can be instantiated with an implementation for sets (locale @{locale Set2}) 
and maps (locale @{locale Map}) to obtain executable functions on graphs.\<close>
(*<*)
text \<open>The necessary graph-related definitions are redefined for 
the adjencecy map representation of graphs (see theory @{file "./graphs/GraphAdjMap_Specs.thy"}). 
The definitions for the adjencecy-map representation of graphs are denoted by the postfix \<open>-Adj\<close>.\<close>
end
context ugraph_adj_map
begin
(*>*)
text \<open>The set of undirected edges of a graph is returned by the function \<open>E(\<cdot>)\<close>. A assumed linear 
order on the vertices is used to identify different instances of the same undirected edge.\<close>
(*<*)
end
context VCP4_To_mTSP
begin
(*>*)
text \<open>{\sloppy The L-reduction itself is formalized in the locale @{locale VCP4_To_mTSP} that depends on two 
executable adjacency-maps (locale @{locale ugraph_adj_map}), one for each of the graphs \<open>G\<close> and \<open>H\<close> 
which are denoted by \<open>g1\<close> and \<open>g2\<close>. The locale @{locale VCP4_To_mTSP} also assumes functions that 
provide \texttt{fold}-operations for the graphs. The reduction functions \<open>f\<close> and \<open>g\<close> are defined in 
the locale @{locale VCP4_To_mTSP} using the assumed \texttt{fold}-operations and some auxiliary 
functions. The theory @{file "reductions/VertexCover4ToMetricTravelingSalesman_AdjList.thy"} 
instantiates the locale @{locale VCP4_To_mTSP} with an implementation of an adjacency list to obtain 
executable instantiations of the functions \<open>f\<close> and \<open>g\<close>. This formalization approach is adapted from 
\citeauthor{abdulaziz_2022} @{cite "abdulaziz_2022"}, who formalized the Depth-first search with 
this approach.\par}

The vertices of the subgraphs \<open>H\<^sub>e\<close> are represented with a triple \<open>(e,w,i)\<close> where \<open>w\<close> is a vertex of 
the edge \<open>e\<close> and \<open>i \<in> {1..6}\<close> is an index. Figure~\ref{fig:He-formalization} shows the 
formalization of a subgraph \<open>H\<^sub>e\<close>. The vertices of the subgraph \<open>H\<^sub>e\<close> have to be named such that the 
subgraph is symmetric, i.e. \<open>H\<^sub>{\<^sub>u\<^sub>,\<^sub>v\<^sub>}=H\<^sub>{\<^sub>v\<^sub>,\<^sub>u\<^sub>}\<close> because \<open>{u,v}\<close> is an undirected edge. 

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
The definition of the function \<open>c\<close> uses a couple of auxiliary functions to distinguish different cases. 
To simplify things, the case for two vertices that are neighbors in subgraph \<open>H\<^sub>e\<close> (weight 1) is handled separately. 
The function @{const is_edge_in_He} checks if there is a subgraph \<open>H\<^sub>e\<close> in \<open>H\<close> where the two 
given vertices are connected by an edge. The function \<open>fold_g1_uedges2\<close> folds the edges of graph \<open>G\<close>. 
The expression @{term "isin2 (\<N>\<^sub>2 (H\<^sub>e e) x) y"} checks if the vertex \<open>y\<close> is in the neighborhood of 
the vertex \<open>x\<close> in the subgraph \<open>H\<^sub>e\<close>.

@{thm[display] is_edge_in_He.simps}

The function @{const are_vertices_in_He} checks if there is a subgraph \<open>H\<^sub>e\<close> in \<open>H\<close> that contains 
both given vertices. The expression @{term "isin2 (V\<^sub>H\<^sub>e e) x \<and> isin2 (V\<^sub>H\<^sub>e e) y"} 
checks if \<open>x\<close> and \<open>y\<close> are vertices in the subgraph \<open>H\<^sub>e\<close>.

@{thm[display] are_vertices_in_He.simps}

The function @{const min_dist_in_He} computes the distance between two
vertices in a subgraph \<open>H\<^sub>e\<close>. The function \<open>rep1\<close> is an assumed function that is used to identify 
different instances of undirected edges. 

@{thm[display] c.simps}

The function \<open>g\<close> depends on two functions @{const shorten_tour} and @{const vc_of_tour}. The 
function @{const shorten_tour} modifies a Hamiltonian cycle s.t. the resulting tour has less total 
weight and the tour contains a Hamiltonian path for every subgraph \<open>H\<^sub>e\<close>. Given a tour \<open>T\<close> of \<open>H\<close>, 
the function @{const shorten_tour} iteratively (for each edge \<open>e\<close> of \<open>G\<close>) removes all vertices of 
the subgraph \<open>H\<^sub>e\<close> from the tour \<open>T\<close> and inserts a Hamiltonian path for the subgraph \<open>H\<^sub>e\<close>. 
The Hamiltonian path is inserted at the position where the tour \<open>T\<close> enters the subgraph \<open>H\<^sub>e\<close> for the 
first time. This replacement of the Hamiltonian path is done regardless of whether the tour \<open>T\<close> 
already contains a Hamiltonian path for the subgraph \<open>H\<^sub>e\<close>. This simplifies definitions and proofs 
by avoiding extra case distinctions. The inserted Hamiltonian path for the subgraph \<open>H\<^sub>e\<close> is 
carefully chosen such that the resulting tour has less total weight. Let \<open>e:={u,v}\<close>, and see 
Figure~\ref{fig:He-formalization} for the naming of the vertices in the subgraph \<open>H\<^sub>e\<close>.
\begin{enumerate}
  \item If the tour \<open>T\<close> does not contain a Hamiltonian path for the subgraph \<open>H\<^sub>e\<close> then the 
    Hamiltonian path that starts at \<open>(e,u,1)\<close> and ends at \<open>(e,u,2)\<close> is inserted.
  \item If the Hamiltonian path for \<open>H\<^sub>e\<close> in the tour \<open>T\<close> starts at a corner vertex 
    \<open>(e,w,i)\<close>, with \<open>i\<in>{1,2}\<close> and \<open>w\<in>{u,v}\<close>, then the Hamiltonian path in the tour \<open>T\<close> is replaced 
    with the Hamiltonian path that starts at \<open>(e,w,i)\<close> and ends at \<open>(e,w,j)\<close>, where \<open>j\<in>{1,2}-{i}\<close>.
  \item If the Hamiltonian path for \<open>H\<^sub>e\<close> in the tour \<open>T\<close> ends at a corner vertex 
    \<open>(e,w,i)\<close>, with \<open>i\<in>{1,2}\<close> and \<open>w\<in>{u,v}\<close>, then the Hamiltonian path in the tour \<open>T\<close> is replaced 
    with the Hamiltonian path that starts at \<open>(e,w,j)\<close> and ends at \<open>(e,w,i)\<close>, where \<open>j\<in>{1,2}-{i}\<close>.
  \item Otherwise, the Hamiltonian path that starts at \<open>(e,u,1)\<close> and ends at \<open>(e,u,2)\<close> is inserted.
\end{enumerate}
This construction is implemented with the following functions. Given a part of tour @{term "x#T"} 
in the graph \<open>H\<close>, the function @{const to_covering_vertex} computes a covering vertex for the edge 
\<open>e\<close> in the graph \<open>G\<close> for which the subgraph \<open>H\<^sub>e\<close> contains the vertex \<open>x\<close>. 

@{thm[display] to_covering_vertex.simps}

The function @{const hp_starting_at} returns a Hamiltonian path for the subgraph \<open>H\<^sub>e\<close> which 
contains the vertex \<open>x\<close>. @{const hp_u1} and @{const hp_v1} are Hamiltonian paths for the subgraph \<open>H\<^sub>e\<close>.

@{thm[display] hp_starting_at.simps}

The function @{const replace_hp} iteratively replaces parts of a given tour with Hamiltonian paths 
for each subgraph \<open>H\<^sub>e\<close>.

@{thm[display] replace_hp.simps}

The function @{const shorten_tour} formalizes property (b) from the L-reduction proof in 
@{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"}.

@{thm[display] shorten_tour.simps}

The function @{const rotate_tour} rotates a cycle until a given predicate is satisfied.

@{thm[display] rotate_tour_acc.simps}

@{thm[display] rotate_tour.simps}\<close>
(*<*)
end
locale fixed_adj_map_G = VCP4_To_mTSP +
  fixes G OPT\<^sub>V\<^sub>C X
  assumes G_assms: "g1.ugraph_adj_map_invar G" "card (g1.uedges G) > 1"
  and opt_mtsp: "g2.is_tsp_Adj (f G) (c G) OPT\<^sub>H"
  and opt_vc: "g1.is_min_vc_Adj G OPT\<^sub>V\<^sub>C" "set_invar1 OPT\<^sub>V\<^sub>C" "card1 OPT\<^sub>V\<^sub>C > 1"
  and max_degree: "\<And>v. v \<in> g1.vertices G \<Longrightarrow> g1.degree_Adj G v \<le> enat 4"
  and invar_X: "card1 X > 1" "set_invar1 X"
begin

abbreviation "cost_of_path\<^sub>c \<equiv> cost_of_path (c G)"
notation card1 ("|_|")
notation g1.uedges ("E'(_')")
notation g1.is_vc_Adj ("is'_vc")
notation g2.is_complete_Adj ("is'_complete")
notation g2.is_hc_Adj ("is'_hc")

lemma f_is_complete_display: "g2.is_complete_Adj (f G)"
  using G_assms(1) by (rule f_is_complete)

lemma g_is_vc_display: "g2.is_hc_Adj (f G) T \<Longrightarrow> g1.is_vc_Adj G (g G T)"
  using G_assms by (rule g_is_vc)

lemma cost_shorten_tour_leq_display:
  "g2.is_hc_Adj (f G) T \<Longrightarrow> cost_of_path (c G) (shorten_tour G T) \<le> cost_of_path (c G) T"
  using G_assms(1,2) opt_vc cost_shorten_tour_leq by auto

(*>*)
text \<open>The following lemma proves the fact that the tour computed by @{const shorten_tour} has less 
total weight than the given tour \<open>T\<close>.

\begin{lemma}\label{lemma:shorten_tour_cost}
  @{theory_text[display,source] "is_hc (f G) T \<Longrightarrow> 
    cost_of_path\<^sub>c (shorten_tour G T) \<le> cost_of_path\<^sub>c T"}
\end{lemma}

If the tour \<open>T\<close> does not contain a Hamiltonian path for a subgraph \<open>H\<^sub>e\<close> then there are at least 4 
edges between vertices of the subgraph \<open>H\<^sub>e\<close> and other vertices of the graph \<open>H\<close>. These edges have at 
least weight 4 are replaced with 2 edges that have a weight of at most 5. If the tour \<open>T\<close> does 
already contain a Hamiltonian path for a subgraph \<open>H\<^sub>e\<close> then it is ensured by the construction that 
the 2 edges between vertices of the subgraph \<open>H\<^sub>e\<close> and other vertices of the graph \<open>H\<close> are replaced 
with edges that have the same weight.\<close>
(*<*)
end
context VCP4_To_mTSP
begin
(*>*)
text \<open>The function @{const vc_of_tour} computes a vertex cover for \<open>G\<close> from a given Hamiltonian cycle 
that contains a Hamiltonian path for every subgraph \<open>H\<^sub>e\<close>. This is done by recursively identifying a 
covering vertex for the next subgraph \<open>H\<^sub>e\<close> with the function @{const to_covering_vertex}.

@{thm[display] vc_of_tour.simps}

@{thm[display] g.simps}\<close>

subsection \<open>Proofs for the L-Reduction\<close>
(*<*)
end
context fixed_adj_map_G 
begin
(*>*)
text \<open>The locale @{locale VCP4_To_mTSP} contains the proofs for the feasibility of the reduction 
functions and the linear inequalities required for the L-reduction.\<close>
text \<open>The function \<open>f\<close> constructs a complete graph.

\begin{theorem}
  @{thm[display] f_is_complete_display}
\end{theorem}
                             
Given Hamiltonian cycle \<open>T\<close>, the function \<open>g\<close> selects, for each edge \<open>e\<close> of \<open>G\<close>, a vertex
to be included in the result. Thus, the function \<open>g\<close> computes a vertex cover for \<open>G\<close> given a 
Hamiltonian cycle \<open>T\<close> for \<open>H\<close>.

\begin{theorem}
  @{thm[display] g_is_vc_display}
\end{theorem}\<close>
(*<*)
end
context fixed_adj_map_G
begin

lemma cost_of_opt_mTSP_display: "cost_of_path (c G) OPT\<^sub>H \<le> 15 * int (card (g1.uedges G)) + card1 OPT\<^sub>V\<^sub>C"
  using G_assms opt_vc opt_mtsp by (rule cost_of_opt_mTSP)
                                                                        
lemma hp_of_vc_display:
  "g1.is_vc_Adj G X \<Longrightarrow> 
    \<exists>T. g2.is_hc_Adj (f G) T \<and> cost_of_path (c G) T \<le> 15 * int (card (g1.uedges G)) + card1 X"
  using invar_X hp_of_vc[OF G_assms] by blast

(*>*)
text \<open>Next, I describe the proofs for the linear inequalities that are required for the L-reduction. 
But first, I prove two necessary lemmas.

I prove an upper bound for the total cost of the optimal Hamiltonian cycle for the graph \<open>H\<close>. This 
lemma corresponds to the property (a) that is used by the L-reduction proof in @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"}. 
Let \<open>OPT\<^sub>H\<close> be an optimal Hamiltonian cycle for \<open>H\<close> and let \<open>OPT\<^sub>V\<^sub>C\<close> be an optimal vertex cover for \<open>G\<close>.
An upper bound for the total cost of \<open>OPT\<^sub>H\<close> is given by the following inequality.

\begin{lemma}\label{lemma:cost_of_opt_mTSP}
  @{thm[display] cost_of_opt_mTSP_display}
\end{lemma}

To prove this lemma, we construct a Hamiltonian cycle \<open>T\<close> for \<open>H\<close> from the optimal vertex cover 
\<open>OPT\<^sub>V\<^sub>C\<close> for \<open>G\<close>. The total cost of \<open>T\<close> is at least the total cost of the optimal Hamiltonian cycle \<open>OPT\<^sub>H\<close>. The 
Hamiltonian cycle \<open>T\<close> traverses each subgraph \<open>H\<^sub>e\<close> with the Hamiltonian path that starts and ends at 
the corner vertices that correspond to the covering vertex of \<open>e\<close> in the vertex cover \<open>OPT\<^sub>V\<^sub>C\<close>. 
There are @{term "card (g1.uedges G)"} many subgraph \<open>H\<^sub>e\<close> and each Hamiltonian path for a subgraph 
\<open>H\<^sub>e\<close> has a total cost of 11. We now need to add @{term "card (g1.uedges G)"} many edges to connect 
the start- and end-vertices of the Hamiltonian paths to form a Hamiltonian cycle for \<open>H\<close>. We pick as 
many edges with weight 4 ("cheaper" edges) as possible. For the remaining connections, we use 
"expensive" edges with a weight of 5. It turns out we can select at most 
@{term "(card (g1.uedges G) - card1 OPT\<^sub>V\<^sub>C)"} many edges of weight 4. Thus, the total weight of the 
constructed Hamiltonian cycle \<open>T\<close> is bounded by the following expression.
\begin{multline*}
  \text{@{term "11 * card (g1.uedges G) + 4 * (card (g1.uedges G) - card1 OPT\<^sub>V\<^sub>C) + 5 * card1 OPT\<^sub>V\<^sub>C"}} \\
  = \text{@{term "15 * card (g1.uedges G) + card1 OPT\<^sub>V\<^sub>C"}}
\end{multline*}
Essentially, the number of "expensive" edges in the Hamiltonian cycle \<open>T\<close> for \<open>H\<close> corresponds to the 
cardinality of the vertex cover for \<open>G\<close>. The generalization of this construction for an arbitrary 
vertex cover \<open>X\<close> is formalized by the following lemma. 

\begin{lemma}\label{lemma:hp_of_vc}
  @{theory_text[display,source] "is_vc G X \<Longrightarrow> 
    \<exists>T. is_hc (f G) T \<and> cost_of_path\<^sub>c T \<le> 15 * |E(G)| + |X|"}
\end{lemma}\<close>
(*<*)
text \<open>\begin{lemma}\leavevmode
  @{thm[display] hp_of_vc_display}
\end{lemma}\<close>
end
context fixed_adj_map_G
begin

lemma card_g_leq_k_display: 
  "g2.is_hc_Adj (f G) T \<Longrightarrow> \<exists>k. card1 (g G T) \<le> k \<and> 15 * int (card (g1.uedges G)) + k \<le> cost_of_path (c G) T"
  using card_g_leq_k[OF G_assms opt_vc] by blast

(*>*)
text \<open>Another property that is required for the proof of the linear inequalities of the L-reduction 
is an upper bound for the cardinality of the vertex cover that is constructed by the function \<open>g\<close>.
The following lemma corresponds to the property (c) that is used by the L-reduction proof in @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"}.
\begin{lemma}\label{lemma:card_g_leq_k}
  @{theory_text[display,source] "is_hc (f G) T \<Longrightarrow> 
    \<exists>k\<ge>|g G T|. 15 * |E(G)| + k \<le> cost_of_path\<^sub>c T"}
\end{lemma}

Intuitively, this follows from the fact that the cardinality of the vertex cover that is computed by \<open>g\<close> can be at most 
the number of "expensive" edges in a Hamiltonian cycle \<open>T\<close> of \<open>H\<close>. This follows from the fact that any 
two edges \<open>e\<close> and \<open>f\<close> in \<open>G\<close> (\<open>e \<noteq> f\<close>), where the subgraphs \<open>H\<^sub>e\<close> and \<open>H\<^sub>f\<close> are connected by a "cheap" 
edge in \<open>T\<close>, are covered by the same vertex in the vertex cover \<open>(g G T)\<close>. Thus, there can only be 
different covering vertices if two subgraphs are connected by an "expensive" edge.\<close>
(*<*)
text \<open>
\begin{lemma}\label{lemma:card_g_leq_k}\leavevmode
  @{thm[display] card_g_leq_k_display}
\end{lemma}\<close>
lemma l_reduction1_display: "cost_of_path (c G) OPT\<^sub>H \<le> 61 * card1 OPT\<^sub>V\<^sub>C"
  using G_assms max_degree opt_vc opt_mtsp by (rule l_reduction1)

lemma l_reduction2_display:
  "g2.is_hc_Adj (f G) T \<Longrightarrow> 
    \<bar> card1 (g G T) - card1 OPT\<^sub>V\<^sub>C \<bar> \<le> 1 * \<bar> cost_of_path (c G) T - cost_of_path (c G) OPT\<^sub>H \<bar>" 
  using G_assms opt_vc opt_mtsp by (rule l_reduction2)
(*>*)
text \<open>With Lemma~\ref{lemma:cost_of_opt_mTSP} we prove the first linear inequality required for 
the L-reduction. By assumption, the degree of every vertex in \<open>G\<close> is at most 4. From 
Lemma~\ref{lemma:max_degree_bound}, we conclude that the number of edges of \<open>G\<close> is at most 4-times 
the cardinality of optimal vertex cover \<open>OPT\<^sub>V\<^sub>C\<close> of \<open>G\<close>. The following chain of inequalities derives 
the first inequality required for the L-reduction.
\begin{align*}
  \text{@{term "cost_of_path (c G) OPT\<^sub>H"}} & \leq\text{@{term "15 * int (card (g1.uedges G)) + card1 OPT\<^sub>V\<^sub>C"}} \\
  & \leq\text{@{term "15 * (4 * card1 OPT\<^sub>V\<^sub>C) + card1 OPT\<^sub>V\<^sub>C"}} \\
  & \leq\text{@{term "61 * card1 OPT\<^sub>V\<^sub>C"}}
\end{align*}
The following theorem states the first inequality required for the L-reduction. 
\begin{theorem}
  @{thm[display] l_reduction1_display}
\end{theorem}
The second inequality for the L-reduction follows from Lemma~\ref{lemma:cost_of_opt_mTSP} and 
Lemma~\ref{lemma:card_g_leq_k}. The following chain of inequalities derives the second linear 
inequality for the L-reduction.
\begin{align*}
  \text{@{term "\<bar> card1 (g G T) - card1 OPT\<^sub>V\<^sub>C \<bar>"}} & \leq\text{@{term "\<bar> k - card1 OPT\<^sub>V\<^sub>C \<bar>"}} \\
  & =\text{@{term "\<bar> 15 * int (card (g1.uedges G)) + k - 15 * int (card (g1.uedges G)) - card1 OPT\<^sub>V\<^sub>C \<bar>"}} \\
  & \leq\text{@{term "\<bar> cost_of_path (c G) T - cost_of_path (c G) OPT\<^sub>H \<bar>"}}
\end{align*}
{\sloppy The following theorem states the second inequality required for the L-reduction.\par}
\begin{theorem}
  @{lemma[display,source] "is_hc (f G) T 
    \<Longrightarrow> \<bar>|g G T| - |OPT\<^sub>V\<^sub>C|\<bar> \<le> 1 * \<bar>cost_of_path\<^sub>c T - cost_of_path\<^sub>c OPT\<^sub>H\<bar>" by (rule l_reduction2_display)}
\end{theorem}\<close>
(*<*)
end
context VCP4_To_mTSP
begin
(*>*)

subsection \<open>Incompleteness and Unfinished Business\<close>

text \<open>In this section, I point out two cases that are not covered in the L-reduction proof by 
@{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"}. I also describe the parts of my formalization that are 
not finished.

The L-reduction proof that is presented in @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} is incomplete 
and does not cover the following cases. 
\begin{enumerate}[label=(\roman*)]
  \item {The proof by @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} fails if the optimal vertex cover 
    of \<open>G\<close> has a cardinality of 1. In this case, the upper-bound for optimal Hamiltonian cycle for 
    \<open>H\<close> does not hold (Lemma~\ref{lemma:cost_of_opt_mTSP}). The construction for the L-reduction 
    still works in this case, but the proofs for this case need to be considered separately. I 
    circumvent this problem by explicitly excluding this case through an additional assumption. 
    Formalizing the proof for this case should be straightforward.}
  \item {The proof for @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} fails to cover all cases when 
    constructing the vertex cover for \<open>G\<close> from a Hamiltonian cycle \<open>T\<close> for \<open>H\<close> (function \<open>g\<close>). There 
    are different types of Hamiltonian paths for a subgraph \<open>H\<^sub>e\<close> that do not start or end at corner 
    vertices of the subgraph \<open>H\<^sub>e\<close> (see Figures~\ref{fig:Hamiltonian-paths-He}). In @{cite "korte_vygen_2018"}, 
    it is only described how to pick a covering vertex if the Hamiltonian path for the corresponding 
    subgraph \<open>H\<^sub>e\<close> starts and ends at a corner vertex of the subgraph \<open>H\<^sub>e\<close>. For some Hamiltonian 
    paths that do not start or end at corners of the subgraph \<open>H\<^sub>e\<close>, it is not immediately clear 
    which covering vertex to choose. Nevertheless, I have solved this issue by extending the 
    definition of the function \<open>g\<close>. The definition of the function \<open>g\<close> described in @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} 
    only replaces parts of the given tour \<open>T\<close> with a Hamiltonian path for a subgraph \<open>H\<^sub>e\<close> when the 
    tour \<open>T\<close> does not already contain a Hamiltonian path for the subgraph \<open>H\<^sub>e\<close>. Thus, the resulting 
    tour may contain Hamiltonian paths for the subgraphs \<open>H\<^sub>e\<close> that do not start or end at corner 
    vertices of the subgraph \<open>H\<^sub>e\<close>. Therefore, the construction of the vertex cover for \<open>G\<close> from the 
    modified tour \<open>T'\<close> would require an extra case distinction to handle the different types of 
    Hamiltonian paths for the subgraphs \<open>H\<^sub>e\<close>. The required case distinction is not made in @{cite"korte_vygen_2018"}. 
    On the other hand, I defined the function \<open>g\<close> using the function @{const shorten_tour} which 
    explicitly covers these cases.
    
    The proof in @{cite \<open>Theorem 21.1\<close> "korte_vygen_2018"} references a proof by @{cite "papadimitriou_yannakakis_1993"} 
    that uses a similar construction to prove the \textsc{MaxSNP}-harness of a restricted version 
    of the \textsc{Metric TSP}, where the values of the edge weights are restricted to only 1 or 2. 
    Because of the restricted edge weights, the proof by @{cite "papadimitriou_yannakakis_1993"} 
    does not have this issue.}
\end{enumerate}

Two aspects make my formalization of the L-reduction incomplete. Firstly, I have not 
finished the proof that shows that a subgraph \<open>H\<^sub>e\<close> only admits the three types of Hamiltonian paths 
depicted in Figure~\ref{fig:Hamiltonian-paths-He}. The theory @{file "./reductions/FindHamiltonianPath.thy"} 
contains an instantiation of a suitable lemma with an executable graph representation. By exhaustive 
search, the instantiated lemma is proven. This result needs to be transferred to the reduction proof. 
At the moment I am not sure what the best way to do this is. Previously, I have also attempted 
to prove this by coming up with an abstract lemma about paths in a subgraph \<open>H\<^sub>e\<close>. My goal was to use 
this abstract lemma, to prove that there is no Hamiltonian path that starts and ends at vertices on 
opposing sides of the subgraph. Unfortunately, I did not have success with this approach.

Secondly, I have not formally proven the polynomial running times of the functions \<open>f\<close> and \<open>g\<close>. To 
formally reason about running times a formal computational model is required. The imperative language 
\texttt{IMP-} provides such a computational model. A possible approach is to refine instantiations 
of the functions \<open>f\<close> and \<open>g\<close> to \texttt{IMP-}. Ultimately, the running times of the refined 
functions would be proven. For this a separate recurrence that counts the number of operations in a 
function call is defined. The counted number of operations is then bounded by the running time of 
the function.\<close>
(*<*)
end
(*>*)

(* ----- *)
 
section \<open>Future Work and Conclusion\<close>

text \<open>In this work, I present my formalization of parts of section 21.1, \textit{Approximation 
Algorithms for the TSP} from @{cite "korte_vygen_2018"} with the interactive theorem prover 
Isabelle/HOL. I continue the work of @{cite "essmann_et_al_2020"} by formalizing and formally 
verifying two approximation algorithms for the \textsc{Metric TSP}: the \textsc{DoubleTree} and the 
\textsc{Christofides-Serdyukov} algorithm. For that, I build on the formalization of graphs by 
\citeauthor{abdulaziz_2020} @{cite "abdulaziz_2020"}. I formalize many graph-related concepts in 
Isabelle/HOL, such as weighted graphs, Eulerian Tours, or Hamiltonian cycles. Moreover, I formalize 
an L-reduction from the \textsc{VCP4} to the \textsc{Metric TSP}. Thereby, I present an approach to 
formalize an L-reduction in Isabelle/HOL. To my knowledge, this is the first formalization of an 
L-reduction in Isabelle/HOL. A consequence of the L-reduction is that the \textsc{Metric TSP} is 
\textsc{MaxSNP}-hard and thus there cannot be an approximation scheme for the \textsc{Metric TSP} 
unless $\textsc{P}=\textsc{NP}$.

To formalize the L-reduction it is necessary to verify executable functions on graphs. 
For that, I use an abstract graph representation that is based on an adjacency map. The graph 
representation is instantiated with a concrete implementation to obtain executable functions on 
graphs. This approach is versatile and can be applied when reasoning about executable functions on 
graphs.

{\sloppy Future work includes proving the existence of the necessary algorithms for the \textsc{DoubleTree} 
and \textsc{Christofides-Serdyukov} algorithm. Therefore, formalizations of algorithms to compute 
a MST, a minimum perfect matching, and an Eulerian tour are needed. I have started (but not finished) 
to implement an adaptor between my formalization and the formalization of Prim's algorithm in 
Isabelle/HOL by \citeauthor{lammich_nipkow_2019} @{cite "lammich_nipkow_2019"}. In chapter 11 
\citeauthor{korte_vygen_2018} @{cite "korte_vygen_2018"} describe an algorithm to compute minimum 
perfect matchings. Euler's algorithm @{cite "korte_vygen_2018"} is a suitable algorithm to compute 
a Eulerian tour.\par}

Furthermore, the Eulerian graphs that are constructed for the \textsc{DoubleTree} and the
\textsc{Christofides-Serdyukov} algorithm generally are multigraphs. Therefore, a formalization of 
multigraphs is required. In the theory @{file "./graphs/MultiGraph.thy"}, I have started (but not 
finished) to formalize an encoding of multigraphs with simple graphs.

{\sloppy For the L-reduction, it is required to prove the polynomial running time of the reduction functions 
\<open>f\<close> and \<open>g\<close>. This can be done by refining the functions to a programming language that provides a
computational model, e.g. \texttt{IMP-} @{cite "wimmer_2021"}. The running times could then be proven 
with the refined functions.\par}\<close>
(*<*)
text \<open>Moreover, the proof that the subgraph \<open>H\<^sub>e\<close> only admits certain Hamiltonian paths has to be
finished.\<close>
end
(*>*)