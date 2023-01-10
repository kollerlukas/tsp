theory VC4_to_mTSP_abs_old
  imports Main tsp.Misc tsp.Berge tsp.GraphExec 
  "HOL-Data_Structures.Map_Specs" "HOL-Data_Structures.Set_Specs"
  tsp.CompleteGraph tsp.TravelingSalesman tsp.VertexCover
begin

(* ----- TODO ----- *)

text \<open>
({u,v},u,1) --- ({u,v},u,5) --- ({u,v},v,2)
     |                               |
({u,v},u,3) --- ({u,v},u,6) --- ({u,v},v,4)
     |                               |
({u,v},u,4) --- ({u,v},v,6) --- ({u,v},v,3)
     |                               |
({u,v},u,2) --- ({u,v},v,5) --- ({u,v},v,1)
\<close>

abbreviation "H\<^sub>e e \<equiv> (case e of uEdge u v \<Rightarrow> 
  [((e,u,1::nat),[(e,u,3),(e,u,5)]),
  ((e,u,2),[(e,u,4),(e,v,5)]),
  ((e,u,3),[(e,u,1),(e,u,4),(e,u,6)]),
  ((e,u,4),[(e,u,2),(e,u,3),(e,v,6)]),
  ((e,u,5),[(e,u,1),(e,v,2)]),
  ((e,u,6),[(e,u,3),(e,v,4)]),
  ((e,v,1),[(e,v,3),(e,v,5)]),
  ((e,v,2),[(e,v,4),(e,u,5)]),
  ((e,v,3),[(e,v,1),(e,v,4),(e,v,6)]),
  ((e,v,4),[(e,v,2),(e,v,3),(e,u,6)]),
  ((e,v,5),[(e,v,1),(e,u,2)]),
  ((e,v,6),[(e,v,3),(e,u,4)])])"

abbreviation "Vs_H\<^sub>e e \<equiv> (case e of uEdge u v \<Rightarrow> 
  [(e,u,1::nat),(e,u,2),(e,u,3),(e,u,4),(e,u,5),(e,u,6),
  (e,v,1),(e,v,2),(e,v,3),(e,v,4),(e,v,5),(e,v,6)])" \<comment> \<open>Vertices of a subgraph that corresponds to the edge \<open>e\<close>.\<close>

fun f_exec :: "'a graph_adj_list \<Rightarrow> ('a uedge \<times> 'a \<times> nat) graph_adj_list" where
  "f_exec G = (let V = concat (map Vs_H\<^sub>e (uedge_list G)) \<comment> \<open>Compute vertices of graph.\<close> in
    compl_graph_exec V) \<comment> \<open>Compute a complete graph for a given set of vertices.\<close>"

fun edge_in_He :: "'a graph_adj_list \<Rightarrow> ('a uedge \<times> 'a \<times> nat) uedge \<Rightarrow> bool" where \<comment> \<open>The function \<open>c\<close> gives the weights for the mTSP-instance \<open>f E\<close>.\<close>
  "edge_in_He G (uEdge (e,u,i) (f,v,j)) = undefined"

fun vertices_in_He :: "'a graph_adj_list \<Rightarrow> ('a uedge \<times> 'a \<times> nat) uedge \<Rightarrow> bool" where \<comment> \<open>The function \<open>c\<close> gives the weights for the mTSP-instance \<open>f E\<close>.\<close>
  "vertices_in_He G (uEdge (e,u,i) (f,v,j)) = undefined"

fun dist_in_He :: "'a uedge \<Rightarrow> ('a uedge \<times> 'a \<times> nat) \<Rightarrow> ('a uedge \<times> 'a \<times> nat) \<Rightarrow> int" where 
  "dist_in_He e (e,u,i) (f,v,j) = min {length P | P. path (e,u,i) (H\<^sub>e e) (f,v,j)}" (* TODO: define path *)

fun c_exec :: "'a graph_adj_list \<Rightarrow> ('a uedge \<times> 'a \<times> nat) uedge \<Rightarrow> int" where \<comment> \<open>The function \<open>c\<close> gives the weights for the mTSP-instance \<open>f E\<close>.\<close>
  "c_exec G (uEdge (e,u,i) (f,v,j)) = 
    (if edge_in_He G (uEdge (e,u,i) (f,v,j)) then 1
    else if vertices_in_He G (uEdge (e,u,i) (f,v,j)) then dist_in_He e (e,u,i) (f,v,j)
    else if u = v \<and> e \<noteq> f then 4
    else 5)"

fun split_list_at :: "'a list \<Rightarrow> 'a \<Rightarrow> ('a list \<times> 'a list) option" where
  "split_list_at [] y = None"
| "split_list_at (x#xs) y = 
  (if x = y then Some ([],xs) 
  else case split_list_at xs y of 
    Some (xs\<^sub>1,xs\<^sub>2) \<Rightarrow> Some (x#xs\<^sub>1,xs\<^sub>2)
  | None \<Rightarrow> None)"

lemma "split_list_at xs y = Some (xs\<^sub>1,xs\<^sub>2) \<Longrightarrow> xs\<^sub>1 @ y#xs\<^sub>2 = xs"
  by (induction xs arbitrary: xs\<^sub>1 xs\<^sub>2) (auto split: if_splits option.splits)

fun rotate_tour_to :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list option" where
  "rotate_tour_to xs y = (case split_list_at xs y of
    Some (xs\<^sub>1,xs\<^sub>2) \<Rightarrow> Some (y#xs\<^sub>2 @ rev (butlast xs\<^sub>1) @ [y]) \<comment> \<open>x\<^sub>1,x\<^sub>2,\<dots>,x\<^sub>i,y,x\<^sub>i\<^sub>+\<^sub>1,\<dots>,x\<^sub>n,x\<^sub>1 \<mapsto> y,x\<^sub>i\<^sub>+\<^sub>1,\<dots>,x\<^sub>n,x\<^sub>1,x\<^sub>2,\<dots>,x\<^sub>i,y\<close>
  | None \<Rightarrow> None)"

lemma "rotate_tour_to xs y = Some xs' \<Longrightarrow> hd xs' = y"
  by (induction xs arbitrary: xs) (auto split: option.splits)

fun does_tour_contain_path :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "does_tour_contain_path T [] = True"
| "does_tour_contain_path T (v#P) = (case rotate_tour_to T v of
    Some T' \<Rightarrow> undefined
  | None \<Rightarrow> False)" (* TODO *)

fun g_exec :: "'a graph_adj_list \<Rightarrow> ('a uedge \<times> 'a \<times> nat) list \<Rightarrow> 'a set" where \<comment> \<open>The function \<open>g\<close> computes a VC4 solution, given a mTSP-solution.\<close>
  "g_exec G [] = {}"
| "g_exec G ((e,u,i)#T) = 
  (if i = 1 \<or> i = 2 then {u} \<union> g_exec G (filter (\<lambda>(f,v,j). False)) T
  else undefined)"

section \<open>Properties of the Functions\<close>

lemma "Vs (uedges (f_exec G)) = {(uEdge u v,u,i) | u v i. {u,v} \<in> uedges G \<and> 1 \<le> i \<and> i \<le> 6}"
  sorry

lemma is_complete_exec: "is_complete (uedges (compl_graph_exec X))"
  sorry

lemma complete_f_exec: "is_complete (uedges (f_exec G))"
  apply (simp only: f_exec.simps Let_def)
  apply (rule is_complete_exec)
  sorry

section \<open>Reduction\<close>

abbreviation "c\<^sub>V\<^sub>C\<^sub>4 \<equiv> \<lambda>X. int (card X)" \<comment> \<open>Cost-function for the VC4 problem: cardinatlity of the vertex cover.\<close>

locale VC4_to_mTSP_abs1 =
  VC4: graph_adj_list Es +
  mTSP: metric_graph_adj_list Hs c for Es :: "'a graph_adj_list" and Hs :: "'b graph_adj_list" and c :: "'b \<times> 'b \<Rightarrow> int" +
  fixes g :: "'b list \<Rightarrow> 'a set" 
    and OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P OPT\<^sub>V\<^sub>C\<^sub>4 and c\<^sub>m\<^sub>T\<^sub>S\<^sub>P :: "'b list \<Rightarrow> int"
  defines "c\<^sub>m\<^sub>T\<^sub>S\<^sub>P T \<equiv> cost_of_path (\<lambda>u v. c (u,v)) T" \<comment> \<open>Cost-function for the mTSP problem: cost of the Hamiltonian cycle.\<close>
  \<comment> \<open>Assumptions about the VC4 problem instance.\<close>
  assumes max_deg_leq_4: "\<And>v. v \<in> Vs VC4.E \<Longrightarrow> degree VC4.E v \<le> 4" 
    and opt_vc4: "is_min_vc VC4.E OPT\<^sub>V\<^sub>C\<^sub>4"
    \<comment> \<open>Assumptions about the mTSP problem instance.\<close>
    and opt_mtsp: "is_tsp mTSP.E (\<lambda>u v. c (u,v)) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
    \<comment> \<open>Assumptions about the relationship of the two graph-problem instances\<close>
    and cost_opt_mtsp_leq: "c\<^sub>m\<^sub>T\<^sub>S\<^sub>P OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 15 * card VC4.E + c\<^sub>V\<^sub>C\<^sub>4 OPT\<^sub>V\<^sub>C\<^sub>4"
    and vc_of_tour: "\<And>T. is_hc mTSP.E T \<Longrightarrow> \<exists>k. c\<^sub>m\<^sub>T\<^sub>S\<^sub>P T = 15 * card VC4.E + k \<and> is_vc VC4.E (g T) \<and> c\<^sub>V\<^sub>C\<^sub>4 (g T) \<le> k"
begin

(* ----- 1st condition for a L-reduction ----- *)

lemma l_reduction1: "c\<^sub>m\<^sub>T\<^sub>S\<^sub>P OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * c\<^sub>V\<^sub>C\<^sub>4 OPT\<^sub>V\<^sub>C\<^sub>4"
proof -
  have "is_vc VC4.E OPT\<^sub>V\<^sub>C\<^sub>4"
    using opt_vc4 by (elim is_min_vcE)
  hence cardE_leq: "card VC4.E \<le> 4 * card OPT\<^sub>V\<^sub>C\<^sub>4"
    using max_deg_leq_4 by (auto intro: VC4.vc_card_E_leq_max_degree simp: numeral_eq_enat)
  thus ?thesis
    using cost_opt_mtsp_leq by (auto simp: c\<^sub>m\<^sub>T\<^sub>S\<^sub>P_def)
qed

(* ----- 2nd condition for a L-reduction ----- *)

lemma g_feasible_solution: "is_hc mTSP.E T \<Longrightarrow> is_vc VC4.E (g T)"
  using vc_of_tour by auto

lemma l_reduction2: 
  assumes "is_hc mTSP.E T"
  shows "\<bar> c\<^sub>V\<^sub>C\<^sub>4 (g T) - c\<^sub>V\<^sub>C\<^sub>4 OPT\<^sub>V\<^sub>C\<^sub>4 \<bar> \<le> 1 * \<bar> c\<^sub>m\<^sub>T\<^sub>S\<^sub>P T - c\<^sub>m\<^sub>T\<^sub>S\<^sub>P OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>"
proof -
  obtain k where cost_T: "c\<^sub>m\<^sub>T\<^sub>S\<^sub>P T = 15 * card VC4.E + k" and "is_vc VC4.E (g T)" "c\<^sub>V\<^sub>C\<^sub>4 (g T) \<le> k"
    using assms vc_of_tour by auto
  moreover hence opt_vc4_leq: "c\<^sub>V\<^sub>C\<^sub>4 OPT\<^sub>V\<^sub>C\<^sub>4 \<le> c\<^sub>V\<^sub>C\<^sub>4 (g T)"
    using opt_vc4 by (auto elim: is_min_vcE)
  ultimately show ?thesis
    using cost_T cost_opt_mtsp_leq by auto
qed

end

locale VC4_to_mTSP_abs2 = 
  VC4: graph_adj_list Es for Es :: "'a graph_adj_list" +
  fixes OPT\<^sub>V\<^sub>C\<^sub>4
  assumes max_deg_leq_4: "\<And>v. v \<in> Vs VC4.E \<Longrightarrow> degree VC4.E v \<le> 4" 
    and opt_vc4: "is_min_vc VC4.E OPT\<^sub>V\<^sub>C\<^sub>4"
begin

definition "Hs \<equiv> f_exec Es"

lemma irrefl_H: "v \<notin> ls_set (\<N> Hs v)"
  sorry

lemma sym_H: "u \<in> lset_set (\<N> Hs v) \<Longrightarrow> v \<in> lset_set (\<N> Hs u)"
  sorry

lemma graph_H: "graph_list_invar Hs"
  using irrefl_H sym_H by (auto intro: graph_list_invarI)

sublocale mTSP: graph_adj_list Hs
  using graph_H by unfold_locales

abbreviation "c\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<equiv> \<lambda>T. cost_of_path (\<lambda>u v. c_exec Es (u,v)) T"

lemma complete_H: "is_complete mTSP.E"
  unfolding mTSP.E_def3 unfolding Hs_def by (rule complete_f_exec)

lemma costs_positive_dc: "c_exec Es e > 0"
  sorry

lemma tri_ineq_dc: 
  "u \<in> Vs mTSP.E \<Longrightarrow> v \<in> Vs mTSP.E \<Longrightarrow> w \<in> Vs mTSP.E \<Longrightarrow> c_exec Es (u,w) \<le> c_exec Es (u,v) + c_exec Es (v,w)"
  sorry

sublocale mTSP': metric_graph_adj_list Hs "c_exec Es"
  using complete_H costs_positive_dc tri_ineq_dc by unfold_locales

definition "g T \<equiv> g_exec Es T"

lemma cost_opt_mtsp_leq:
  assumes opt_mtsp: "is_tsp mTSP.E (\<lambda>u v. c_exec Es (u,v)) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "c\<^sub>m\<^sub>T\<^sub>S\<^sub>P OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> int (15 * card VC4.E) + int (card OPT\<^sub>V\<^sub>C\<^sub>4)"
  sorry

lemma vc_of_tour: 
  assumes "is_hc mTSP.E T"
  shows "\<exists>k. c\<^sub>m\<^sub>T\<^sub>S\<^sub>P T = 15 * card VC4.E + k \<and> is_vc VC4.E (g T) \<and> c\<^sub>V\<^sub>C\<^sub>4 (g T) \<le> k"
  sorry

lemma l_reduction1: 
  assumes "is_tsp mTSP.E (\<lambda>u v. c_exec Es (u,v)) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "c\<^sub>m\<^sub>T\<^sub>S\<^sub>P OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * c\<^sub>V\<^sub>C\<^sub>4 OPT\<^sub>V\<^sub>C\<^sub>4"
  apply (rule VC4_to_mTSP_abs1.l_reduction1)
  using assms max_deg_leq_4 opt_vc4 cost_opt_mtsp_leq vc_of_tour 
  apply unfold_locales 
  apply auto
  sorry

lemma g_feasible_solution: 
  assumes "is_hc mTSP.E T" 
  shows "is_vc VC4.E (g T)"
  using assms vc_of_tour by auto

lemma l_reduction2: 
  assumes "is_tsp mTSP.E (\<lambda>u v. c_exec Es (u,v)) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
      and "is_hc mTSP.E T"
  shows "\<bar> c\<^sub>V\<^sub>C\<^sub>4 (g T) - c\<^sub>V\<^sub>C\<^sub>4 OPT\<^sub>V\<^sub>C\<^sub>4 \<bar> \<le> 1 * \<bar> c\<^sub>m\<^sub>T\<^sub>S\<^sub>P T - c\<^sub>m\<^sub>T\<^sub>S\<^sub>P OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>"
  apply (rule VC4_to_mTSP_abs1.l_reduction2)
  using assms max_deg_leq_4 opt_vc4 cost_opt_mtsp_leq vc_of_tour 
  apply unfold_locales 
  using assms apply auto
  done

end

abbreviation "uf_exec Es \<equiv> (uedges o f_exec) Es"

(* ----- 1st condition for a L-reduction ----- *)

lemma l_reduction1: 
  assumes "\<And>v. v \<in> Vs (uedges Es) \<Longrightarrow> degree (uedges Es) v \<le> 4"
      and "is_min_vc (uedges Es) OPT\<^sub>V\<^sub>C\<^sub>4"  
      and "is_tsp (uedges (f_exec Es)) (\<lambda>u v. c_exec Es (u,v)) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
      and "is_hc (uedges (f_exec Es)) T"
  shows "cost_of_path (\<lambda>u v. c_exec Es (u,v)) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * c\<^sub>V\<^sub>C\<^sub>4 OPT\<^sub>V\<^sub>C\<^sub>4"
  apply (rule VC4_to_mTSP_abs2.l_reduction1)
  using assms apply unfold_locales
  
  sorry

(* ----- 2nd condition for a L-reduction ----- *)

lemma g_feasible_solution: 
  assumes "is_hc (uf_exec Es) T" 
  shows "is_vc (uedges Es) (g_exec Es T)"
  sorry

lemma l_reduction2: 
  assumes "is_min_vc (uedges Es) OPT\<^sub>V\<^sub>C\<^sub>4" 
    and "is_tsp (uf_exec Es) (\<lambda>u v. c_exec Es (u,v)) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
    and "is_hc (uf_exec Es) T"
  shows "\<bar> c\<^sub>V\<^sub>C\<^sub>4 (g_exec Es T) - c\<^sub>V\<^sub>C\<^sub>4 OPT\<^sub>V\<^sub>C\<^sub>4 \<bar> \<le> 1 * \<bar> cost_of_path (\<lambda>u v. c_exec Es (u,v)) T - cost_of_path (\<lambda>u v. c_exec Es (u,v)) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>"
  sorry


(* ----- TODO ----- *)

text \<open>
({u,v},u,1) --- ({u,v},u,5) --- ({u,v},v,2)
     |                               |
({u,v},u,3) --- ({u,v},u,6) --- ({u,v},v,4)
     |                               |
({u,v},u,4) --- ({u,v},v,6) --- ({u,v},v,3)
     |                               |
({u,v},u,2) --- ({u,v},v,5) --- ({u,v},v,1)
\<close>

definition "H\<^sub>e u v \<equiv> (let e = {u,v} in 
  {{(e,u,1::nat),(e,u,3)},
  {(e,u,1),(e,u,5)},
  {(e,u,2),(e,u,4)},
  {(e,u,2),(e,v,5)},
  {(e,u,3),(e,u,4)},
  {(e,u,3),(e,u,6)},
  {(e,u,4),(e,v,6)},

  {(e,v,1::nat),(e,v,3)},
  {(e,v,1),(e,v,5)},
  {(e,v,2),(e,v,4)},
  {(e,v,2),(e,u,5)},
  {(e,v,3),(e,v,4)},
  {(e,v,3),(e,v,6)},
  {(e,v,4),(e,u,6)}})"

abbreviation "H E \<equiv> \<Union> {H\<^sub>e u v | u v. {u,v} \<in> E}"

definition "f E \<equiv> (let V\<^sub>H = Vs (H E) in complete_graph V\<^sub>H)"

locale VC4_to_mTSP_abs2 = 
  graph_abs E for E :: "'a set set" +
  fixes f :: "'a set set \<Rightarrow> ('a set \<times> 'a \<times> nat) set set" \<comment> \<open>Given a VC4-instance, the function \<open>f\<close> constructs the graph for a mTSP-instance.\<close>
    and c :: "('a set \<times> 'a \<times> nat) set \<Rightarrow> nat" \<comment> \<open>The function \<open>c\<close> gives the weights for the mTSP-instance \<open>f E\<close>.\<close>
    and g :: "('a set \<times> 'a \<times> nat) list \<Rightarrow> 'a set" \<comment> \<open>The function \<open>g\<close> computes a VC4 solution, given a mTSP-solution.\<close>
  assumes fE_complete: "is_complete (f E)"
      and pos_costs: "\<And>e'. e' \<in> f E \<Longrightarrow> c e' \<ge> 0"
      and c_tri_ineq: "\<And>u v w. u \<in> Vs (f E) \<Longrightarrow> v \<in> Vs (f E) \<Longrightarrow> w \<in> Vs (f E) 
        \<Longrightarrow> c {u,w} \<le> c {u,v} + c {v,w}"
      \<comment> \<open>Assumptions needed for the Reduction.\<close>
      and cost_1: "\<And>u v x y. {u,v} \<in> E \<Longrightarrow> {x,y} \<in> H\<^sub>e u v \<Longrightarrow> c {x,y} = 1"
      and cost_dist: "\<And>u v x y. {u,v} \<in> E \<Longrightarrow> x \<in> Vs (H\<^sub>e u v) \<Longrightarrow> y \<in> Vs (H\<^sub>e u v) \<Longrightarrow> {x,y} \<notin>  H\<^sub>e u v 
        \<Longrightarrow> c {u',v'} = distH\<^sub>e u' v'" (* TODO: How to define distance measure? *)
      and cost_4: "\<And>e\<^sub>1 e\<^sub>2 v i j x y. x = (e\<^sub>1,v,i) \<Longrightarrow> x = (e\<^sub>2,v,j) \<Longrightarrow> c {x,y} = 4"
      and cost_5: "\<And>e\<^sub>1 e\<^sub>2 v i j x y. False \<Longrightarrow> c {x,y} = 5" (* TODO: How to easily formalize 'otherwise'? *)
begin

abbreviation "H \<equiv> f E"

abbreviation "c\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<equiv> \<lambda>T. int (cost_of_path c T)"
abbreviation "c\<^sub>V\<^sub>C\<^sub>4 \<equiv> \<lambda>X. int (card X)"

lemma
  assumes "is_vc E X"
  obtains T where "is_hc H T" "cost_of_path c T = 15 * card E + card X"
  sorry
  (* TODO: How do I obtain a partition of E? \<rightarrow> executable graph model! *)

lemma
  assumes opt_vc: "is_min_vc E OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "is_tsp H c OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path c OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 15 * card E + card OPT\<^sub>V\<^sub>C"
  sorry

lemma
  assumes "is_hc H T"
  obtains u P v where "is_hp H u P v" "cost_of_path c P \<le> 0"
  sorry (* TODO: How do I formalize: contains a Hamiltonian path of each subgraph H\<^sub>e? *)

lemma
  assumes "is_hc H T" "cost_of_path c T = 15 * card E + k"
  obtains X where "is_vc E X" "card x = k"
  sorry

end

(* ----- 1st condition for a L-reduction ----- *)

lemma l_reduction1:
  assumes opt_vc: "is_min_vc E OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "is_tsp H c OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path c OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * card OPT\<^sub>V\<^sub>C" (is "?c' OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> ?\<alpha> * ?c OPT\<^sub>V\<^sub>C")
  sorry

(* ----- 2nd condition for a L-reduction ----- *)

text \<open>The function \<open>g\<close> maps a feasible solution of mTSP to a feasible solution of VC4.\<close>
lemma
  assumes "is_hc H T"
  shows "is_vc E (g T)"
  sorry

lemma l_reduction2:
  assumes opt_vc: "is_min_vc E OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "is_tsp H c OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P" 
      and "is_hc H T"
  shows "\<bar> c\<^sub>m\<^sub>T\<^sub>S\<^sub>P (g T) - c\<^sub>m\<^sub>T\<^sub>S\<^sub>P OPT\<^sub>V\<^sub>C \<bar> \<le> 1 * \<bar> c\<^sub>m\<^sub>T\<^sub>S\<^sub>P T - c\<^sub>m\<^sub>T\<^sub>S\<^sub>P OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>"
  sorry

end

end