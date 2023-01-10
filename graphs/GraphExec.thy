theory GraphExec
  imports Main tsp.Misc tsp.Berge tsp.CompleteGraph tsp.WeightedGraph
  "HOL-Data_Structures.Map_Specs" "HOL-Data_Structures.Set_Specs"
begin

(* OLD, NOT NEEDED; TODO: remove *)

definition "uedge \<equiv> \<lambda>(u,v). {u,v}"

locale irrefl_sym_digraph = 
  fixes dE :: "('a \<times> 'a) set" \<comment> \<open>The graph is only represented by the set of directed edges.\<close>
  assumes finite_dE: "finite dE"
      and irrefl: "\<And>u. (u,u) \<notin> dE" \<comment> \<open>The set of edges is irreflexive.\<close>
      and sym: "\<And>u v. (u,v) \<in> dE \<Longrightarrow> (v,u) \<in> dE" \<comment> \<open>The set of edges is symmetric.\<close>
begin

definition "E \<equiv> uedge ` dE"

lemma finite_uedge_dE: "finite E"
  unfolding E_def by (simp add: finite_dE)

lemma edge_invar_uedge_E:
  assumes "e \<in> E" 
  obtains u v where "e = {u,v}" "u \<noteq> v"
proof -
  obtain u v where "e = {u,v}" and "(u,v) \<in> dE"
    using assms unfolding E_def uedge_def by auto  
  moreover hence "u \<noteq> v"
    using irrefl by auto
  ultimately show ?thesis
    using that by auto
qed

lemma graph_E: "graph_invar E"
  using finite_uedge_dE edge_invar_uedge_E by (intro graph_invarI2) force+

sublocale graph_abs E \<comment> \<open>A symmetric digraph is a undirected graph.\<close>
  using graph_E by unfold_locales

end

locale graph_adj_map = 
  Map map_empty update map_delete lookup map_invar + 
  Set set_empty insert set_delete isin set set_invar
  for map_empty :: "'map" and update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map" and map_delete lookup map_invar and 
    set_empty :: "'vset" and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and set_delete isin set set_invar +
  fixes G :: "'map" and \<N>\<^sub>G
  defines "\<N>\<^sub>G v \<equiv> (case lookup G v of None \<Rightarrow> set_empty | Some N \<Rightarrow> N)"
  assumes finite_edges: "finite {(u,v) | u v. v \<in> set (\<N>\<^sub>G u)}" \<comment> \<open>We assume the set of edges to be finite.\<close>
      and irrefl: "\<And>v. v \<notin> set (\<N>\<^sub>G v)" \<comment> \<open>The set of edges is irreflexive.\<close>
      and sym: "\<And>u v. u \<in> set (\<N>\<^sub>G v) \<Longrightarrow> v \<in> set (\<N>\<^sub>G u)" \<comment> \<open>The graph is undirected, thus the directed-edges have to be symmetric.\<close>
begin

definition "dE \<equiv> {(u,v) | u v. v \<in> set (\<N>\<^sub>G u)}" \<comment> \<open>We convert the adjacency map to a directed graph.\<close>

lemma finite_dE: "finite dE"
  unfolding dE_def using finite_edges .

lemma irrefl_dE: "(u,u) \<notin> dE"
  unfolding dE_def using irrefl by auto

lemma sym_dE: "(u,v) \<in> dE \<Longrightarrow> (v,u) \<in> dE"
  unfolding dE_def using sym by auto

sublocale irrefl_sym_digraph dE \<comment> \<open>The adjacency map represents a irreflexive & symmetric digraph.\<close>
  using finite_dE irrefl_dE sym_dE by unfold_locales

lemma E_def2: "E = uedge ` {(u,v) | u v. v \<in> set (\<N>\<^sub>G u)}"
  unfolding E_def by (auto simp: dE_def)

end

section \<open>List Implementation for Sets\<close>

type_synonym 'a lset = "'a list"

definition lset_empty :: "'a lset" 
  where "lset_empty = []"

fun lset_delete :: "'a \<Rightarrow> 'a lset \<Rightarrow> 'a lset" where
  "lset_delete a as = filter (\<lambda>x. a \<noteq> x) as"

fun lset_insert :: "'a \<Rightarrow> 'a lset \<Rightarrow> 'a lset" where
  "lset_insert a as = a#lset_delete a as"

fun lset_isin :: "'a lset \<Rightarrow> 'a \<Rightarrow> bool" where
  "lset_isin as a = (filter (\<lambda>x. a = x) as \<noteq> [])"

fun lset_set :: "'a lset \<Rightarrow> 'a set" where
  "lset_set as = set as"

fun lset_invar :: "'a lset \<Rightarrow> bool" where
  "lset_invar as = distinct as"

lemma lset_empty: "lset_set lset_empty = {}"
  by (auto simp: lset_empty_def)

lemma lset_isin: "lset_invar s \<Longrightarrow> lset_isin s x = (x \<in> lset_set s)"
  by (induction s) auto

lemma lset_insert: "lset_invar s \<Longrightarrow> lset_set (lset_insert x s) = lset_set s \<union> {x}"
  by auto

lemma lset_delete: "lset_invar s \<Longrightarrow> lset_set (lset_delete x s) = lset_set s - {x}"
  by (induction s) auto

lemma lset_invar_empty: "lset_invar lset_empty"
  by (auto simp: lset_empty_def)

lemma lset_invar_insert: "lset_invar s \<Longrightarrow> lset_invar (lset_insert x s)"
  by auto

lemma lset_invar_delete: "lset_invar s \<Longrightarrow> lset_invar (lset_delete x s)"
  by auto

lemmas lset_specs = lset_empty lset_isin lset_insert lset_delete lset_invar_empty lset_invar_insert 
  lset_invar_delete

interpretation lset: Set lset_empty lset_insert lset_delete lset_isin lset_set lset_invar
  using lset_specs by unfold_locales

section \<open>Adjacency List implementation for Maps\<close>

type_synonym ('a,'b) adj_list = "('a \<times> 'b) list"

definition adjl_empty :: "('a,'b) adj_list" where
  "adjl_empty = []"

fun adjl_delete :: "'a \<Rightarrow> ('a,'b) adj_list \<Rightarrow> ('a,'b) adj_list" where
  "adjl_delete a M = filter (\<lambda>(x,y). a \<noteq> x) M"

fun adjl_update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) adj_list \<Rightarrow> ('a,'b) adj_list" where
  "adjl_update a b M = (a,b)#adjl_delete a M"

fun adjl_lookup :: "('a,'b) adj_list \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "adjl_lookup [] a = None"
| "adjl_lookup ((x,y)#M) a = (if a = x then Some y else adjl_lookup M a)"

fun adjl_invar :: "('a,'b) adj_list \<Rightarrow> bool" where
  "adjl_invar M = distinct (map fst M)"

lemma adj_list_empty: "adjl_lookup adjl_empty = (\<lambda>_. None)"
  unfolding adjl_empty_def by auto

lemma adj_list_delete: "adjl_invar M \<Longrightarrow> adjl_lookup (adjl_delete a M) = (adjl_lookup M) (a := None)"
  by (induction M) auto

lemma adj_list_update: "adjl_invar M \<Longrightarrow> adjl_lookup (adjl_update a b M) = (adjl_lookup M) (a := Some b)"
  by (auto simp add: adj_list_delete simp del: adjl_delete.simps)

lemma adj_list_invar_empty: "adjl_invar adjl_empty"            
  by (auto simp: adjl_empty_def)

lemma adj_list_invar_update: "adjl_invar M \<Longrightarrow> adjl_invar (adjl_update a b M)"
  by (induction M) auto

lemma adj_list_invar_delete: "adjl_invar M \<Longrightarrow> adjl_invar (adjl_delete a M)"
  by (induction M) auto

lemmas adj_list_specs = adj_list_empty adj_list_update adj_list_delete adj_list_invar_empty 
  adj_list_invar_update adj_list_invar_delete

interpretation adj_list: Map adjl_empty adjl_update adjl_delete adjl_lookup adjl_invar
  using adj_list_specs by unfold_locales

section \<open>Graph Implementation with Adjacency-Lists\<close>

type_synonym 'v graph_adj_list = "('v,'v lset) adj_list"
type_synonym 'v dedge = "'v \<times> 'v" \<comment> \<open>graph list edge\<close>

datatype 'v uedge = uEdge 'v 'v

fun uEdge_eq :: "'v uedge \<Rightarrow> 'v uedge \<Rightarrow> bool" where
  "uEdge_eq (uEdge u\<^sub>1 v\<^sub>1) (uEdge u\<^sub>2 v\<^sub>2) = (u\<^sub>1 = u\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2 \<or> u\<^sub>1 = v\<^sub>2 \<and> v\<^sub>1 = u\<^sub>2)"

(* quotient_type 'v uedge = "'v dedge" / uEdge_eq
  morphisms Rep_uedge Abs_uedge
proof (rule equivpI)
  show "reflp uEdge_eq"
    by (auto simp: reflp_def)
  show "symp uEdge_eq"
    by (auto simp: symp_def)
  show "transp uEdge_eq"
    by (auto simp: transp_def)
qed *)

(* instantiation uedge :: (equal) equal
begin

instance 
proof (standard, goal_cases)

end *)

value "uEdge (1::nat) 2 = uEdge (2::nat) 1"

abbreviation "lset_opt A\<^sub>o\<^sub>p\<^sub>t \<equiv> (case A\<^sub>o\<^sub>p\<^sub>t of None \<Rightarrow> lset_empty | Some A \<Rightarrow> A)"

abbreviation "\<N> Es v \<equiv> lset_opt (adjl_lookup Es v)" \<comment> \<open>Neighbourhood\<close>

fun graph_adjl_invar :: "'v graph_adj_list \<Rightarrow> bool" where
  "graph_adjl_invar G = (adjl_invar G \<and> (\<forall>(u,N\<^sub>u) \<in> set G. lset_invar N\<^sub>u))"

fun dedges :: "'v graph_adj_list \<Rightarrow> 'v dedge list" where
  "dedges G = concat (map (\<lambda>(u,N\<^sub>u). map (Pair u) N\<^sub>u) G)"

fun uedge_list :: "'v graph_adj_list \<Rightarrow> 'v uedge list" where
  "uedge_list G = (let f = (\<lambda>(u,v) Es. 
      case find (uEdge_eq (uEdge u v)) Es of None \<Rightarrow> (uEdge u v)#Es | Some _ \<Rightarrow> Es) in
    fold f (dedges G) [])"

fun uedges :: "'v graph_adj_list \<Rightarrow> 'v set set" where \<comment> \<open>Abstraction function\<close>
  "uedges G = set (map uedge (dedges G))"

lemma distinct_dedges: "graph_adjl_invar G \<Longrightarrow> distinct (dedges G)"
proof (induction G rule: pair_list.induct)
  case (2 u N\<^sub>u G)
  hence "\<And>e. e \<in> set (dedges G) \<Longrightarrow> fst e \<noteq> u"
    by force
  moreover have "\<And>e. e \<in> set (dedges [(u,N\<^sub>u)]) \<Longrightarrow> fst e = u"
    by auto
  ultimately have "set (dedges [(u,N\<^sub>u)]) \<inter> set (dedges G) = {}"
    by blast
  moreover have "distinct (dedges [(u,N\<^sub>u)])"
    using 2 by (auto simp: distinct_map inj_on_def)
  moreover have "distinct (dedges G)"
    using 2 by auto
  ultimately show ?case
    by auto
qed auto

lemma distinct_uedges: "\<And>u v. uEdge u v \<in> set (uedge_list G) \<Longrightarrow> uEdge v u \<notin> set (uedge_list G)"
proof (induction G rule: pair_list.induct)
  case 1
  then show ?case by auto
next
  case (2 x N\<^sub>x G)
  then show ?case sorry
qed

lemma adjl_member_unique:
  assumes "graph_adjl_invar G" and "(u,N\<^sub>u) \<in> set G" "(u,N\<^sub>v) \<in> set G"
  shows "N\<^sub>u = N\<^sub>v"
proof (rule ccontr)
  assume "N\<^sub>u \<noteq> N\<^sub>v"
  hence "\<not> distinct (map fst G)"
    using assms by (meson eq_key_imp_eq_value)
  thus False
    using assms by auto
qed

lemma adjl_member_adjl_lookup:
  assumes "graph_adjl_invar G" and "(u,N\<^sub>u) \<in> set G"
  shows "adjl_lookup G u = Some N\<^sub>u"
  using assms 
proof (induction G rule: pair_list.induct)
  case (2 v N\<^sub>v G)
  thus ?case 
  proof cases
    assume "u = v"
    moreover hence "N\<^sub>v = N\<^sub>u"
      using "2.prems" by (intro adjl_member_unique[of "(v,N\<^sub>v)#G"]) auto
    ultimately show ?thesis
      by auto
  qed auto
qed auto
    
lemma adjl_lookup_adjl_member: 
  assumes "graph_adjl_invar G" and "adjl_lookup G u = Some N\<^sub>u" 
  shows "(u,N\<^sub>u) \<in> set G"
  using assms
proof (induction G rule: pair_list.induct)
  case (2 v N\<^sub>v Es)
  thus ?case 
    by (cases "u = v") (auto simp add: adj_list_delete simp del: adjl_delete.simps)
qed auto

lemma neighbour_member:
  assumes "v \<in> lset_set (\<N> G u)"
  obtains N\<^sub>u where "adjl_lookup G u = Some N\<^sub>u" "v \<in> lset_set N\<^sub>u"
proof -
  obtain N\<^sub>u where "\<N> G u = N\<^sub>u" "v \<in> lset_set N\<^sub>u"
    using assms by auto
  moreover hence "adjl_lookup G u = Some N\<^sub>u"
    using lset_empty by (fastforce split: option.splits)+
  ultimately show ?thesis
    using that by auto
qed

lemma neighbourhood_memberI: 
  assumes "graph_adjl_invar G" and "(u,v) \<in> set (dedges G)"
  shows "v \<in> lset_set (\<N> G u)"
proof -
  obtain N\<^sub>u where "v \<in> lset_set N\<^sub>u" "(u,N\<^sub>u) \<in> set G"
    using assms by auto
  moreover hence "adjl_lookup G u = Some N\<^sub>u"
    using assms by (intro adjl_member_adjl_lookup)
  ultimately show ?thesis
    by auto
qed

lemma dedges_memberI: 
  assumes "graph_adjl_invar G" and "v \<in> lset_set (\<N> G u)"
  shows "(u,v) \<in> set (dedges G)"
proof -
  obtain N\<^sub>u where "adjl_lookup G u = Some N\<^sub>u" "v \<in> lset_set N\<^sub>u"
    using assms by (elim neighbour_member)
  moreover hence "(u,N\<^sub>u) \<in> set G"
    using assms by (intro adjl_lookup_adjl_member)
  ultimately show ?thesis
    by auto
qed

lemma dedges_superset: 
  assumes "graph_adjl_invar G"
  shows "{(u,v) | u v. v \<in> lset_set (\<N> G u)} \<subseteq> set (dedges G)" 
  (is "?dE \<subseteq> set (dedges G)")
proof
  fix e
  assume "e \<in> ?dE"
  then obtain u v where [simp]: "e = (u,v)" and "v \<in> lset_set (\<N> G u)"
    by auto
  hence "(u,v) \<in> set (dedges G)"
    using assms by (intro dedges_memberI)
  thus "e \<in> set (dedges G)"
    by auto
qed

lemma dedges_subset: 
  assumes "graph_adjl_invar G"
  shows "set (dedges G) \<subseteq> {(u,v) | u v. v \<in> lset_set (\<N> G u)}" 
  (is "set (dedges G) \<subseteq> ?dE")
proof (intro subsetI)
  fix e
  assume "e \<in> set (dedges G)"
  moreover then obtain u v where [simp]: "e = (u,v)"
    by auto
  ultimately have "v \<in> lset_set (\<N> G u)"
    using assms by (intro neighbourhood_memberI) auto
  thus "e \<in> ?dE"
    by auto
qed

lemma dedges_eq: 
  assumes "graph_adjl_invar G"
  shows "set (dedges G) = {(u,v) | u v. v \<in> lset_set (\<N> G u)}"
  using assms dedges_superset dedges_subset by blast

locale graph_adj_list = 
  fixes G :: "'v graph_adj_list"
  assumes graph_G: "graph_adjl_invar G"
    and irrefl: "\<And>v. v \<notin> lset_set (\<N> G v)"
    and sym: "\<And>u v. u \<in> lset_set (\<N> G v) \<Longrightarrow> v \<in> lset_set (\<N> G u)"
    and no_disconnected_vertices: "\<And>u N\<^sub>u. (u,N\<^sub>u) \<in> set G \<Longrightarrow> N\<^sub>u \<noteq> lset_empty"
begin

lemma finite_edge_set: "finite {(u,v) | u v. v \<in> lset_set (\<N> G u)}"
  using graph_G by (intro finite_subset[OF dedges_superset]) auto

sublocale graph_adj_map adjl_empty adjl_update adjl_delete adjl_lookup adjl_invar
  lset_empty lset_insert lset_delete lset_isin lset_set lset_invar G "\<N> G"
  unfolding graph_adj_map_def
  using adj_list.Map_axioms lset.Set_axioms apply auto
  using finite_edge_set irrefl sym by unfold_locales

lemma dE_def2: "dE = set (dedges G)"
  using graph_G by (subst dedges_eq) (auto simp: dE_def)

lemma E_def3: "E = uedges G"
  unfolding E_def using dE_def2 by (auto simp: dE_def)

lemma "Vs E = set (map fst G)"
  sorry

lemma "{u,v} \<in> E \<longleftrightarrow> u \<in> lset_set (\<N> G v)"
  sorry

end

fun compl_graph_exec :: "'a list \<Rightarrow> 'a graph_adj_list" where 
  "compl_graph_exec X = map (\<lambda>x. (x,filter ((\<noteq>) x) X)) X"

definition "is_complete_exec G \<equiv> (\<forall>(u,N\<^sub>u) \<in> set G. lset_set N\<^sub>u = set (map fst G) - {u})"

lemma is_complete_execI:
  assumes "\<And>u N\<^sub>u. (u,N\<^sub>u) \<in> set G \<Longrightarrow> lset_set N\<^sub>u = set (map fst G) - {u}"
  shows "is_complete_exec G"
  using assms by (auto simp: is_complete_exec_def)

lemma "is_complete_exec (compl_graph_exec X)"
proof (rule is_complete_execI)
  fix u N\<^sub>u
  assume "(u,N\<^sub>u) \<in> set (compl_graph_exec X)"
  hence "N\<^sub>u = filter ((\<noteq>) u) X"
    by auto
  moreover have "map fst (compl_graph_exec X) = X"
  proof (induction X)
    case Nil
    then show ?case by auto
  next
    case (Cons u X)
    hence "map fst (compl_graph_exec (u#X)) = map fst (map (\<lambda>x. (x,filter ((\<noteq>) x) (u#X))) (u#X))"
      by auto
    also have "... = u#map fst (compl_graph_exec X)"
      by auto
    also have "... = u#X"
      using Cons by auto
    finally show ?case .
  qed 
  ultimately show "lset_set N\<^sub>u = set (map fst (compl_graph_exec X)) - {u}"
    by auto
qed

context graph_adj_list
begin

lemma "is_complete_exec G \<longleftrightarrow> is_complete E"
proof
  assume "is_complete_exec G"
  show "is_complete E"
  proof (rule is_completeI)
    fix u v
    assume "u \<in> Vs E" "v \<in> Vs E" "u \<noteq> v"
    show "{u,v} \<in> E"
      sorry
  qed
next
  assume "is_complete E"
  show "is_complete_exec G"
  proof (rule is_complete_execI)
    fix u N\<^sub>u
    assume "(u,N\<^sub>u) \<in> set G"
    show "lset_set N\<^sub>u = set (map fst G) - {u}"
      sorry
  qed
qed

end

locale metric_graph_adj_list = 
  graph_adj_list G for G :: "'a graph_adj_list" +
  fixes c :: "'a dedge \<Rightarrow> 'b::{ordered_semiring_0,semiring_numeral}"
  assumes complete: "is_complete E"
    and costs_positive: "\<And>e. c e > 0"
    and tri_ineq: "u \<in> Vs E \<Longrightarrow> v \<in> Vs E \<Longrightarrow> w \<in> Vs E \<Longrightarrow> c (u,w) \<le> c (u,v) + c (v,w)"
begin

end

section \<open>Example: Computing Reachability between Vertices with DFS\<close>

locale some_path =
  graph_abs E for E :: "'v set set" +
  fixes find_path :: "'v \<Rightarrow> 'v \<Rightarrow> 'v list option" \<comment> \<open>Some executable function on a abstract graph representation.\<close>
  assumes find_path_walk: "\<And>u v P. find_path u v = Some P \<Longrightarrow> walk_betw E u P v" \<comment> \<open>The function \<open>find_path\<close> only returns valid paths.\<close>
      and connected_find_path: "\<And>u v. v \<in> connected_component E u \<Longrightarrow> \<exists>P. find_path u v = Some P" \<comment> \<open>If there is a path between the vertices \<open>u\<close> and \<open>v\<close> then the function \<open>find_path\<close> will return a path.\<close>
begin

lemma find_path_connected_iff: "(\<exists>P. find_path u v = Some P) \<longleftrightarrow> v \<in> connected_component E u"
  using find_path_walk connected_find_path by blast

end

lemma "length (dedges (al_delete u Es)) \<le> length (dedges Es)"
  sorry

lemma length_dedges_al_delete_eq: 
  assumes "al_lookup Es u = None" 
  shows "length (dedges (al_delete u Es)) = length (dedges Es)"
  sorry

lemma length_dedges_al_delete_leq: "length (dedges (al_delete u Es)) \<le> length (dedges Es)"
  sorry

lemma length_edges_al_delete:
  assumes "al_lookup Es u = Some (x#N\<^sub>u)"
  shows "length N\<^sub>u + length (dedges (al_delete u Es)) < length (dedges Es)"
  sorry

function find_path_dfs :: "'v graph_list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v list option" where
  "find_path_dfs Es u v =
    (if u = v then Some [u]
    else (case al_lookup Es u of 
      Some (x#N\<^sub>u) \<Rightarrow> 
      if x = v then Some [u,v] \<comment> \<open>We found a path from \<open>u\<close> to \<open>v\<close>.\<close>
      else let Es' = al_update u N\<^sub>u Es in \<comment> \<open>Construct remove the edge \<open>(u,x)\<close> from the graph \<open>G\<close>.\<close>
        (case find_path_dfs Es' x v of 
          Some P \<Rightarrow> Some (u#P) \<comment> \<open>Try to find a path from \<open>x\<close> to \<open>v\<close>.\<close>
        | None \<Rightarrow> find_path_dfs Es' u v) \<comment> \<open>There is no path from \<open>x\<close> to \<open>v\<close>. We need to explore a different neighbour of \<open>u\<close>.\<close>
    | _ \<Rightarrow> None))"
  by pat_completeness auto
termination find_path_dfs
  apply (relation "measure (\<lambda>(Es,u,v). length (dedges Es))")
  subgoal
    by simp
  subgoal for Es u v N\<^sub>u x N\<^sub>u' Es'
    using length_edges_al_delete by force
  subgoal for Es u v N\<^sub>u x N\<^sub>u' Es'
    using length_edges_al_delete by force
  done

definition "Es\<^sub>t\<^sub>e\<^sub>s\<^sub>t \<equiv> [(1::nat,[2]),(2,[1,4,3]),(3,[2]),(4,[2])]"
value "find_path_dfs Es\<^sub>t\<^sub>e\<^sub>s\<^sub>t 1 3" \<comment> \<open>Test of the function \<open>find_path_dfs\<close>.\<close>

context graph_adj_list
begin

definition "find_path_dfs\<^sub>G = (\<lambda>u v. find_path_dfs Es u v)"

lemma find_path_walk:
  assumes "find_path_dfs\<^sub>G u v = Some P" 
  shows "walk_betw E u P v"
  sorry

lemma connected_find_path:
  assumes "v \<in> connected_component E u" 
  shows "\<exists>P. find_path_dfs\<^sub>G u v = Some P"
  sorry

sublocale some_path E find_path_dfs\<^sub>G
  using find_path_walk connected_find_path by unfold_locales

thm find_path_connected_iff

end

end