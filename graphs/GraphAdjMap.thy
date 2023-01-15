theory GraphAdjMap
  imports Main tsp.Misc tsp.Berge "HOL-Data_Structures.Map_Specs" "HOL-Data_Structures.Set_Specs"
    tsp.WeightedGraph
begin

fun the_default where 
  "the_default None def = def"
| "the_default (Some A) _ = A"

definition "set_of_pair \<equiv> \<lambda>(u,v). {u,v}"

(* ------ Test Stuff (START) ------ *)

(* section \<open>Executable Type for Undirected Edges\<close>

fun uedge_eq :: "'v \<times> 'v \<Rightarrow> 'v \<times> 'v \<Rightarrow> bool" where
  "uedge_eq (u\<^sub>1,v\<^sub>1) (u\<^sub>2,v\<^sub>2) = (u\<^sub>1 = u\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2 \<or> u\<^sub>1 = v\<^sub>2 \<and> v\<^sub>1 = u\<^sub>2)"

lemma reflp_list_eq: "reflp uedge_eq"
  unfolding reflp_def by simp

lemma symp_list_eq: "symp uedge_eq"
  unfolding symp_def by simp

lemma transp_list_eq: "transp uedge_eq"
  unfolding transp_def by simp

lemma equivp_list_eq: "equivp uedge_eq"
  by (intro equivpI reflp_list_eq symp_list_eq transp_list_eq)

quotient_type 'v uedge = "'v \<times> 'v" / uedge_eq
  morphisms Rep_uedge Abs_uedge
  by (rule equivp_list_eq) *)

(* term uedge
context includes lifting_syntax
begin

lemma uedge_eq_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" (* "right_unique A" "right_total A"*) 
  shows "(A ===> A ===> (=)) uedge_eq uedge_eq"
  apply transfer_prover
  sorry

quotient_type 'v uedge = "'v \<times> 'v" / uedge_eq parametric uedge_eq_transfer
  (* morphisms Rep_uedge Abs_uedge *)
  by (rule equivp_list_eq)
end *)

(* subsection \<open>Constructors for Undirected Edges\<close>

lift_definition uEdge :: "'v \<times> 'v \<Rightarrow> 'v uedge" is "\<lambda>(u,v). (u,v)" .

lift_definition set_of_uedge :: "'v uedge \<Rightarrow> 'v set" is "\<lambda>(u,v). {u,v}" by auto

lemma set_of_uEdge[simp]: "set_of_uedge (uEdge (u,v)) = {u,v}"
  by (metis case_prod_conv set_of_uedge.abs_eq uEdge.abs_eq)

instantiation uedge :: (equal) equal
begin

lift_definition equal_uedge :: "'a uedge \<Rightarrow> 'a uedge \<Rightarrow> bool" is uedge_eq
  by auto

instance
  by standard (transfer; clarsimp)

end
  
value "uEdge (1::int,2::nat) = uEdge (2::nat,1::nat)"

fun test :: "'a uedge \<Rightarrow> bool" where
  "test (uEdge u v) = undefined" *)

locale ugraph_abs_antisym = 
  fixes E :: "('a \<times> 'a) set"
  assumes finite: "finite E"
      and irreflexive: "\<And>v. (v,v) \<notin> E"
      and anti_symmetric: "\<And>u v. (u,v) \<in> E \<Longrightarrow> (v,u) \<notin> E"
begin

definition "uE \<equiv> set_of_pair ` E"

lemma finite_uE: "finite uE"
  unfolding uE_def using finite by auto

lemma irreflexive2: "(u,v) \<in> E \<Longrightarrow> u \<noteq> v"
  using irreflexive by auto

lemma edge_invar_uE:
  assumes "e \<in> uE"
  obtains u v where "e = {u,v}" "u \<noteq> v"
  using assms[unfolded uE_def] irreflexive2 by (auto simp: set_of_pair_def)

lemma graph_uE: "graph_invar uE"
  using finite_uE edge_invar_uE  by (force intro!: graph_invarI2)+

sublocale graph_abs uE
  using graph_uE by unfold_locales

end

(* ------ Test Stuff (END) ------ *)

context Map
begin

lemma invar_fold_update: "invar M \<Longrightarrow> invar (fold (\<lambda>x. update x (f x)) xs M)"
  by (induction xs arbitrary: M) (auto simp: map_specs)

lemma fold_update:
  assumes "invar M" "distinct xs"
  shows "lookup (fold (\<lambda>x. update x (f x)) xs M) y = 
    (if y \<in> set xs then Some (f y) else lookup M y)"
  using assms by (induction xs arbitrary: M) (auto simp: map_specs)

end

context Set2
begin

lemma invar_fold_union:
  assumes "invar X" "\<And>x. x \<in> List.set xs \<Longrightarrow> invar x"
  shows "invar (fold union xs X)"
  using assms invar_union by (induction xs arbitrary: X) auto

lemma fold_union:
  assumes "invar X" "\<And>x. x \<in> List.set xs \<Longrightarrow> invar x"
  shows "set (fold union xs X) = set X \<union> \<Union> (List.set (map set xs))"
  using assms invar_union by (induction xs arbitrary: X) (auto simp: set_union)

lemma fold_union_empty:
  assumes "\<And>x. x \<in> List.set xs \<Longrightarrow> invar x"
  shows "set (fold union xs empty) = \<Union> (List.set (map set xs))"
  using assms fold_union set_specs by auto

fun insert_all where
  "insert_all xs X = fold insert xs X"

lemma invar_insert_all: "invar X \<Longrightarrow> invar (insert_all xs X)"
  by (induction xs arbitrary: X) (auto simp: set_specs)

lemma set_insert_all: "invar X \<Longrightarrow> set (insert_all xs X) = set X \<union> List.set xs"
  using invar_insert_all by (induction xs arbitrary: X) (auto simp: set_specs)

fun set_of_list where
  "set_of_list xs = insert_all xs empty"

lemma invar_set_of_list: "invar (set_of_list xs)"
  using invar_insert_all by (auto simp: set_specs)

lemma set_of_list: "set (set_of_list xs) = List.set xs"
  using set_insert_all by (auto simp: set_specs)

lemma isin_set_of_list: "isin (set_of_list xs) x \<longleftrightarrow> x \<in> List.set xs"
  using invar_set_of_list set_of_list by (auto simp: set_specs)

(* lemma set_of_list_comm: "isin (set_of_list (xs @ ys)) x \<longleftrightarrow> isin (set_of_list (ys @ xs)) x"
  by (auto simp: isin_set_of_list simp del: set_of_list.simps) *)

end

section \<open>Abstract Adjacency Map\<close>

locale graph_adj_map = 
  Map map_empty update map_delete lookup map_invar + 
  Set2 set_empty set_delete isin set set_invar insert union inter diff
  for map_empty :: "'map" and update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map" and map_delete lookup 
    map_invar and set_empty :: "'vset" and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and set_delete isin set 
    set_invar union inter diff
begin

definition neighborhood ("\<N>") where
  "neighborhood M v \<equiv> the_default (lookup M v) set_empty" 
  \<comment> \<open>Neighbourhood of a vertex \<open>v\<close> in the adjacency map \<open>M\<close>.\<close>

lemma neighborhood_empty: "\<N> map_empty v = set_empty"
  unfolding neighborhood_def by (auto simp: map_specs)

lemma neighborhood_update: "map_invar M \<Longrightarrow> \<N> (update x N\<^sub>x M) = (\<N> M)(x := N\<^sub>x)"
  unfolding neighborhood_def by (auto simp: map_specs)

lemma neighborhood_map_delete: "map_invar M \<Longrightarrow> \<N> (map_delete x M) = (\<N> M)(x := set_empty)"
  unfolding neighborhood_def by (auto simp: map_specs)

abbreviation "adj_map_invar M \<equiv> map_invar M \<and> (\<forall>v. set_invar (\<N> M v))"

lemma map_delete_set_invar:
  assumes "adj_map_invar M" "\<And>v. set_invar (\<N> M v)" 
  shows "set_invar (\<N> (map_delete x M) v)"
proof cases
  assume "x = v"
  hence "\<N> (map_delete x M) v = set_empty"
    using assms by (auto simp: neighborhood_map_delete) 
  thus ?thesis
    by (auto simp: set_specs)
next
  assume "x \<noteq> v"
  hence "\<N> (map_delete x M) v = \<N> M v"
    using assms by (auto simp: neighborhood_map_delete)
  thus ?thesis
    using assms by auto
qed

lemma map_delete_adj_map_invar: "adj_map_invar M \<Longrightarrow> adj_map_invar (map_delete x M)"
  using map_specs by (auto simp: map_delete_set_invar)

lemma update_adj_map_invar: "adj_map_invar M \<Longrightarrow> set_invar N\<^sub>x \<Longrightarrow> adj_map_invar (update x N\<^sub>x M)"
  using map_specs by (auto simp: neighborhood_update)

definition "edges M \<equiv> {(u,v) | u v. isin (\<N> M u) v}" 
  \<comment> \<open>Translate adjacency map \<open>M\<close> to a set of directed edges.\<close>

lemma edges_empty: "edges map_empty = {}"
  unfolding edges_def by (auto simp: neighborhood_empty set_specs)

definition "vertices M \<equiv> {u | u v. isin (\<N> M u) v} \<union> {v | u v. isin (\<N> M u) v}" 
  \<comment> \<open>Vertices of the graph represented by \<open>M\<close>.\<close>

lemma vertices_memberE: 
  assumes "v \<in> vertices M"
  obtains u where "isin (\<N> M v) u" | u where "isin (\<N> M u) v"
  using assms[unfolded vertices_def] by blast

lemma vertices_memberI1: "isin (\<N> M u) v \<Longrightarrow> u \<in> vertices M"
  unfolding vertices_def by auto

lemma vertices_memberI2: "isin (\<N> M u) v \<Longrightarrow> v \<in> vertices M"
  unfolding vertices_def by auto

lemma edges_are_pair_of_vertices: "edges G \<subseteq> vertices G \<times> vertices G"
  unfolding edges_def vertices_def by auto

lemma edges_finite: 
  assumes "finite (vertices G)" 
  shows "finite (edges G)"
proof (rule finite_subset[OF edges_are_pair_of_vertices])
  show "finite (vertices G \<times> vertices G)"
    using assms by auto
qed

inductive path_betw :: "'map \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
  singleton_path: "v \<in> vertices M \<Longrightarrow> path_betw M v [v] v"
| prepend_path: "path_betw M u P v \<Longrightarrow> isin (\<N> M w) u \<Longrightarrow> path_betw M w (w#P) v" 
  \<comment> \<open>Define predicate for paths on graphs that are represented by adjacency maps.\<close>
  (* TODO: connect with definition for set-set graph representation *)

lemma singleton_pathI: "v \<in> vertices M \<Longrightarrow> path_betw M v [v] v"
  by (auto intro: path_betw.intros elim: vertices_memberE)

lemma singleton_pathI1: "isin (\<N> M u) v \<Longrightarrow> path_betw M u [u] u"
  by (auto intro: vertices_memberI1 path_betw.intros)

lemma singleton_pathI2: "isin (\<N> M u) v \<Longrightarrow> path_betw M v [v] v"
  by (auto intro: vertices_memberI2 path_betw.intros)

lemma append_path: 
  assumes "path_betw M u P v" "isin (\<N> M v) w" and "invar M"
  shows "path_betw M u (P @ [w]) w"
  using assms by (induction M u P v rule: path_betw.induct) 
    (auto intro: path_betw.intros vertices_memberI2)

definition "path_dist M u v \<equiv> Min ({enat (length P) | P. path_betw M u P v} \<union> {\<infinity>})" 
  \<comment> \<open>The distance between two nodes in a graph represented by an adjacency map.\<close>

definition 
  "is_hc_adj G T \<equiv> (\<exists>u. path_betw G u T u) \<and> distinct (tl T) \<and> vertices G = List.set (tl T)"
  \<comment> \<open>Definition of a Hamiltonian Cycle for Adjacency Maps.\<close> 
  (* TODO: connect with definition for set-set graph representation *)

lemma is_hcI: 
  "(\<exists>u. path_betw G u T u) \<Longrightarrow> distinct (tl T) \<Longrightarrow> vertices G = List.set (tl T) \<Longrightarrow> is_hc_adj G T"
  by (auto simp: is_hc_adj_def)

lemma is_hcE: 
  assumes "is_hc_adj G T "
  shows "\<exists>u. path_betw G u T u" "distinct (tl T)" "vertices G = List.set (tl T)"
  using assms[unfolded is_hc_adj_def] by auto

definition "is_tsp_adj G c T \<equiv> is_hc_adj G T 
  \<and> (\<forall>T'. is_hc_adj G T' \<longrightarrow> cost_of_path c T \<le> cost_of_path c T')"
  (* TODO: connect with definition for set-set graph representation *)

lemma is_tspI: "is_hc_adj G T \<Longrightarrow> (\<And>T'. is_hc_adj G T' \<Longrightarrow> cost_of_path c T \<le> cost_of_path c T') 
  \<Longrightarrow> is_tsp_adj G c T"
  by (auto simp: is_tsp_adj_def)

lemma is_tspE: 
  assumes "is_tsp_adj G c T"
  shows "is_hc_adj G T" "\<And>T'. is_hc_adj G T' \<Longrightarrow> cost_of_path c T \<le> cost_of_path c T'"
  using assms[unfolded is_tsp_adj_def] by auto

definition "is_vc_adj G X \<equiv> 
  (\<forall>u v. isin (\<N> G u) v \<longrightarrow> isin X u \<or> isin X v) \<and> (\<forall>v. isin X v \<longrightarrow> v \<in> vertices G)"
  \<comment> \<open>Definition of a Vertex Cover for Adjacency Maps.\<close> 
  (* TODO: connect with definition for set-set graph representation *)

lemma is_vcI: "(\<And>u v. isin (\<N> G u) v \<Longrightarrow> isin X u \<or> isin X v) 
  \<Longrightarrow> (\<And>v. isin X v \<Longrightarrow> v \<in> vertices G) \<Longrightarrow> is_vc_adj G X"
  by (auto simp: is_vc_adj_def)

lemma is_vcE: 
  assumes "is_vc_adj G X"
  shows "\<And>u v. isin (\<N> G u) v \<Longrightarrow> isin X u \<or> isin X v" "\<And>v. isin X v \<Longrightarrow> v \<in> vertices G"
  using assms[unfolded is_vc_adj_def] by auto

definition "is_min_vc_adj G X \<equiv> is_vc_adj G X 
  \<and> (\<forall>X'. is_vc_adj G X' \<longrightarrow> card (set X) \<le> card (set X'))"
  (* TODO: connect with definition for set-set graph representation *)

lemma is_min_vcI: 
  "is_vc_adj G X \<Longrightarrow> (\<And>X'. is_vc_adj G X' \<Longrightarrow> card (set X) \<le> card (set X')) \<Longrightarrow> is_min_vc_adj G X"
  by (auto simp: is_min_vc_adj_def)

lemma is_min_vcE: 
  assumes "is_min_vc_adj G X"
  shows "is_vc_adj G X" "\<And>X'. is_vc_adj G X' \<Longrightarrow> card (set X) \<le> card (set X')"
  using assms[unfolded is_min_vc_adj_def] by auto

end

datatype 'v uedge = uEdge 'v 'v

definition "set_of_uedge e \<equiv> case e of uEdge u v \<Rightarrow> {u,v}"

locale ugraph_adj_map = 
  graph_adj_map map_empty update map_delete lookup map_invar set_empty insert set_delete isin set 
  set_invar union inter diff
  for map_empty :: "'map" and update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map" and map_delete lookup 
    map_invar and set_empty :: "'vset" and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and set_delete isin set 
    set_invar union inter diff +
  fixes rep :: "'v uedge \<Rightarrow> 'v uedge"
  assumes is_rep: "\<And>u v. rep (uEdge u v) = rep (uEdge v u)" 
    "\<And>u v. rep (uEdge u v) = uEdge u v \<or> rep (uEdge u v) = uEdge v u"
begin

definition "uedges G \<equiv> (\<lambda>(u,v). rep (uEdge u v)) ` edges G" 
  \<comment> \<open>Translate adjacency map \<open>M\<close> to a set of undirected edges.\<close>

lemma uedges_def2: "uedges G = {rep (uEdge u v) | u v. isin (\<N> G u) v}"
  unfolding uedges_def set_of_pair_def edges_def by auto

lemma uedges_empty: "uedges map_empty = {}"
  unfolding uedges_def by (auto simp: edges_empty)

lemma uedges_finite: "finite (vertices G) \<Longrightarrow> finite (uedges G)"
  unfolding uedges_def using edges_finite by auto

lemma set_of_uedge: "set_of_uedge (uEdge u v) = {u,v}"
  unfolding set_of_uedge_def by auto

abbreviation "ugraph_adj_map_invar G \<equiv>
  map_invar G \<and>
  (\<forall>v. set_invar (\<N> G v)) \<and> \<comment> \<open>The invariants of the datastructures are satisfied.\<close>
  finite (uedges G) \<and> \<comment> \<open>We assume the set of edges to be finite.\<close>
  (\<forall>v. \<not> isin (\<N> G v) v) \<and> \<comment> \<open>The set of edges is irreflexive.\<close>
  (\<forall>u v. isin (\<N> G u) v \<longrightarrow> isin (\<N> G v) u)" 
    \<comment> \<open>The graph is undirected, thus the directed-edges have to be symmetric.\<close>

lemma ugraph_adj_map_invarI:
  assumes "map_invar G" "\<And>v. set_invar (\<N> G v)" "finite (uedges G)" "\<And>v. \<not> isin (\<N> G v) v" 
    "\<And>u v. isin (\<N> G u) v \<longrightarrow> isin (\<N> G v) u"
  shows "ugraph_adj_map_invar G"
  using assms by auto

lemma adj_vertices_neq:
  assumes "ugraph_adj_map_invar G" "isin (\<N> G u) v"
  shows "u \<noteq> v"
  using assms by auto

lemma vertices_def2: 
  assumes "ugraph_adj_map_invar G"
  shows "vertices G = {u | u v. isin (\<N> G u) v}"
  using assms unfolding vertices_def by blast

lemma isin_neighborhood_set_edge: 
  assumes "isin (\<N> G u) v"
  shows "{u,v} \<in> set_of_uedge ` uedges G"
proof -
  have "rep (uEdge u v) \<in> uedges G"
    using assms by (auto simp: uedges_def2)
  then consider "uEdge u v \<in> uedges G" | "uEdge v u \<in> uedges G"
    using is_rep by metis
  then consider "set_of_uedge (uEdge u v) \<in> set_of_uedge ` uedges G" 
    | "set_of_uedge (uEdge v u) \<in> set_of_uedge ` uedges G"
    by cases (auto intro: imageI)
  thus "{u,v} \<in> set_of_uedge ` uedges G"
    by cases (auto simp: set_of_uedge doubleton_eq_iff)
qed

lemma set_edge_isin_neighborhood: 
  assumes "ugraph_adj_map_invar G" "{u,v} \<in> set_of_uedge ` uedges G"
  shows "isin (\<N> G u) v"
proof -
  obtain e\<^sub>u where [simp]: "{u,v} = set_of_uedge e\<^sub>u" and "e\<^sub>u \<in> uedges G"
    using assms by auto
  moreover then obtain x y where "e\<^sub>u = rep (uEdge x y)"
    and xy_isin: "isin (\<N> G x) y" "isin (\<N> G y) x"
    using assms by (auto simp: uedges_def2)
  moreover then consider "e\<^sub>u = uEdge x y" | "e\<^sub>u = uEdge y x"
    using is_rep by auto
  ultimately consider "{u,v} = set_of_uedge (uEdge x y)" | "{u,v} = set_of_uedge (uEdge y x)"
    by cases metis+
  hence "{u,v} = {x,y}" 
    by (auto simp: set_of_uedge)
  then consider "u = x" "v = y" | "u = y" "v = x"
    by fastforce
  thus "isin (\<N> G u) v"
    using xy_isin by cases auto
qed

lemma vs_uedges_subset_vertices:
  assumes "u \<in> Vs (set_of_uedge ` uedges G)"
  shows "u \<in> vertices G"
proof -
  obtain e where "u \<in> e" "e \<in> set_of_uedge ` uedges G"
    using assms by (elim vs_member_elim)
  then obtain e\<^sub>u where [simp]: "e = set_of_uedge e\<^sub>u" and "e\<^sub>u \<in> uedges G"
    by auto
  then obtain x y where "e\<^sub>u = rep (uEdge x y)" and xy_isin: "x \<in> vertices G" "y \<in> vertices G"
    unfolding uedges_def2 by (auto simp: vertices_def)
  then consider "e\<^sub>u = uEdge x y" | "e\<^sub>u = uEdge y x"
    using is_rep by auto
  then consider "u = x" | "u = y"
    using \<open>u \<in> e\<close> by cases (auto simp: set_of_uedge_def)
  thus ?thesis
    using xy_isin by auto
qed

lemma vertices_subset_vs_uedges:
  assumes "u \<in> vertices G"
  shows "u \<in> Vs (set_of_uedge ` uedges G)"
proof -
  consider v where "isin (\<N> G u) v" | v where "isin (\<N> G v) u"
    using assms[unfolded vertices_def] by auto
  then consider v where "{u,v} \<in> set_of_uedge ` uedges G"
    using isin_neighborhood_set_edge by cases fast+
  thus ?thesis
    by cases auto
qed

lemma vs_uedges: "Vs (set_of_uedge ` (uedges G)) = vertices G" 
  using vs_uedges_subset_vertices vertices_subset_vs_uedges by auto

lemma rep_idem: "rep (rep e) = rep e"
proof -
  obtain u v where [simp]: "e = uEdge u v"
    by (cases e)
  then consider "rep e = uEdge u v" | "rep e = uEdge v u"
    using is_rep by auto
  thus ?thesis
    using is_rep by cases auto
qed

lemma rep_simps:
  assumes "rep e = uEdge u v"
  shows "rep e = rep (uEdge u v)" "rep e = rep (uEdge v u)" 
    "rep (uEdge u v) = uEdge u v" "rep (uEdge v u) = uEdge u v"
proof -
  show "rep e = rep (uEdge u v)" 
    apply (subst assms[symmetric])
    apply (rule rep_idem[symmetric])
    done
  thus "rep e = rep (uEdge v u)" 
    by (auto simp add: is_rep) 
  thus "rep (uEdge u v) = uEdge u v" "rep (uEdge v u) = uEdge u v"
    using assms by (auto simp add: is_rep) 
qed 

lemma repE:
  assumes "rep e = uEdge u v"
  obtains "e = uEdge u v" | "e = uEdge v u"
  using assms is_rep by (cases e) (metis uedge.inject)

lemma rep_cases:
  assumes "rep e = rep (uEdge u v)"
  obtains "rep e = uEdge u v" | "rep e = uEdge v u"
  using assms is_rep by auto

end

locale ugraph_adj_map_by_linorder = \<comment> \<open>Represent an undirected graph by a anti-symmetric digraph. 
  A linear order on the vertices is used to identify symmetric edges.\<close>
  graph_adj_map map_empty update map_delete lookup map_invar set_empty insert set_delete isin set 
  set_invar union inter diff
  for map_empty :: "'map" and update :: "'v::linorder \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map" and map_delete 
    lookup map_invar and set_empty :: "'vset" and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and set_delete 
    isin set set_invar union inter diff
begin

fun rep :: "'v uedge \<Rightarrow> 'v uedge" where
  "rep (uEdge u v) = (if u \<le> v then uEdge u v else uEdge v u)"

sublocale ugraph_adj_map map_empty update map_delete lookup map_invar 
  set_empty insert set_delete isin set set_invar union inter diff rep
  by unfold_locales auto

end

locale ugraph_adj_map_fold_uedges =
  ugraph_adj_map map_empty update map_delete lookup map_invar set_empty insert set_delete isin set 
  set_invar union inter diff rep
  for map_empty :: "'map" and update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map" and map_delete lookup 
    map_invar and set_empty :: "'vset" and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and set_delete isin set 
    set_invar union inter diff rep +
  fixes fold_uedges :: "('v uedge \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'map \<Rightarrow> 'b \<Rightarrow> 'b" 
    \<comment> \<open>Function that folds the undirected edges of a graph represented by an adjacency map.\<close>
  assumes fold_uedges: "\<And>G f a\<^sub>0. ugraph_adj_map_invar G \<Longrightarrow>
    \<exists>es. distinct es \<and> map rep es = es \<and> List.set es = uedges G \<and> fold_uedges f G a\<^sub>0 = fold f es a\<^sub>0"
begin

lemma fold_uedgesE:
  assumes "ugraph_adj_map_invar G"    
  obtains es where "distinct es" "map rep es = es" "List.set es = uedges G" 
    "fold_uedges f G a\<^sub>0 = fold f es a\<^sub>0"
  using assms fold_uedges by blast

(* lemma fold_neq_obtain_edge:
  assumes "ugraph_adj_map_invar G" "fold_uedges f G a\<^sub>0 \<noteq> a\<^sub>0"
  obtains u v where "uEdge u v \<in> uedges G"
proof -
  obtain es where "distinct es" "map rep es = es" and set_es: "List.set es = uedges G" and
    "fold_uedges f G a\<^sub>0 = fold f es a\<^sub>0"
    using assms by (elim fold_uedgesE)
  hence "fold f es a\<^sub>0 \<noteq> a\<^sub>0"
    using assms by auto
  hence "es \<noteq> []"
    by auto
  moreover then obtain e where "hd es = e"
    by auto
  moreover then obtain u v where [simp]: "uEdge u v = e"
    by (cases e) auto
  ultimately have "uEdge u v \<in> uedges G"
    using set_es by fastforce
  thus ?thesis
    using that by blast
qed *)

end

locale ugraph_adj_map_fold_vset =
  ugraph_adj_map map_empty update map_delete lookup map_invar set_empty insert set_delete isin set 
  set_invar union inter diff rep
  for map_empty :: "'map" and update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map" and map_delete lookup 
    map_invar and set_empty :: "'vset" and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and set_delete isin set 
    set_invar union inter diff rep +
  fixes fold_vset :: "('v \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'vset \<Rightarrow> 'b \<Rightarrow> 'b"
  \<comment> \<open>Function that folds the vertices of a graph represented by an adjacency map.\<close>
  assumes finite_sets: "\<And>X. finite (set X)"
  assumes fold_vset: "\<And>X f a\<^sub>0. set_invar X \<Longrightarrow>
    \<exists>xs. distinct xs \<and> List.set xs = set X \<and> fold_vset f X a\<^sub>0 = fold f xs a\<^sub>0"
begin

lemma fold_vsetE:
  assumes "set_invar X"
  obtains xs where "distinct xs" "List.set xs = set X" "fold_vset f X a\<^sub>0 = fold f xs a\<^sub>0"
  using assms fold_vset by blast

(* lemma fold_vset_empty: "fold_vset f set_empty M = fold f [] M"
proof -
  obtain xs where "List.set xs = set set_empty" "fold_vset f set_empty M = fold f xs M"
    using set_specs fold_vset by metis
  thus ?thesis
    using set_specs by auto
qed

lemma fold_vset_induct[consumes 1, case_names empty insert]:
  assumes "set_invar X"
      and "\<And>M. P (fold_vset f set_empty M)"
      and "\<And>M X x. set_invar X \<Longrightarrow> \<not> isin X x \<Longrightarrow> P (fold_vset f X M) \<Longrightarrow> 
    P (fold_vset f (insert x X) M)"
  shows "P (fold_vset f X M)"
proof -
  obtain xs where "distinct xs" "List.set xs = set X" "fold_vset f X M = fold f xs M"
    using assms fold_vset by blast
  moreover have "P (fold f xs M)"
    using assms by (induction xs arbitrary: M) (auto simp: fold_vset_empty)
  ultimately show ?thesis 
    by auto
qed *)

end

locale graph_of_vertices_for_ugraph_adj_map =
  ugraph_adj_map_fold_vset map_empty update map_delete lookup map_invar set_empty insert set_delete 
  isin set set_invar union inter diff rep fold_vset
  for map_empty :: "'map" and update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map" and map_delete lookup 
    map_invar and set_empty :: "'vset" and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and set_delete isin set 
    set_invar union inter diff rep and fold_vset :: "('v \<Rightarrow> 'map \<Rightarrow> 'map) \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map"
begin

fun graph_of_vertices :: "('v \<Rightarrow> 'vset) \<Rightarrow> 'vset \<Rightarrow> 'map" where
  "graph_of_vertices n X = fold_vset (\<lambda>v. update v (n v)) X map_empty"
  \<comment> \<open>We construct a graph from a given set of vertices \<open>X\<close> and a function \<open>n\<close> that computes the 
  neighborhood of each vertex.\<close>

lemma map_invar_graph_of_vertices: 
  assumes "set_invar X"
  shows "map_invar (graph_of_vertices n X)"
proof -
  let ?f="\<lambda>x. update x (n x)"
  obtain xs where "fold_vset ?f X map_empty = fold ?f xs map_empty"
    using assms by (elim fold_vsetE)
  moreover have "map_invar (fold ?f xs map_empty)"
    using map_specs by (intro invar_fold_update)
  ultimately show ?thesis
    by auto
qed

lemma graph_of_vertices_neighborhood:
  assumes "set_invar X"
  shows "\<N> (graph_of_vertices n X) v = (if isin X v then n v else set_empty)"
proof -
  let ?f="\<lambda>x. update x (n x)"
  obtain xs where "distinct xs" "List.set xs = set X" 
    "fold_vset ?f X map_empty = fold ?f xs map_empty"
    using assms by (elim fold_vsetE)
  thus ?thesis
    using assms set_specs map_specs by (auto simp: fold_update neighborhood_def)
qed

lemma non_empty_neighborhood_isin_X:
  assumes "set_invar X" 
      and "\<And>x. isin X x \<Longrightarrow> set_invar (n x)" \<comment> \<open>Every neighborhood satisfies the invariants.\<close>
      and "\<And>x. isin X x \<Longrightarrow> \<exists>y. isin (n x) y" \<comment> \<open>Every neighborhood is non-empty.\<close>
      and "\<And>x y. isin X x \<Longrightarrow> isin (n x) y \<Longrightarrow> isin X y" \<comment> \<open>Every neighborhood can only be a subset of \<open>X\<close>.\<close>
      and "isin (\<N> (graph_of_vertices n X) u) v"
  shows "isin X u"
  using assms set_specs graph_of_vertices_neighborhood by (cases "isin X u") auto

lemma isin_neighborhood_isin_X:
 assumes "set_invar X" 
      and "\<And>x. isin X x \<Longrightarrow> set_invar (n x)" \<comment> \<open>Every neighborhood satisfies the invariants.\<close>
      and "\<And>x. isin X x \<Longrightarrow> \<exists>y. isin (n x) y" \<comment> \<open>Every neighborhood is non-empty.\<close>
      and "\<And>x y. isin X x \<Longrightarrow> isin (n x) y \<Longrightarrow> isin X y" \<comment> \<open>Every neighborhood can only be a subset of \<open>X\<close>.\<close>
      and "isin (\<N> (graph_of_vertices n X) u) v"
  shows "isin X v"
proof -
  have "isin X u"
    using assms by (rule non_empty_neighborhood_isin_X)
  thus ?thesis
    using assms graph_of_vertices_neighborhood by auto
qed

lemma vertices_graph_of_vertices: 
  assumes "set_invar X" 
      and "\<And>x. isin X x \<Longrightarrow> set_invar (n x)" \<comment> \<open>Every neighborhood satisfies the invariants.\<close>
      and "\<And>x. isin X x \<Longrightarrow> \<exists>y. isin (n x) y" \<comment> \<open>Every neighborhood is non-empty.\<close>
      and "\<And>x y. isin X x \<Longrightarrow> isin (n x) y \<Longrightarrow> isin X y" \<comment> \<open>Every neighborhood can only be a subset of \<open>X\<close>.\<close>
  shows "vertices (graph_of_vertices n X) = set X" (is "vertices ?G\<^sub>X = set X")
proof (rule equalityI[OF subsetI subsetI])
  fix v
  assume "v \<in> vertices ?G\<^sub>X"
  then consider u where "isin (\<N> ?G\<^sub>X v) u" | u where "isin (\<N> ?G\<^sub>X u) v"
    unfolding vertices_def by blast
  hence "isin X v"
    using assms non_empty_neighborhood_isin_X isin_neighborhood_isin_X by cases blast+
  thus "v \<in> set X"
    using assms set_specs by auto
next
  fix v
  assume "v \<in> set X"
  hence "isin X v"
    using assms set_specs by auto
  moreover then obtain u where "isin (n v) u"
    using assms by blast
  ultimately show "v \<in> vertices ?G\<^sub>X"
    using assms graph_of_vertices_neighborhood by (auto simp: vertices_def)
qed

lemma finite_graph_of_vertices: 
  assumes "set_invar X" 
      and "\<And>x. isin X x \<Longrightarrow> set_invar (n x)" \<comment> \<open>Every neighborhood satisfies the invariants.\<close>
      and "\<And>x. isin X x \<Longrightarrow> \<exists>y. isin (n x) y" \<comment> \<open>Every neighborhood is non-empty.\<close>
      and "\<And>x y. isin X x \<Longrightarrow> isin (n x) y \<Longrightarrow> isin X y" \<comment> \<open>Every neighborhood can only be a subset of \<open>X\<close>.\<close>
  shows "finite (uedges (graph_of_vertices n X))"
  using assms finite_sets uedges_finite vertices_graph_of_vertices by auto

lemma invar_graph_of_vertices:
  assumes "set_invar X" 
      and "\<And>x. isin X x \<Longrightarrow> set_invar (n x)" \<comment> \<open>Every neighborhood satisfies the invariants.\<close>
      and "\<And>x. isin X x \<Longrightarrow> \<exists>y. isin (n x) y" \<comment> \<open>Every neighborhood is non-empty.\<close>
      and "\<And>x y. isin X x \<Longrightarrow> isin (n x) y \<Longrightarrow> isin X y" \<comment> \<open>Every neighborhood can only be a subset of \<open>X\<close>.\<close>
      \<comment> \<open>The following assumptions are needed to obtain a valid undirected graph.\<close>
      and "\<And>x. isin X x \<Longrightarrow> \<not> isin (n x) x" \<comment> \<open>The neighborhood function is irreflexive.\<close>
      and "\<And>x y. isin X x \<Longrightarrow> isin (n x) y \<Longrightarrow> isin (n y) x" \<comment> \<open>The neighborhood function is symmetric.\<close>
  shows "ugraph_adj_map_invar (graph_of_vertices n X)" (is "ugraph_adj_map_invar ?G\<^sub>X")
proof (intro ugraph_adj_map_invarI)
  show "map_invar ?G\<^sub>X"
    using assms by (intro map_invar_graph_of_vertices)
  show "\<And>v. set_invar (\<N> ?G\<^sub>X v)"
    using assms(1,2) graph_of_vertices_neighborhood set_specs by auto
  show "finite (uedges ?G\<^sub>X)"
    using assms by (intro finite_graph_of_vertices)
  show "\<And>v. \<not> isin (\<N> ?G\<^sub>X v) v"
    using assms(1,5) graph_of_vertices_neighborhood set_specs 
      by (auto simp del: graph_of_vertices.simps split: if_splits) 
  show "\<And>u v. isin (\<N> ?G\<^sub>X u) v \<longrightarrow> isin (\<N> ?G\<^sub>X v) u"
  proof
    fix u v
    assume "isin (\<N> ?G\<^sub>X u) v"
    hence "isin X u" and "isin (n u) v"
      using assms(1) graph_of_vertices_neighborhood set_specs by (auto split: if_splits)
    hence "isin X v" and "isin (n v) u"
      using assms(4,6) by blast+
    thus "isin (\<N> ?G\<^sub>X v) u"
      using assms(1) graph_of_vertices_neighborhood by auto
  qed
qed

end

(* TODO: move below to other thy *)

section \<open>List Implementation for Sets\<close>

type_synonym 'a lset = "'a list"

definition lset_empty :: "'a lset" ("\<emptyset>\<^sub>l") where [simp]: "lset_empty = []"

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
  by auto

lemma lset_isin: "lset_invar s \<Longrightarrow> lset_isin s x = (x \<in> lset_set s)"
  by (induction s) auto

lemma lset_insert: "lset_invar s \<Longrightarrow> lset_set (lset_insert x s) = lset_set s \<union> {x}"
  by auto

lemma lset_delete: "lset_invar s \<Longrightarrow> lset_set (lset_delete x s) = lset_set s - {x}"
  by (induction s) auto

lemma lset_invar_empty: "lset_invar lset_empty"
  by auto

lemma lset_invar_insert: "lset_invar s \<Longrightarrow> lset_invar (lset_insert x s)"
  by auto

lemma lset_invar_delete: "lset_invar s \<Longrightarrow> lset_invar (lset_delete x s)"
  by auto

lemmas lset_specs = lset_empty lset_isin lset_insert lset_delete lset_invar_empty lset_invar_insert 
  lset_invar_delete

interpretation lset: Set lset_empty lset_insert lset_delete lset_isin lset_set lset_invar
  using lset_specs by unfold_locales

section \<open>List implementation for Maps\<close>

type_synonym ('a,'b) lmap = "('a \<times> 'b) list"

definition lmap_empty :: "('a,'b) lmap" where [simp]: "lmap_empty = []"

fun lmap_delete :: "'a \<Rightarrow> ('a,'b) lmap \<Rightarrow> ('a,'b) lmap" where
  "lmap_delete a M = filter (\<lambda>(x,y). a \<noteq> x) M"

fun lmap_update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) lmap \<Rightarrow> ('a,'b) lmap" where
  "lmap_update a b M = (a,b)#lmap_delete a M"

fun lmap_lookup :: "('a,'b) lmap \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "lmap_lookup [] a = None"
| "lmap_lookup ((x,y)#M) a = (if a = x then Some y else lmap_lookup M a)"

fun lmap_invar :: "('a,'b) lmap \<Rightarrow> bool" where
  "lmap_invar M = distinct (map fst M)"

lemma lmap_empty: "lmap_lookup lmap_empty = (\<lambda>_. None)"
  unfolding lmap_empty_def by auto

lemma lmap_delete: "lmap_invar M \<Longrightarrow> lmap_lookup (lmap_delete a M) = (lmap_lookup M) (a := None)"
  by (induction M) auto

lemma lmap_update: 
  "lmap_invar M \<Longrightarrow> lmap_lookup (lmap_update a b M) = (lmap_lookup M) (a := Some b)"
  by (auto simp add: lmap_delete simp del: lmap_delete.simps)

lemma lmap_invar_empty: "lmap_invar lmap_empty"            
  by auto

lemma lmap_invar_update: "lmap_invar M \<Longrightarrow> lmap_invar (lmap_update a b M)"
  by (induction M) auto

lemma lmap_invar_delete: "lmap_invar M \<Longrightarrow> lmap_invar (lmap_delete a M)"
  by (induction M) auto

lemmas lmap_specs = lmap_empty lmap_update lmap_delete lmap_invar_empty lmap_invar_update 
  lmap_invar_delete

interpretation list_map: Map lmap_empty lmap_update lmap_delete lmap_lookup lmap_invar
  using lmap_specs by unfold_locales

section \<open>Adjacency List implementation for Adjacency Maps\<close>

global_interpretation graph_adj_list: ugraph_adj_map_by_linorder 
  lmap_empty lmap_update lmap_delete lmap_lookup lmap_invar
  lset_empty lset_insert lset_delete lset_isin lset_set lset_invar
  defines \<N>_adj_list = "graph_adj_list.neighborhood"
      and edges_of_adj_list = "graph_adj_list.edges"     
      and adj_list_invar = "graph_adj_list.adj_map_invar"
      and path_adj_list = "graph_adj_list.path"
      and path_dist_adj_list = "graph_adj_list.path_dist"
      and uedges_of_adj_list = "graph_adj_list.uedges"     
      and ugraph_adj_list_invar = "graph_adj_list.ugraph_adj_map_invar"
      and uedge_rep = "graph_adj_list.rep"
  by unfold_locales

section \<open>Graph Implementation with Adjacency-Lists\<close>

type_synonym 'a graph_adj_list = "('a,'a lset) lmap"

subsection \<open>Folding Edges of undirected Graph\<close>

fun comp_uedges :: "('a::linorder) graph_adj_list \<Rightarrow> 'a uedge list" where \<comment> \<open>Computes a list of adjacent vertices in a graph represented by an adjaceny map & identifies symmetric edges.\<close>
  "comp_uedges [] = []"
| "comp_uedges ((v,N\<^sub>v)#G) = (let N\<^sub>v' = filter (\<lambda>x. v \<le> x) N\<^sub>v in 
  concat (map (\<lambda>(v,N\<^sub>v). (map (uEdge v) N\<^sub>v')) G))"

lemma lmap_delete_hd: "distinct (map fst ((v,N\<^sub>v)#G)) \<Longrightarrow> lmap_delete v ((v,N\<^sub>v)#G) = G"
  by (induction G) auto

lemma adj_list_invar_tl: "adj_list_invar ((v,N\<^sub>v)#G) \<Longrightarrow> adj_list_invar G"
proof -
  assume "adj_list_invar ((v,N\<^sub>v)#G)"
  moreover hence "lmap_delete v ((v,N\<^sub>v)#G) = G"
    unfolding adj_list_invar_def by (intro lmap_delete_hd) auto
  ultimately show "adj_list_invar G"
    unfolding adj_list_invar_def
    apply (subst \<open>lmap_delete v ((v,N\<^sub>v)#G) = G\<close>[symmetric])
    apply (subst(2) \<open>lmap_delete v ((v,N\<^sub>v)#G) = G\<close>[symmetric])
    apply (intro graph_adj_list.map_delete_adj_map_invar[unfolded \<N>_adj_list_def])
    apply simp
    done
qed (* TODO: clean up *)

lemma distinct_comp_uedges: 
  assumes "adj_list_invar G" 
  shows "distinct (comp_uedges G)"
  using assms
proof (induction G rule: pair_list.induct)
  case 1
  then show ?case by auto
next
  case (2 v N\<^sub>v G)
  hence "distinct (comp_uedges G)"
    using adj_list_invar_tl by auto

  have "\<And>x y. (uEdge x y) \<in> set (map uedge_rep (comp_uedges G)) \<Longrightarrow> x \<noteq> v"
    sorry

  thm graph_adj_list.map_delete_adj_map_invar

  then show ?case 
    apply (auto simp: Let_def)
    sorry
qed

lemma map_rep_comp_uedges: 
  assumes "adj_list_invar G" 
  shows "map uedge_rep (comp_uedges G) = comp_uedges G"
  using assms
proof (induction G rule: pair_list.induct)
  case 1
  then show ?case by auto
next
  case (2 v N\<^sub>v G)
  hence "adj_list_invar G"
    using adj_list_invar_tl by auto
  hence "distinct (map uedge_rep (comp_uedges G))"
    using 2 by auto
  hence "\<And>x y. (uEdge x y) \<in> set (map uedge_rep (comp_uedges G)) \<Longrightarrow> x \<noteq> v"
    sorry

  thm graph_adj_list.map_delete_adj_map_invar

  then show ?case 
    apply (auto simp: Let_def)
    sorry
qed

lemma 
  assumes "adj_list_invar ((v,N\<^sub>v)#G)" 
  shows "adj_list_invar G"
proof -
  have "distinct (map fst G)"
    using assms[unfolded adj_list_invar_def] by auto
  moreover have "\<forall>v. lset_invar (graph_adj_list.\<N> G v)"
    using assms[unfolded adj_list_invar_def]
    sorry
  ultimately show ?thesis
    apply (auto simp: adj_list_invar_def)
    sorry
qed

lemma comp_uedges_of_adj_list: 
  assumes "adj_list_invar G"
  shows "uedge ` set (comp_uedges G) = uedges_of_adj_list G"
  using assms
proof (induction G rule: pair_list.induct)
  case 1
  thus ?case 
    by (auto simp: graph_adj_list.uedges_empty[unfolded lmap_empty_def])
next
  case (2 v N\<^sub>v G)
  hence "adj_list_invar G"
    unfolding adj_list_invar_def
    by (auto simp: adj_list_invar_def)
  hence "uedge ` set (comp_uedges G) = uedges_of_adj_list G"
    by auto

  then show ?case 
    
    sorry
qed

fun fold_uedges :: "(('a \<times> 'a) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a graph_adj_list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "fold_uedges f G a\<^sub>0 = fold f (comp_uedges G) a\<^sub>0"

lemma fold_edges_specs:
  assumes "adj_list_invar G" 
  obtains es where "distinct (map uedge es)" "uedge ` set es = uedges_of_adj_list G" 
    "fold_uedges f G a\<^sub>0 = fold f es a\<^sub>0" 
  using assms distinct_comp_uedges comp_uedges_of_adj_list by fastforce

lemma fold_edges_specs': "\<And>G f a\<^sub>0. adj_list_invar G \<Longrightarrow> ugraph_adj_list_invar G \<Longrightarrow>
    \<exists>es. distinct (map uedge es) \<and> uedge ` set es = uedges_of_adj_list G \<and> fold_uedges f G a\<^sub>0 = fold f es a\<^sub>0" 
  using fold_edges_specs by metis

global_interpretation ugraph_adj_list_fold: ugraph_adj_map_fold 
  lmap_empty lmap_update lmap_delete lmap_lookup lmap_invar
  lset_empty lset_insert lset_delete lset_isin lset_set lset_invar fold_uedges
  apply unfold_locales
  apply (intro fold_edges_specs'[unfolded adj_list_invar_def ugraph_adj_list_invar_def uedges_of_adj_list_def])
  apply simp+
  done

value "\<N>_adj_list [(1::nat,[2::nat,3])] (1::nat)"

thm path_dist_adj_list_def

locale ugraph_adj_list = \<comment> \<open>Undirected graph represented by an adjacency list.\<close>
  fixes G :: "'a graph_adj_list"
  assumes adj_list_invar: "adj_list_invar G"
      and graph_invar: "ugraph_adj_list_invar G"
begin

end

end