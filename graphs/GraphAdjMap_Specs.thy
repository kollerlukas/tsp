theory GraphAdjMap_Specs
  imports Main tsp.Misc tsp.Berge "HOL-Data_Structures.Map_Specs" "HOL-Data_Structures.Set_Specs"
    tsp.WeightedGraph tsp.HamiltonianCycle tsp.TravelingSalesman tsp.VertexCover
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

locale fold_set2 =
  Set2 empty delete isin set invar insert union inter diff
  for empty :: "'set" and delete isin set invar and insert :: "'a \<Rightarrow> 'set \<Rightarrow> 'set" and union inter diff +
  fixes fold_set :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'set \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes finite_sets: "\<And>X. finite (set X)"
  assumes fold_set: "\<And>X f a. invar X \<Longrightarrow> \<exists>xs. distinct xs \<and> List.set xs = set X \<and> fold_set f X a = fold f xs a"
begin

lemma fold_setE:
  assumes "invar X"    
  obtains xs where "distinct xs" "List.set xs = set X" "fold_set f X a = fold f xs a"
  using assms fold_set by blast

end

locale filter_set2 =
  fold_set2 empty delete isin set invar insert union inter diff fold_set
  for empty :: "'set" and delete isin set invar and insert :: "'a \<Rightarrow> 'set \<Rightarrow> 'set" and union inter 
    diff and fold_set :: "('a \<Rightarrow> 'set \<Rightarrow> 'set) \<Rightarrow> 'set \<Rightarrow> 'set \<Rightarrow> 'set"
begin

fun filter_set where
  "filter_set f X = fold_set (\<lambda>x. if f x then insert x else id) X empty"

lemma invar_filter_set: 
  assumes "invar X"
  shows "invar (filter_set f X)"
proof -
  let ?f="\<lambda>x. if f x then insert x else id"
  obtain xs where "distinct xs" "List.set xs = set X" "fold_set ?f X empty = fold ?f xs empty"
    using assms by (elim fold_setE)
  moreover have "\<And>X. invar X \<Longrightarrow> invar (fold ?f xs X)"
    by (induction xs) (auto simp add: set_specs)
  ultimately show ?thesis
    using set_specs by auto
qed

lemma filter_set_elim:
  assumes "invar X"
  obtains xs where "distinct xs" "List.set xs = set X" "set (filter_set f X) = List.set (filter f xs)"
proof -
  let ?f="\<lambda>x. if f x then insert x else id"
  obtain xs where distinct_set: "distinct xs" "List.set xs = set X" 
    and "fold_set ?f X empty = fold ?f xs empty"
    using assms by (elim fold_setE)
  hence "set (filter_set f X) = set (set_of_list (filter f xs))"
    by (auto simp add: fold_filter set_of_list)
  also have "... = List.set (filter f xs)"
    by (auto simp add: set_of_list simp del: set_of_list.simps)
  finally show ?thesis
    using that distinct_set by auto
qed

end

section \<open>Abstract Adjacency Map\<close>

locale graph_adj_map = 
  Map map_empty update map_delete lookup map_invar + 
  Set2 set_empty set_delete isin set set_invar insert union inter diff
  for map_empty :: "'map" and update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map" and map_delete lookup 
    map_invar and set_empty :: "'vset" and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and set_delete isin set 
    set_invar union inter diff
begin

end

subsection \<open>Definitions\<close>

text \<open>We redefine most definitions on graphs for adjacency maps.\<close>

context graph_adj_map
begin

definition neighborhood ("\<N>") where
  "neighborhood M v \<equiv> the_default (lookup M v) set_empty" 
  \<comment> \<open>Neighbourhood of a vertex \<open>x\<close> in the adjacency map \<open>M\<close>.\<close>

lemma neighborhood_empty: "\<N> map_empty v = set_empty"
  unfolding neighborhood_def by (auto simp: map_specs)

lemma lookup_non_empty_neighborhood: "isin (\<N> M u) v \<Longrightarrow> lookup M u = Some (\<N> M u)"
  unfolding neighborhood_def by (metis invar_empty set_empty mem_not_empty set_isin the_default.elims)

lemma neighborhood_update: "map_invar M \<Longrightarrow> \<N> (update v N\<^sub>v M) = (\<N> M)(v := N\<^sub>v)"
  unfolding neighborhood_def by (auto simp: map_specs)

lemma neighborhood_map_delete: "map_invar M \<Longrightarrow> \<N> (map_delete v M) = (\<N> M)(v := set_empty)"
  unfolding neighborhood_def by (auto simp: map_specs)

abbreviation "adj_map_invar M \<equiv> map_invar M \<and> (\<forall>v. set_invar (\<N> M v))"

lemma map_delete_set_invar:
  assumes "adj_map_invar M"
  shows "set_invar (\<N> (map_delete u M) v)"
proof cases
  assume "u = v"
  hence "\<N> (map_delete u M) v = set_empty"
    using assms by (auto simp: neighborhood_map_delete) 
  thus ?thesis
    by (auto simp: set_specs)
next
  assume "u \<noteq> v"
  hence "\<N> (map_delete u M) v = \<N> M v"
    using assms by (auto simp: neighborhood_map_delete)
  thus ?thesis
    using assms by auto
qed

lemma map_delete_adj_map_invar: "adj_map_invar M \<Longrightarrow> adj_map_invar (map_delete x M)"
  using map_specs by (auto simp: map_delete_set_invar)

lemma update_adj_map_invar: "adj_map_invar M \<Longrightarrow> set_invar N\<^sub>v \<Longrightarrow> adj_map_invar (update v N\<^sub>v M)"
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

lemma vertices_subgraph:
  assumes "v \<in> vertices M\<^sub>1" "\<And>u v. isin (\<N> M\<^sub>1 u) v \<Longrightarrow> isin (\<N> M\<^sub>2 u) v"
  shows "v \<in> vertices M\<^sub>2"
  using assms(1) apply (rule vertices_memberE)
  using assms(2) apply (auto intro!: vertices_memberI1)[1]
  using assms(2) apply (auto intro!: vertices_memberI2)[1]
  done

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

lemma path_non_empty: "path_betw M u P v \<Longrightarrow> P \<noteq> []"
  by (rule path_betw.cases) auto

lemma singleton_pathI: "v \<in> vertices M \<Longrightarrow> path_betw M v [v] v"
  by (auto intro: path_betw.intros elim: vertices_memberE)

lemma singleton_pathI1: "isin (\<N> M u) v \<Longrightarrow> path_betw M u [u] u"
  by (auto intro: vertices_memberI1 path_betw.intros)

lemma singleton_pathI2: "isin (\<N> M u) v \<Longrightarrow> path_betw M v [v] v"
  by (auto intro: vertices_memberI2 path_betw.intros)

lemma hd_path_betw: "path_betw M u P v \<Longrightarrow> hd P = u"
  by (induction M u P v rule: path_betw.induct) auto

lemma last_path_betw: 
  assumes "path_betw M u P v"
  shows "last P = v"
  using assms path_non_empty by (induction M u P v rule: path_betw.induct) auto

lemma append_path_betw: 
  assumes "path_betw M u P v" "isin (\<N> M v) w" and "invar M"
  shows "path_betw M u (P @ [w]) w"
  using assms by (induction M u P v rule: path_betw.induct) 
    (auto intro: path_betw.intros vertices_memberI2)

lemma path_subgraph:
  assumes "path_betw M\<^sub>1 u P v" "\<And>u v. isin (\<N> M\<^sub>1 u) v \<Longrightarrow> isin (\<N> M\<^sub>2 u) v"
  shows "path_betw M\<^sub>2 u P v"
  using assms vertices_subgraph by (induction M\<^sub>1 u P v rule: path_betw.induct) 
    (auto intro!: path_betw.intros)

lemma path_subpath:
  assumes "path_betw M u (P\<^sub>1 @ w#P\<^sub>2) v"
  shows "path_betw M w (w#P\<^sub>2) v"
  using assms 
proof (induction P\<^sub>1 arbitrary: u)
  case Nil
  moreover hence "w = u"
    using hd_path_betw by fastforce
  ultimately show ?case 
    by auto
next
  case (Cons x P\<^sub>1)
  moreover obtain y where "path_betw M y (P\<^sub>1 @ w#P\<^sub>2) v"
    using Cons.prems by (rule path_betw.cases) auto
  ultimately show ?case 
    by auto
qed
  
lemma path_vertices:
  assumes "path_betw M u P v"
  shows "List.set P \<subseteq> vertices M"
  using assms by (induction M u P v rule: path_betw.induct) (auto intro: vertices_memberI1)

definition "path_dist M u v \<equiv> Min ({enat (length (tl P)) | P. path_betw M u P v \<and> distinct P} \<union> {\<infinity>})" 
  \<comment> \<open>The distance between two nodes in a graph represented by an adjacency map.\<close>

definition "degree_Adj M v \<equiv> (let \<N>\<^sub>v = set (\<N> M v) in if \<N>\<^sub>v = {} then \<infinity> else card \<N>\<^sub>v)"

definition "is_complete_Adj G \<equiv> (\<forall>u v. u \<in> vertices G \<and> v \<in> vertices G \<and> u \<noteq> v \<longrightarrow> isin (\<N> G u) v)"

lemma is_complete_AdjI: 
  "(\<And>u v. u \<in> vertices G \<Longrightarrow> v \<in> vertices G \<Longrightarrow> u \<noteq> v \<Longrightarrow> isin (\<N> G u) v) \<Longrightarrow> is_complete_Adj G"
  unfolding is_complete_Adj_def by auto

lemma is_complete_AdjE: 
  "is_complete_Adj G \<Longrightarrow> u \<in> vertices G \<Longrightarrow> v \<in> vertices G \<Longrightarrow> u \<noteq> v \<Longrightarrow> isin (\<N> G u) v"
  unfolding is_complete_Adj_def by auto

lemma path_betw_in_complete_graph:
  assumes "is_complete_Adj G" "P \<noteq> []" "distinct_adj P" "List.set P \<subseteq> vertices G" "x = hd P" "y = last P"
  shows "path_betw G x P y"
  using assms
proof (induction P arbitrary: x y rule: list012.induct)
  case (3 u v P)
  moreover hence "path_betw G v (v#P) (last (v#P))" "isin (\<N> G u) v"
    by (auto elim!: is_complete_AdjE) 
  ultimately have "path_betw G u (u#v#P) (last (v#P))"
    by (intro path_betw.intros) auto
  thus ?case 
    using 3 by auto
qed (auto intro: path_betw.intros)

definition "is_hc_Adj G T \<equiv> (\<exists>u. path_betw G u T u) \<and> distinct (tl T) \<and> vertices G = List.set (tl T)"
  \<comment> \<open>Definition of a Hamiltonian Cycle for Adjacency Maps.\<close> 

lemma is_hc_AdjI: "(\<exists>u. path_betw G u T u) \<Longrightarrow> distinct (tl T) \<Longrightarrow> vertices G = List.set (tl T) \<Longrightarrow> is_hc_Adj G T"
  by (auto simp: is_hc_Adj_def)

lemma is_hc_AdjE: 
  assumes "is_hc_Adj G T"
  obtains u where "path_betw G u T u" "distinct (tl T)" "vertices G = List.set (tl T)"
  using assms[unfolded is_hc_Adj_def] by auto

definition "is_tsp_Adj G c T \<equiv> is_hc_Adj G T 
  \<and> (\<forall>T'. is_hc_Adj G T' \<longrightarrow> cost_of_path c T \<le> cost_of_path c T')"

lemma is_tsp_AdjI: "is_hc_Adj G T \<Longrightarrow> (\<And>T'. is_hc_Adj G T' \<Longrightarrow> cost_of_path c T \<le> cost_of_path c T') \<Longrightarrow> is_tsp_Adj G c T"
  by (auto simp: is_tsp_Adj_def)

lemma is_tsp_AdjE: 
  assumes "is_tsp_Adj G c T"
  shows "is_hc_Adj G T" "\<And>T'. is_hc_Adj G T' \<Longrightarrow> cost_of_path c T \<le> cost_of_path c T'"
  using assms[unfolded is_tsp_Adj_def] by auto

definition "is_vc_Adj G X \<equiv> 
  (\<forall>u v. isin (\<N> G u) v \<longrightarrow> isin X u \<or> isin X v) \<and> (\<forall>v. isin X v \<longrightarrow> v \<in> vertices G)"
  \<comment> \<open>Definition of a Vertex Cover for Adjacency Maps.\<close> 

lemma is_vc_AdjI: "(\<And>u v. isin (\<N> G u) v \<Longrightarrow> isin X u \<or> isin X v) \<Longrightarrow> (\<And>v. isin X v \<Longrightarrow> v \<in> vertices G) \<Longrightarrow> is_vc_Adj G X"
  by (auto simp: is_vc_Adj_def)

lemma is_vc_AdjE: 
  assumes "is_vc_Adj G X"
  shows "\<And>u v. isin (\<N> G u) v \<Longrightarrow> isin X u \<or> isin X v" "\<And>v. isin X v \<Longrightarrow> v \<in> vertices G"
  using assms[unfolded is_vc_Adj_def] by auto

definition "is_min_vc_Adj G X \<equiv> is_vc_Adj G X \<and> (\<forall>X'. is_vc_Adj G X' \<longrightarrow> card (set X) \<le> card (set X'))"

lemma is_min_vc_AdjI: 
  "is_vc_Adj G X \<Longrightarrow> (\<And>X'. is_vc_Adj G X' \<Longrightarrow> card (set X) \<le> card (set X')) \<Longrightarrow> is_min_vc_Adj G X"
  by (auto simp: is_min_vc_Adj_def)

lemma is_min_vc_AdjE: 
  assumes "is_min_vc_Adj G X"
  shows "is_vc_Adj G X" "\<And>X'. is_vc_Adj G X' \<Longrightarrow> card (set X) \<le> card (set X')"
  using assms[unfolded is_min_vc_Adj_def] by auto

end

section \<open>Undirected Adjacency Map\<close>

datatype 'v uedge = uEdge 'v 'v

definition "set_of_uedge e \<equiv> case e of uEdge u v \<Rightarrow> {u,v}"

locale ugraph_adj_map = 
  graph_adj_map map_empty update map_delete lookup map_invar set_empty insert set_delete isin set 
  set_invar union inter diff
  for map_empty :: "'map" and update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map" and map_delete lookup 
    map_invar and set_empty :: "'vset" and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and set_delete isin set 
    set_invar union inter diff +
  fixes rep :: "'v uedge \<Rightarrow> 'v uedge" \<comment> \<open>Representative-function to identify tuples as an undirected edge.\<close>
  assumes is_rep: "\<And>u v. rep (uEdge u v) = rep (uEdge v u)" 
    "\<And>u v. rep (uEdge u v) = uEdge u v \<or> rep (uEdge u v) = uEdge v u"
begin

definition "uedges G \<equiv> (\<lambda>(u,v). rep (uEdge u v)) ` edges G" 
  \<comment> \<open>Translate adjacency map \<open>M\<close> to a set of undirected edges.\<close>

lemma uedges_def2: "uedges G = {rep (uEdge u v) | u v. isin (\<N> G u) v}"
  unfolding uedges_def set_of_pair_def edges_def by auto

lemma isin_uedges: "isin (\<N> G u) v \<Longrightarrow> rep (uEdge u v) = e \<Longrightarrow> e \<in> uedges G"
  unfolding uedges_def2 by auto

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
    \<comment> \<open>The graph is undirected, thus the directed-edges are symmetric.\<close>

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

lemma rev_path:
  assumes "path_betw G u P v" "ugraph_adj_map_invar G"
  shows "path_betw G v (rev P) u"
  using assms by (induction G u P v rule: path_betw.induct) 
    (auto intro!: path_betw.intros append_path_betw)

lemma finite_paths: 
  assumes "ugraph_adj_map_invar G"
  shows "finite {P | P. path_betw G u P v \<and> distinct P}"
  sorry (* TODO: how to prove *)

lemma distinct_subpath:
  assumes "path_betw G u P v"
  obtains P' where "path_betw G u P' v" "distinct P'" "length P' \<le> length P"
  using assms
proof (induction G u P v arbitrary: thesis rule: path_betw.induct)
  case (singleton_path v G)
  moreover hence "path_betw G v [v] v"
    by (auto intro: path_betw.intros)
  ultimately show ?case 
    by auto
next
  case (prepend_path G u P v w)
  then obtain P' where P'_path: "path_betw G u P' v" "distinct P'" "length P' \<le> length P"
    by auto
  consider "w \<in> List.set P'" | "w \<notin> List.set P'"
    by auto
  thus ?case
  proof cases
    assume "w \<in> List.set P'"
    then obtain P'\<^sub>1 P'\<^sub>2 where [simp]: "P' = P'\<^sub>1 @ w#P'\<^sub>2"
      by (meson split_list)
    hence "distinct (w#P'\<^sub>2)"
      using P'_path by auto
    moreover have "path_betw G w (w#P'\<^sub>2) v"
      using P'_path by (intro path_subpath) auto
    moreover have "length (w#P'\<^sub>2) \<le> length (w#P)"
      using P'_path by auto
    ultimately show ?thesis 
      using prepend_path by auto
  next
    assume "w \<notin> List.set P'"
    moreover hence "distinct (w#P')"
      using P'_path by auto  
    moreover have "path_betw G w (w#P') v"
      using prepend_path P'_path by (auto intro: path_betw.intros)
    moreover have "length (w#P') \<le> length (w#P)"
      using P'_path by auto
    ultimately show ?thesis 
      using prepend_path by auto
  qed
qed

lemma path_dist_less:
  assumes "ugraph_adj_map_invar G" "path_betw G u P v"
  shows "path_dist G u v \<le> length (tl P)"
  using assms(2)
proof (rule distinct_subpath)
  fix P'
  assume "path_betw G u P' v" "distinct P'" "length P' \<le> length P"
  moreover hence "path_dist G u v \<le> length (tl P')"
    unfolding path_dist_def using assms finite_paths by (auto intro!: Min_le)
  ultimately show ?thesis
    by (simp add: order_subst1)
qed

lemma path_dist_less_inf:
  assumes "ugraph_adj_map_invar G" "path_betw G u P v"
  shows "path_dist G u v < \<infinity>"
proof -
  have "path_dist G u v \<le> length (tl P)"
    using assms by (intro path_dist_less)
  also have "... < \<infinity>"
    by auto
  finally show ?thesis
    by auto
qed

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

lemma rep_elim:
  assumes "rep e = rep (uEdge u v)"
  obtains "e = uEdge u v" | "e = uEdge v u"
  using assms is_rep by (cases e) (metis uedge.inject)

lemma rep_cases:
  assumes "rep e = rep (uEdge u v)"
  obtains "rep e = uEdge u v" | "rep e = uEdge v u"
  using assms is_rep by auto

lemma rep_isin_uedges_elim:
  assumes "ugraph_adj_map_invar G" "rep e \<in> uedges G"
  obtains u v where "e = uEdge u v" "isin (\<N> G u) v"
proof -
  obtain u v where "rep e = rep (uEdge u v)" and v_isin_Nu: "isin (\<N> G u) v"
    using assms[unfolded uedges_def2] by auto
  then consider "e = uEdge u v" | "e = uEdge v u"
    by (elim rep_elim)
  thus ?thesis
    using that assms v_isin_Nu by cases auto
qed                       

lemma rep_isin_uedges_elim2:
  assumes "ugraph_adj_map_invar G" "rep (uEdge u v) \<in> uedges G"
  shows "isin (\<N> G u) v"
  using assms rep_isin_uedges_elim by blast

lemma rep_of_edge: "e \<in> uedges G \<Longrightarrow> rep e = e"
  unfolding uedges_def2 by (auto simp add: rep_idem)

lemma rep_of_edge_is_edge: "e \<in> uedges G \<Longrightarrow> rep e \<in> uedges G"
  unfolding uedges_def by (auto simp add: rep_idem)

lemma isin_uedges_elim:
  assumes "ugraph_adj_map_invar G" "e \<in> uedges G"
  obtains u v where "e = uEdge u v" "isin (\<N> G u) v"
proof -
  have "rep e \<in> uedges G"
    using assms by (auto simp add: rep_of_edge)
  thus ?thesis
    using assms that by (elim rep_isin_uedges_elim)
qed

lemma uedge_not_refl_elim:
  assumes "ugraph_adj_map_invar G" "e \<in> uedges G"
  obtains u v where "rep e = uEdge u v" "u \<noteq> v"
  using assms
proof (rule isin_uedges_elim)
  fix u v
  assume "e = uEdge u v" "isin (\<N> G u) v"
  moreover hence "u \<noteq> v"
    using assms by (auto intro: adj_vertices_neq)
  ultimately show ?thesis
    using assms that by (auto simp: rep_of_edge)
qed

lemma uedge_not_refl:
  assumes "ugraph_adj_map_invar G" "rep (uEdge u v) \<in> uedges G"
  shows "u \<noteq> v"
proof -
  have "isin (\<N> G u) v" 
    using assms rep_isin_uedges_elim by blast
  thus "u \<noteq> v"
    using assms by (auto intro: adj_vertices_neq)
qed

lemma rep_eq_iff: "rep (uEdge u\<^sub>1 v\<^sub>1) = rep (uEdge u\<^sub>2 v\<^sub>2) \<longleftrightarrow> (u\<^sub>1 = u\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2) \<or> (u\<^sub>1 = v\<^sub>2 \<and> v\<^sub>1 = u\<^sub>2)"
proof
  consider "rep (uEdge u\<^sub>1 v\<^sub>1) = uEdge u\<^sub>1 v\<^sub>1" "rep (uEdge u\<^sub>2 v\<^sub>2) = uEdge u\<^sub>2 v\<^sub>2"
    | "rep (uEdge u\<^sub>1 v\<^sub>1) = uEdge u\<^sub>1 v\<^sub>1" "rep (uEdge u\<^sub>2 v\<^sub>2) = uEdge v\<^sub>2 u\<^sub>2"
    | "rep (uEdge u\<^sub>1 v\<^sub>1) = uEdge v\<^sub>1 u\<^sub>1" "rep (uEdge u\<^sub>2 v\<^sub>2) = uEdge u\<^sub>2 v\<^sub>2"
    | "rep (uEdge u\<^sub>1 v\<^sub>1) = uEdge v\<^sub>1 u\<^sub>1" "rep (uEdge u\<^sub>2 v\<^sub>2) = uEdge v\<^sub>2 u\<^sub>2"
    using is_rep by auto
  moreover assume "rep (uEdge u\<^sub>1 v\<^sub>1) = rep (uEdge u\<^sub>2 v\<^sub>2)"
  ultimately consider "uEdge u\<^sub>1 v\<^sub>1 = uEdge u\<^sub>2 v\<^sub>2" | "uEdge u\<^sub>1 v\<^sub>1 = uEdge v\<^sub>2 u\<^sub>2"
    | "uEdge v\<^sub>1 u\<^sub>1 = uEdge u\<^sub>2 v\<^sub>2" | "uEdge v\<^sub>1 u\<^sub>1 = uEdge v\<^sub>2 u\<^sub>2"
    by cases fastforce+
  thus "(u\<^sub>1 = u\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2) \<or> (u\<^sub>1 = v\<^sub>2 \<and> v\<^sub>1 = u\<^sub>2)"
    by cases auto
next
  assume "(u\<^sub>1 = u\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2) \<or> (u\<^sub>1 = v\<^sub>2 \<and> v\<^sub>1 = u\<^sub>2)"
  thus "rep (uEdge u\<^sub>1 v\<^sub>1) = rep (uEdge u\<^sub>2 v\<^sub>2)"
    using is_rep by auto
qed

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

lemma inj_set_of_uedge:
  assumes "ugraph_adj_map_invar G"
  shows "inj_on set_of_uedge (uedges G)"
proof
  fix e\<^sub>1 e\<^sub>2
  assume "e\<^sub>1 \<in> uedges G"
  moreover then obtain u\<^sub>1 v\<^sub>1 where [simp]: "e\<^sub>1 = uEdge u\<^sub>1 v\<^sub>1" and "isin (\<N> G u\<^sub>1) v\<^sub>1"
    using assms by (elim isin_uedges_elim)
  moreover assume "e\<^sub>2 \<in> uedges G"
  moreover then obtain u\<^sub>2 v\<^sub>2 where [simp]: "e\<^sub>2 = uEdge u\<^sub>2 v\<^sub>2" and "isin (\<N> G u\<^sub>2) v\<^sub>2"
    using assms by (elim isin_uedges_elim)
  moreover assume "set_of_uedge e\<^sub>1 = set_of_uedge e\<^sub>2"
  moreover hence "rep e\<^sub>1 = rep e\<^sub>2"
    unfolding set_of_uedge_def by (auto simp add: rep_eq_iff doubleton_eq_iff)
  ultimately show "e\<^sub>1 = e\<^sub>2"
    by (auto simp add: rep_of_edge)
qed

lemma uedges_anti_sym:
  assumes "ugraph_adj_map_invar G" "uEdge u v \<in> uedges G"
  shows "uEdge v u \<notin> uedges G"
proof (rule ccontr; simp)
  assume "uEdge v u \<in> uedges G"
  moreover have "set_of_uedge (uEdge u v) = set_of_uedge (uEdge v u)"
    unfolding set_of_uedge_def by auto
  ultimately have "uEdge u v = uEdge v u"
    using assms inj_set_of_uedge[unfolded inj_on_def] by auto
  moreover have "uEdge u v \<noteq> uEdge v u"
    using assms uedge_not_refl_elim rep_of_edge by auto
  ultimately show False by blast
qed

lemma card_uedges:
  assumes "ugraph_adj_map_invar G"
  shows "card (set_of_uedge ` uedges G) = card (uedges G)"
  using assms inj_set_of_uedge by (intro card_image)

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

lemma vs_uedges: "Vs (set_of_uedge ` uedges G) = vertices G" 
  using vs_uedges_subset_vertices vertices_subset_vs_uedges by auto

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

section \<open>Equivalence of Graph-Definitions\<close>
  
(* TODO: connect with definitions for set-set graph representation *)

context graph_adj_map
begin

end

context ugraph_adj_map
begin

lemma graph_invar:
  assumes "ugraph_adj_map_invar G" 
  shows "graph_invar (set_of_uedge ` uedges G)" (is "graph_invar ?E")
  apply (intro graph_invarI2)
  sorry

lemma path_equiv: 
  assumes "ugraph_adj_map_invar G" "path_betw G u P v"
  shows "walk_betw (set_of_uedge ` uedges G) u P v"
  oops (* TODO *)

lemma degree_equiv:
  assumes "ugraph_adj_map_invar G"
  shows "degree_Adj G v = degree (set_of_uedge ` uedges G) v"
  sorry (* TODO *)

lemma is_complete_equiv: 
  assumes "is_complete_Adj G"
  shows "is_complete (set_of_uedge ` uedges G)"
  using assms by (auto intro!: is_completeI isin_neighborhood_set_edge 
      elim!: is_complete_AdjE simp add: vs_uedges)

lemma is_hc_equiv: 
  assumes "ugraph_adj_map_invar G" "is_hc_Adj G T"
  shows "is_hc (set_of_uedge ` uedges G) T"
  oops (* TODO *)

lemma is_tsp_equiv: 
  assumes "ugraph_adj_map_invar G" "is_tsp_Adj G c T"
  shows "is_tsp (set_of_uedge ` uedges G) c T"
  oops (* TODO *)

lemma is_vc_equiv: 
  assumes "ugraph_adj_map_invar G" "is_vc_Adj G X" "set_invar X"
  shows "is_vc (set_of_uedge ` uedges G) (set X)"
  sorry (* TODO *)

lemma uedges_leq_max_degree_card_vc:
  assumes "ugraph_adj_map_invar G" "set_invar X"
    and max_degree: "\<And>v. v \<in> vertices G \<Longrightarrow> degree_Adj G v \<le> enat k" 
    and vc_X: "is_vc_Adj G X"
  shows "card (uedges G) \<le> k * card (set X)"
  using assms(1)
proof (subst card_uedges[symmetric]; simp; intro graph_abs.card_E_leq_max_degree_card_vc)
  let ?E="set_of_uedge ` uedges G"
  show "graph_abs ?E"
    using assms graph_invar by unfold_locales
  show "\<And>v. v \<in> Vs ?E \<Longrightarrow> degree ?E v \<le> enat k"
    using assms by (auto simp: vs_uedges degree_equiv)
  show "is_vc ?E (set X)"
    using assms by (auto simp: is_vc_equiv)
qed

lemma is_min_vc_equiv: 
  assumes "ugraph_adj_map_invar G" "set_invar X"
  shows "is_min_vc_Adj G X \<longleftrightarrow> is_min_vc (set_of_uedge ` uedges G) (set X)"
  oops (* TODO *)

end

section \<open>Folding Functions for Adjacency Maps\<close>

subsection \<open>Folding Edges of Adjacency Maps\<close>

locale ugraph_adj_map_fold_uedges =
  ugraph_adj_map map_empty update map_delete lookup map_invar set_empty insert set_delete isin set 
  set_invar union inter diff rep
  for map_empty :: "'map" and update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map" and map_delete lookup 
    map_invar and set_empty :: "'vset" and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and set_delete isin set 
    set_invar union inter diff rep +
  fixes fold_uedges :: "('v uedge \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'map \<Rightarrow> 'b \<Rightarrow> 'b" 
    \<comment> \<open>Function that folds the undirected edges of a graph represented by an adjacency map.\<close>
  assumes fold_uedges: "\<And>G f a. ugraph_adj_map_invar G \<Longrightarrow> \<exists>es. distinct es \<and> List.set es = uedges G \<and> fold_uedges f G a = fold f es a"
begin

lemma fold_uedgesE:
  assumes "ugraph_adj_map_invar G"    
  obtains es where "distinct es" "List.set es = uedges G" 
    "fold_uedges f G a = fold f es a"
  using assms fold_uedges by blast

lemma fold_neq_obtain_edge:
  assumes "ugraph_adj_map_invar G" "fold_uedges f G a \<noteq> a"
  obtains e where "e \<in> uedges G" "f e a \<noteq> a"
proof -
  obtain es where "distinct es" and set_es: "List.set es = uedges G" and
    "fold_uedges f G a = fold f es a"
    using assms by (elim fold_uedgesE)
  thus ?thesis
    using that assms by (auto elim!: fold_neq_find)
qed

end

subsection \<open>Folding Vertices of Adjacency Maps\<close>

locale ugraph_adj_map_fold_vset =
  ugraph_adj_map map_empty update map_delete lookup map_invar set_empty insert set_delete isin set 
  set_invar union inter diff rep
  for map_empty :: "'map" and update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'map \<Rightarrow> 'map" and map_delete lookup 
    map_invar and set_empty :: "'vset" and insert :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset" and set_delete isin set 
    set_invar union inter diff rep +
  fixes fold_vset :: "('v \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'vset \<Rightarrow> 'b \<Rightarrow> 'b"
  \<comment> \<open>Function that folds the vertices of a graph represented by an adjacency map.\<close>
  assumes finite_sets: "\<And>X. finite (set X)"
  assumes fold_vset: "\<And>X f a. set_invar X \<Longrightarrow> \<exists>xs. distinct xs \<and> List.set xs = set X \<and> fold_vset f X a = fold f xs a"
begin

lemma fold_vsetE:
  assumes "set_invar X"
  obtains xs where "distinct xs" "List.set xs = set X" "fold_vset f X a = fold f xs a"
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

subsection \<open>Compute Adjacency Maps from Set of Vertices\<close>

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

end