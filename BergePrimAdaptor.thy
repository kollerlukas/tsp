(* Author: Lukas Koller *)
theory BergePrimAdaptor
  imports Main Misc "Prim_Dijkstra_Simple.Undirected_Graph" MST
    (* "Prim_Dijkstra_Simple.Prim_Impl" *)
begin

text \<open>Translate graph from \<open>Berge\<close> to graph from \<open>Prim_Dijkstra_Simple.Undirected_Graph\<close>.\<close>
definition "prim_of_berge E \<equiv> Undirected_Graph.graph (Vs E) {(u,v)| u v. {u,v} \<in> E}"

text \<open>Function to translate from \<open>Berge.path\<close> to \<open>Undirected_Graph.path\<close>.\<close>
fun dedges_of_path where
  "dedges_of_path [] = []"
| "dedges_of_path [v] = []"
| "dedges_of_path (u#v#P) = (u,v) # (dedges_of_path (v#P))"

lemma dedges_length: "length (dedges_of_path P) = length (edges_of_path P)"
  by (induction P rule: dedges_of_path.induct) auto

lemma dedges_of_path_nilE:
  assumes "dedges_of_path P = []"
  obtains v where "P = [] \<or> P = [v]"
  using assms by (induction P rule: dedges_of_path.induct) auto

lemma dedges_of_path_nonnilE:
  assumes "dedges_of_path P \<noteq> []"
  shows "P \<noteq> []" "\<And>v. P \<noteq> [v]"
  using assms by auto

lemma dedges_of_path_nil_length: "dedges_of_path P = [] \<Longrightarrow> length P \<le> 1"
  by (induction P rule: dedges_of_path.induct) auto

lemma dedges_of_path_nonnil:
  assumes "length P > 1"
  shows "dedges_of_path P \<noteq> []"
  using assms by (induction P rule: dedges_of_path.induct) auto

lemma map_dedges_of_path: "map uedge (dedges_of_path P) = edges_of_path P"
  by (induction P rule: dedges_of_path.induct) auto 

lemma tl_dedges_of_path:
  assumes "P = dedges_of_path P'"
  shows "tl P = dedges_of_path (tl P')"
  using assms by (induction P' rule: dedges_of_path.induct) auto

lemma prim_epath_last_node:
  assumes "P \<noteq> []" "hd P = u" "Undirected_Graph.path G u (dedges_of_path P) v"
  shows "last P = v"
  using assms by (induction P arbitrary: u rule: dedges_of_path.induct) auto

lemma simple_path_equiv1: 
  assumes "is_simple P" 
  shows "Undirected_Graph.simple (dedges_of_path P)"
  unfolding Undirected_Graph.simple_def using assms 
  by (auto elim: is_simpleE simp: map_dedges_of_path)

lemma simple_path_equiv2: 
  assumes "Undirected_Graph.simple (dedges_of_path P)" 
  shows "is_simple P"
  unfolding Undirected_Graph.simple_def using assms
  by (auto intro: is_simpleI simp: simple_def map_dedges_of_path)

text \<open>Function to translate from \<open>Undirected_Graph.path\<close> to \<open>Berge.path\<close>.\<close>
fun vpath_of_epath where
  "vpath_of_epath [] = []"
| "vpath_of_epath P = map fst P @ [snd (last P)]"

lemma vpath_of_epathE:
  assumes "P\<^sub>v = vpath_of_epath P"
  obtains "P\<^sub>v = []" | u v vs where "P\<^sub>v = u#v#vs"
  using assms by (induction P rule: list012.induct) auto

lemma berge_vpath_of_epath:
  assumes "path E P" "length P > 1"
  shows "P = vpath_of_epath (dedges_of_path P)"
  using assms by (induction P rule: list0123.induct) auto

lemma walk_vpath_elim:
  assumes "walk_betw E u P\<^sub>v v"
  obtains "P\<^sub>v = [u]" "u = v" | P where "P\<^sub>v = vpath_of_epath P"
  using assms walk_between_nonempty_path[OF assms(1)]
proof (induction P\<^sub>v rule: list012.induct)
  case (3 u v P\<^sub>v)
  hence "u#v#P\<^sub>v = vpath_of_epath (dedges_of_path (u#v#P\<^sub>v))"
    by (intro berge_vpath_of_epath) auto
  then show ?case 
    using 3 by blast
qed auto

lemma prim_vpath_of_epath:
  assumes "Undirected_Graph.path G u P v"
  shows "P = dedges_of_path (vpath_of_epath P)"
  using assms
proof (induction P arbitrary: u rule: dedges_of_path.induct)
  case (3 e\<^sub>1 e\<^sub>2 P)
  then obtain x\<^sub>1 x\<^sub>2 where 
    [simp]: "e\<^sub>1 = (u,x\<^sub>1)" and "e\<^sub>1 \<in> edges G" "Undirected_Graph.path G x\<^sub>1 (e\<^sub>2#P) v" and
    [simp]: "e\<^sub>2 = (x\<^sub>1,x\<^sub>2)" and "e\<^sub>2 \<in> edges G" "Undirected_Graph.path G x\<^sub>2 P v"
    by auto
  hence "e\<^sub>1#e\<^sub>2#P = (u,x\<^sub>1)#dedges_of_path (vpath_of_epath (e\<^sub>2#P))"
    using "3.IH" by fastforce
  also have "... = dedges_of_path (vpath_of_epath (e\<^sub>1#e\<^sub>2#P))"
    by auto
  finally show ?case .
qed auto

lemma prim_vpath_of_epathE:
  assumes "Undirected_Graph.path G u P v"
  obtains P' where "P = dedges_of_path P'"
  using assms prim_vpath_of_epath[of G] by auto



context graph_abs
begin

lemma prim_finite: "finite (Vs E)" "finite {(u,v)| u v. {u,v} \<in> E}"
  using graph finite_subset[of "{(u,v)| u v. {u,v} \<in> E}" "Vs E \<times> Vs E"] 
  by (auto intro: vs_member_intro)

lemma prim_nodes_aux: "fst ` {(u,v) |u v. {u,v} \<in> E} \<union> snd ` {(u,v) |u v. {u,v} \<in> E} \<subseteq> Vs E" 
  (is "fst ` ?V \<union> snd ` ?V \<subseteq> Vs E")
proof 
  fix v
  assume "v \<in> fst ` ?V \<union> snd ` ?V"
  then consider "v \<in> fst ` ?V" | "v \<in> snd ` ?V"
    by auto
  thus "v \<in> Vs E"
    by cases (auto intro: edges_are_Vs)
qed

lemma prim_nodes[simp]: "nodes (prim_of_berge E) = Vs E"
  unfolding prim_of_berge_def using graph_accs[OF prim_finite] prim_nodes_aux 
  by (auto simp: Un_absorb2)

lemma prim_edges[simp]: "edges (prim_of_berge E) = {(u,v)| u v. {u,v} \<in> E}"
  unfolding prim_of_berge_def using graph graph_accs[OF prim_finite] by (auto simp: insert_commute)

lemma nodes_equiv1: "v \<in> Vs E \<Longrightarrow> v \<in> nodes (prim_of_berge E)"
  using graph_accs[OF prim_finite] by auto

lemma nodes_equiv2: "v \<in> nodes (prim_of_berge E) \<Longrightarrow> v \<in> Vs E"
  by auto

lemma edges_equiv1: "{u,v} \<in> E \<Longrightarrow> (u,v) \<in> edges (prim_of_berge E)"
  by auto

lemma edges_equiv2: "(u,v) \<in> edges (prim_of_berge E) \<Longrightarrow> {u,v} \<in> E"
  by auto

lemma edges_eq: "E = uedge ` edges (prim_of_berge E)"
  using graph by (auto simp: uedge_def)



lemma path_edges_subset1: 
  assumes "set (edges_of_path P) \<subseteq> E"
  shows "set (dedges_of_path P) \<subseteq> edges (prim_of_berge E)"
  using assms by (induction P rule: edges_of_path.induct) auto

lemma path_edges_subset2: 
  assumes "set (dedges_of_path P) \<subseteq> edges (prim_of_berge E)"
  shows "set (edges_of_path P) \<subseteq> E"
  using assms by (induction P rule: dedges_of_path.induct) auto

lemma berge_walk_is_prim_path:
  assumes "walk_betw E u P v"
  shows "Undirected_Graph.path (prim_of_berge E) u (dedges_of_path P) v"
  using assms path_transs1 by (induction u P v rule: induct_walk_betw) auto

lemma prim_path_is_berge_path:
  assumes "set P \<subseteq> Vs E" "Undirected_Graph.path (prim_of_berge E) u (dedges_of_path P) v"
  shows "path E P"
  using assms by (induction P arbitrary: u rule: dedges_of_path.induct) (auto intro: path.intros)

lemma prim_path_is_berge_walk:
  assumes "P \<noteq> []" "hd P = u" "u \<in> Vs E" 
      and "Undirected_Graph.path (prim_of_berge E) u (dedges_of_path P) v"
  shows "walk_betw E u P v"
proof (rule nonempty_path_walk_between)
  have "set (edges_of_path P) \<subseteq> E"
    using path_edges[OF assms(4)] by (intro path_edges_subset2)
  hence "set P \<subseteq> Vs E"
    using assms by (intro edges_of_vpath_are_vs) auto
  thus "path E P" "P \<noteq> []" "hd P = u" "last P = v"
    using assms prim_path_is_berge_path by (auto simp: prim_epath_last_node)
qed

lemma walk_iff_rtrancl_edges: 
  assumes "u \<in> Vs E" "v \<in> Vs E"
  shows "(\<exists>P. walk_betw E u P v) \<longleftrightarrow> (u,v) \<in> (edges (prim_of_berge E))\<^sup>*"
proof
  assume "\<exists>P. walk_betw E u P v"
  thus "(u,v) \<in> (edges (prim_of_berge E))\<^sup>*"
    using berge_walk_is_prim_path by (intro iffD2[OF rtrancl_edges_iff_path]) auto
next
  assume "(u,v) \<in> (edges (prim_of_berge E))\<^sup>*"
  thus "\<exists>P. walk_betw E u P v"
    using assms
  proof (induction rule: rtrancl_induct)
    case base
    hence "walk_betw E u [u] u"
      by (auto intro: path.intros nonempty_path_walk_between)
    thus ?case
      by auto
  next
    case (step y z)
    hence "{y,z} \<in> E" 
      by (intro edges_equiv2)
    moreover hence "y \<in> Vs E"
      by (intro vs_member_intro) auto
    ultimately obtain P where "walk_betw E u P y" "path E [y,z]"
      using step.prems step.IH by (auto intro: path.intros)
    moreover hence "walk_betw E y [y,z] z"
      by (auto intro: path.intros nonempty_path_walk_between)
    ultimately have "walk_betw E u (P @ tl [y,z]) z"
      by (intro walk_transitive)
    thus ?case 
      by auto
  qed  
qed

lemma conn_comp_equiv: 
  assumes "u \<in> Vs E" "v \<in> Vs E"
  shows "v \<in> connected_component E u \<longleftrightarrow> (u,v) \<in> (edges (prim_of_berge E))\<^sup>*"
proof
  assume "v \<in> connected_component E u"
  thus "(u,v) \<in> (edges (prim_of_berge E))\<^sup>*"
    using assms 
    by (intro iffD1[OF walk_iff_rtrancl_edges]) (auto elim: in_connected_component_has_path)
next
  assume "(u,v) \<in> (edges (prim_of_berge E))\<^sup>*"
  hence "(\<exists>p. walk_betw E u p v)"
    using assms by (intro iffD2[OF walk_iff_rtrancl_edges])
  thus "v \<in> connected_component E u"
    by (auto intro: has_path_in_connected_component)
qed

lemma connected_equiv1: 
  assumes "is_connected E" 
  shows "connected (prim_of_berge E)"
proof (rule connectedI)
  fix u v
  assume "u \<in> nodes (prim_of_berge E)" "v \<in> nodes (prim_of_berge E)"
  moreover hence "v \<in> connected_component E u"
    using assms by (auto elim: is_connectedE)
  ultimately show "(u,v) \<in> (edges (prim_of_berge E))\<^sup>*"
    using conn_comp_equiv by auto
qed

lemma connected_equiv2: 
  assumes "connected (prim_of_berge E)" 
  shows "is_connected E"
proof (rule is_connectedI)
  fix u v
  assume "u \<in> Vs E" "v \<in> Vs E"
  moreover hence "(u,v) \<in> (edges (prim_of_berge E))\<^sup>*"
    using assms by (intro connectedD) auto
  ultimately show "v \<in> connected_component E u"
    using conn_comp_equiv by auto
qed

lemma dedges_path_hd_Vs_mem:
  assumes "Undirected_Graph.path (prim_of_berge E) u (dedges_of_path P) v" "dedges_of_path P \<noteq> []"
  shows "hd P = u" "u \<in> Vs E"
  using assms by (induction P rule: dedges_of_path.induct) (auto intro: edges_are_Vs edges_equiv2)

lemma acyclic_equiv1: 
  assumes "is_acyclic E"
  shows "cycle_free (prim_of_berge E)"
proof (rule cycle_freeI)
  fix P u
  assume "Undirected_Graph.path (prim_of_berge E) u P u" "P \<noteq> []" "simple P"
  moreover then obtain P' where "P = dedges_of_path P'"
    by (auto elim: prim_vpath_of_epathE)
  moreover have "is_simple P'"
    using calculation by (auto intro: simple_path_equiv2)
  moreover have "0 < length (edges_of_path P')"
    using calculation by (auto simp: dedges_length[symmetric])
  moreover have "walk_betw E u P' u"
    using calculation dedges_path_hd_Vs_mem by (intro prim_path_is_berge_walk) auto
  ultimately have "is_cycle E P'"
    by (auto intro: is_cycleI)
  thus "False"
    using assms is_acyclicE by auto
qed

lemma acyclic_equiv2: 
  assumes "cycle_free (prim_of_berge E)"
  shows "is_acyclic E"
proof (rule ccontr)
  assume "\<not> is_acyclic E"
  then obtain C where "is_cycle E C"
    by (auto elim: not_acyclicE)
  then obtain u where "is_simple C" "0 < length (edges_of_path C)" "walk_betw E u C u"
    by (auto elim: is_cycleE)
  moreover hence "Undirected_Graph.path (prim_of_berge E) u (dedges_of_path C) u"
    by (intro berge_walk_is_prim_path)
  moreover have "dedges_of_path C \<noteq> []"
    using calculation by (auto simp: dedges_length[symmetric])
  moreover have "simple (dedges_of_path C)"
    using calculation by (intro simple_path_equiv1)
  ultimately show "False"
    using assms by (intro cycle_freeD) auto
qed

lemma tree_equiv1: "is_tree E \<Longrightarrow> tree (prim_of_berge E)"
  unfolding tree_def using connected_equiv1 acyclic_equiv1 is_treeE by auto

lemma tree_equiv2: "tree (prim_of_berge E) \<Longrightarrow> is_tree E" 
  using connected_equiv2 acyclic_equiv2 by (auto intro: is_treeI simp: tree_def)

end

locale graph_abs2 = 
  E\<^sub>1: graph_abs E\<^sub>1 +
  E\<^sub>2: graph_abs E\<^sub>2 for E\<^sub>1 :: "'a set set" and E\<^sub>2 :: "'a set set"
begin

lemma st_equiv1: 
  assumes "E\<^sub>1.is_st E\<^sub>2"
  shows "is_spanning_tree (prim_of_berge E\<^sub>1) (prim_of_berge E\<^sub>2)"
  unfolding is_spanning_tree_def
proof (intro conjI)
  have "is_tree E\<^sub>2"
    using assms by (elim E\<^sub>1.is_stE)
  thus "tree (prim_of_berge E\<^sub>2)"
    by (intro E\<^sub>2.tree_equiv1)

  have "Vs E\<^sub>1 = Vs E\<^sub>2"
    using assms by (elim E\<^sub>1.is_stE)
  thus "nodes (prim_of_berge E\<^sub>2) = nodes (prim_of_berge E\<^sub>1)"
    by auto

  have "E\<^sub>2 \<subseteq> E\<^sub>1"
    using assms by (elim E\<^sub>1.is_stE)
  thus "edges (prim_of_berge E\<^sub>2) \<subseteq> edges (prim_of_berge E\<^sub>1)"
    by auto
qed

lemma st_equiv2: 
  assumes "is_spanning_tree (prim_of_berge E\<^sub>1) (prim_of_berge E\<^sub>2)"
  shows "E\<^sub>1.is_st E\<^sub>2"
  using assms[unfolded is_spanning_tree_def] 
proof (intro E\<^sub>1.is_stI)
  have "tree (prim_of_berge E\<^sub>2)"
    using assms[unfolded is_spanning_tree_def] by auto
  thus "is_tree E\<^sub>2"
    by (intro E\<^sub>2.tree_equiv2)

  have "nodes (prim_of_berge E\<^sub>2) = nodes (prim_of_berge E\<^sub>1)" 
    using assms[unfolded is_spanning_tree_def] by auto
  thus "Vs E\<^sub>1 = Vs E\<^sub>2"
    by auto

  have "edges (prim_of_berge E\<^sub>2) \<subseteq> edges (prim_of_berge E\<^sub>1)"
    using assms[unfolded is_spanning_tree_def] by auto
  thus "E\<^sub>2 \<subseteq> E\<^sub>1"  
    by (subst E\<^sub>2.edges_eq; subst E\<^sub>1.edges_eq) auto
qed

end

context graph_abs
begin

lemma st_equiv1: "is_st T \<Longrightarrow> is_spanning_tree (prim_of_berge E) (prim_of_berge T)"
  using st_is_graph by (intro graph_abs2.st_equiv1) unfold_locales

lemma spanning_tree_is_graph:
  assumes "is_spanning_tree (prim_of_berge E) (prim_of_berge T)"
  shows "graph_invar T"
  sorry (* TODO *)

lemma st_equiv2: "is_spanning_tree (prim_of_berge E) (prim_of_berge T) \<Longrightarrow> is_st T"
  using spanning_tree_is_graph by (intro graph_abs2.st_equiv2) unfold_locales

end

locale nat_w_graph_abs = (* nat weights *)
  pos_w_graph_abs E c for E :: "'a set set" and c :: "'a set \<Rightarrow> nat"
begin

lemma cost_of_st_eq: "graph_invar T \<Longrightarrow> cost_of_st T = weight c (prim_of_berge T)"
  by (subst graph_abs.edges_eq[of T]; unfold_locales) (auto simp: Undirected_Graph.weight_alt)

lemma mst_equiv1:
  assumes "is_mst T"
  shows "is_MST c (prim_of_berge E) (prim_of_berge T)"
  unfolding is_MST_def
proof
  have "is_st T"
    using assms by (auto elim: is_mstE)
  thus "is_spanning_tree (prim_of_berge E) (prim_of_berge T)"
    by (intro st_equiv1)
  show " \<forall>T'. is_spanning_tree (prim_of_berge E) T' \<longrightarrow> weight c (prim_of_berge T) \<le> weight c T'"
    sorry
qed

lemma mst_equiv2:
  assumes "is_MST c (prim_of_berge E) (prim_of_berge T)"
  shows "is_mst T"
proof (intro is_mstI)
  show "is_st T"
    using assms[unfolded is_MST_def] by (auto intro: st_equiv2)
  show "\<And>T'. is_st T' \<Longrightarrow> cost_of_st T \<le> cost_of_st T'"
  proof -
    fix T'
    assume "is_st T'"
    moreover hence "graph_invar T'"
      by (intro st_is_graph)
    moreover hence "is_spanning_tree (prim_of_berge E) (prim_of_berge T')"
      using calculation by (intro st_equiv1)
    moreover hence "weight c (prim_of_berge T) \<le> weight c (prim_of_berge T')"
      using assms[unfolded is_MST_def] by auto
    moreover have "graph_invar T"
      using \<open>is_st T\<close> by (intro st_is_graph)
    ultimately show "cost_of_st T \<le> cost_of_st T'"
      by (auto simp: cost_of_st_eq)
  qed
qed

end

text \<open>Translate graph from \<open>Prim_Dijkstra_Simple.Undirected_Graph\<close> to graph from \<open>Berge\<close>.\<close>
definition "berge_of_prim G \<equiv> uedge ` edges G"

locale prim_graph_abs =
  fixes V E G
  defines "G \<equiv> graph V E"
  assumes finite_V: "finite V" and finite_E: "finite E"
      and E_irrefl: "irrefl E" and V_subset: "V \<subseteq> fst ` E \<union> snd ` E"
begin

lemma edges_G[simp]: "edges G = E \<union> E\<inverse>" 
  and nodes_G[simp]: "nodes G = fst ` E \<union> snd ` E"
  unfolding G_def using graph_accs[OF finite_V finite_E] E_irrefl V_subset 
  by (auto simp: irrefl_def)

lemma berge_edges_invar:
  assumes "e \<in> berge_of_prim G"
  obtains u v where "e = {u,v}" "u \<noteq> v" "(u,v) \<in> edges G"
proof -
  obtain u v where "e = {u,v}" "(u,v) \<in> edges G"
    using assms by (auto simp: berge_of_prim_def uedge_def)
  moreover hence "u \<noteq> v"
    by (intro edges_irreflI)
  ultimately show ?thesis
    using that by auto
qed

lemma berge_finite: "finite (berge_of_prim G)"
  unfolding berge_of_prim_def uedge_def using finite_E by blast

lemma berge_finite_Vs: "finite (Vs (berge_of_prim G))"
  using berge_finite berge_edges_invar by (auto intro: finite_VsI)
  
lemma berge_graph: "graph_invar (berge_of_prim G)"
  using berge_finite berge_edges_invar by (intro graph_invarI2) metis+

lemma edges_equiv1: "(u,v) \<in> edges G \<Longrightarrow> {u,v} \<in> berge_of_prim G"
  unfolding berge_of_prim_def uedge_def by auto

lemma edges_equiv1_uedge: "e \<in> edges G \<Longrightarrow> uedge e \<in> berge_of_prim G"
  unfolding berge_of_prim_def uedge_def by auto

lemma edges_equiv2: "{u,v} \<in> berge_of_prim G \<Longrightarrow> (u,v) \<in> edges G"
  using berge_edges_invar by (metis doubleton_eq_iff edges_sym')+

lemma berge_of_prim_def2: "berge_of_prim G = {{u,v} | u v. (u,v) \<in> edges G}"
  unfolding berge_of_prim_def by (auto simp add: uedge_def)
  
lemma berge_nodes[simp]: "Vs (berge_of_prim G) = nodes G"
proof 
  show "Vs (berge_of_prim G) \<subseteq> nodes G"
  proof
    fix v
    assume "v \<in> Vs (berge_of_prim G)"
    then obtain u where "{u,v} \<in> berge_of_prim G"
      using berge_graph by (elim vs_member_elim2) auto
    hence "(u,v) \<in> edges G"
      using edges_equiv2 by auto
    then consider "(u,v) \<in> E" "u \<noteq> v" | "(v,u) \<in> E" "u \<noteq> v"
      by auto
    thus "v \<in> nodes G"
      by cases force+
  qed
next
  show "nodes G \<subseteq> Vs (berge_of_prim G)"
  proof 
    fix v
    assume "v \<in> nodes G"
    then consider u where "(v,u) \<in> E" | u where "(u,v) \<in> E"
      by force
    thus "v \<in> Vs (berge_of_prim G)"
      by cases (fastforce intro: edges_are_Vs[OF edges_equiv1])+
  qed
qed

lemma nodes_equiv1: "v \<in> nodes G \<Longrightarrow> v \<in> Vs (berge_of_prim G)"
  by auto

lemma nodes_equiv2: "v \<in> Vs (berge_of_prim G) \<Longrightarrow> v \<in> nodes G"
  by auto



lemma path_edges_subset1: 
  assumes "set (edges_of_path P) \<subseteq> berge_of_prim G"
  shows "set (dedges_of_path P) \<subseteq> edges G"
  using assms 
proof (induction P rule: edges_of_path.induct)
  case (3 u v P)
  moreover hence "(u,v) \<in> edges G"
    by (intro edges_equiv2) auto
  ultimately show ?case
    by auto
qed auto

lemma path_edges_subset2: 
  assumes "set (dedges_of_path P) \<subseteq> edges G"
  shows "set (edges_of_path P) \<subseteq> berge_of_prim G"
  using assms by (induction P rule: dedges_of_path.induct) (auto simp: berge_of_prim_def2)

thm induct_walk_betw

lemma berge_walk_is_prim_path:
  assumes "walk_betw (berge_of_prim G) u (vpath_of_epath P) v" (is "walk_betw ?E u ?P v")
  shows "Undirected_Graph.path G u P v"
  using assms
proof (induction u "vpath_of_epath P" v arbitrary: P rule: induct_walk_betw)
  case (path1 v)
  thus ?case 
    by (auto elim: vpath_of_epathE)
next
  case (path2 u v P\<^sub>v w)

  hence "(u,v) \<in> edges G"
    by (intro edges_equiv2)


  thm vpath_of_epathE

  then show ?case 
    sorry
qed

lemma prim_path_is_berge_path:
  assumes "Undirected_Graph.path G u P v"
  shows "path (berge_of_prim G) (vpath_of_epath P)"
  using assms 
proof (induction P arbitrary: u rule: list012.induct)
  case (2 e)
  then obtain u v where "e = (u,v)" "e \<in> edges G"
    by auto
  moreover hence "vpath_of_epath [e] = [u,v]"
    by auto
  moreover have "{u,v} \<in> berge_of_prim G" 
    using calculation by (intro edges_equiv1) auto
  ultimately show ?case  
    by (subst \<open>vpath_of_epath [e] = [u,v]\<close>) (intro edge_is_path)
next
  case (3 e\<^sub>1 e\<^sub>2 P)
  moreover then obtain x y where "e\<^sub>1 = (u,x)" "e\<^sub>2 = (x,y)" 
    by auto
  ultimately show ?case by (auto intro: edges_equiv1)
qed auto

lemma prim_path_is_berge_walk:
  assumes "P \<noteq> []" "fst (hd P) = u" "u \<in> Vs (berge_of_prim G)" 
      and "Undirected_Graph.path G u P v"
  shows "walk_betw (berge_of_prim G) u (vpath_of_epath P) v"
proof (rule nonempty_path_walk_between)
  show "path (berge_of_prim G) (vpath_of_epath P)"
    using assms by (intro prim_path_is_berge_path)
  show "vpath_of_epath P \<noteq> []"
    using assms by (cases P) auto  
  moreover show "hd (vpath_of_epath P) = u"
    using assms by (cases P) auto
  ultimately show "last (vpath_of_epath P) = v"
    using assms by (metis prim_epath_last_node prim_vpath_of_epath)
qed

lemma walk_iff_rtrancl_edges: 
  assumes "u \<in> Vs (berge_of_prim G)" "v \<in> Vs (berge_of_prim G)"
  shows "(\<exists>P. walk_betw (berge_of_prim G) u P v) \<longleftrightarrow> (u,v) \<in> (edges G)\<^sup>*"
proof
  assume "\<exists>P. walk_betw (berge_of_prim G) u P v"
  then obtain P\<^sub>v where "walk_betw (berge_of_prim G) u P\<^sub>v v"
    by auto
  then consider "P\<^sub>v = [u]" "u = v" | P where "walk_betw (berge_of_prim G) u (vpath_of_epath P) v"
    by (auto elim: walk_vpath_elim)
  thus "(u,v) \<in> (edges G)\<^sup>*"
  proof cases
    fix P
    assume "walk_betw (berge_of_prim G) u (vpath_of_epath P) v"
    thus "(u,v) \<in> (edges G)\<^sup>*"
      using berge_walk_is_prim_path by (intro iffD2[OF rtrancl_edges_iff_path]) auto
  qed auto
next
  assume "(u,v) \<in> (edges G)\<^sup>*"
  thus "\<exists>P. walk_betw (berge_of_prim G) u P v"
    using assms
  proof (induction rule: rtrancl_induct)
    case base
    hence "walk_betw (berge_of_prim G) u [u] u"
      by (intro nonempty_path_walk_between) (auto intro: path1)
    thus ?case
      by auto
  next
    case (step y z)
    hence "{y,z} \<in> (berge_of_prim G)" 
      by (intro edges_equiv1)
    moreover hence "y \<in> Vs (berge_of_prim G)"
      by (intro vs_member_intro) auto
    ultimately obtain P where "walk_betw (berge_of_prim G) u P y" "path (berge_of_prim G) [y,z]"
      using step.prems step.IH by (auto intro: path.intros)
    moreover hence "walk_betw (berge_of_prim G) y [y,z] z"
      by (intro nonempty_path_walk_between) (auto intro: path.intros)
    ultimately have "walk_betw (berge_of_prim G) u (P @ tl [y,z]) z"
      by (intro walk_transitive)
    thus ?case 
      by auto
  qed  
qed

lemma conn_comp_equiv: 
  assumes "u \<in> Vs (berge_of_prim G)" "v \<in> Vs (berge_of_prim G)"
  shows "v \<in> connected_component (berge_of_prim G) u \<longleftrightarrow> (u,v) \<in> (edges G)\<^sup>*"
proof
  assume "v \<in> connected_component (berge_of_prim G) u"
  then obtain P where "walk_betw (berge_of_prim G) u P v" 
    using assms by (elim in_connected_component_has_path) auto
  thus "(u,v) \<in> (edges G)\<^sup>*"
    using assms by (intro iffD1[OF walk_iff_rtrancl_edges]) auto
next
  assume "(u,v) \<in> (edges G)\<^sup>*"
  hence "(\<exists>p. walk_betw (berge_of_prim G) u p v)"
    using assms by (intro iffD2[OF walk_iff_rtrancl_edges])
  thus "v \<in> connected_component (berge_of_prim G) u"
    by (auto intro: has_path_in_connected_component)
qed

lemma connected_equiv1: 
  assumes "is_connected (berge_of_prim G)" 
  shows "connected G"
proof (rule connectedI)
  fix u v
  assume "u \<in> nodes G" "v \<in> nodes G"
  moreover hence "v \<in> connected_component (berge_of_prim G) u"
    using assms by (intro is_connectedE) auto
  ultimately show "(u,v) \<in> (edges G)\<^sup>*"
    using conn_comp_equiv by auto
qed

lemma connected_equiv2: 
  assumes "connected G" 
  shows "is_connected (berge_of_prim G)"
proof (rule is_connectedI)
  fix u v
  assume "u \<in> Vs (berge_of_prim G)" "v \<in> Vs (berge_of_prim G)"
  moreover hence "(u,v) \<in> (edges G)\<^sup>*"
    using assms by (intro connectedD) auto
  ultimately show "v \<in> connected_component (berge_of_prim G) u"
    using conn_comp_equiv by auto
qed

lemma dedges_path_hd_Vs_mem:
  assumes "Undirected_Graph.path G u P v" "P \<noteq> []"
  shows "fst (hd P) = u" "u \<in> Vs (berge_of_prim G)"
  using assms 
proof (induction P rule: dedges_of_path.induct)
  case (2 e)
  {
    case 1
    then show ?case by auto
  next
    case 2
    then show ?case 
      by (intro edges_are_Vs) (auto intro: edges_equiv1)
  }
next
  case (3 e\<^sub>1 e\<^sub>2 P)
  {
    case 1
    then show ?case by auto
  next
    case 2
    moreover hence "uedge e\<^sub>1 \<in> berge_of_prim G"
      by (intro edges_equiv1_uedge) auto
    ultimately show ?case
      by (intro vs_member_intro) auto
  }
qed auto

lemma acyclic_equiv1: 
  assumes "is_acyclic (berge_of_prim G)"
  shows "cycle_free G"
proof (rule cycle_freeI)
  fix P u
  assume "Undirected_Graph.path G u P u" "P \<noteq> []" "simple P"
  moreover hence "P = dedges_of_path (vpath_of_epath P)" (is "P = dedges_of_path ?P")
    apply (intro prim_vpath_of_epath)
    by (auto elim: prim_vpath_of_epathE)
  moreover have "is_simple ?P"
    using calculation by (auto intro: simple_path_equiv2)
  moreover have "0 < length (edges_of_path ?P)"
    using calculation by (auto simp: dedges_length[symmetric])
  moreover have "walk_betw (berge_of_prim G) u ?P u"
    using calculation dedges_path_hd_Vs_mem by (intro prim_path_is_berge_walk)
  ultimately have "is_cycle (berge_of_prim G) ?P"
    by (auto intro: is_cycleI)
  thus "False"
    using assms is_acyclicE by auto
qed

lemma acyclic_equiv2: 
  assumes "cycle_free G"
  shows "is_acyclic (berge_of_prim G)"
proof (rule ccontr)
  assume "\<not> is_acyclic (berge_of_prim G)"
  then obtain C where "is_cycle (berge_of_prim G) C"
    by (auto elim: not_acyclicE)
  then obtain u where "is_simple C" "0 < length (edges_of_path C)" 
    "walk_betw (berge_of_prim G) u C u"
    by (auto elim: is_cycleE)
  moreover hence "1 < length C"
    using edges_of_path_length by (metis zero_less_diff)
  moreover have "walk_betw (berge_of_prim G) u (vpath_of_epath (dedges_of_path C)) u"
    using calculation by (subst berge_vpath_of_epath[symmetric]) auto
  moreover hence "Undirected_Graph.path G u (dedges_of_path C) u"
    by (intro berge_walk_is_prim_path)
  moreover have "dedges_of_path C \<noteq> []"
    using calculation by (auto simp: dedges_length[symmetric])
  moreover have "simple (dedges_of_path C)"
    using calculation by (intro simple_path_equiv1)
  ultimately show "False"
    using assms by (intro cycle_freeD) auto
qed

lemma tree_equiv1: "is_tree (berge_of_prim G) \<Longrightarrow> tree G"
  unfolding tree_def using connected_equiv1 acyclic_equiv1 is_treeE by auto

lemma tree_equiv2: "tree G \<Longrightarrow> is_tree (berge_of_prim G)" 
  using connected_equiv2 acyclic_equiv2 by (auto intro: is_treeI simp: tree_def)

end


(* TODO ... *)

context graph_abs
begin

text \<open>Convert to graph from \<open>Prim_Dijkstra_Simple\<close>.\<close>
abbreviation "G\<^sub>E \<equiv> Undirected_Graph.graph (Vs E) {(u,v)| u v. {u,v} \<in> E}"

end

locale st_graph_abs = (* spanning tree equivalence *)
  E: graph_abs E +
  T: graph_abs T for E :: "'a set set " and T :: "'a set set"
begin

lemma edges_subset_iff: "T \<subseteq> E \<longleftrightarrow> edges T.G\<^sub>E \<subseteq> edges E.G\<^sub>E"
proof
  assume "T \<subseteq> E"
  show "edges T.G\<^sub>E \<subseteq> edges E.G\<^sub>E"
  proof
    fix x
    assume "x \<in> edges T.G\<^sub>E"
    moreover then obtain u v where [simp]: "x = (u,v)"
      using old.prod.exhaust by blast
    ultimately show "x \<in> edges E.G\<^sub>E"
      using T.edges_equiv[of u v] \<open>T \<subseteq> E\<close> E.edges_equiv[of u v] by auto
  qed
next
  assume "edges T.G\<^sub>E \<subseteq> edges E.G\<^sub>E"
  show "T \<subseteq> E"
  proof
    fix x
    assume "x \<in> T"
    moreover then obtain u v where [simp]: "x = {u,v}"
      using T.graph by auto
    ultimately show "x \<in> E"
      using T.edges_equiv[of u v] \<open>edges T.G\<^sub>E \<subseteq> edges E.G\<^sub>E\<close> E.edges_equiv[of u v] by auto
  qed
qed

lemma st_equiv: "E.is_st T \<longleftrightarrow> is_spanning_tree E.G\<^sub>E T.G\<^sub>E"
  apply (rule iffI)
  using T.tree_equiv E.nodes_equiv T.nodes_equiv edges_subset_iff 
  by (auto intro: E.is_stI simp: E.is_stE is_spanning_tree_def)

lemma st_equiv2: "E.is_st (uedge ` edges T.G\<^sub>E) \<longleftrightarrow> is_spanning_tree E.G\<^sub>E T.G\<^sub>E"
  using st_equiv by (subst T.edges_equiv2[symmetric])

end

context graph_abs
begin

lemma st_equiv: 
  fixes T
  defines "G\<^sub>T \<equiv> graph (Vs T) {(u, v) |u v. {u, v} \<in> T}" 
  assumes "graph_invar T"
  shows "is_st T \<longleftrightarrow> is_spanning_tree G\<^sub>E G\<^sub>T"
  unfolding G\<^sub>T_def using assms by (intro st_graph_abs.st_equiv) unfold_locales

lemma st_equiv2: 
  fixes G\<^sub>T
  assumes "graph_invar (uedge ` edges G\<^sub>T)"
  shows "is_st (uedge ` edges G\<^sub>T) \<longleftrightarrow> is_spanning_tree G\<^sub>E G\<^sub>T"
  using st_graph_abs.st_equiv2
  apply (intro st_graph_abs.st_equiv2)
  sorry

end

locale nat_w_graph_abs = (* nat weights *)
  pos_w_graph_abs E c for E :: "'a set set" and c :: "'a set \<Rightarrow> nat"
begin

lemma cost_of_st_equiv: 
  fixes T
  defines "G\<^sub>T \<equiv> graph (Vs T) {(u, v) |u v. {u, v} \<in> T}"
  assumes "graph_invar T"
  shows "cost_of_st T = weight c G\<^sub>T"
proof -
  have "cost_of_st T = sum c (uedge ` edges G\<^sub>T)"
    using assms graph_abs.edges_equiv2[unfolded graph_abs_def, of T] by auto
  also have "... = Undirected_Graph.weight c G\<^sub>T"
    unfolding Undirected_Graph.weight_alt by auto
  finally show ?thesis .
qed

lemma mst_equiv: 
  fixes T
  defines "G\<^sub>T \<equiv> graph (Vs T) {(u, v) |u v. {u, v} \<in> T}"
  assumes "graph_invar T"
  shows "is_mst T \<longleftrightarrow> is_MST c G\<^sub>E G\<^sub>T"
proof 
  assume "is_mst T"
  hence "is_st T" and min_st: "\<And>T'. is_st T' \<Longrightarrow> cost_of_st T \<le> cost_of_st T'"
    by (auto elim: is_mstE)
  moreover hence "is_spanning_tree G\<^sub>E G\<^sub>T" 
    using assms st_equiv[OF st_graph_invar] by auto
  moreover have "\<And>T'. is_spanning_tree G\<^sub>E T' \<Longrightarrow> weight c G\<^sub>T \<le> weight c T'"
  proof -
    fix T'
    assume "is_spanning_tree G\<^sub>E T'"
    hence "is_st (uedge ` edges T')"
      apply (intro st_equiv2)
      sorry

    show "weight c G\<^sub>T \<le> weight c T'"

      using assms st_equiv cost_of_st_equiv[OF st_graph_invar]
      sorry
  qed
  ultimately show "is_MST c G\<^sub>E G\<^sub>T"
    unfolding is_MST_def by auto
next
  assume "is_MST c G\<^sub>E G\<^sub>T"
  hence "is_spanning_tree G\<^sub>E G\<^sub>T" 
    and min_st: "\<And>G\<^sub>T'. is_spanning_tree G\<^sub>E G\<^sub>T' \<Longrightarrow> weight c G\<^sub>T \<le> weight c G\<^sub>T'"
    unfolding is_MST_def by auto
  moreover hence st_T: "is_st T" 
    using assms st_equiv[OF st_graph_invar] sorry
  moreover have "\<And>T'. is_st T' \<Longrightarrow> cost_of_st T \<le> cost_of_st T'"
  proof -
    fix T'
    assume st_T': "is_st T'"
    hence st_G\<^sub>T: "is_spanning_tree G\<^sub>E (graph (Vs T') {(u, v) |u v. {u, v} \<in> T'})" 
      (is "is_spanning_tree G\<^sub>E ?G\<^sub>T'")
      using assms st_equiv[OF st_graph_invar] by auto
    have "cost_of_st T = weight c G\<^sub>T"
      unfolding G\<^sub>T_def using st_T by (intro cost_of_st_equiv[OF st_graph_invar])
    also have "... \<le> weight c ?G\<^sub>T'"
      using min_st st_G\<^sub>T by auto
    also have "... = cost_of_st T'"
      using st_T' by (intro cost_of_st_equiv[OF st_graph_invar, symmetric])
    finally show "cost_of_st T \<le> cost_of_st T'" .
  qed
  ultimately show "is_mst T" 
    by (intro is_mstI)
qed (* TODO: fix locale stuff *)

end

(* TODO: use Prim_Dijkstra_Simple implementation *)

fun prim_impl' where
  "prim_impl' c E = undefined" (* translate params to prim_impl, or prim_list_impl_int *)

(* interpretation mst E c prim_impl'
  sorry *)

end