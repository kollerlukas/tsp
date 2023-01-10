(* Author: Lukas Koller *)
theory BergePrimAdaptor
  imports Main tsp.Misc "Prim_Dijkstra_Simple.Undirected_Graph" tsp.MinSpanningTree 
    (* "Prim_Dijkstra_Simple.Prim_Impl" *)
begin

section \<open>From Berge to Prim\<close>

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

lemma vpath_of_epath_cancel:
  "dedges_of_path (vpath_of_epath (dedges_of_path P\<^sub>v)) = dedges_of_path P\<^sub>v"
  by (induction P\<^sub>v rule: list0123.induct) auto

lemma walk_vpath_elim_epath:
  assumes "walk_betw E u P\<^sub>v v"
  obtains "P\<^sub>v = [u]" "u = v" 
  | P where "P\<^sub>v = vpath_of_epath P" "dedges_of_path (vpath_of_epath P) = P"
  using assms walk_between_nonempty_path[OF assms(1)]
proof (induction P\<^sub>v rule: list012.induct)
  case (3 u v P\<^sub>v)
  hence "u#v#P\<^sub>v = vpath_of_epath (dedges_of_path (u#v#P\<^sub>v))"
    by (intro berge_vpath_of_epath) auto
  then show ?case 
    using 3 vpath_of_epath_cancel by metis
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

lemma epath_split_hd1:
  assumes "dedges_of_path (vpath_of_epath (e\<^sub>1#e\<^sub>2#P)) = e\<^sub>1#e\<^sub>2#P" "hd (vpath_of_epath (e\<^sub>1#e\<^sub>2#P)) = u"
  obtains x where "e\<^sub>1 = (u,x)" "fst e\<^sub>2 = x"
  using assms by (induction P) fastforce+

lemma epath_split_hd2:
  assumes "dedges_of_path (vpath_of_epath (e\<^sub>1#e\<^sub>2#P)) = e\<^sub>1#e\<^sub>2#P"
  obtains u x where "e\<^sub>1 = (u,x)" "fst e\<^sub>2 = x"
  using assms by (induction P) (meson epath_split_hd1)+


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

context graph_abs2
begin

lemma st_equiv1: 
  assumes "is_st E\<^sub>1 E\<^sub>2"
  shows "is_spanning_tree (prim_of_berge E\<^sub>1) (prim_of_berge E\<^sub>2)"
  unfolding is_spanning_tree_def
proof (intro conjI)
  have "is_tree E\<^sub>2"
    using assms by (elim is_stE)
  thus "tree (prim_of_berge E\<^sub>2)"
    by (intro E\<^sub>2.tree_equiv1)

  have "Vs E\<^sub>1 = Vs E\<^sub>2"
    using assms by (elim is_stE)
  thus "nodes (prim_of_berge E\<^sub>2) = nodes (prim_of_berge E\<^sub>1)"
    by auto

  have "E\<^sub>2 \<subseteq> E\<^sub>1"
    using assms by (elim is_stE)
  thus "edges (prim_of_berge E\<^sub>2) \<subseteq> edges (prim_of_berge E\<^sub>1)"
    by auto
qed

lemma st_equiv2: 
  assumes "is_spanning_tree (prim_of_berge E\<^sub>1) (prim_of_berge E\<^sub>2)"
  shows "is_st E\<^sub>1 E\<^sub>2" 
proof (intro is_stI)
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

lemma st_equiv1: "is_st E T \<Longrightarrow> is_spanning_tree (prim_of_berge E) (prim_of_berge T)"
  using st_is_graph by (intro graph_abs2.st_equiv1) unfold_locales

lemma st_equiv2: 
  "graph_invar T \<Longrightarrow> is_spanning_tree (prim_of_berge E) (prim_of_berge T) \<Longrightarrow> is_st E T"
  by (intro graph_abs2.st_equiv2) unfold_locales

end

section \<open>From Prim to Berge\<close>

text \<open>Translate graph from \<open>Prim_Dijkstra_Simple.Undirected_Graph\<close> to graph from \<open>Berge\<close>.\<close>
definition "berge_of_prim G \<equiv> uedge ` edges G"

lemma berge_of_prim_def2: "berge_of_prim G = {{u,v} | u v. (u,v) \<in> edges G}"
  unfolding berge_of_prim_def by (auto simp add: uedge_def)

locale prim_graph_abs =
  fixes V E G
  defines "G \<equiv> graph V E"
  assumes finite_V: "finite V" and finite_E: "finite E"
      and irrefl_E: "irrefl E" and V_subset: "V \<subseteq> fst ` E \<union> snd ` E"
begin

lemma edges_G[simp]: "edges G = E \<union> E\<inverse>" 
  and nodes_G[simp]: "nodes G = fst ` E \<union> snd ` E"
  unfolding G_def using graph_accs[OF finite_V finite_E] irrefl_E V_subset 
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

sublocale graph_abs "berge_of_prim G"
  using berge_graph by unfold_locales

lemma edges_equiv1: "(u,v) \<in> edges G \<Longrightarrow> {u,v} \<in> berge_of_prim G"
  unfolding berge_of_prim_def uedge_def by auto

lemma edges_equiv1_uedge: "e \<in> edges G \<Longrightarrow> uedge e \<in> berge_of_prim G"
  unfolding berge_of_prim_def uedge_def by auto

lemma edges_equiv2: "{u,v} \<in> berge_of_prim G \<Longrightarrow> (u,v) \<in> edges G"
  using berge_edges_invar by (metis doubleton_eq_iff edges_sym')+

lemma edges_equiv2_uedge: "uedge e \<in> berge_of_prim G \<Longrightarrow> e \<in> edges G"
  unfolding uedge_def using edges_equiv2 by (auto split: prod.splits)
  
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

lemma edges_eq: "edges G = {(u,v) | u v. {u,v} \<in> berge_of_prim G}"
  using edges_equiv1 edges_equiv2 by auto



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

lemma berge_vpath_hd_of_epath_is_prim_edge:
  assumes "path (berge_of_prim G) (vpath_of_epath (e#P))" (is "path ?E _")
      and "dedges_of_path (vpath_of_epath (e#P)) = (e#P)"
  shows "e \<in> edges G"
  using assms
proof (induction P)
  case Nil
  then obtain u v where [simp]: "e = (u,v)" and "path ?E [u,v]"
    by (cases e) auto
  thus ?case 
    by (intro edges_equiv2_uedge) (auto simp: uedge_def)
next
  case (Cons e\<^sub>1 P)
  then obtain u x where [simp]: "e = (u,x)" and [simp]: "fst e\<^sub>1 = x"
    by (elim epath_split_hd2)
  hence "uedge e \<in> ?E"
    using Cons path_edges_subset by (auto simp: uedge_def)
  thus ?case 
    by (intro edges_equiv2_uedge)
qed

lemma berge_walk_is_prim_path:
  assumes "walk_betw (berge_of_prim G) u (vpath_of_epath P) v" (is "walk_betw ?E u _ v")
      and "dedges_of_path (vpath_of_epath P) = P"
  shows "Undirected_Graph.path G u P v"
  using walk_between_nonempty_path[OF assms(1)] assms(2)
proof (induction P arbitrary: u rule: list012.induct)
  case 1
  thus ?case using walk_nonempty by fastforce
next
  case (2 e)
  moreover hence "e \<in> edges G"
    by (intro berge_vpath_hd_of_epath_is_prim_edge)
  ultimately show ?case 
    by auto
next
  case (3 e\<^sub>1 e\<^sub>2 P)
  then obtain x where [simp]: "e\<^sub>1 = (u,x)" and [simp]: "fst e\<^sub>2 = x"
    by (elim epath_split_hd1)
  moreover have "e\<^sub>1 \<in> edges G"
    using 3 by (intro berge_vpath_hd_of_epath_is_prim_edge[of e\<^sub>1 "e\<^sub>2#P"])
  ultimately show ?case 
    using 3 by auto
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
  then consider "P\<^sub>v = [u]" "u = v" 
    | P where "walk_betw (berge_of_prim G) u (vpath_of_epath P) v" 
      "dedges_of_path (vpath_of_epath P) = P"
    by (auto elim: walk_vpath_elim_epath)
  thus "(u,v) \<in> (edges G)\<^sup>*"
  proof cases
    fix P
    assume "walk_betw (berge_of_prim G) u (vpath_of_epath P) v" 
      "dedges_of_path (vpath_of_epath P) = P"
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
    using vpath_of_epath_cancel by (intro berge_walk_is_prim_path)
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

locale prim_graph_abs2 =
  G: prim_graph_abs V E G + 
  T: prim_graph_abs V E' T for V E E' G T
begin

lemma st_equiv1: 
  assumes "is_st (berge_of_prim G) (berge_of_prim T)" 
  shows "is_spanning_tree G T"
  unfolding is_spanning_tree_def
proof (intro conjI)
  have "is_tree (berge_of_prim T)"
    using assms by (elim is_stE)
  thus "tree T"
    by (intro T.tree_equiv1)

  have "Vs (berge_of_prim G) = Vs (berge_of_prim T)"
    using assms by (elim is_stE)
  thus "nodes T = nodes G"
    by auto

  have "berge_of_prim T \<subseteq> berge_of_prim G"
    using assms by (elim is_stE)
  thus "edges T \<subseteq> edges G"
    by (subst T.edges_eq; subst G.edges_eq) auto
qed

lemma st_equiv2: 
  assumes "is_spanning_tree G T" 
  shows "is_st (berge_of_prim G) (berge_of_prim T)"
proof (intro is_stI)
  have "tree T"
    using assms[unfolded is_spanning_tree_def] by auto
  thus "is_tree (berge_of_prim T)"
    by (intro T.tree_equiv2)

  have "nodes G = nodes T" 
    using assms[unfolded is_spanning_tree_def] by auto
  thus "Vs (berge_of_prim G) = Vs (berge_of_prim T)"
    by auto

  have "edges T \<subseteq> edges G"
    using assms[unfolded is_spanning_tree_def] by auto
  thus "berge_of_prim T \<subseteq> berge_of_prim G"
    unfolding berge_of_prim_def2 by auto
qed

end

lemma uedge_union_converse: "uedge ` (A \<union> A\<inverse>) = uedge ` A"
  unfolding uedge_def by auto

lemma uedge_set: "uedge ` A = {{u,v} |u v. (u,v) \<in> A}"
  unfolding uedge_def by auto

lemma Vs_uedge: "Vs (uedge ` A) = fst ` A \<union> snd ` A"
  unfolding Vs_def uedge_def by force

lemma vertex_in_uedge:
  assumes "e \<in> A" "v \<in> uedge e"
  shows "v \<in> fst ` A \<union> snd ` A"
proof -
  have "v \<in> Vs (uedge ` A)"
    using assms by (intro vs_member_intro) auto
  thus ?thesis
    by (auto simp: Vs_uedge) 
qed

locale prim_subgraph_abs =
  prim_graph_abs V E G for V E G +
  fixes E\<^sub>T
  assumes E\<^sub>T_subset: "E\<^sub>T \<subseteq> E" 
      (* Berge cannot represent a graph with a single node! *)
      and card_nodes_G: "card (nodes G) \<ge> 2"
begin

lemma finite_E\<^sub>T: "finite E\<^sub>T"
  by (intro finite_subset[OF E\<^sub>T_subset finite_E])

lemma irrefl_E\<^sub>T: "irrefl E\<^sub>T"
  by (intro irrefl_subset[OF irrefl_E E\<^sub>T_subset])

lemma prim_subgraph_nodes: "nodes (graph V E\<^sub>T) = V \<union> fst ` E\<^sub>T \<union> snd ` E\<^sub>T"
  using finite_V finite_E\<^sub>T by (auto simp: graph_accs(1))

lemma prim_subgraph_edges: "edges (graph V E\<^sub>T) = E\<^sub>T \<union> E\<^sub>T\<inverse>"
  using finite_V finite_E\<^sub>T irrefl_E\<^sub>T by (auto simp: graph_accs(2) irrefl_def)

lemma st_V_subset:
  assumes "is_st (berge_of_prim G) (berge_of_prim (graph V E\<^sub>T))"
      (is "is_st (berge_of_prim G) (berge_of_prim ?T)")
  shows "V \<subseteq> fst ` E\<^sub>T \<union> snd ` E\<^sub>T"
proof -
  have "V \<subseteq> Vs (berge_of_prim G)"
    using V_subset by auto
  also have "... = Vs (berge_of_prim ?T)"
    using assms by (elim is_stE)
  also have "... = Vs (uedge ` (E\<^sub>T \<union> E\<^sub>T\<inverse>))"
    unfolding berge_of_prim_def2 using assms by (auto simp: prim_subgraph_edges uedge_set)
  also have "... = fst ` E\<^sub>T \<union> snd ` E\<^sub>T"
    by (auto simp: uedge_union_converse Vs_uedge)
  finally show ?thesis .
qed

lemma connected_graph_get_edge_for_node:
  assumes "connected (graph V E\<^sub>T)" 
      and "u \<in> nodes (graph V E\<^sub>T)" "v \<in> nodes (graph V E\<^sub>T)" "u \<noteq> v"
  obtains e where "e \<in> E\<^sub>T" "u \<in> uedge e"
proof -
  have "(u,v) \<in> (edges (graph V E\<^sub>T))\<^sup>*"
    using assms[unfolded connected_def] by auto
  then obtain P where "Undirected_Graph.path (graph V E\<^sub>T) u P v"
    using rtrancl_edges_iff_path by fastforce
  then obtain e P' where "Undirected_Graph.path (graph V E\<^sub>T) u (e#P') v"
    using assms by (cases P) auto
  hence "e \<in> E\<^sub>T \<union> E\<^sub>T\<inverse>" and "u \<in> uedge e"
    by (auto simp: prim_subgraph_edges)
  then obtain e' where "e' \<in> E\<^sub>T" "u \<in> uedge e'"
    by fastforce
  thus ?thesis
    using that by auto
qed

lemma connected_graph_nodes_subset:
  assumes "connected (graph V E\<^sub>T)" "u \<in> nodes (graph V E\<^sub>T)" "v \<in> nodes (graph V E\<^sub>T)" "u \<noteq> v"
  shows "nodes (graph V E\<^sub>T) \<subseteq> fst ` E\<^sub>T \<union> snd ` E\<^sub>T"
proof
  fix x
  assume vertex_x: "x \<in> nodes (graph V E\<^sub>T)"
  consider "x \<noteq> u" | "x \<noteq> v"
    using assms by auto
  thus "x \<in> fst ` E\<^sub>T \<union> snd ` E\<^sub>T"
  proof cases
    assume "x \<noteq> u"
    then obtain e where "e \<in> E\<^sub>T" "x \<in> uedge e"
      using assms vertex_x by (elim connected_graph_get_edge_for_node)
    hence "x \<in> fst ` E\<^sub>T \<union> snd ` E\<^sub>T"
      by (intro vertex_in_uedge)
    thus ?thesis
      by auto
  next
    assume "x \<noteq> v"
    then obtain e where "e \<in> E\<^sub>T" "x \<in> uedge e"
      using assms vertex_x by (elim connected_graph_get_edge_for_node)
    hence "x \<in> fst ` E\<^sub>T \<union> snd ` E\<^sub>T"
      by (intro vertex_in_uedge)
    thus ?thesis
      by auto
  qed
qed

lemma spanning_tree_V_subset:
  assumes "is_spanning_tree G (graph V E\<^sub>T)"
  obtains "V \<subseteq> fst ` E\<^sub>T \<union> snd ` E\<^sub>T"
  using nodes_finite assms[unfolded is_spanning_tree_def] card_nodes_G
proof (induction "nodes (graph V E\<^sub>T)" rule: finite2_induct)
  case (singleton x)
  hence "card {x} \<ge> 2"
    by auto
  thus ?case 
    by auto
next
  case (insert2 u v)
  moreover hence "connected (graph V E\<^sub>T)"
    unfolding tree_def by auto
  ultimately have "nodes (graph V E\<^sub>T) \<subseteq> fst ` E\<^sub>T \<union> snd ` E\<^sub>T"
    by (intro that connected_graph_nodes_subset) auto
  hence "V \<subseteq> fst ` E\<^sub>T \<union> snd ` E\<^sub>T"
     by (auto simp: prim_subgraph_nodes)
   thus ?case
    by (intro that connected_graph_nodes_subset) auto
qed auto (* induction just for case distinction *)

lemmas subgraph_props = finite_V st_V_subset finite_E\<^sub>T irrefl_E\<^sub>T spanning_tree_V_subset

lemma st_equiv1: 
  assumes "is_st (berge_of_prim G) (berge_of_prim (graph V E\<^sub>T))" 
  shows "is_spanning_tree G (graph V E\<^sub>T)"
  unfolding G_def
  using assms subgraph_props
  apply (intro prim_graph_abs2.st_equiv1)
  apply unfold_locales
  apply (auto simp: G_def)
  done

lemma st_equiv2: 
  assumes "is_spanning_tree G (graph V E\<^sub>T)" 
  shows "is_st (berge_of_prim G) (berge_of_prim (graph V E\<^sub>T))" 
  unfolding G_def
  using assms subgraph_props
  apply (intro prim_graph_abs2.st_equiv2)
  apply unfold_locales
  apply (auto simp: G_def)
  done

end

context prim_graph_abs
begin

lemma st_equiv1: 
  assumes "E\<^sub>T \<subseteq> E" "card (nodes G) \<ge> 2" and "is_st (berge_of_prim G) (berge_of_prim (graph V E\<^sub>T))" 
  shows "is_spanning_tree G (graph V E\<^sub>T)"
  using assms unfolding G_def by (intro prim_subgraph_abs.st_equiv1) unfold_locales

lemma st_equiv2: 
  assumes "E\<^sub>T \<subseteq> E" "card (nodes G) \<ge> 2" and "is_spanning_tree G (graph V E\<^sub>T)"
  shows "is_st (berge_of_prim G) (berge_of_prim (graph V E\<^sub>T))" 
  using assms unfolding G_def by (intro prim_subgraph_abs.st_equiv2) unfold_locales

lemma prim_of_berge_of_prim: "prim_of_berge (berge_of_prim G) = G"
  unfolding prim_of_berge_def by (metis berge_nodes edges_eq graph_eq)

end

section \<open>Minimum Spanning-Tree Equivalence\<close>

locale nat_w_graph_abs = (* nat weights *)
  pos_w_graph_abs E c for E :: "'a set set" and c :: "'a set \<Rightarrow> nat"
begin

lemma cost_of_st_eq1: "graph_invar T \<Longrightarrow> cost_of_st\<^sub>c T = weight c (prim_of_berge T)"
  by (subst graph_abs.edges_eq[of T]; unfold_locales) (auto simp: weight_alt)

lemma cost_of_st_eq2: "cost_of_st\<^sub>c (berge_of_prim T) = weight c T"
  unfolding weight_alt berge_of_prim_def by auto

lemma mst_equiv1:
  assumes "is_mst E c T"
  shows "is_MST c (prim_of_berge E) (prim_of_berge T)"
  unfolding is_MST_def
proof
  have "is_st E T"
    using assms by (elim is_mstE)
  thus "is_spanning_tree (prim_of_berge E) (prim_of_berge T)"
    by (intro st_equiv1)
  have "is_st E T"
    using assms by (elim is_mstE)
  then consider "graph_invar T" "T = {}" | "graph_invar T" "card (Vs T) \<ge> 2"
    using graph_subset[OF graph is_stE(1)] by (auto elim: st_card_Vs)
  thus "\<forall>T'. is_spanning_tree (prim_of_berge E) T' \<longrightarrow> weight c (prim_of_berge T) \<le> weight c T'"
  proof (intro allI impI; cases)
    fix T'
    assume "is_spanning_tree (prim_of_berge E) T'" and "T = {}" "graph_invar T"
    hence "weight c (prim_of_berge T) = 0"
      by (auto simp: cost_of_st_eq1[symmetric])
    thus "weight c (prim_of_berge T) \<le> weight c T'"
      by auto
  next
    fix T'
    assume "is_spanning_tree (prim_of_berge E) T'" and "card (Vs T) \<ge> 2" "graph_invar T"
    hence "is_st E (berge_of_prim T')"
      sorry (* TODO: need a lemma *)
    moreover have "\<And>T'. is_st E T' \<Longrightarrow> cost_of_st\<^sub>c T \<le> cost_of_st\<^sub>c T'"
      using assms by (elim is_mstE)
    ultimately have "cost_of_st\<^sub>c T \<le> cost_of_st\<^sub>c (berge_of_prim T')"
      by auto
    hence "weight c (prim_of_berge T) \<le> cost_of_st\<^sub>c (berge_of_prim T')"
      using \<open>card (Vs T) \<ge> 2\<close> \<open>graph_invar T\<close> by (auto simp: cost_of_st_eq1)
    also have "... \<le> weight c T'"
      by (auto simp: cost_of_st_eq2)
    finally show "weight c (prim_of_berge T) \<le> weight c T'"
      by auto
  qed
qed

lemma mst_equiv2:
  assumes "graph_invar T" "is_MST c (prim_of_berge E) (prim_of_berge T)"
  shows "is_mst E c T"
proof (intro is_mstI)
  show "is_st E T"
    using assms[unfolded is_MST_def] by (auto intro: st_equiv2)
  show "\<And>T'. is_st E T' \<Longrightarrow> cost_of_st\<^sub>c T \<le> cost_of_st\<^sub>c T'"
  proof -
    fix T'
    assume "is_st E T'"
    moreover hence "graph_invar T'"
      by (intro st_is_graph)
    moreover hence "is_spanning_tree (prim_of_berge E) (prim_of_berge T')"
      using calculation by (intro st_equiv1)
    moreover hence "weight c (prim_of_berge T) \<le> weight c (prim_of_berge T')"
      using assms[unfolded is_MST_def] by auto
    moreover have "graph_invar T"
      using \<open>is_st E T\<close> by (intro st_is_graph)
    ultimately show "cost_of_st\<^sub>c T \<le> cost_of_st\<^sub>c T'"
      by (auto simp: cost_of_st_eq1)
  qed
qed

end

(* TODO: use Prim_Dijkstra_Simple implementation *)

fun prim_impl where
  "prim_impl c E = undefined" (* translate params to prim_impl, or prim_list_impl_int *)

(* interpretation mst E c prim_impl'
  sorry *)

end