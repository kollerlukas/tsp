(* Author: Lukas Koller *)
theory MSTPrimAdaptor
  imports Main Misc "Prim_Dijkstra_Simple.Undirected_Graph" MST
    (* "Prim_Dijkstra_Simple.Prim_Impl" *)
begin

context graph_abs
begin

text \<open>Convert to graph from \<open>Prim_Dijkstra_Simple\<close>.\<close>
abbreviation "G\<^sub>E \<equiv> Undirected_Graph.graph (Vs E) {(u,v)| u v. {u,v} \<in> E}"

lemma G\<^sub>E_finite: "finite (Vs E)" "finite {(u,v)| u v. {u,v} \<in> E}"
  using graph finite_subset[of "{(u,v)| u v. {u,v} \<in> E}" "Vs E \<times> Vs E"] 
  by (auto intro: vs_member_intro)

lemma nodes_equiv1: "v \<in> Vs E \<Longrightarrow> v \<in> nodes G\<^sub>E"
  using graph_accs[OF G\<^sub>E_finite] by auto

lemma nodes_equiv2: "v \<in> nodes G\<^sub>E \<Longrightarrow> v \<in> Vs E "
proof -
  let ?E'="{(u,v) |u v. {u,v} \<in> E}"
  assume "v \<in> nodes G\<^sub>E"
  then consider "v \<in> Vs E" | "v \<in> fst ` ?E'" | "v \<in> snd ` ?E'"
    using graph_accs[OF G\<^sub>E_finite] by auto
  thus "v \<in> Vs E"
  proof cases
    assume "v \<in> fst ` ?E'"
    then obtain u' v' where "v = fst (u',v')" "{u',v'} \<in> E"
      by auto
    thus "v \<in> Vs E"
      by (intro vs_member_intro[of v _ E]) auto
  next
    assume "v \<in> snd ` ?E'"
    then obtain u' v' where "v = snd (u',v')" "{u',v'} \<in> E"
      by auto
    thus "v \<in> Vs E"
      by (intro vs_member_intro[of v _ E]) auto
  qed auto
qed

lemma edges_equiv1: "{u,v} \<in> E \<longleftrightarrow> (u,v) \<in> edges G\<^sub>E"
  using graph graph_accs[OF G\<^sub>E_finite] by (auto simp: insert_commute)

lemma edges_equiv2: "(u,v) \<in> edges G \<longleftrightarrow> {u,v} \<in> uedge ` edges G"
  using edges_sym' by (fastforce simp: uedge_def doubleton_eq_iff)+

lemma edges_eq: "E = uedge ` edges G\<^sub>E"
proof
  show "E \<subseteq> uedge ` edges G\<^sub>E"
  proof
    fix e
    assume "e \<in> E"
    moreover then obtain u v where [simp]: "e = {u,v}"
      using graph by auto
    ultimately have "(u,v) \<in> edges G\<^sub>E"
      by (intro iffD1[OF edges_equiv1]) auto
    thus "e \<in> uedge ` edges G\<^sub>E"   
      by (auto intro: iffD1[OF edges_equiv2])
  qed
next
  show "uedge ` edges G\<^sub>E \<subseteq> E"
  proof
    fix e
    assume "e \<in> uedge ` edges G\<^sub>E"
    moreover then obtain u v where "e = {u,v}" "(u,v) \<in> edges G\<^sub>E"
      by (auto simp: uedge_def)   
    ultimately show "e \<in> E"
      by (subst \<open>e = {u,v}\<close>) (intro iffD2[OF edges_equiv1])
  qed
qed

end

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

lemma map_dedges_of_path: "map Undirected_Graph.uedge (dedges_of_path P) = edges_of_path P"
  by (induction P rule: dedges_of_path.induct) auto 

lemma tl_dedges_of_path:
  assumes "P = dedges_of_path P'"
  shows "tl P = dedges_of_path (tl P')"
  using assms by (induction P' rule: dedges_of_path.induct) auto

context graph_abs
begin

lemma edges_subset_iff: "set (dedges_of_path P) \<subseteq> edges G\<^sub>E \<longleftrightarrow> set (edges_of_path P) \<subseteq> E"
proof
  show "set (dedges_of_path P) \<subseteq> edges G\<^sub>E \<Longrightarrow> set (edges_of_path P) \<subseteq> E"
    by (induction P rule: dedges_of_path.induct) (auto intro: iffD2[OF edges_equiv1])
next
  show "set (edges_of_path P) \<subseteq> E \<Longrightarrow> set (dedges_of_path P) \<subseteq> edges G\<^sub>E"
  proof (induction P rule: dedges_of_path.induct)
    case (3 u v P)
    moreover hence "(u,v) \<in> edges G\<^sub>E"
      by (intro iffD1[OF edges_equiv1]) auto
    ultimately show ?case 
      by auto
  qed auto
qed

lemma vpath_of_epath:
  assumes "Undirected_Graph.path G u P v"
  shows "P = dedges_of_path (map fst P @ [snd (last P)])"
  using assms
proof (induction P arbitrary: u rule: dedges_of_path.induct)
  case (3 e\<^sub>1 e\<^sub>2 P)
  then obtain x\<^sub>1 x\<^sub>2 where 
    "e\<^sub>1 = (u,x\<^sub>1)" "e\<^sub>1 \<in> edges G" "Undirected_Graph.path G x\<^sub>1 (e\<^sub>2#P) v" 
    "e\<^sub>2 = (x\<^sub>1,x\<^sub>2)" "e\<^sub>2 \<in> edges G" "Undirected_Graph.path G x\<^sub>2 P v"
    by auto
  hence "e\<^sub>1#e\<^sub>2#P = (u,x\<^sub>1)#dedges_of_path (map fst (e\<^sub>2#P) @ [snd (last (e\<^sub>2#P))])"
    using \<open>Undirected_Graph.path G x\<^sub>1 (e\<^sub>2#P) v\<close> "3.IH" by blast
  also have "... = dedges_of_path (map fst (e\<^sub>1#e\<^sub>2#P) @ [snd (last (e\<^sub>1#e\<^sub>2#P))])"
    using \<open>e\<^sub>1 = (u,x\<^sub>1)\<close> \<open>e\<^sub>2 = (x\<^sub>1,x\<^sub>2)\<close> by auto
  finally show ?case by blast
qed auto

lemma vpath_of_epathE:
  assumes "Undirected_Graph.path G\<^sub>E u P v"
  obtains P' where "P = dedges_of_path P'"
  using assms vpath_of_epath[of G\<^sub>E] by auto

lemma simple_path_equiv: "is_simple P \<longleftrightarrow> Undirected_Graph.simple (dedges_of_path P)"
  unfolding Undirected_Graph.simple_def
  by (auto intro: is_simpleI elim: is_simpleE simp: map_dedges_of_path) 

lemma walk_is_path:
  assumes "walk_betw E u P v"
  shows "Undirected_Graph.path G\<^sub>E u (dedges_of_path P) v"
proof -
  have "path E P" "P \<noteq> []" "hd P = u" "last P = v" "u \<in> Vs E"
    using assms by (auto simp: mem_path_Vs elim: walk_between_nonempty_path)
  thus "Undirected_Graph.path G\<^sub>E u (dedges_of_path P) v"
  proof (induction P arbitrary: u rule: path.induct)
    case (path2 u' x P)
    hence [simp]: "u = u'" and "(u,x) \<in> edges G\<^sub>E" 
      "Undirected_Graph.path G\<^sub>E x (dedges_of_path (x#P)) v"
      using iffD1[OF edges_equiv1] by auto
    moreover hence "Undirected_Graph.path G\<^sub>E u [(u,x)] x"
      by (auto intro: path_emptyI)
    ultimately show ?case 
      using \<open>u \<in> Vs E\<close> path_transs1 by auto
  qed (auto intro: path_emptyI)
qed

lemma path_equiv2:
  assumes "set P \<subseteq> Vs E" "Undirected_Graph.path G\<^sub>E u (dedges_of_path P) v"
  shows "path E P"
  using assms
proof (induction P arbitrary: u rule: dedges_of_path.induct)
  case (3 u' x P)
  hence "{u',x} \<in> E" "path E (x#P)"
    using 3 by (auto intro: iffD2[OF edges_equiv1])  
  thus ?case 
    by (auto intro: path.intros)
qed auto

lemma epath_last_node:
  assumes "P \<noteq> []" "hd P = u" "Undirected_Graph.path G u (dedges_of_path P) v"
  shows "last P = v"
  using assms by (induction P arbitrary: u rule: dedges_of_path.induct) auto

lemma path_is_walk:
  assumes "P \<noteq> []" "hd P = u" "u \<in> Vs E" "Undirected_Graph.path G\<^sub>E u (dedges_of_path P) v"
  shows "walk_betw E u P v"
proof (rule nonempty_path_walk_between)
  have "set (edges_of_path P) \<subseteq> E"
    using assms path_edges[of G\<^sub>E u "dedges_of_path P" v] edges_subset_iff by auto
  hence "set P \<subseteq> Vs E"
    using assms edges_of_vpath_are_vs list.sel(1) by metis
  thus "path E P" "P \<noteq> []" "hd P = u" "last P = v"
    using assms path_equiv2 by (auto simp: epath_last_node)
qed

lemma walk_equiv_path: "walk_betw E u P v 
  \<longleftrightarrow> P \<noteq> [] \<and> hd P = u \<and> u \<in> Vs E \<and> Undirected_Graph.path G\<^sub>E u (dedges_of_path P) v"
proof
  assume "walk_betw E u P v"
  moreover hence "path E P" "P \<noteq> []" "hd P = u" "last P = v" "u \<in> Vs E"
    by (auto simp: mem_path_Vs elim: walk_between_nonempty_path)
  ultimately show "P \<noteq> [] \<and> hd P = u \<and> u \<in> Vs E \<and> Undirected_Graph.path G\<^sub>E u (dedges_of_path P) v"
    using walk_is_path by auto
next
  assume assms: "P \<noteq> [] \<and> hd P = u \<and> u \<in> Vs E \<and> Undirected_Graph.path G\<^sub>E u (dedges_of_path P) v"
  show "walk_betw E u P v"
  proof (rule nonempty_path_walk_between)
    have "set (edges_of_path P) \<subseteq> E"
      using assms path_edges[of G\<^sub>E u "dedges_of_path P" v] edges_subset_iff by auto
    hence "set P \<subseteq> Vs E"
      using assms edges_of_vpath_are_vs list.sel(1) by metis
    thus "path E P" "P \<noteq> []" "hd P = u" "last P = v"
      using assms path_equiv2 by (auto simp: epath_last_node)
  qed
qed

lemma walk_iff_rtrancl_edges: 
  assumes "u \<in> Vs E" "v \<in> Vs E"
  shows "(\<exists>P. walk_betw E u P v) \<longleftrightarrow> (u,v) \<in> (edges G\<^sub>E)\<^sup>*"
proof
  assume "\<exists>P. walk_betw E u P v"
  thus "(u,v) \<in> (edges G\<^sub>E)\<^sup>*"
    using walk_is_path[of u _ v] rtrancl_edges_iff_path[of u v G\<^sub>E] by auto
next
  assume "(u,v) \<in> (edges G\<^sub>E)\<^sup>*"
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
      by (intro iffD2[OF edges_equiv1])
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
  shows "v \<in> connected_component E u \<longleftrightarrow> (u,v) \<in> (edges G\<^sub>E)\<^sup>*"
proof
  assume "v \<in> connected_component E u"
  hence "(\<exists>p. walk_betw E u p v)"
    using assms by (auto elim: in_connected_component_has_path)
  thus "(u,v) \<in> (edges G\<^sub>E)\<^sup>*"
    using assms walk_iff_rtrancl_edges by auto
next
  assume "(u,v) \<in> (edges G\<^sub>E)\<^sup>*"
  hence "(\<exists>p. walk_betw E u p v)"
    using assms walk_iff_rtrancl_edges by auto
  thus "v \<in> connected_component E u"
    by (auto intro: has_path_in_connected_component)
qed

lemma connected_equiv: "is_connected E \<longleftrightarrow> connected G\<^sub>E"
proof 
  assume "is_connected E"
  show "connected G\<^sub>E"
  proof (rule connectedI)
    fix u v
    assume "u \<in> nodes G\<^sub>E" "v \<in> nodes G\<^sub>E"
    hence "u \<in> Vs E" "v \<in> Vs E"
      using nodes_equiv2 by auto
    hence "v \<in> connected_component E u"
      using \<open>is_connected E\<close> by (auto elim: is_connectedE)
    thus "(u,v) \<in> (edges G\<^sub>E)\<^sup>*"
      using \<open>u \<in> Vs E\<close> \<open>v \<in> Vs E\<close> conn_comp_equiv by auto
  qed
next
  assume "connected G\<^sub>E"
  show "is_connected E"
  proof (rule is_connectedI)
    fix u v
    assume "u \<in> Vs E" "v \<in> Vs E"
    hence "u \<in> nodes G\<^sub>E" "v \<in> nodes G\<^sub>E"
      using nodes_equiv1 by auto
    hence "(u,v) \<in> (edges G\<^sub>E)\<^sup>*"
      using \<open>Undirected_Graph.connected G\<^sub>E\<close> by (auto elim: connectedD)
    thus "v \<in> connected_component E u"
      using \<open>u \<in> Vs E\<close> \<open>v \<in> Vs E\<close> conn_comp_equiv by auto
  qed
qed

lemma dedges_path_hd_Vs_mem:
  assumes "Undirected_Graph.path G\<^sub>E u (dedges_of_path P) v" "dedges_of_path P \<noteq> []"
  shows "hd P = u" "u \<in> Vs E"
  using assms 
proof (induction P rule: dedges_of_path.induct)
  case (3 u' v P)
  {
    case 1
    thus ?case by auto
  next
    case 2
    hence "{u,v} \<in> E"
      by (auto intro: iffD2[OF edges_equiv1])
    thus ?case 
      by (auto simp: edges_are_Vs)
  }
qed auto

lemma acyclic_equiv: "is_acyclic E \<longleftrightarrow> cycle_free G\<^sub>E"
proof
  assume "is_acyclic E"
  show "cycle_free G\<^sub>E"
  proof (rule cycle_freeI)
    fix P u
    assume "Undirected_Graph.path G\<^sub>E u P u" "P \<noteq> []" "simple P"
    moreover then obtain P' where "P = dedges_of_path P'"
      using vpath_of_epathE[of u P u] by auto
    ultimately have "is_simple P'" "0 < length (edges_of_path P')" "walk_betw E u P' u"
      using simple_path_equiv dedges_of_path_nonnilE dedges_path_hd_Vs_mem 
        walk_equiv_path[of u P' u] by (auto simp: dedges_length[symmetric, of P'])
    hence "is_cycle E P'"
      by (auto intro: is_cycleI)
    thus "False"
      using \<open>is_acyclic E\<close> is_acyclicE by auto
  qed
next
  assume "cycle_free G\<^sub>E"
  show "is_acyclic E"
  proof (rule ccontr)
    assume "\<not> is_acyclic E"
    then obtain C where "is_cycle E C"
      by (auto elim: not_acyclicE)
    then obtain u where "is_simple C" "0 < length (edges_of_path C)" "walk_betw E u C u"
      by (auto elim: is_cycleE)
    hence "Undirected_Graph.path G\<^sub>E u (dedges_of_path C) u" "dedges_of_path C \<noteq> []" 
      "simple (dedges_of_path C)"
      using walk_equiv_path[of u C u] simple_path_equiv 
      by (auto simp: dedges_length[symmetric, of C])
    thus "False"
      using \<open>cycle_free G\<^sub>E\<close> cycle_freeD[of G\<^sub>E] by auto
  qed
qed

lemma tree_equiv: "is_tree E \<longleftrightarrow> tree G\<^sub>E"
  using connected_equiv acyclic_equiv by (auto intro: is_treeI simp: is_treeE tree_def)

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