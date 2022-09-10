(* Author: Lukas Koller *)
theory MST                                           
  imports Main "Prim_Dijkstra_Simple.Prim_Impl" CompleteGraph WeightedGraph 
    (* default graph defintions from Berge? *)
begin

text \<open>Connected Graph\<close>
definition "is_connected E \<equiv> \<forall>u\<in>Vs E.\<forall>v\<in>Vs E. u \<in> connected_component E v"

lemma is_connectedI: 
  "(\<And>u v. u\<in>Vs E \<Longrightarrow> v\<in>Vs E \<Longrightarrow> u \<in> connected_component E v) \<Longrightarrow> is_connected E"
  unfolding is_connected_def by auto

lemma is_connectedE: "is_connected E \<Longrightarrow> u\<in>Vs E \<Longrightarrow> v\<in>Vs E \<Longrightarrow> u \<in> connected_component E v"
  unfolding is_connected_def by auto

lemma is_connectedE2: 
  assumes "is_connected E" "u\<in>Vs E" "v\<in>Vs E" "u \<noteq> v"
  obtains P where "walk_betw E u P v"
  using assms[unfolded is_connected_def connected_component_def] by fastforce

text \<open>Acyclic Graph\<close>
definition "simple_path P \<equiv> distinct (edges_of_path P)"

lemma simple_pathI: "distinct (edges_of_path P) \<Longrightarrow> simple_path P"
  unfolding simple_path_def by auto

lemma simple_pathE: "simple_path P \<Longrightarrow> distinct (edges_of_path P)"
  unfolding simple_path_def by auto

lemma simple_pathI2: "distinct P \<Longrightarrow> simple_path P"
  using distinct_edges_of_vpath by (auto intro: simple_pathI) 

lemma simple_path_rev: "simple_path P \<Longrightarrow> simple_path (rev P)"
  using edges_of_path_rev[of P] distinct_rev[of "edges_of_path P"] by (auto simp: simple_path_def)

lemma simple_path_cons: "simple_path (v#P) \<Longrightarrow> simple_path P"
  unfolding simple_path_def using distinct_edges_of_paths_cons[of v P] by auto

lemma distinct_hd_last_neq: "distinct xs \<Longrightarrow> length xs > 1 \<Longrightarrow> hd xs \<noteq> last xs"
  by (induction xs) auto

lemma rev_hd_last_eq: "xs \<noteq> [] \<Longrightarrow> xs = rev xs \<Longrightarrow> hd xs = last xs"
proof (induction xs rule: list012.induct)
  case (3 x x' xs)
  thus ?case 
    by (metis last_rev)
qed auto

lemma simple_path_rev_neq:
  assumes "simple_path P" "length P > 2"
  shows "P \<noteq> rev P"
  using assms
proof (induction P rule: list0123.induct)
  case (4 u v w P)
  show ?case 
  proof (rule ccontr)
    assume "\<not> u#v#w#P \<noteq> rev (u#v#w#P)"
    hence "edges_of_path (u#v#w#P) = rev (edges_of_path (u#v#w#P))"
      by (auto simp: edges_of_path_rev)
    thus "False"
      using 4 rev_hd_last_eq[of "edges_of_path (u#v#w#P)"] 
        distinct_hd_last_neq[OF simple_pathE[of "u#v#w#P"]] by auto
  qed
qed auto

text \<open>Definition for a cycle in a graph. A cycle is a vertex-path, thus a cycle needs to contain 
at least one edge, otherwise the singleton path \<open>[v]\<close> is a cycle. Therefore, no graph would be 
acyclic.\<close>
definition "is_cycle E C \<equiv> simple_path C \<and> length (edges_of_path C) > 0 \<and> (\<exists>v. walk_betw E v C v)"

lemma is_cycleI:
  "simple_path C \<Longrightarrow> length (edges_of_path C) > 0 \<Longrightarrow> walk_betw E v C v \<Longrightarrow> is_cycle E C"
  unfolding is_cycle_def by auto

lemma is_cycleE:
  assumes "is_cycle E C"
  obtains v where "simple_path C" "length (edges_of_path C) > 0" "walk_betw E v C v"
  using assms[unfolded is_cycle_def] by auto

lemma is_cycleE_hd:
  assumes "is_cycle E C"
  shows "simple_path C" "length (edges_of_path C) > 0" "walk_betw E (hd C) C (hd C)"
proof -
  show "simple_path C" "0 < length (edges_of_path C)"
    using assms by (auto elim: is_cycleE)
  obtain v where "walk_betw E v C v"
    using assms by (auto elim: is_cycleE)
  moreover hence "v = hd C"
    by (auto simp: walk_between_nonempty_path)
  ultimately show "walk_betw E (hd C) C (hd C)"
    by auto
qed

lemma cycle_non_nil: "is_cycle E C \<Longrightarrow> C \<noteq> []"
  by (auto elim: is_cycleE walk_nonempty)

text \<open>Not using \<open>graph_abs\<close> because for the Double-Tree algorithm we need to talk about cycles 
in subgraphs.\<close>
lemma cycle_length:
  assumes "graph_invar E" "is_cycle E C"
  shows "length C > 2"
  using assms
proof (induction C rule: list0123.induct)
  case (3 u v)
  then obtain v' where "simple_path [u,v]" "length (edges_of_path [u,v]) > 0" 
    "walk_betw E v' [u,v] v'"
    by (auto elim: is_cycleE)
  hence "u = v'" "v = v'" "path E [u,v]"
    using walk_between_nonempty_path[of _ _ "[u,v]"] by auto
  hence "u = v" "{u,v} \<in> E"
    by (auto elim: path.cases)
  thus ?case 
    using assms by auto
qed (auto elim: is_cycleE)

lemma cycle_edge_length:
  assumes "graph_invar E" "is_cycle E C"
  shows "length (edges_of_path C) > 1"
  using assms edges_of_path_length[of C] cycle_length[of E C] by auto

lemma cycle_edges_hd_last_neq:
  assumes "graph_invar E" "is_cycle E C"
  shows "hd (edges_of_path C) \<noteq> last (edges_of_path C)" (is "?e\<^sub>1 \<noteq> ?e\<^sub>2")
  using assms cycle_edge_length distinct_hd_last_neq[OF simple_pathE] by (auto elim: is_cycleE)

lemma path_drop:
  assumes "path X P"
  shows "path X (drop i P)"
  using assms path_suff[of X "take i P" "drop i P"] append_take_drop_id[of i P] by auto

lemma path_take:
  assumes "path X P"
  shows "path X (take i P)"
  using assms path_pref[of X "take i P" "drop i P"] append_take_drop_id[of i P] by auto

lemma path_swap:
  assumes "P\<^sub>1 \<noteq> []" "P\<^sub>2 \<noteq> []" "path E (P\<^sub>1 @ P\<^sub>2)" "hd P\<^sub>1 = last P\<^sub>2"
  shows "path E (P\<^sub>2 @ tl P\<^sub>1)"
  using assms path_suff[of E P\<^sub>1 P\<^sub>2] path_pref[of E P\<^sub>1 P\<^sub>2] path_concat[of E P\<^sub>2 P\<^sub>1] by auto

lemma path_last_edge:
  assumes "path E (u#P @ [v])"
  shows "{last (u#P),v} \<in> E"
  using assms by (induction P arbitrary: u) auto

lemma path_rotate:
  assumes "path E (u#P\<^sub>1 @ v#P\<^sub>2 @ [u])" (is "path E ?P")
  shows "path E (v#P\<^sub>2 @ u#P\<^sub>1 @ [v])" (is "path E ?P'")
proof -
  have "path E (v#P\<^sub>2 @ u#P\<^sub>1)"
    using assms path_swap[of "u#P\<^sub>1" "v#P\<^sub>2 @ [u]" E] by auto
  moreover have "path E [v]"
    using assms mem_path_Vs[of E ?P v] by auto
  moreover have "{last (v#P\<^sub>2 @ u#P\<^sub>1),v} \<in> E"
    using assms path_last_edge[of E u P\<^sub>1 v] path_pref[of E "u#P\<^sub>1 @ [v]" "P\<^sub>2 @ [u]"] by auto
  ultimately show ?thesis
    using path_append[of E "v#P\<^sub>2 @ u#P\<^sub>1" "[v]"] by auto
qed

lemma edges_of_path_append:
  assumes "P\<^sub>1 \<noteq> []"
  shows "edges_of_path (P\<^sub>1 @ u#P\<^sub>2) = edges_of_path P\<^sub>1 @ [{last P\<^sub>1,u}] @ edges_of_path (u#P\<^sub>2)"
  using assms by (induction P\<^sub>1 rule: list012.induct) auto

lemma edges_of_path_rotate:
  "set (edges_of_path (u#P\<^sub>1 @ v#P\<^sub>2 @ [u])) = set (edges_of_path (v#P\<^sub>2 @ u#P\<^sub>1 @ [v]))"
  (is "set (edges_of_path ?P) = set (edges_of_path ?P')")
proof -
  have "set (edges_of_path ?P) 
    = set (edges_of_path (u#P\<^sub>1)) \<union> {{last (u#P\<^sub>1),v}} \<union> set (edges_of_path (v#P\<^sub>2 @ [u]))"
    using edges_of_path_append[of "u#P\<^sub>1" v "P\<^sub>2 @ [u]"] by auto
  also have "... = set (edges_of_path (u#P\<^sub>1)) \<union> {{last (u#P\<^sub>1),v}} 
    \<union> set (edges_of_path (v#P\<^sub>2)) \<union> {{last (v#P\<^sub>2),u}}"
    using edges_of_path_append[of "v#P\<^sub>2" u "[]"] by auto  
  also have 
    "... = set (edges_of_path (v#P\<^sub>2)) \<union> {{last (v#P\<^sub>2),u}} \<union> set (edges_of_path (u#P\<^sub>1 @ [v]))"
    using edges_of_path_append[of "u#P\<^sub>1" v "[]"] by auto
  also have "... = set (edges_of_path ?P')"
    using edges_of_path_append[of "v#P\<^sub>2" u "P\<^sub>1 @ [v]"] by auto
  finally show ?thesis .
qed

lemma length_edges_of_path_rotate:
  "length (edges_of_path (u#P\<^sub>1 @ v#P\<^sub>2 @ [u])) = length (edges_of_path (v#P\<^sub>2 @ u#P\<^sub>1 @ [v]))"
  (is "length (edges_of_path ?P) = length (edges_of_path ?P')")
proof -
  have "length (edges_of_path ?P) = length ?P -1"
    using edges_of_path_length[of ?P] by auto
  also have "... = length (edges_of_path ?P')"
    using edges_of_path_length[of ?P'] by auto
  finally show ?thesis .
qed

lemma simple_path_rotate:
  assumes "simple_path (u#P\<^sub>1 @ v#P\<^sub>2 @ [u])" (is "simple_path ?P")
  shows "simple_path (v#P\<^sub>2 @ u#P\<^sub>1 @ [v])" (is "simple_path ?P'")
proof (rule simple_pathI; rule card_distinct) 
  have "card (set (edges_of_path ?P')) = card (set (edges_of_path ?P))"
    by (auto simp: edges_of_path_rotate)
  also have "... = length (edges_of_path ?P)"
    apply (rule distinct_card)
    using assms by (auto elim: simple_pathE)
  also have "... = length (edges_of_path ?P')"
    by (auto simp: length_edges_of_path_rotate)
  finally show "card (set (edges_of_path ?P')) = length (edges_of_path ?P')" .
qed

lemma split_hd: 
  assumes "xs \<noteq> []"
  obtains xs' where "xs = hd xs#xs'"
  using assms list.exhaust_sel by blast

lemma split_last:
  assumes "xs \<noteq> []" 
  obtains xs' where "xs = xs' @ [last xs]"
  using assms append_butlast_last_id by metis

lemma cycle_path_split:
  assumes "graph_invar E" "is_cycle E C" "v \<in> set C" "v \<noteq> hd C"
  obtains u P\<^sub>1 P\<^sub>2 where "C = u#P\<^sub>1 @ v#P\<^sub>2 @ [u]"
proof -
  obtain u where "walk_betw E u C u"
    using assms by (auto elim: is_cycleE)
  hence [simp]: "hd C = u" "last C = u"
    by (auto elim: nonempty_path_walk_between)
  moreover have "C \<noteq> []"
    using assms cycle_length by auto
  ultimately obtain C' where "C = u#C'"
    by (auto elim: split_hd[of C])
  moreover hence "C' \<noteq> []"
    using assms cycle_length[of E C] by auto
  ultimately obtain C'' where [simp]: "C = u#C'' @ [u]"
    using \<open>last C = u\<close> by (auto elim: split_last[of C'])
  hence "v \<in> set C''"
    using assms by auto
  then obtain P\<^sub>1 P\<^sub>2 where "C = u#P\<^sub>1 @ v#P\<^sub>2 @ [u]"
    using split_list[of v C''] by auto
  thus ?thesis
    using that by auto
qed

lemma cycle_rotate:
  assumes "graph_invar E" "is_cycle E C" "v \<in> set C"
  obtains C' where "is_cycle E C'" "walk_betw E v C' v"
proof (cases "v = hd C")
  case True
  hence "is_cycle E C" "walk_betw E v C v"
    using assms by (auto elim: is_cycleE_hd)
  thus ?thesis 
    using that by auto
next
  case False
  then obtain u P\<^sub>1 P\<^sub>2 where [simp]: "C = u#P\<^sub>1 @ v#P\<^sub>2 @ [u]"
    using assms by (elim cycle_path_split) auto
  let ?C'="v#P\<^sub>2 @ u#P\<^sub>1 @ [v]"
  have "path E C" "simple_path C" "length (edges_of_path C) > 0"
    using assms by (auto elim: is_cycleE walk_between_nonempty_path)
  moreover hence "walk_betw E v ?C' v"
    using path_rotate by (fastforce intro: nonempty_path_walk_between)+
  moreover have "simple_path ?C'" "length (edges_of_path ?C') > 0"
    using calculation simple_path_rotate[of u P\<^sub>1 v P\<^sub>2] length_edges_of_path_rotate[of u P\<^sub>1 v P\<^sub>2]
    by auto
  moreover have "is_cycle E ?C'"
    using calculation by (auto intro: is_cycleI)
  ultimately show ?thesis using that by auto
qed

lemma cycle_degree:
  assumes "graph_invar E" "is_cycle E C" "v \<in> set C"
  shows "degree E v \<ge> 2"
proof -
  obtain C' where "is_cycle E C'" "walk_betw E v C' v"
    using assms cycle_rotate[of E] by auto
  moreover hence "path E C'" "v = hd C'" "v = last C'"
    by (auto simp: walk_between_nonempty_path)
  moreover have 
    "v \<in> hd (edges_of_path C')" (is "v \<in> ?e\<^sub>1") "v \<in> last (edges_of_path C')" (is "v \<in> ?e\<^sub>2") 
    using assms calculation cycle_length[of E C'] last_v_in_last_e[of C'] hd_v_in_hd_e[of C']
    by auto
  moreover have "edges_of_path C' \<noteq> []"
    using assms calculation cycle_edge_length[of E C'] by auto
  moreover hence "?e\<^sub>1 \<in> set (edges_of_path C')" "?e\<^sub>2 \<in> set (edges_of_path C')" 
    using hd_in_set[of "edges_of_path C'"] last_in_set[of "edges_of_path C'"] by auto
  moreover have "{?e\<^sub>1,?e\<^sub>2} \<subseteq> {e \<in> E. v \<in> e}"
    using calculation path_edges_subset[of E C', OF \<open>path E C'\<close>] by auto
  moreover have "finite {?e\<^sub>1,?e\<^sub>2}" "card {?e\<^sub>1,?e\<^sub>2} = 2"
    using assms \<open>is_cycle E C'\<close> cycle_edges_hd_last_neq by auto
  moreover hence "card' {?e\<^sub>1,?e\<^sub>2} = 2"
    using card'_finite_nat[of "{?e\<^sub>1,?e\<^sub>2}"] by auto
  ultimately have "card' {e \<in> E. v \<in> e} \<ge> 2"
    using card'_mono[of "{?e\<^sub>1,?e\<^sub>2}" "{e \<in> E. v \<in> e}"] by presburger
  thus ?thesis
    unfolding degree_def2 by (auto simp: degree_def)
qed

definition "is_acyclic E \<equiv> \<nexists>C. is_cycle E C"

lemma is_acyclicI: "(\<nexists>C. is_cycle E C) \<Longrightarrow> is_acyclic E"
  unfolding is_acyclic_def by auto

lemma is_acyclicE:
  assumes "is_acyclic E"
  shows "\<nexists>C. is_cycle E C"
  using assms[unfolded is_acyclic_def] by auto

lemma not_acyclicE:
  assumes "\<not> is_acyclic E"
  obtains C where "is_cycle E C"
  using assms[unfolded is_acyclic_def] by auto

lemma not_acyclicE2:
  assumes "graph_invar E" "\<not> is_acyclic E"
  obtains u v P P' where "simple_path P" "walk_betw E u P v" 
    "simple_path P'" "walk_betw E u P' v" "P \<noteq> P'"
proof -
  obtain C where "is_cycle E C"
    using assms by (auto elim: not_acyclicE)
  moreover then obtain v where "simple_path C" "walk_betw E v C v"
    by (auto elim: is_cycleE)
  moreover hence "simple_path (rev C)" "walk_betw E v (rev C) v"
    using walk_symmetric[of E v C v] simple_path_rev by auto
  moreover hence "C \<noteq> rev C"
    using assms calculation simple_path_rev_neq[OF _ cycle_length] by auto
  ultimately show thesis
    using that by auto
qed

text \<open>Tree\<close>
definition "is_tree T \<equiv> is_connected T \<and> is_acyclic T"

lemma is_treeI: "is_connected T \<Longrightarrow> is_acyclic T \<Longrightarrow> is_tree T"
  unfolding is_tree_def by auto

lemma is_treeE: 
  assumes "is_tree T" 
  shows "is_connected T" "is_acyclic T"
  using assms[unfolded is_tree_def] by auto

context graph_abs
begin

text \<open>Spanning Tree\<close>
definition "is_st T \<equiv> T \<subseteq> E \<and> Vs E = Vs T \<and> is_tree T"

lemma is_stI: "T \<subseteq> E \<Longrightarrow> Vs E = Vs T \<Longrightarrow> is_tree T \<Longrightarrow> is_st T"
  unfolding is_st_def by auto

lemma is_stE:
  assumes "is_st T"
  shows "T \<subseteq> E" "Vs E = Vs T" "is_tree T"
  using assms[unfolded is_st_def] by auto

lemma st_graph_invar:
  assumes "is_st T"
  shows "graph_invar T"
proof -
  have "\<forall>e\<in>T. \<exists>u v. e = {u, v} \<and> u \<noteq> v" 
    using assms graph is_stE by blast
  moreover have "finite (Vs T)"
    using assms graph by (auto simp: is_stE)
  ultimately show ?thesis by auto
qed

text \<open>Convert to graph from \<open>Prim_Dijkstra_Simple\<close>.\<close>
abbreviation "G \<equiv> Undirected_Graph.graph (Vs E) {(u,v)| u v. {u,v} \<in> E}"

lemma G_finite: "finite (Vs E)" "finite {(u,v)| u v. {u,v} \<in> E}"
  using graph finite_subset[of "{(u,v)| u v. {u,v} \<in> E}" "Vs E \<times> Vs E"] 
  by (auto intro: vs_member_intro)

lemma nodes_equiv: "v \<in> Vs E \<longleftrightarrow> v \<in> nodes G"
proof
  assume "v \<in> Vs E"
  thus "v \<in> nodes G"
    using graph_accs[OF G_finite] by auto
next
  let ?E'="{(u,v) |u v. {u,v} \<in> E}"
  assume "v \<in> nodes G"
  hence "v \<in> Vs E \<or> v \<in> fst ` ?E' \<or> v \<in> snd ` ?E'"
    using graph_accs[OF G_finite] by auto
  thus "v \<in> Vs E"
  proof (elim disjE)
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

lemma edges_equiv: "{u,v} \<in> E \<longleftrightarrow> (u,v) \<in> edges G"
  using graph graph_accs[OF G_finite] by (auto simp: insert_commute)

lemma edges_equiv2: "E = uedge ` edges G"
proof
  show "E \<subseteq> uedge ` edges G"
  proof
    fix e
    assume "e \<in> E"
    moreover then obtain u v where [simp]: "e = {u,v}"
      using graph by auto
    ultimately have "(u,v) \<in> edges G"
      using edges_equiv[of u v] by auto
    thus "e \<in> uedge ` edges G"
      unfolding uedge_def by auto
  qed
next
  show "uedge ` edges G \<subseteq> E"
  proof
    fix e
    assume "e \<in> uedge ` edges G"
    moreover then obtain e' where "e = uedge e'" "e' \<in> edges G"
      by auto   
    moreover then obtain u v where [simp]: "e' = (u,v)"
      by fastforce
    moreover hence "e = {u,v}"
      unfolding uedge_def using calculation by auto
    ultimately show "e \<in> E"
      using edges_equiv[of u v] by auto
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

lemma edges_subset_iff: "set (dedges_of_path P) \<subseteq> edges G \<longleftrightarrow> set (edges_of_path P) \<subseteq> E"
proof
  show "set (dedges_of_path P) \<subseteq> edges G \<Longrightarrow> set (edges_of_path P) \<subseteq> E"
  proof (induction P rule: dedges_of_path.induct)
    case (3 u v P)
    thus ?case 
      using edges_equiv[of u v] by auto
  qed auto
next
  show "set (edges_of_path P) \<subseteq> E \<Longrightarrow> set (dedges_of_path P) \<subseteq> edges G"
  proof (induction P rule: dedges_of_path.induct)
    case (3 u v P)
    thus ?case 
      using edges_equiv[of u v] by auto
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
  assumes "Undirected_Graph.path G u P v"
  obtains P' where "P = dedges_of_path P'"
  using assms vpath_of_epath by auto

lemma simple_path_equiv: "simple_path P \<longleftrightarrow> Undirected_Graph.simple (dedges_of_path P)"
  unfolding Undirected_Graph.simple_def
  by (auto intro: simple_pathI elim: simple_pathE simp: map_dedges_of_path) 

lemma list_hd_singleton: "length xs = 1 \<Longrightarrow> hd xs = x \<Longrightarrow> xs = [x]"
  by (induction xs) auto

lemma walk_is_path:
  assumes "walk_betw E u P v"
  shows "Undirected_Graph.path G u (dedges_of_path P) v"
proof -
  have "path E P" "P \<noteq> []" "hd P = u" "last P = v" "u \<in> Vs E"
    using assms by (auto simp: mem_path_Vs elim: walk_between_nonempty_path)
  thus "Undirected_Graph.path G u (dedges_of_path P) v"
  proof (induction P arbitrary: u rule: path.induct)
    case (path2 u' x P)
    hence [simp]: "u = u'" and "(u,x) \<in> edges G" 
      "Undirected_Graph.path G x (dedges_of_path (x#P)) v"
      using edges_equiv[of u x] by auto
    moreover hence "Undirected_Graph.path G u [(u,x)] x"
      by (auto intro: path_emptyI)
    ultimately show ?case 
      using \<open>u \<in> Vs E\<close> path_transs1 by auto
  qed (auto intro: path_emptyI)
qed

lemma path_equiv2:
  assumes "set P \<subseteq> Vs E" "Undirected_Graph.path G u (dedges_of_path P) v"
  shows "path E P"
  using assms
proof (induction P arbitrary: u rule: dedges_of_path.induct)
  case (3 u' x P)
  hence "{u',x} \<in> E" "path E (x#P)"
    using 3 edges_equiv[of u x] by auto  
  thus ?case 
    by (auto intro: path.intros)
qed auto

lemma edges_of_vpath_are_vs:
  assumes "\<And>v. P = [v] \<Longrightarrow> v \<in> Vs E" "set (edges_of_path P) \<subseteq> E"
  shows "set P \<subseteq> Vs E"
  using assms
proof (induction P rule: list0123.induct)
  case (3 u v)
  thus ?case 
    by (auto intro: vs_member_intro[of _ "{u,v}" E])
qed auto

lemma epath_last_node:
  assumes "P \<noteq> []" "hd P = u" "Undirected_Graph.path G u (dedges_of_path P) v"
  shows "last P = v"
  using assms by (induction P arbitrary: u rule: dedges_of_path.induct) auto

lemma path_is_walk:
  assumes "P \<noteq> []" "hd P = u" "u \<in> Vs E" "Undirected_Graph.path G u (dedges_of_path P) v"
  shows "walk_betw E u P v"
proof (rule nonempty_path_walk_between)
  have "set (edges_of_path P) \<subseteq> E"
    using assms path_edges[of G u "dedges_of_path P" v] edges_subset_iff by auto
  hence "set P \<subseteq> Vs E"
    using assms edges_of_vpath_are_vs list.sel(1) by metis
  thus "path E P" "P \<noteq> []" "hd P = u" "last P = v"
    using assms path_equiv2 epath_last_node by auto
qed

lemma walk_equiv_path: "walk_betw E u P v 
  \<longleftrightarrow> P \<noteq> [] \<and> hd P = u \<and> u \<in> Vs E \<and> Undirected_Graph.path G u (dedges_of_path P) v"
proof
  assume "walk_betw E u P v"
  moreover hence "path E P" "P \<noteq> []" "hd P = u" "last P = v" "u \<in> Vs E"
    by (auto simp: mem_path_Vs elim: walk_between_nonempty_path)
  ultimately show "P \<noteq> [] \<and> hd P = u \<and> u \<in> Vs E \<and> Undirected_Graph.path G u (dedges_of_path P) v"
    using walk_is_path by auto
next
  assume assms: "P \<noteq> [] \<and> hd P = u \<and> u \<in> Vs E \<and> Undirected_Graph.path G u (dedges_of_path P) v"
  show "walk_betw E u P v"
  proof (rule nonempty_path_walk_between)
    have "set (edges_of_path P) \<subseteq> E"
      using assms path_edges[of G u "dedges_of_path P" v] edges_subset_iff by auto
    hence "set P \<subseteq> Vs E"
      using assms edges_of_vpath_are_vs list.sel(1) by metis
    thus "path E P" "P \<noteq> []" "hd P = u" "last P = v"
      using assms path_equiv2 epath_last_node by auto
  qed
qed

lemma walk_iff_rtrancl_edges: 
  assumes "u \<in> Vs E" "v \<in> Vs E"
  shows "(\<exists>P. walk_betw E u P v) \<longleftrightarrow> (u,v) \<in> (edges G)\<^sup>*"
proof
  assume "\<exists>P. walk_betw E u P v"
  thus "(u,v) \<in> (edges G)\<^sup>*"
    using walk_is_path[of u _ v] rtrancl_edges_iff_path[of u v G] by auto
next
  assume "(u,v) \<in> (edges G)\<^sup>*"
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
    hence "{y,z} \<in> E" "y \<in> Vs E"
      using edges_equiv[of y z] by (auto intro: vs_member_intro[of y "{y,z}"])
    then obtain P where "walk_betw E u P y" "path E [y,z]"
      using step.prems step.IH by (auto intro: path.intros)
    moreover hence "walk_betw E y [y,z] z"
      by (auto intro: path.intros nonempty_path_walk_between)
    ultimately have "walk_betw E u (P@[z]) z"
      using walk_transitive[of E u P y "[y,z]" z] by auto
    thus ?case 
      by auto
  qed  
qed

lemma conn_comp_equiv: 
  assumes "u \<in> Vs E" "v \<in> Vs E"
  shows "v \<in> connected_component E u \<longleftrightarrow> (u,v) \<in> (edges G)\<^sup>*"
proof
  assume "v \<in> connected_component E u"
  hence "(\<exists>p. walk_betw E u p v)"
    using assms by (auto elim: in_connected_component_has_path)
  thus "(u,v) \<in> (edges G)\<^sup>*"
    using assms walk_iff_rtrancl_edges by auto
next
  assume "(u,v) \<in> (edges G)\<^sup>*"
  hence "(\<exists>p. walk_betw E u p v)"
    using assms walk_iff_rtrancl_edges by auto
  thus "v \<in> connected_component E u"
    by (auto intro: has_path_in_connected_component)
qed

lemma connected_equiv: "is_connected E \<longleftrightarrow> connected G"
proof 
  assume "is_connected E"
  show "connected G"
  proof (rule connectedI)
    fix u v
    assume "u \<in> nodes G" "v \<in> nodes G"
    hence "u \<in> Vs E" "v \<in> Vs E"
      using nodes_equiv by auto
    hence "v \<in> connected_component E u"
      using \<open>is_connected E\<close> by (auto elim: is_connectedE)
    thus "(u,v) \<in> (edges G)\<^sup>*"
      using \<open>u \<in> Vs E\<close> \<open>v \<in> Vs E\<close> conn_comp_equiv by auto
  qed
next
  assume "connected G"
  show "is_connected E"
  proof (rule is_connectedI)
    fix u v
    assume "u \<in> Vs E" "v \<in> Vs E"
    hence "u \<in> nodes G" "v \<in> nodes G"
      using nodes_equiv by auto
    hence "(u,v) \<in> (edges G)\<^sup>*"
      using \<open>Undirected_Graph.connected G\<close> by (auto elim: connectedD)
    thus "v \<in> connected_component E u"
      using \<open>u \<in> Vs E\<close> \<open>v \<in> Vs E\<close> conn_comp_equiv by auto
  qed
qed

lemma walks_len_gr1:
  assumes "walk_betw E u P v" "walk_betw E u P' v" "P \<noteq> P'"
  shows "length P > 1 \<or> length P' > 1"
proof (rule ccontr)
  assume "\<not> (length P > 1 \<or> length P' > 1)"
  hence "length P \<le> 1" "length P' \<le> 1"
    by auto
  moreover have "length P \<ge> 1" "length P' \<ge> 1"
    using assms by (auto simp: walk_nonempty Suc_leI)
  ultimately have "length P = 1" "length P' = 1"
    by auto
  moreover have "hd P = u" "hd P' = u"
    using assms by (auto elim: walk_between_nonempty_path)
  ultimately have "P = [u]" "P' = [u]"
    by (auto intro: list_hd_singleton)
  thus "False"
    using assms by auto
qed

lemma dedges_path_hd_Vs_mem:
  assumes "Undirected_Graph.path G u (dedges_of_path P) v" "dedges_of_path P \<noteq> []"
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
      using edges_equiv[of u v] by auto
    thus ?case 
      by (auto simp: edges_are_Vs)
  }
qed auto

lemma acyclic_equiv: "is_acyclic E \<longleftrightarrow> cycle_free G"
proof
  assume "is_acyclic E"
  show "cycle_free G"
  proof (rule cycle_freeI)
    fix P u
    assume "Undirected_Graph.path G u P u" "P \<noteq> []" "simple P"
    moreover then obtain P' where "P = dedges_of_path P'"
      using vpath_of_epathE[of u P u] by auto
    ultimately have "simple_path P'" "0 < length (edges_of_path P')" "walk_betw E u P' u"
      using simple_path_equiv dedges_of_path_nonnilE dedges_path_hd_Vs_mem 
        walk_equiv_path[of u P' u] by (auto simp: dedges_length[symmetric, of P'])
    hence "is_cycle E P'"
      by (auto intro: is_cycleI)
    thus "False"
      using \<open>is_acyclic E\<close> is_acyclicE by auto
  qed
next
  assume "cycle_free G"
  show "is_acyclic E"
  proof (rule ccontr)
    assume "\<not> is_acyclic E"
    then obtain C where "is_cycle E C"
      by (auto elim: not_acyclicE)
    then obtain u where "simple_path C" "0 < length (edges_of_path C)" "walk_betw E u C u"
      by (auto elim: is_cycleE)
    hence "Undirected_Graph.path G u (dedges_of_path C) u" "dedges_of_path C \<noteq> []" 
      "simple (dedges_of_path C)"
      using walk_equiv_path[of u C u] simple_path_equiv 
      by (auto simp: dedges_length[symmetric, of C])
    thus "False"
      using \<open>cycle_free G\<close> cycle_freeD[of G] by auto
  qed
qed

lemma tree_equiv: "is_tree E \<longleftrightarrow> tree G"
  using connected_equiv acyclic_equiv by (auto intro: is_treeI simp: is_treeE tree_def)

end

locale st_graph_abs = (* spanning tree equivalence *)
  E: graph_abs E +
  T: graph_abs T for E :: "'a set set " and T :: "'a set set"
begin

lemma edges_subset_iff: "T \<subseteq> E \<longleftrightarrow> edges T.G \<subseteq> edges E.G"
proof
  assume "T \<subseteq> E"
  show "edges T.G \<subseteq> edges E.G"
  proof
    fix x
    assume "x \<in> edges T.G"
    moreover then obtain u v where [simp]: "x = (u,v)"
      using old.prod.exhaust by blast
    ultimately show "x \<in> edges E.G"
      using T.edges_equiv[of u v] \<open>T \<subseteq> E\<close> E.edges_equiv[of u v] by auto
  qed
next
  assume "edges T.G \<subseteq> edges E.G"
  show "T \<subseteq> E"
  proof
    fix x
    assume "x \<in> T"
    moreover then obtain u v where [simp]: "x = {u,v}"
      using T.graph by auto
    ultimately show "x \<in> E"
      using T.edges_equiv[of u v] \<open>edges T.G \<subseteq> edges E.G\<close> E.edges_equiv[of u v] by auto
  qed
qed

lemma st_equiv: "E.is_st T \<longleftrightarrow> is_spanning_tree E.G T.G"
  apply (rule iffI)
  using T.tree_equiv E.nodes_equiv T.nodes_equiv edges_subset_iff 
  by (auto intro: E.is_stI simp: E.is_stE is_spanning_tree_def)

end

context graph_abs
begin

lemma st_equiv: 
  fixes T
  defines "T\<^sub>G \<equiv> graph (Vs T) {(u, v) |u v. {u, v} \<in> T}" 
  assumes "graph_invar T"
  shows "is_st T \<longleftrightarrow> is_spanning_tree G T\<^sub>G"
  using graph assms st_graph_abs.st_equiv[unfolded st_graph_abs_def graph_abs_def, of E T] by auto

end

context w_graph_abs
begin

definition "cost_of_st T \<equiv> (\<Sum>e\<in>T. c e)"

text \<open>Minimum Spanning Tree\<close>
definition "is_mst T \<equiv> is_st T \<and> (\<forall>T'. is_st T' \<longrightarrow> cost_of_st T \<le> cost_of_st T')"

lemma is_mstE:
  assumes "is_mst T"
  shows "is_st T" "\<And>T'. is_st T' \<Longrightarrow> cost_of_st T \<le> cost_of_st T'"
  using assms[unfolded is_mst_def] by auto

lemma mst_eq_cost:
  assumes "is_mst T\<^sub>1" "is_mst T\<^sub>2"
  shows "cost_of_st T\<^sub>1 = cost_of_st T\<^sub>2"
  using assms[unfolded is_mst_def] by fastforce

end

locale nat_w_graph_abs = (* nat weights *)
  pos_w_graph_abs E c for E :: "'a set set" and c :: "'a set \<Rightarrow> nat"
begin

lemma cost_of_st_equiv: 
  fixes T
  defines "T\<^sub>G \<equiv> graph (Vs T) {(u, v) |u v. {u, v} \<in> T}"
  assumes "graph_invar T"
  shows "cost_of_st T = weight c T\<^sub>G"
proof -
  have "cost_of_st T = (\<Sum>e \<in> T. c e)"
    unfolding cost_of_st_def by auto
  also have "... = (\<Sum>e \<in> uedge ` edges T\<^sub>G. c e)"
    using assms graph_abs.edges_equiv2[unfolded graph_abs_def, of T] by auto
  also have "... = Undirected_Graph.weight c T\<^sub>G"
    unfolding Undirected_Graph.weight_alt by auto
  finally show ?thesis .
qed

lemma mst_equiv: 
  fixes T
  defines "T\<^sub>G \<equiv> graph (Vs T) {(u, v) |u v. {u, v} \<in> T}" 
  shows "is_mst T \<longleftrightarrow> is_MST c G T\<^sub>G"
proof 
  assume "is_mst T"
  hence "is_st T" "\<And>T'. is_st T' \<Longrightarrow> cost_of_st T \<le> cost_of_st T'"
    by (auto elim: is_mstE)

  hence "is_spanning_tree G T\<^sub>G" 
    "\<forall>T'. is_spanning_tree G T' \<longrightarrow> weight c T\<^sub>G \<le> weight c T'"
    subgoal
      using assms st_equiv[OF st_graph_invar] by auto
    subgoal
      using assms st_equiv cost_of_st_equiv[OF st_graph_invar]
      sorry
    sorry

  thus "is_MST c G T\<^sub>G"
    unfolding is_MST_def by auto
next
  assume "is_MST c G T\<^sub>G"
  hence "is_spanning_tree G T\<^sub>G" 
    "\<forall>T'. is_spanning_tree G T' \<longrightarrow> weight c T\<^sub>G \<le> weight c T'"
    unfolding is_MST_def by auto

  show "is_mst T"
    sorry
qed


end

locale mst = w_graph_abs E c for E c +
  fixes comp_mst
  assumes mst: "is_mst (comp_mst c E)"
begin

end

(* TODO: use Prim_Dijkstra_Simple *)

fun prim_impl' where
  "prim_impl' c E = undefined" (* translate params to prim_impl, or prim_list_impl_int *)

(* interpretation mst E c prim_impl'
  sorry *)

end