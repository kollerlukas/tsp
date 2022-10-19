(* Author: Lukas Koller *)
theory MST                                           
  imports Main Misc CompleteGraph WeightedGraph 
begin

section \<open>Connected Graphs\<close>

definition "is_connected E \<equiv> \<forall>u\<in>Vs E.\<forall>v\<in>Vs E. u \<in> connected_component E v"

lemma is_connectedI: 
  "(\<And>u v. u\<in>Vs E \<Longrightarrow> v\<in>Vs E \<Longrightarrow> u \<in> connected_component E v) \<Longrightarrow> is_connected E"
  unfolding is_connected_def by auto

lemma is_connectedI2: 
  assumes "\<And>u v. u\<in>Vs E \<Longrightarrow> v\<in>Vs E \<Longrightarrow> u \<noteq> v \<Longrightarrow> u \<in> connected_component E v"
  shows "is_connected E"
proof (rule is_connectedI)
  fix u v 
  assume "u \<in> Vs E" "v \<in> Vs E"
  thus "u \<in> connected_component E v"
    using assms by (cases "u = v") (auto simp: in_own_connected_component)
qed

lemma is_connectedE: "is_connected E \<Longrightarrow> u \<in> Vs E \<Longrightarrow> v \<in> Vs E \<Longrightarrow> u \<in> connected_component E v"
  unfolding is_connected_def by auto

lemma is_connectedE2: 
  assumes "is_connected E" "u \<in> Vs E" "v \<in> Vs E" "u \<noteq> v"
  obtains P where "walk_betw E u P v"
  using assms[unfolded is_connected_def connected_component_def] by fastforce

context compl_graph_abs
begin

lemma is_connected: "is_connected E"
proof (intro is_connectedI2)
  fix u v
  assume "u \<in> Vs E" "v \<in> Vs E" "u \<noteq> v"
  moreover hence "{v,u} \<in> E"
    by (auto intro: edge_in_E_intro)
  ultimately show "u \<in> connected_component E v"
    by (subst insert_absorb[symmetric]) (auto intro: in_con_comp_insert)
qed

end

lemma path_connected:
  assumes "path E P"
  shows "is_connected (set (edges_of_path P))" (is "is_connected ?E\<^sub>P")
proof (rule is_connectedI)
  fix u v
  assume "u \<in> Vs ?E\<^sub>P" "v \<in> Vs ?E\<^sub>P"
  then have "u \<in> set P" "v \<in> set P"
    using edges_of_path_Vs[of P] by auto
  then obtain i\<^sub>u i\<^sub>v where u_v_simps: "u = P ! i\<^sub>u" "i\<^sub>u < length P" "v = P ! i\<^sub>v" "i\<^sub>v < length P"
    using set_conv_nth[of P] by auto
  consider "i\<^sub>u = i\<^sub>v" | "i\<^sub>u < i\<^sub>v" | "i\<^sub>v < i\<^sub>u"
    by linarith
  thus "u \<in> connected_component ?E\<^sub>P v"
  proof cases
    assume "i\<^sub>u = i\<^sub>v"
    thus ?thesis
      using u_v_simps in_own_connected_component[of "P ! i\<^sub>u" ?E\<^sub>P] by auto
  next
    assume "i\<^sub>u < i\<^sub>v"
    then obtain P' where "walk_betw ?E\<^sub>P u P' v"
      using assms u_v_simps by (auto elim: walk_of_pathE[of E P i\<^sub>u i\<^sub>v])
    thus ?thesis
      unfolding connected_component_def using walk_symmetric[of ?E\<^sub>P u P' v] by auto
  next
    assume "i\<^sub>v < i\<^sub>u"
    thus ?thesis
      unfolding connected_component_def using assms u_v_simps walk_on_path[of E P i\<^sub>v i\<^sub>u] by auto
  qed
qed

lemma connected_bridge:
  assumes "is_connected X" "X' \<subseteq> X" "Vs X' \<noteq> {}" "Vs X' \<subset> Vs X"
  obtains u v where "{u,v} \<in> X" "u \<in> Vs X'" "v \<in> Vs X - Vs X'"
proof -
  obtain u v where "u \<in> Vs X'" "v \<in> Vs X - Vs X'"
    using assms by auto
  moreover hence "u \<in> Vs X" "v \<in> Vs X" "u \<noteq> v"
    using assms calculation by auto
  moreover then obtain P where "walk_betw X u P v"
    using assms is_connectedE2[of X u v] by auto
  moreover have "set P \<subseteq> Vs X' \<union> (Vs X - Vs X')"
    using calculation walk_in_Vs[of X u P v] by auto
  moreover have "set (edges_of_path P) \<subseteq> X"
    using calculation path_edges_subset[OF walk_between_nonempty_path(1), of X u P v] by auto
  ultimately obtain u v where "{u,v} \<in> X" "u \<in> Vs X'" "v \<in> Vs X - Vs X'"
    by (elim walk_split[of X u P v "Vs X'" "Vs X - Vs X'"]) fastforce+
  thus ?thesis
    using that by auto
qed

section \<open>Simple Paths\<close>

definition "is_simple P \<equiv> distinct (edges_of_path P)"

lemma is_simpleI: "distinct (edges_of_path P) \<Longrightarrow> is_simple P"
  unfolding is_simple_def by auto

lemma is_simpleE: "is_simple P \<Longrightarrow> distinct (edges_of_path P)"
  unfolding is_simple_def by auto

lemma is_simpleI2: "distinct P \<Longrightarrow> is_simple P"
  using distinct_edges_of_vpath by (auto intro: is_simpleI) 

lemma simple_path_rev: "is_simple P \<Longrightarrow> is_simple (rev P)"
  using edges_of_path_rev[of P] distinct_rev[of "edges_of_path P"] by (auto simp: is_simple_def)

lemma simple_path_cons: "is_simple (v#P) \<Longrightarrow> is_simple P"
  unfolding is_simple_def using distinct_edges_of_paths_cons[of v P] by auto

lemma is_simple_rev_neq:
  assumes "is_simple P" "length P > 2"
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
        distinct_hd_last_neq[OF is_simpleE[of "u#v#w#P"]] by auto
  qed
qed auto

lemma is_simple_rotate:
  assumes "is_simple (u#P\<^sub>1 @ v#P\<^sub>2 @ [u])" (is "is_simple ?P")
  shows "is_simple (v#P\<^sub>2 @ u#P\<^sub>1 @ [v])" (is "is_simple ?P'")
proof (rule is_simpleI; rule card_distinct) 
  have "card (set (edges_of_path ?P')) = card (set (edges_of_path ?P))"
    by (auto simp: edges_of_path_rotate)
  also have "... = length (edges_of_path ?P)"
    apply (rule distinct_card)
    using assms by (auto elim: is_simpleE)
  also have "... = length (edges_of_path ?P')"
    by (auto simp: length_edges_of_path_rotate)
  finally show "card (set (edges_of_path ?P')) = length (edges_of_path ?P')" .
qed

section \<open>Acyclic Graphs\<close>

text \<open>Definition for a cycle in a graph. A cycle is a vertex-path, thus a cycle needs to contain 
at least one edge, otherwise the singleton path \<open>[v]\<close> is a cycle. Therefore, no graph would be 
acyclic.\<close>
definition "is_cycle E C \<equiv> (\<exists>v. walk_betw E v C v) \<and> is_simple C \<and> length (edges_of_path C) > 0"

lemma is_cycleI:
  "is_simple C \<Longrightarrow> length (edges_of_path C) > 0 \<Longrightarrow> walk_betw E v C v \<Longrightarrow> is_cycle E C"
  unfolding is_cycle_def by auto

lemma is_cycleE:
  assumes "is_cycle E C"
  obtains v where "is_simple C" "length (edges_of_path C) > 0" "walk_betw E v C v"
  using assms[unfolded is_cycle_def] by auto

lemma is_cycleE_hd:
  assumes "is_cycle E C"
  shows "is_simple C" "length (edges_of_path C) > 0" "walk_betw E (hd C) C (hd C)"
proof -
  show "is_simple C" "0 < length (edges_of_path C)"
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

lemma cycle_hd_last_eq: 
  assumes "is_cycle E C" 
  shows "hd C = last C"
proof -
  obtain v where "walk_betw E v C v"
    using assms by (auto elim: is_cycleE)
  hence "hd C = v" "last C = v"
    by (auto elim: walk_between_nonempty_path)
  thus ?thesis
    by (auto elim: walk_between_nonempty_path)
qed

text \<open>Not using \<open>graph_abs\<close> because for the Double-Tree algorithm we need to talk about cycles 
in subgraphs.\<close>
lemma cycle_length:
  assumes "graph_invar E" "is_cycle E C"
  shows "length C > 2"
  using assms
proof (induction C rule: list0123.induct)
  case (3 u v)
  then obtain v' where "is_simple [u,v]" "length (edges_of_path [u,v]) > 0" 
    "walk_betw E v' [u,v] v'"
    by (auto elim: is_cycleE)
  hence "u = v'" "v = v'" "path E [u,v]"
    using walk_between_nonempty_path[of _ _ "[u,v]"] by auto
  hence "u = v" "{u,v} \<in> E"
    by (auto elim: path.cases)
  thus ?case 
    using assms by auto
qed (auto elim: is_cycleE)

lemma cycle_edges_subset: 
  assumes "is_cycle E C" 
  shows "set (edges_of_path C) \<subseteq> E"
proof -
  obtain v where "walk_betw E v C v"
    using assms by (auto elim: is_cycleE)
  thus ?thesis
    by (rule path_edges_subset[OF walk_between_nonempty_path(1)])
qed

lemma cycle_edge_length:
  assumes "graph_invar E" "is_cycle E C"
  shows "length (edges_of_path C) > 1"
  using assms edges_of_path_length[of C] cycle_length[of E C] by auto

lemma cycle_edges_hd_last_neq:
  assumes "graph_invar E" "is_cycle E C"
  shows "hd (edges_of_path C) \<noteq> last (edges_of_path C)" (is "?e\<^sub>1 \<noteq> ?e\<^sub>2")
  using assms cycle_edge_length distinct_hd_last_neq[OF is_simpleE] by (auto elim: is_cycleE)

lemma cycle_path_split:
  assumes "graph_invar E" "is_cycle E C" "v \<in> set C" "v \<noteq> hd C"
  obtains u P\<^sub>1 P\<^sub>2 where "C = u#P\<^sub>1 @ v#P\<^sub>2 @ [u]"
proof -
  obtain u where "walk_betw E u C u"
    using assms by (auto elim: is_cycleE)
  moreover hence "u = hd C"
    by (auto simp: walk_between_nonempty_path)
  moreover hence "u \<noteq> v"
    using assms by auto
  moreover obtain P\<^sub>1 P\<^sub>2 where "C = u#P\<^sub>1 @ v#P\<^sub>2 @ [u]"
    using assms calculation walk_path_split[of E u C v] by auto
  ultimately show ?thesis
    using that by blast
qed

lemma cycle_rotate:
  assumes "graph_invar E" "is_cycle E C" "v \<in> set C"
  obtains C' where "is_cycle E C'" "walk_betw E v C' v" 
    "set (edges_of_path C) = set (edges_of_path C')"
proof cases
  assume "v = hd C"
  hence "is_cycle E C" "walk_betw E v C v"
    using assms by (auto elim: is_cycleE_hd)
  thus ?thesis 
    using that by auto
next
  assume "v \<noteq> hd C"
  then obtain u P\<^sub>1 P\<^sub>2 where [simp]: "C = u#P\<^sub>1 @ v#P\<^sub>2 @ [u]"
    using assms by (elim cycle_path_split) auto
  let ?C'="v#P\<^sub>2 @ u#P\<^sub>1 @ [v]"
  have "path E C" "is_simple C" "length (edges_of_path C) > 0"
    using assms by (auto elim: is_cycleE walk_between_nonempty_path)
  moreover hence "walk_betw E v ?C' v"
    using path_rotate by (fastforce intro: nonempty_path_walk_between)+
  moreover have "is_simple ?C'" "length (edges_of_path ?C') > 0"
    using calculation is_simple_rotate[of u P\<^sub>1 v P\<^sub>2] length_edges_of_path_rotate[of u P\<^sub>1 v P\<^sub>2]
    by auto
  moreover have "is_cycle E ?C'"
    using calculation by (auto intro: is_cycleI)
  moreover have "set (edges_of_path C) = set (edges_of_path ?C')"
    using edges_of_path_rotate by fastforce
  ultimately show ?thesis using that by auto
qed (* TODO: might be able to simplify proof with \<open>Misc.walk_rotate\<close>. Need to show \<open>is_simple\<close>. *)

lemma cycle_edges_for_v:
  assumes "graph_invar E" "is_cycle E C" "v \<in> set C"
  obtains e\<^sub>1 e\<^sub>2 where "e\<^sub>1 \<noteq> e\<^sub>2" "e\<^sub>1 \<in> set (edges_of_path C)" "v \<in> e\<^sub>1" 
    "e\<^sub>2 \<in> set (edges_of_path C)" "v \<in> e\<^sub>2"
proof -
  obtain C' where "is_cycle E C'" "walk_betw E v C' v" 
    "set (edges_of_path C) = set (edges_of_path C')"
    using cycle_rotate[OF assms] by auto
  moreover hence "v = hd C'" "v = last C'" "length C' > 2" "edges_of_path C' \<noteq> []"
    using assms cycle_length walk_between_nonempty_path[of E v C' v] cycle_edge_length[of E C'] 
    by auto
  moreover obtain e\<^sub>1 e\<^sub>2 where "e\<^sub>1 = hd (edges_of_path C')" "e\<^sub>2 = last (edges_of_path C')"
    by auto
  moreover hence "e\<^sub>1 \<in> set (edges_of_path C')" "e\<^sub>2 \<in> set (edges_of_path C')"
    using calculation hd_in_set[of C'] last_in_set[of C'] by auto
  moreover hence "e\<^sub>1 \<in> set (edges_of_path C)" "e\<^sub>2 \<in> set (edges_of_path C)"
    using calculation by auto
  moreover have "v \<in> e\<^sub>1" "v \<in> e\<^sub>2"
    using calculation last_v_in_last_e[of C'] hd_v_in_hd_e[of C'] by auto
  moreover have "e\<^sub>1 \<noteq> e\<^sub>2"
    using assms calculation cycle_edges_hd_last_neq by auto
  ultimately show ?thesis
    using that by auto
qed

lemma cycle_degree:
  assumes "graph_invar E" "is_cycle E C" "v \<in> set C"
  shows "degree E v \<ge> 2"
proof -
  obtain e\<^sub>1 e\<^sub>2 where "e\<^sub>1 \<noteq> e\<^sub>2" "e\<^sub>1 \<in> set (edges_of_path C)" "v \<in> e\<^sub>1" 
    "e\<^sub>2 \<in> set (edges_of_path C)" "v \<in> e\<^sub>2"
    using cycle_edges_for_v[OF assms] by auto
  moreover have "set (edges_of_path C) \<subseteq> E"
    using assms cycle_edges_subset by auto
  moreover have "{e \<in> {e\<^sub>1,e\<^sub>2}. v \<in> e} = {e\<^sub>1,e\<^sub>2}" "{e\<^sub>1,e\<^sub>2} \<subseteq> {e \<in> E. v \<in> e}"
    using calculation by auto
  moreover have "finite {e\<^sub>1,e\<^sub>2}" "card {e\<^sub>1,e\<^sub>2} = 2"
    using assms calculation by auto
  moreover hence "card' {e\<^sub>1,e\<^sub>2} = 2"
    using card'_finite_nat[of "{e\<^sub>1,e\<^sub>2}"] by auto
  moreover hence "degree {e\<^sub>1,e\<^sub>2} v = 2"
    unfolding degree_def2 using calculation by auto
  ultimately show ?thesis
    using subset_edges_less_degree[of "{e\<^sub>1,e\<^sub>2}" E v] by auto
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
  obtains u v P P' where "is_simple P" "walk_betw E u P v" 
    "is_simple P'" "walk_betw E u P' v" "P \<noteq> P'"
proof -
  obtain C where "is_cycle E C"
    using assms by (auto elim: not_acyclicE)
  moreover then obtain v where "is_simple C" "walk_betw E v C v"
    by (auto elim: is_cycleE)
  moreover hence "is_simple (rev C)" "walk_betw E v (rev C) v"
    using walk_symmetric[of E v C v] simple_path_rev by auto
  moreover hence "C \<noteq> rev C"
    using assms calculation is_simple_rev_neq[OF _ cycle_length] by auto
  ultimately show thesis
    using that by auto
qed

context graph_abs
begin

lemma degree_edges_of_path_hd_leq_1:
  assumes "distinct P"
  shows "degree (set (edges_of_path P)) (hd P) \<le> 1" (is "degree ?E\<^sub>P (hd P) \<le> 1")
  using assms
proof (induction P rule: list012.induct) (* induction just for case distinction *)
  case (3 u v P)
  then show ?case 
    using degree_edges_of_path_hd by fastforce
qed auto

lemma non_acyclic_path_not_distinct:
  assumes "path E P" 
      and "\<not> is_acyclic (set (edges_of_path P))" (is "\<not> is_acyclic ?E\<^sub>P")
  shows "\<not> distinct P"
proof
  assume "distinct P"

  have "?E\<^sub>P \<subseteq> E"
    using assms path_edges_subset by auto
  hence graph_E\<^sub>P: "graph_invar ?E\<^sub>P"
    using graph finite_subset[OF Vs_subset[of ?E\<^sub>P E]] by auto
  moreover obtain C where cycle_C: "is_cycle ?E\<^sub>P C"
    using assms by (auto elim: not_acyclicE)
  ultimately have "length C > 2"
    using cycle_length by auto
  hence "Vs (set (edges_of_path C)) \<noteq> {}" (is "Vs ?E\<^sub>C \<noteq> {}")
    using vs_edges_path_eq[of C] by (auto simp: set_empty[of C])
  then obtain e where "e \<in> ?E\<^sub>C"
    by (auto elim: vs_member_elim)
  moreover then obtain u v where "e = {u,v}"
    by (auto elim: v_in_edge_in_path_inj)
  ultimately have "{u,v} \<in> ?E\<^sub>C"
    by auto
  moreover have "?E\<^sub>C \<subseteq> ?E\<^sub>P"
    by (metis cycle_C cycle_edges_subset)
  moreover have "{u,v} \<in> ?E\<^sub>P"
    using calculation by auto
  moreover have "u \<in> set P" "v \<in> set P"
    using calculation v_in_edge_in_path_gen[of \<open>{u,v}\<close>] by auto
  moreover have "u \<noteq> v"
    using calculation graph_E\<^sub>P by auto
  moreover have "2 \<le> card (set P)"
    using calculation card_mono[of "set P" "{u,v}"] by auto
  ultimately have "length P > 1"
    using card_length[of P] by auto

  consider "Vs ?E\<^sub>C = Vs ?E\<^sub>P" | "Vs ?E\<^sub>C \<subset> Vs ?E\<^sub>P"
    using \<open>?E\<^sub>C \<subseteq> ?E\<^sub>P\<close>Vs_subset[of ?E\<^sub>C ?E\<^sub>P] by auto
  thus "False"
  proof cases
    assume "Vs ?E\<^sub>C = Vs ?E\<^sub>P"
    moreover have "hd P \<in> hd (edges_of_path P)"
      using \<open>length P > 1\<close> hd_v_in_hd_e[of P] by auto
    moreover have "hd (edges_of_path P) \<in> ?E\<^sub>P"
      using \<open>length P > 1\<close> edges_of_path_length[of P] by (intro hd_in_set) auto
    moreover have "hd P \<in> Vs ?E\<^sub>P"
      using calculation by (auto intro: vs_member_intro)
    ultimately have "hd P \<in> Vs ?E\<^sub>C"
      by auto
    hence "hd P \<in> set C"
      using v_in_edge_in_path_gen by (fastforce elim: vs_member_elim)

    have "degree ?E\<^sub>P (hd P) \<le> 1"
      using \<open>distinct P\<close> degree_edges_of_path_hd_leq_1[of P] by auto
    moreover have "degree ?E\<^sub>P (hd P) \<ge> 2"
      using \<open>hd P \<in> set C\<close> cycle_degree[OF graph_E\<^sub>P cycle_C] by auto
    ultimately have  "enat 2 \<le> enat 1"
      by (metis numeral_eq_enat one_enat_def dual_order.trans)
    thus ?thesis
      using enat_ord_simps by auto
  next
    assume "Vs ?E\<^sub>C \<subset> Vs ?E\<^sub>P"
    moreover have "is_connected ?E\<^sub>P"
      using assms path_connected by auto
    ultimately obtain u v where "{u,v} \<in> ?E\<^sub>P" "u \<in> Vs ?E\<^sub>C" "v \<in> Vs ?E\<^sub>P - Vs ?E\<^sub>C"
      using \<open>Vs ?E\<^sub>C \<noteq> {}\<close> \<open>?E\<^sub>C \<subseteq> ?E\<^sub>P\<close> connected_bridge[of ?E\<^sub>P ?E\<^sub>C] by auto
    moreover hence "u \<in> set C" "v \<notin> Vs ?E\<^sub>C" "u \<in> set P"
      using vs_member_elim[of _ ?E\<^sub>C] v_in_edge_in_path_gen[of _ C] 
            v_in_edge_in_path_gen[of "{u,v}" P u] by auto
    moreover hence "{u,v} \<notin> ?E\<^sub>C"
      using v_in_edge_in_path[of v u C] insert_commute by auto
    moreover then obtain e\<^sub>1 e\<^sub>2 where "e\<^sub>1 \<noteq> e\<^sub>2" "e\<^sub>1 \<in> ?E\<^sub>C" "u \<in> e\<^sub>1" "e\<^sub>2 \<in> ?E\<^sub>C" "u \<in> e\<^sub>2"
      using cycle_C calculation cycle_edges_for_v[OF \<open>graph_invar ?E\<^sub>P\<close>, of C u] by auto
    moreover hence "e\<^sub>1 \<in> ?E\<^sub>P" "e\<^sub>1 \<noteq> {u,v}" "e\<^sub>2 \<in> ?E\<^sub>P" "e\<^sub>2 \<noteq> {u,v}"
      using \<open>?E\<^sub>C \<subseteq> ?E\<^sub>P\<close> calculation by auto
    moreover hence "{{u,v},e\<^sub>1,e\<^sub>2} \<subseteq> ?E\<^sub>P" "card' {{u,v},e\<^sub>1,e\<^sub>2} = 3"
      using calculation by auto
    moreover have "degree {{u,v},e\<^sub>1,e\<^sub>2} u = 3"
      unfolding degree_def using calculation by auto
    ultimately have "degree ?E\<^sub>P u \<ge> 3"
      using subset_edges_less_degree[of "{{u,v},e\<^sub>1,e\<^sub>2}" ?E\<^sub>P u] by auto
    hence "enat 3 \<le> enat 2"
      using degree_edges_of_path_leq_2[OF \<open>distinct P\<close> \<open>length P > 1\<close> \<open>u \<in> set P\<close>]
      by (metis numeral_eq_enat dual_order.trans) (* TODO: clean up \<open>enat\<close> stuff *)
    thus ?thesis
      using enat_ord_simps by auto
  qed
qed

end

section \<open>Trees\<close>

definition "is_tree T \<equiv> is_connected T \<and> is_acyclic T"

lemma is_treeI: "is_connected T \<Longrightarrow> is_acyclic T \<Longrightarrow> is_tree T"
  unfolding is_tree_def by auto

lemma is_treeE: 
  assumes "is_tree T" 
  shows "is_connected T" "is_acyclic T"
  using assms[unfolded is_tree_def] by auto

section \<open>Spanning Trees\<close>

context graph_abs
begin

definition "is_st T \<equiv> T \<subseteq> E \<and> Vs E = Vs T \<and> is_tree T"

lemma is_stI: "T \<subseteq> E \<Longrightarrow> Vs E = Vs T \<Longrightarrow> is_tree T \<Longrightarrow> is_st T"
  unfolding is_st_def by auto

lemma is_stE:
  assumes "is_st T"
  shows "T \<subseteq> E" "Vs E = Vs T" "is_tree T"
  using assms[unfolded is_st_def] by auto

lemma st_is_graph:
  assumes "is_st T"
  shows "graph_invar T"
  using assms by (intro graph_subset[OF graph is_stE(1)])

end

context w_graph_abs
begin

abbreviation "cost_of_st T \<equiv> sum c T"

text \<open>Minimum Spanning Tree\<close>
definition "is_mst T \<equiv> is_st T \<and> (\<forall>T'. is_st T' \<longrightarrow> cost_of_st T \<le> cost_of_st T')"

lemma is_mstI:
  assumes "is_st T" "\<And>T'. is_st T' \<Longrightarrow> cost_of_st T \<le> cost_of_st T'"
  shows "is_mst T"
  using assms by (auto simp: is_mst_def)

lemma is_mstE:
  assumes "is_mst T"
  shows "is_st T" "\<And>T'. is_st T' \<Longrightarrow> cost_of_st T \<le> cost_of_st T'"
  using assms[unfolded is_mst_def] by auto

lemma is_mstE2:
  assumes "is_mst T"
  shows "T \<subseteq> E" "Vs E = Vs T" "is_tree T" "\<And>T'. is_st T' \<Longrightarrow> cost_of_st T \<le> cost_of_st T'"
  using assms is_mstE by (auto simp: is_stE)

lemma mst_eq_cost:
  assumes "is_mst T\<^sub>1" "is_mst T\<^sub>2"
  shows "cost_of_st T\<^sub>1 = cost_of_st T\<^sub>2"
  using assms[unfolded is_mst_def] by fastforce

end

locale mst = 
  w_graph_abs E c for E c +
  fixes comp_mst
  assumes mst: "is_connected E \<Longrightarrow> is_mst (comp_mst c E)"
begin

end

end