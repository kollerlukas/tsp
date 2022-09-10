(* Author: Lukas Koller *)
theory DoubleTree
  imports Main MST TSP Eulerian
begin

section \<open>\textsc{DoubleTree} Approximation Algorithm for mTSP\<close>
                                                
locale double_tree_algo = 
  metric_graph_abs E c + 
  mst E c comp_mst + 
  eulerian comp_et for E :: "'a set set" and c comp_mst and comp_et :: "'a mgraph \<Rightarrow> 'a list"
begin

text \<open>Hamiltonian Cycle of Eulerian Tour\<close>
fun hc_of_et :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "hc_of_et [] H = H"
| "hc_of_et [v] H = v#H"
| "hc_of_et (v#P) H = (if v \<in> List.set H then hc_of_et P H else hc_of_et P (v#H))"

lemma hc_of_et_set_eq: "set P \<union> set H = set (hc_of_et P H)"
  by (induction P H rule: hc_of_et.induct) auto

lemma hc_of_et_non_nil: "P \<noteq> [] \<Longrightarrow> (hc_of_et P H) \<noteq> []"
  by (induction P H rule: hc_of_et.induct) auto

lemma hc_of_et_vs:
  assumes "is_et X P" 
  shows "set (hc_of_et P []) = mVs X"
proof
  show "set (hc_of_et P []) \<subseteq> mVs X"
    using assms[unfolded is_et_def mpath_def2] mem_path_Vs[of "set_mset X" P] 
          hc_of_et_set_eq[of P "[]"] by (auto simp: mVs_def)
next
  show "mVs X \<subseteq> set (hc_of_et P [])"
    unfolding mVs_def
  proof
    fix v
    assume "v \<in> Vs (set_mset X)"
    then obtain e where "e \<in># X" "v \<in> e"
      by (auto elim: vs_member_elim)
    moreover hence "e \<in># mset (edges_of_path P)"
      using assms[unfolded is_et_def] by auto
    ultimately show "v \<in> set (hc_of_et P [])"
      using v_in_edge_in_path_gen[of e P v] hc_of_et_set_eq[of P] by auto
  qed
qed

lemma hc_of_et_path:
  assumes "is_et X P" "set_mset X \<subseteq> E"
  shows "path E (hc_of_et P [])" (is "path E ?H")
proof -
  have "set P \<subseteq> Vs E"
    using assms[unfolded is_et_def mpath_def2] Vs_subset[of "set_mset X" E] 
    by (auto simp: mem_path_Vs subsetI)
  hence "set ?H \<subseteq> Vs E"
    using hc_of_et_set_eq[of P "[]"] by auto
  then show ?thesis
    unfolding mpath_def using path_complete_graph[of ?H] by auto
qed

lemma hc_of_et_distinct: "distinct H \<Longrightarrow> distinct (tl (hc_of_et P H))"
  by (induction P H rule: hc_of_et.induct) (auto simp: Let_def distinct_tl)

lemma hc_of_et_last_aux: "H \<noteq> [] \<Longrightarrow> last H = last (hc_of_et P H)"
  by (induction P H rule: hc_of_et.induct) auto

lemma hc_of_et_last: "P \<noteq> [] \<Longrightarrow> hd P = last (hc_of_et P [])"
  using hc_of_et_last_aux by (induction P rule: list012.induct) auto

lemma hc_of_et_hd: "P \<noteq> [] \<Longrightarrow> last P = hd (hc_of_et P H)"
  by (induction P H rule: hc_of_et.induct) auto

lemma hc_of_et_cycle:
  assumes "P \<noteq> []" "is_et X P"
  shows "hd (hc_of_et P []) = last (hc_of_et P [])" (is "hd ?H = last ?H")
proof -
  have "hd ?H = last P"
    using assms hc_of_et_hd[of P "[]"] by auto
  also have "... = hd P"
    using assms[unfolded is_et_def] by auto
  also have "... = last ?H"
    using assms hc_of_et_last by auto
  finally show ?thesis .
qed

lemma hc_of_et_walk_betw:
  assumes "P \<noteq> []" "is_et X P" "set_mset X \<subseteq> E"
  obtains v where "walk_betw E v (hc_of_et P []) v"
proof
  let ?H="hc_of_et P []"
  let ?v="hd ?H"
  show "walk_betw E ?v ?H ?v"
  proof (rule nonempty_path_walk_between)
    show "path E ?H" "?H \<noteq> []" "hd ?H = ?v" "last ?H = ?v"
      using assms hc_of_et_path[of X P] hc_of_et_non_nil[of P "[]"] hc_of_et_cycle[of P X] by auto
  qed
qed

lemma hc_of_et_correct: 
  assumes "is_et X P" "mVs X = Vs E" "set_mset X \<subseteq> E"
  shows "is_hc (hc_of_et P [])"
proof (cases "P = []")
  case True
  hence "X = {#}"
    using assms et_nil[of X] by auto
  hence "Vs E = {}"
    using assms by (auto simp: mVs_def Vs_def)
  hence "E = {}"
    using vs_member[of _ E] graph by fastforce
  then show ?thesis 
    using \<open>P = []\<close> hc_nil_iff by auto
next
  case False
  then obtain v where "hc_of_et P [] \<noteq> []" "walk_betw E v (hc_of_et P []) v"
    using assms hc_of_et_non_nil by (auto elim: hc_of_et_walk_betw[of P X])
  then show ?thesis
    apply (rule is_hcI_non_nil)
    using assms hc_of_et_walk_betw[of P X] hc_of_et_vs[of X P] hc_of_et_distinct[of "[]" P] 
          hc_of_et_cycle[of P X] by auto
qed

definition double_tree where
  "double_tree = (
    let T = comp_mst c E;
        T\<^sub>2\<^sub>x = mset_set T + mset_set T;
        P = comp_et T\<^sub>2\<^sub>x in
        hc_of_et P [])"

text \<open>Feasibility of \textsc{DoubleTree}\<close>

lemma T2x_eulerian:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T"
  shows "is_eulerian T\<^sub>2\<^sub>x"
  using assms[unfolded is_mst_def is_st_def] finite_E finite_subset[of T E]
        double_graph_eulerian[of T T\<^sub>2\<^sub>x] by auto

lemma T2x_vs:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T"
  shows "mVs T\<^sub>2\<^sub>x = Vs E"
  using assms[unfolded is_mst_def is_st_def] finite_subset[OF _ finite_E] by (auto simp: mVs_def) 

lemma T2x_edges:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T"
  shows "set_mset T\<^sub>2\<^sub>x \<subseteq> E"
  using assms[unfolded is_mst_def is_st_def] finite_subset[OF _ finite_E] by auto 

lemmas dt_correctness = T2x_eulerian[OF mst] T2x_vs[OF mst] T2x_edges[OF mst]

lemma "is_hc (double_tree)" (is "is_hc ?H")
  apply (simp only: double_tree_def Let_def)
  apply (rule hc_of_et_correct, rule eulerian)
  using dt_correctness by auto

text \<open>Approximation of \textsc{DoubleTree}\<close>

lemma cost_of_path_hc_of_et:
  assumes "set P \<union> set H \<subseteq> Vs E"
  shows "cost_of_path (hc_of_et P H) \<le> cost_of_path (rev P @ H)"
  using assms
proof (induction P H rule: hc_of_et.induct)
  case (3 u v P H)
  then show ?case 
    using cost_of_path_app_tri_ineq[of "rev (v#P)" H u] by auto
qed auto

lemma hc_of_et_reduces_cost: "set P \<subseteq> Vs E \<Longrightarrow> cost_of_path (hc_of_et P []) \<le> cost_of_path P"
  using cost_of_path_hc_of_et[of P "[]"] cost_of_path_rev[of P] by auto

lemma cost_of_et:
  assumes "is_et T P" 
  shows "cost_of_path P = (\<Sum>e\<in>#T. c e)"
  using assms cost_of_path_sum[of P] et_edges[of T P] by auto

lemma et_not_single_v:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T" "is_et T\<^sub>2\<^sub>x P"
  shows "length P \<noteq> 1"
  using assms
proof (induction P rule: list012.induct) (* induction just for case distinction *)
  case (2 v)
  hence "T\<^sub>2\<^sub>x = {#}" "mpath T\<^sub>2\<^sub>x [v]"
    unfolding is_et_def by auto
  hence "mVs T\<^sub>2\<^sub>x = {}" "v \<in> mVs T\<^sub>2\<^sub>x"
    unfolding mpath_def2 by (auto simp: mVs_def Vs_def)
  then show ?case by auto
qed auto

lemma hc_of_et_cost_le_dt:
  assumes "is_mst T" "T\<^sub>2\<^sub>x = mset_set T + mset_set T" "is_et T\<^sub>2\<^sub>x P"
  shows "cost_of_path (hc_of_et P []) \<le> 2 * cost_of_st T"
proof -
  have "set P \<subseteq> Vs E"
    using assms et_vertices[of T\<^sub>2\<^sub>x P, OF _ et_not_single_v] T2x_vs[of T T\<^sub>2\<^sub>x] by auto
  hence "cost_of_path (hc_of_et P []) \<le> cost_of_path P"
    using hc_of_et_reduces_cost[of P] by auto
  also have "... = (\<Sum>e\<in>#T\<^sub>2\<^sub>x. c e)"
    using assms cost_of_et by auto
  also have "... = (\<Sum>e\<in>T. c e) + (\<Sum>e\<in>T. c e)"
    using assms by (simp add: sum_unfold_sum_mset)
  also have "... = 2 * (\<Sum>e\<in>T. c e)"
    using mult_2 by auto
  also have "... = 2 * cost_of_st T"
    by (auto simp: cost_of_st_def)
  finally show ?thesis .
qed

lemma dt_mst_approx:
  assumes "is_mst T"
  shows "cost_of_path double_tree \<le> 2 * cost_of_st T"
proof -
  let ?T="comp_mst c E"
  let ?T\<^sub>2\<^sub>x="mset_set ?T + mset_set ?T"
  let ?P="comp_et ?T\<^sub>2\<^sub>x"
  
  have "cost_of_path double_tree = cost_of_path (hc_of_et ?P [])"
    unfolding double_tree_def by (auto simp: Let_def)
  also have "... \<le> 2 * cost_of_st ?T"
    using mst hc_of_et_cost_le_dt[of ?T ?T\<^sub>2\<^sub>x ?P] eulerian[OF T2x_eulerian, of ?T ?T\<^sub>2\<^sub>x] by auto
  also have "... = 2 * cost_of_st T"
    using assms mst_eq_cost[OF mst, of T] by auto
  finally show ?thesis .
qed

lemma set_tl_subset: "set (tl A) \<subseteq> set A"
  by (induction A) auto

lemma drop_tl: "i > 0 \<Longrightarrow> drop i xs = drop (i - 1) (tl xs)"
  using drop_Suc[of "i-1"] Suc_diff_1[of i] by auto

lemma edges_of_path_append_subset2: "set (edges_of_path p) \<subseteq> set (edges_of_path (p @ p'))"
  by (induction p arbitrary: p' rule: edges_of_path.induct) auto

lemma edges_of_path_drop_take_subset: 
  "set (edges_of_path (drop i\<^sub>u (take i\<^sub>v H))) \<subseteq> set (edges_of_path H)"
proof -
  have "set (edges_of_path (drop i\<^sub>u (take i\<^sub>v H))) \<subseteq> set (edges_of_path (take i\<^sub>v H))"
    using edges_of_path_append_subset append_take_drop_id[of i\<^sub>u "take i\<^sub>v H"] by metis
  also have "... \<subseteq> set (edges_of_path H)"
    using edges_of_path_append_subset2[of "take i\<^sub>v H"] append_take_drop_id[of i\<^sub>v H] by metis
  finally show ?thesis .
qed

lemma hc_connected_component:
  assumes "is_hc H" "u = (tl H) ! i\<^sub>u" "i\<^sub>u < length (tl H)" "v = (tl H) ! i\<^sub>v" "i\<^sub>v < length (tl H)" 
          "i\<^sub>u < i\<^sub>v" 
  shows "u \<in> connected_component (set (edges_of_path (tl H))) v" 
    (is "u \<in> connected_component ?E' v")
proof -
  let ?P="drop (i\<^sub>u + 1) (take (i\<^sub>v + 2) H)"
  let ?P'="drop i\<^sub>u (take (i\<^sub>v + 1) (tl H))"
  have "?P = ?P'"
    using drop_tl[of "i\<^sub>u + 1" "take (i\<^sub>v + 2) H"] tl_take[of "i\<^sub>v + 2" H] by auto

  have "u = H ! (i\<^sub>u + 1)" "v = H ! (i\<^sub>v + 1)"
    using assms nth_tl[of _ H] by auto
  hence "walk_betw E u ?P v" "length ?P > 1"
    using assms hc_walk_betw1[of H "i\<^sub>u + 1" "i\<^sub>v + 1"] by auto
  hence "walk_betw (set (edges_of_path ?P')) u ?P' v"
    using assms \<open>?P = ?P'\<close> walk_on_edges_of_path[of E u ?P v] by auto
  hence "walk_betw ?E' u ?P' v"
    using edges_of_path_drop_take_subset[of i\<^sub>u "i\<^sub>v + 1" "tl H"] 
            walk_subset[of "set (edges_of_path ?P')" ?E'] by auto
  then show "u \<in> connected_component ?E' v"
    using walk_symmetric[of ?E' u _ v] by auto
qed

lemma tl_edges_of_path: "tl (edges_of_path P) = edges_of_path (tl P)"
  by (induction P rule: edges_of_path.induct) auto

lemma tl_hc_connected:
  assumes "is_hc H"
  shows "is_connected (set (tl (edges_of_path H)))" (is "is_connected ?E'")
proof (rule is_connectedI)
  fix u v
  assume "u \<in> Vs ?E'" "v \<in> Vs ?E'"
  hence "u \<in> Vs (set (edges_of_path (tl H)))" "v \<in> Vs (set (edges_of_path (tl H)))"
    by (auto simp: tl_edges_of_path)
  hence "u \<in> set (tl H)" "v \<in> set (tl H)"
    using assms edges_of_path_Vs[of "tl H"] by auto
  then obtain i\<^sub>u i\<^sub>v where i\<^sub>u_i\<^sub>v_simps:"u = (tl H) ! i\<^sub>u" "i\<^sub>u < length (tl H)" 
    "v = (tl H) ! i\<^sub>v" "i\<^sub>v < length (tl H)"
    using set_conv_nth[of "tl H"] by auto

  have "i\<^sub>u = i\<^sub>v \<or> i\<^sub>u < i\<^sub>v \<or> i\<^sub>v < i\<^sub>u"
    by auto
  then show "u \<in> connected_component ?E' v"
  proof (elim disjE)
    assume "i\<^sub>u = i\<^sub>v"
    hence "u = v"
      using i\<^sub>u_i\<^sub>v_simps by auto
    then show "u \<in> connected_component ?E' v"
      using in_own_connected_component by auto
  next
    assume "i\<^sub>u < i\<^sub>v"
    then show "u \<in> connected_component ?E' v"
      using assms i\<^sub>u_i\<^sub>v_simps hc_connected_component by (auto simp: tl_edges_of_path)
  next
    assume "i\<^sub>v < i\<^sub>u"
    hence "v \<in> connected_component ?E' u"
      using assms i\<^sub>u_i\<^sub>v_simps hc_connected_component by (auto simp: tl_edges_of_path)
    then show "u \<in> connected_component ?E' v"
      using connected_components_member_sym[of v ?E' u] by auto
  qed
qed

lemma hc_degree_leq_2:
  assumes "is_hc H" "x \<in> set H"
  shows "degree (set (tl (edges_of_path H))) x \<le> 2"
  using assms i0_lb
proof (induction H rule: list0123.induct) (* induction just for case distinction *)
  case (4 u v w P)
  let ?H="u#v#w#P"
  have prems: "distinct (tl ?H)" "2 \<le> length (tl ?H)" 
    using 4 by (elim is_hc_nonnilE) auto
  have "x = hd (tl ?H) \<or> x = last (tl ?H) \<or> (x \<noteq> hd (tl ?H) \<and> x \<noteq> last (tl ?H))"
    by auto
  then show ?case
  proof (elim disjE)
    assume "x = hd (tl ?H)"
    hence "degree (set (edges_of_path (tl ?H))) x = 1"
      using prems degree_edges_of_path_hd[of "tl ?H"] by auto
    also have "... \<le> 2"
      using one_le_numeral by blast
    finally show ?case by (auto simp: tl_edges_of_path)
  next
    assume "x = last (tl ?H)"
    hence "degree (set (edges_of_path (tl ?H))) x = 1"
      using prems degree_edges_of_path_last[of "tl ?H"] by auto
    also have "... \<le> 2"
      using one_le_numeral by blast
    finally show ?case by (auto simp: tl_edges_of_path)
  next
    have "x \<in> set (tl ?H)"
      using "4.prems" is_hc_nonnilE[of ?H] hc_vs_set[of ?H] by blast
    assume "x \<noteq> hd (tl ?H) \<and> x \<noteq> last (tl ?H)"
    then show ?case
      using "4.prems" prems \<open>x \<in> set (tl ?H)\<close> degree_edges_of_path_ge_2[of "tl ?H" x] by auto
  qed
qed auto

lemma walk_split:
  assumes "walk_betw E u P v" "u \<in> E\<^sub>1" "v \<in> E\<^sub>2" "set P \<subseteq> E\<^sub>1 \<union> E\<^sub>2"
  obtains x y where "{x,y} \<in> set (edges_of_path P)" "x \<in> E\<^sub>1" "y \<in> E\<^sub>2"
  sorry

lemma connected_bridge:
  assumes "is_connected E\<^sub>2" "Vs E\<^sub>1 \<noteq> {}" "E\<^sub>1 \<subset> E\<^sub>2"
  obtains u v where "{u,v} \<in> E\<^sub>2" "u \<in> Vs E\<^sub>1" "v \<in> Vs E\<^sub>2 - Vs E\<^sub>1"
proof -
  have "Vs E\<^sub>1 \<subset> Vs E\<^sub>1"
    sorry
  moreover hence "Vs E\<^sub>2 - Vs E\<^sub>1 \<noteq> {}"
    using assms by auto
  moreover then obtain u v where "u \<in> Vs E\<^sub>1" "v \<in> Vs E\<^sub>2 - Vs E\<^sub>1"
    using assms by auto
  moreover hence "u \<in> Vs E\<^sub>2" "v \<in> Vs E\<^sub>2" "u \<noteq> v"
    using calculation by auto
  moreover then obtain P where "walk_betw E\<^sub>2 u P v"
    using assms by (auto elim: is_connectedE2)
  ultimately show ?thesis
    using walk_split by auto
qed

lemma
  assumes "\<not> is_acyclic (set (edges_of_path P))" (is "\<not> is_acyclic ?E\<^sub>P")
  shows "\<not> distinct P"
proof -
  obtain C where "is_cycle ?E\<^sub>P C"
    using assms by (auto elim: not_acyclicE)
  let ?E\<^sub>C="set (edges_of_path C)"
  have "is_connected ?E\<^sub>P"
    sorry
  then obtain u v where "{u,v} \<in> ?E\<^sub>P" "u \<in> Vs ?E\<^sub>C" "v \<in> Vs ?E\<^sub>P - Vs ?E\<^sub>C"
    using connected_bridge sorry

  obtain C' where "is_cycle ?E\<^sub>P C'" "walk_betw ?E\<^sub>P u C' u"
    using cycle_rotate sorry

  have "degree ?E\<^sub>P u \<ge> 3"
    sorry

  show ?thesis
    sorry
qed


lemma tl_hc_acyclic:
  assumes "is_hc H"
  shows "is_acyclic (set (tl (edges_of_path H)))" (is "is_acyclic ?E'")
proof (rule ccontr)
  assume "\<not> is_acyclic ?E'"
  moreover hence "graph_invar ?E'"
    sorry
  ultimately obtain u v P P' where "simple_path P" "walk_betw ?E' u P v" 
    "simple_path P'" "walk_betw ?E' u P' v" "P \<noteq> P'"
    by (elim not_acyclicE2) auto

  
  show "False"
    sorry
qed

lemma edges_of_path_tl: "edges_of_path (tl P) = tl (edges_of_path P)"
  by (induction P rule: edges_of_path.induct) auto

lemma tl_hc_Vs:
  assumes "is_hc H"
  shows "Vs E = Vs (set (tl (edges_of_path H)))" (is "Vs E = Vs ?E'")
proof -
  have "Vs E = set (tl H)"
    using assms by (auto simp: is_hcE)
  also have "... = Vs (set (edges_of_path (tl H)))"
    apply (cases "H = []")
    using vs_member[of _ "{}"] apply fastforce
    using hc_non_nil_length_gr2[of H, OF assms] vs_edges_path_eq[of "tl H"] apply auto
    done
  also have "... = Vs ?E'"
    by (auto simp: edges_of_path_tl[of H])
  finally show ?thesis .
qed

lemma tl_hc_tree:
  assumes "is_hc H"
  shows "is_tree (set (tl (edges_of_path H)))"
  using tl_hc_connected[OF assms] tl_hc_acyclic[OF assms] by (auto intro: is_treeI)

lemma tl_hc_st:
  assumes "is_hc H"
  shows "is_st (set (tl (edges_of_path H)))" (is "is_st ?E'")
  using assms hc_edges_subset set_tl_subset[of "edges_of_path H"] tl_hc_Vs tl_hc_tree 
  by (intro is_stI) auto

lemma mst_mtsp_approx:
  assumes "is_mst T" "is_mtsp OPT"
  shows "cost_of_st T \<le> cost_of_path OPT"
  using assms
proof (cases OPT)
  case Nil
  hence "E = {}"
    using assms hc_nil_iff by (auto simp: is_mtspE is_tspE)
  hence "T = {}"
    using assms is_mstE is_stE by auto
  hence "cost_of_st T = 0"
    unfolding cost_of_st_def by auto
  then show ?thesis
    using cost_of_path_pos by auto
next
  case (Cons v OPT')
  let ?E'="edges_of_path OPT"
  let ?e="hd (edges_of_path OPT)"
  have "is_st (set (tl ?E'))"
    using assms tl_hc_st[of OPT] by (auto simp: is_mtspE is_tspE)
  hence "cost_of_st T \<le> cost_of_st (set (tl ?E'))"
    using assms by (auto elim: is_mstE)
  also have "... = (\<Sum>e\<in>set (tl ?E'). c e)"
    unfolding cost_of_st_def by auto
  also have "... \<le> (\<Sum>e\<in>set ?E'. c e)"
    using costs_ge_0 sum_mono2[of "set ?E'" "set (tl ?E')" c] by (auto simp: set_tl_subset)
  also have "... \<le> cost_of_path OPT"
    using cost_of_path_leq_sum[of OPT] by auto
  finally show ?thesis .
qed

lemma dt_approx:
  assumes "is_mtsp OPT"
  shows "cost_of_path double_tree \<le> 2 * cost_of_path OPT"
proof -
  have "cost_of_path double_tree \<le> 2 * cost_of_st (comp_mst c E)"
    using dt_mst_approx[OF mst] .
  also have "... \<le> 2 * cost_of_path OPT"
    using mst_mtsp_approx[OF mst assms] by (auto simp: mult_2_mono)
  finally show ?thesis .
qed

end

interpretation double_tree_algo 
  sorry



end