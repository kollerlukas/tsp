(* Author: Lukas Koller *)
theory ChristofidesSerdyukov
  imports Main MST TSP Eulerian MinWeightMatching DoubleTree
begin

section \<open>\textsc{Christofides-Serdyukov} Approximation Algorithm for \textsc{mTSP}\<close>

locale christofides_serdyukov_algo = 
  metric_graph_abs E c + 
  mst E c comp_mst + 
  eulerian comp_et +
  min_weight_matching E c comp_match 
  for E :: "'a set set" and c comp_mst and comp_et :: "'a mgraph \<Rightarrow> 'a list" and comp_match
begin

definition christofides_serdyukov where
  "christofides_serdyukov = (
    let T = comp_mst c E;
        W = {v \<in> Vs T. \<not> even' (degree T v)};
        M = comp_match ({e \<in> E. e \<subseteq> W}) c;
        J = mset_set T + mset_set M;
        P = comp_et J in
        comp_hc_of_et P [])"

end

subsection \<open>Feasibility of \textsc{Christofides-Serdyukov}\<close>

locale christofides_serdyukov_aux = 
  christofides_serdyukov_algo E c comp_mst comp_et comp_match
  for E :: "'a set set" and c comp_mst and comp_et :: "'a mgraph \<Rightarrow> 'a list" and comp_match +
  fixes T W E\<^sub>W M J
  defines "T \<equiv> comp_mst c E"
      and "W \<equiv> {v \<in> Vs T. \<not> even' (degree T v)}"
      and "E\<^sub>W \<equiv> {e \<in> E. e \<subseteq> W}"
      and "M \<equiv> comp_match E\<^sub>W c"
      and "J \<equiv> mset_set T + mset_set M"
begin

lemma subset_T: "T \<subseteq> E"
  unfolding T_def using is_connected mst by (auto simp: is_mstE2)

lemma Vs_T: "Vs T = Vs E"
  unfolding T_def using is_connected mst by (auto simp: is_mstE2)

lemma graph_T: "graph_invar T"
  using graph subset_T finite_subset[OF Vs_subset] by blast

lemma finite_T: "finite T"
  using finite_E subset_T finite_subset by auto

lemma subset_W: "W \<subseteq> Vs E"
  unfolding W_def using Vs_subset[OF subset_T] by auto

lemma subset_E\<^sub>W: "E\<^sub>W \<subseteq> E"
  unfolding E\<^sub>W_def by auto

lemma finite_E\<^sub>W: "finite E\<^sub>W"
  using subset_E\<^sub>W finite_E finite_subset by auto

lemma finite_Vs_E\<^sub>W: "finite (Vs E\<^sub>W)"
  using graph subset_E\<^sub>W finite_subset[OF Vs_subset] by auto

lemma even_card_W: "even (card W)"
  unfolding W_def
  using graph_abs.even_num_of_odd_degree_vertices[unfolded graph_abs_def, OF graph_T] .

lemma W_eq_Vs_E\<^sub>W: "W = Vs E\<^sub>W"
  unfolding E\<^sub>W_def using graph complete even_card_W restr_graph_Vs[OF subset_W] by auto

lemma even_card_Vs_E\<^sub>W: "even (card (Vs E\<^sub>W))"
  using even_card_W by (auto simp: W_eq_Vs_E\<^sub>W)

lemma complete_E\<^sub>W: "is_complete E\<^sub>W"
  unfolding E\<^sub>W_def using restr_graph_compl[OF subset_W] by auto

lemma perf_match_exists: obtains M' where "is_perf_match E\<^sub>W M'"
  unfolding E\<^sub>W_def using restr_perf_match_exists[OF subset_W even_card_Vs_E\<^sub>W[unfolded E\<^sub>W_def]] 
  by auto

lemma min_match_M: "is_min_match E\<^sub>W c M"
  unfolding M_def using match[OF perf_match_exists] by auto

lemma subset_M: "M \<subseteq> E"
  using min_match_M is_min_matchE2[of E\<^sub>W c M] subset_E\<^sub>W by (auto simp: M_def)

lemma W_eq_Vs_M: "W = Vs M"
  using is_min_matchE2[OF min_match_M] by (auto simp: W_eq_Vs_E\<^sub>W)

lemma Vs_M_subset: "Vs M \<subseteq> Vs E"
  using W_eq_Vs_M subset_W by blast

lemma finite_M: "finite M"
  using finite_E subset_M finite_subset by auto

lemma match_M: "matching M"
  using min_match_M by (auto simp: is_min_matchE2)

lemma Vs_J: "mVs J = Vs E"
proof -
  have "mVs J = mVs (mset_set T) \<union> mVs (mset_set M)"
    unfolding J_def by (auto simp: mVs_union)
  also have "... = Vs T \<union> Vs M"
    using finite_T finite_M by (auto simp: mVs_mset_set)
  also have "... = Vs E \<union> Vs M"
    using is_connected mst by (auto simp: T_def is_mstE2)
  also have "... = Vs E"
    using Vs_subset[OF subset_M] by (auto simp: sup_absorb1)
  finally show ?thesis .
qed

lemma eulerian_J: "is_eulerian J"
proof (rule is_eulerianI)
  fix v
  assume "v \<in> mVs J"
  hence "v \<in> Vs T"
    using Vs_J Vs_T by auto
  consider "v \<in> W" | "v \<notin> W"
    using mVs_union by auto
  thus "even' (mdegree J v)"
  proof cases
    assume "v \<in> W"
    moreover hence "\<not> even' (degree T v)"
      unfolding W_def by auto
    moreover have "degree T v \<noteq> \<infinity>"
      using finite_T by (auto simp: non_inf_degr)
    moreover have "degree M v = 1"
      using calculation W_eq_Vs_M degree_matching_in_M[OF match_M] by auto
    moreover hence "mdegree J v = degree T v + 1"
      unfolding J_def by (auto simp: mdegree_add mdegree_eq_degree)
    ultimately show "even' (mdegree J v)"
      using not_even_add1 by auto
  next
    assume "v \<notin> W"
    moreover hence "even' (degree T v)"
      unfolding W_def using \<open>v \<in> Vs T\<close> by auto
    moreover have "v \<notin> Vs M"
      using calculation W_eq_Vs_M by auto
    moreover hence "degree M v = 0"
      by (auto simp: degree_not_Vs)
    moreover hence "mdegree J v = degree T v"
      unfolding J_def by (auto simp: mdegree_add mdegree_eq_degree)
    ultimately show "even' (mdegree J v)"
      by auto
  qed
qed

lemma edges_J_subset: "set_mset J \<subseteq> E"
  unfolding J_def using subset_T subset_M by (simp add: finite_M finite_T)

lemmas christofides_serdyukov_correctness = eulerian_J Vs_J edges_J_subset

end

locale christofides_serdyukov_algo_feasibility =
  hc_of_et E c comp_mst comp_et +
  christofides_serdyukov_algo E c comp_mst comp_et comp_match + 
  christofides_serdyukov_aux E c comp_mst comp_et comp_match
  for E :: "'a set set" and c comp_mst and comp_et :: "'a mgraph \<Rightarrow> 'a list" and comp_match
begin

lemmas [simp] = J_def T_def W_def E\<^sub>W_def M_def

lemma cs_is_hc: "is_hc (christofides_serdyukov)"
  unfolding christofides_serdyukov_def Let_def
  apply (rule hc_of_et_correct, rule eulerian)
  using christofides_serdyukov_correctness by auto

end

subsection \<open>Approximation of \textsc{Christofides-Serdyukov}\<close>

locale christofides_serdyukov_algo_approx =
  hc_of_et E c comp_mst comp_et +
  christofides_serdyukov_algo E c comp_mst comp_et comp_match +
  christofides_serdyukov_aux E c comp_mst comp_et comp_match +
  mtsp_opt E c
  for E :: "'a set set" and c comp_mst and comp_et :: "'a mgraph \<Rightarrow> 'a list" and comp_match
begin

end

locale christofides_serdyukov_algo_approx_restr_E =
  christofides_serdyukov_algo_approx +
  restr_compl_graph_abs +
  assumes even_card_V: "even (card V)"
      and min_match_M: "is_min_match E\<^sub>V c M"
begin

lemma Vs_E\<^sub>V_eq_V: "Vs E\<^sub>V = V"
  using even_card_V by (intro Vs_E\<^sub>V_eq_V) auto

text \<open>Short-Cut a Hamiltonian cycle to a subgraph.\<close>
lemma short_cut_hc:
  assumes "u \<in> V" "walk_betw E u P u" "distinct (tl P)" "set (tl P) = Vs E" 
  obtains P\<^sub>V where "walk_betw E\<^sub>V u P\<^sub>V u"
    and "distinct (tl P\<^sub>V)" "set (tl P\<^sub>V) = Vs E\<^sub>V" 
    and "cost_of_path P\<^sub>V \<le> cost_of_path P"
proof -
  have "path E P" "P \<noteq> []" "hd P = u" "last P = u"
    using assms by (auto elim: walk_between_nonempty_path)
  moreover have "u \<in> Vs E\<^sub>V"
    using assms by (auto simp: Vs_E\<^sub>V_eq_V)
  moreover hence "path E\<^sub>V (short_cut E\<^sub>V P)" (is "path E\<^sub>V ?P\<^sub>V")
    using calculation even_card_V short_cut_path[of "hd P" "tl P"] by auto
  moreover have "?P\<^sub>V \<noteq> []"
    using calculation short_cut_nonnil[of _ "hd P" "tl P"] by auto
  moreover have "hd ?P\<^sub>V = u"
    using calculation short_cut_hd1 by fastforce
  moreover have "last ?P\<^sub>V = u"
    using calculation last_short_cut2 by fastforce
  moreover have "walk_betw E\<^sub>V u ?P\<^sub>V u"
    using calculation by (intro nonempty_path_walk_between) auto
  moreover have "distinct (tl ?P\<^sub>V)"
    using assms by (intro distinct_tl_short_cut)
  moreover have "Vs E\<^sub>V \<subseteq> set P"
    using assms Vs_subset[OF E\<^sub>V_subset] set_tl_subset by fastforce
  moreover hence "Vs E\<^sub>V \<subseteq> set ?P\<^sub>V"
    using calculation short_cut_Vs_superset[of "hd P" "tl P"] by fastforce
  moreover have "set ?P\<^sub>V = Vs E\<^sub>V"
    using calculation set_short_cut[of "hd P" "tl P"] by auto
  moreover hence "length ?P\<^sub>V > 1"
    using assms even_card_V Vs_E\<^sub>V_eq_V by (intro list_eq_even_len_gr1) auto
  moreover have "set (tl ?P\<^sub>V) = Vs E\<^sub>V"
    apply (subst \<open>set ?P\<^sub>V = Vs E\<^sub>V\<close>[symmetric])
    apply (intro set_tl_eq_set)
    using calculation by auto
  moreover have "cost_of_path ?P\<^sub>V \<le> cost_of_path P"
    using calculation path_Vs_subset by (intro cost_of_path_short_cut_tri_ineq)
  ultimately show ?thesis
    using that by auto
qed

lemma short_cut_OPT:
  assumes "V \<noteq> {}" "OPT \<noteq> []"
  obtains u OPT\<^sub>V where "walk_betw E\<^sub>V u OPT\<^sub>V u" "u \<in> V"
    and "distinct (tl OPT\<^sub>V)" "set (tl OPT\<^sub>V) = Vs E\<^sub>V" 
    and "cost_of_path OPT\<^sub>V \<le> cost_of_path OPT"
proof -
  obtain u where OPT_prems: "walk_betw E u OPT u" "distinct (tl OPT)" "set (tl OPT) = Vs E"
    using assms(2) opt by (auto elim: is_tsp_nonnilE)
  thus ?thesis
  proof cases
    assume "u \<in> V"
    moreover then obtain OPT\<^sub>V where "walk_betw E\<^sub>V u OPT\<^sub>V u"
      and "distinct (tl OPT\<^sub>V)" "set (tl OPT\<^sub>V) = Vs E\<^sub>V" 
      and "cost_of_path OPT\<^sub>V \<le> cost_of_path OPT"
      using OPT_prems by (auto elim: short_cut_hc)
    ultimately show ?thesis
      by (intro that) auto
  next
    assume "u \<notin> V"
    moreover then obtain v where "v \<in> V"
      using assms by auto
    moreover hence "v \<in> set OPT"
      using V_subset OPT_prems set_tl_subset[of OPT] by auto
    moreover obtain P\<^sub>1 P\<^sub>2 where [simp]: "OPT = u#P\<^sub>1 @ v#P\<^sub>2 @ [u]"
      using calculation walk_path_split[OF graph OPT_prems(1)] by auto
    hence "path E (u#P\<^sub>1 @ v#P\<^sub>2 @ [u])"
      using OPT_prems by auto
    hence "path E (v#P\<^sub>2 @ u#P\<^sub>1 @ [v])" (is "path E ?OPT'")
      by (rule path_rotate)
    hence "walk_betw E v ?OPT' v"
      by (intro nonempty_path_walk_between) auto
    moreover have "distinct (tl ?OPT')"
      using OPT_prems \<open>OPT = u#P\<^sub>1 @ v#P\<^sub>2 @ [u]\<close> by auto
    moreover have "set (tl ?OPT') = Vs E"
      using OPT_prems by auto
    moreover obtain OPT\<^sub>V where "walk_betw E\<^sub>V v OPT\<^sub>V v"
      and "distinct (tl OPT\<^sub>V)" "set (tl OPT\<^sub>V) = Vs E\<^sub>V" 
      and "cost_of_path OPT\<^sub>V \<le> cost_of_path ?OPT'"
      using calculation by (auto elim: short_cut_hc)
    moreover hence "cost_of_path OPT\<^sub>V \<le> cost_of_path OPT"
      by (auto simp: cost_of_path_rotate)
    ultimately show ?thesis
      by (intro that) auto
  qed
qed

lemma OPT_nil:
  assumes "OPT = []"
  shows "V = {}"
proof -
  have "Vs E = {}"
    using assms opt is_tsp_nilE by auto
  thus ?thesis
    using Vs_subset[OF E\<^sub>V_subset] by (auto simp: Vs_E\<^sub>V_eq_V)
qed

lemma perf_matchings_leq_cost_OPT:
  assumes "V \<noteq> {}"
  obtains M\<^sub>1 M\<^sub>2 P where "is_perf_match E\<^sub>V (set M\<^sub>1)" "is_perf_match E\<^sub>V (set M\<^sub>2)" 
    and "mset M\<^sub>1 + mset M\<^sub>2 = mset (edges_of_path P)"
    and "cost_of_path P \<le> cost_of_path OPT"
proof -
  have "OPT \<noteq> []"
    using assms OPT_nil by auto
  then obtain u OPT\<^sub>V where "walk_betw E\<^sub>V u OPT\<^sub>V u" "u \<in> V" 
    and "distinct (tl OPT\<^sub>V)" "set (tl OPT\<^sub>V) = Vs E\<^sub>V" 
    and "cost_of_path OPT\<^sub>V \<le> cost_of_path OPT"
    using assms short_cut_OPT by auto
  moreover hence "path E\<^sub>V OPT\<^sub>V" "OPT\<^sub>V \<noteq> []" "hd OPT\<^sub>V = u" "last OPT\<^sub>V = u"
    by (auto elim: walk_between_nonempty_path)
  moreover hence "hd OPT\<^sub>V = last OPT\<^sub>V"
    by auto

  moreover have "matching (set (even_edges (tl OPT\<^sub>V)))"
    using calculation by (auto intro: matching_even_edges)
  moreover have "path E\<^sub>V (tl OPT\<^sub>V)"
    using calculation by (intro tl_path_is_path)
  moreover hence "set (even_edges (tl OPT\<^sub>V)) \<subseteq> E\<^sub>V"
    by (intro path_even_edges_subset)
  moreover have "even (length (tl OPT\<^sub>V))"
    using even_card_V calculation by (auto simp: Vs_E\<^sub>V_eq_V distinct_card)
  moreover hence "Vs (set (even_edges (tl OPT\<^sub>V))) = set (tl OPT\<^sub>V)"
    by (intro Vs_even_edges_eq)
  moreover have "is_perf_match E\<^sub>V (set (even_edges (tl OPT\<^sub>V)))" (is "is_perf_match E\<^sub>V (set ?M\<^sub>1)")
    using calculation by (auto simp: Vs_E\<^sub>V_eq_V intro: is_perf_matchI)
  
  moreover have "distinct (butlast OPT\<^sub>V)"
    using calculation hd_last_eq_distinct_set_iff(1)[of OPT\<^sub>V] by auto
  moreover hence "matching (set (even_edges (butlast OPT\<^sub>V)))"
    by (auto intro: matching_even_edges)
  moreover have "set (butlast OPT\<^sub>V) = Vs E\<^sub>V"
    using calculation hd_last_eq_distinct_set_iff(2)[of OPT\<^sub>V] by auto
  moreover have "path E\<^sub>V (butlast OPT\<^sub>V)"
    using calculation by (intro butlast_path_is_path)
  moreover hence "set (even_edges (butlast OPT\<^sub>V)) \<subseteq> E\<^sub>V"
    by (intro path_even_edges_subset)
  moreover have "even (length (butlast OPT\<^sub>V))"
    using calculation by (auto simp: distinct_card)
  moreover hence "Vs (set (even_edges (butlast OPT\<^sub>V))) = set (butlast OPT\<^sub>V)"
    by (intro Vs_even_edges_eq)
  moreover have "is_perf_match E\<^sub>V (set (even_edges (butlast OPT\<^sub>V)))" 
    (is "is_perf_match E\<^sub>V (set ?M\<^sub>2)")
    using calculation by (auto simp: Vs_E\<^sub>V_eq_V intro: is_perf_matchI)

  moreover have "odd (length OPT\<^sub>V)"
    using calculation by (auto simp: Vs_E\<^sub>V_eq_V)
  moreover hence edges_OPT\<^sub>V_union: "mset ?M\<^sub>1 + mset ?M\<^sub>2 = mset (edges_of_path OPT\<^sub>V)"
    by (intro even_edges_mset_union)

  ultimately show ?thesis
    by (intro that) auto
qed

lemma min_match_leq_half_OPT: "2 * cost_of_match M \<le> cost_of_path OPT"
proof cases
  assume "V = {}"
  hence "Vs E\<^sub>V = {}"
    by (auto simp: Vs_E\<^sub>V_eq_V)
  hence "Vs M = {}" "M \<subseteq> E\<^sub>V"
    using is_min_matchE2[OF min_match_M] by auto
  moreover hence "graph_invar M"
    by (intro graph_subset[OF E\<^sub>V_graph])
  ultimately have "M = {}"
    using Vs_empty_iff[of M] by auto 
  hence "2 * cost_of_match M = 0"
    by auto
  also have "... \<le> cost_of_path OPT"
    using cost_of_path_pos by auto
  finally show ?thesis .
next
  assume "V \<noteq> {}"
  (* obtain two matching \<open>M\<close> and \<open>M'\<close> s.t \<open>M + M' = edges_of_path P\<close> *)
  then obtain M\<^sub>1 M\<^sub>2 P where "is_perf_match E\<^sub>V (set M\<^sub>1)" "is_perf_match E\<^sub>V (set M\<^sub>2)" 
    and match_union: "mset M\<^sub>1 + mset M\<^sub>2 = mset (edges_of_path P)"
    and cost_P: "cost_of_path P \<le> cost_of_path OPT" 
    using perf_matchings_leq_cost_OPT by auto
  moreover hence "cost_of_match M \<le> cost_of_match (set M\<^sub>1)"
    and "cost_of_match M \<le> cost_of_match (set M\<^sub>2)"
    using min_match_M by (auto elim: is_min_matchE)
  ultimately have "2 * cost_of_match M \<le> cost_of_match (set M\<^sub>1) + cost_of_match (set M\<^sub>2)"
    by (auto simp: mult_2[symmetric] add_mono)
  also have "... \<le> \<Sum>\<^sub># (image_mset c (mset M\<^sub>1)) + \<Sum>\<^sub># (image_mset c (mset M\<^sub>2))"
    using cost_of_match_sum by (auto simp: add_mono)
  also have "... = \<Sum>\<^sub># (image_mset c (mset M\<^sub>1 + mset M\<^sub>2))"
    by auto
  also have "... \<le> cost_of_path OPT"
    using cost_P by (auto simp: match_union cost_of_path_sum)
  finally show ?thesis .
qed

end

context christofides_serdyukov_algo_approx
begin

lemmas defs[simp] = J_def T_def W_def E\<^sub>W_def M_def

lemma cost_cs_leq: "cost_of_path christofides_serdyukov \<le> cost_of_st T + cost_of_match M"
proof -
  have "mpath J (comp_et J)" and et_edges: "J = mset (edges_of_path (comp_et J))"
    using eulerian[OF eulerian_J] by (auto elim: is_etE) 
  hence comp_et_subset: "set (comp_et J) \<subseteq> Vs E"
    using mpath_Vs_subset[of J] Vs_J by auto

  have "cost_of_path christofides_serdyukov = cost_of_path (comp_hc_of_et (comp_et J) [])"
    unfolding christofides_serdyukov_def by (auto simp: Let_def)
  also have "... \<le> cost_of_path (comp_et J)"
    using comp_et_subset by (intro hc_of_et_reduces_cost)
  also have "... \<le>  \<Sum>\<^sub># (image_mset c J)"
    using et_edges by (auto simp: cost_of_path_sum)
  also have "... = cost_of_st T + cost_of_match M"
    by (auto simp: sum_unfold_sum_mset)
  finally show ?thesis .
qed

lemma min_match_leq_half_OPT: "2 * cost_of_match M \<le> cost_of_path OPT"
  unfolding defs
  apply (intro christofides_serdyukov_algo_approx_restr_E.min_match_leq_half_OPT)
  apply unfold_locales
  using subset_W apply simp
  using even_card_W apply simp
  using perf_match_exists match by auto (* TODO: clean up! *)

lemma cs_approx: "2 * cost_of_path christofides_serdyukov \<le> 3 * cost_of_path OPT"
proof -
  have "2 * cost_of_path christofides_serdyukov 
      \<le> (cost_of_st T + cost_of_match M) + (cost_of_st T + cost_of_match M)"
    using cost_cs_leq by (auto simp: mult_2[symmetric] add_mono)
  also have "... = 2 * cost_of_st T + 2 * cost_of_match M"
    by (auto simp: mult_2)
  also have "... \<le> 2 * cost_of_path OPT + 2 * cost_of_match M"
    using is_connected mst mst_mtsp_approx add_right_mono[OF mult_2_mono] by auto    
  also have "... \<le> 2 * cost_of_path OPT + cost_of_path OPT"
    using min_match_leq_half_OPT add_left_mono by auto
  also have "... = 3 * cost_of_path OPT"
    by (auto simp: mult_3)
  finally show ?thesis .
qed

end

end