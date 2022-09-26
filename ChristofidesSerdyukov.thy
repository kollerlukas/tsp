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
        W = {v | v. v \<in> Vs T \<and> \<not> even' (degree T v)};
        M = comp_match ({{u,v} | u v. u \<in> W \<and> v \<in> W \<and> u \<noteq> v}) c;
        J = mset_set T + mset_set M;
        P = comp_et J in
        comp_hc_of_et P [])"

end

subsection \<open>Feasibility of \textsc{Christofides-Serdyukov}\<close>

locale christofides_serdyukov_J = 
  christofides_serdyukov_algo E c comp_mst comp_et comp_match
  for E :: "'a set set" and c comp_mst and comp_et :: "'a mgraph \<Rightarrow> 'a list" and comp_match +
  fixes T W E\<^sub>W M
  defines "W \<equiv> {v | v. v \<in> Vs T \<and> \<not> even' (degree T v)}"
      and "E\<^sub>W \<equiv> {{u,v} | u v. u \<in> W \<and> v \<in> W \<and> u \<noteq> v} \<inter> E"
      and "M \<equiv> comp_match E\<^sub>W c"
  assumes mst_T: "is_mst T"
begin

lemma subset_T: "T \<subseteq> E"
  using mst_T by (auto simp: is_mstE2)

lemma graph_T: "graph_invar T"
  using graph subset_T finite_subset[OF Vs_subset] by blast

lemma finite_T: "finite T"
  using finite_E subset_T finite_subset by auto

lemma subset_W: "W \<subseteq> Vs E"
  unfolding W_def using Vs_subset[OF subset_T] by auto

lemma E\<^sub>W_def2: "E\<^sub>W = {{u,v} | u v. u \<in> W \<and> v \<in> W \<and> u \<noteq> v}"
  unfolding E\<^sub>W_def using complete subset_W sorry

lemma subset_E\<^sub>W: "E\<^sub>W \<subseteq> E"
  unfolding E\<^sub>W_def by auto

lemma finite_E\<^sub>W: "finite E\<^sub>W"
  using subset_E\<^sub>W finite_E finite_subset by auto

lemma finite_Vs_E\<^sub>W: "finite (Vs E\<^sub>W)"
  using graph subset_E\<^sub>W finite_subset[OF Vs_subset] by auto

lemma even_Vs_E\<^sub>W: "even (card (Vs E\<^sub>W))"
proof -
  have "even' (\<Sum>v \<in> Vs E. degree E v)"
    sorry (* follows from handshake thm *)
  moreover have "(\<Sum>v \<in> Vs E. degree E v) = 
    (\<Sum>v \<in> Vs E\<^sub>W. degree E v) + (\<Sum>v \<in> Vs E - Vs E\<^sub>W. degree E v)"
    sorry
  moreover have "even' (\<Sum>v \<in> Vs E - Vs E\<^sub>W. degree E v)"
    sorry (* sum of even vals is even *)
  ultimately have "even' (\<Sum>v \<in> Vs E\<^sub>W. degree E v)"
    sorry (* a \<noteq> \<infinity> \<and> b \<noteq> \<infinity> \<Longrightarrow> even' (a+b) \<and> even' b \<Longrightarrow> even' a *)
  thus "even (card (Vs E\<^sub>W))"
    using even_sum_of_odd_vals_iff sorry
qed  (* follows from handshake thm *)

lemma complete_E\<^sub>W: "\<And>u v. u \<in> Vs E\<^sub>W \<Longrightarrow> v \<in> Vs E\<^sub>W \<Longrightarrow> u \<noteq> v \<Longrightarrow> {u,v} \<in> E\<^sub>W"
proof -
  fix u v
  assume "u \<in> Vs E\<^sub>W" "v \<in> Vs E\<^sub>W" "u \<noteq> v"
  moreover hence "u \<in> W" "v \<in> W"
    sorry
  moreover have "{u,v} \<in> E"
    using calculation Vs_subset[OF subset_E\<^sub>W] complete by blast
  ultimately show "{u,v} \<in> E\<^sub>W"
    unfolding E\<^sub>W_def by auto
qed

lemma perf_match_exists: "\<exists>M. is_perf_match E\<^sub>W M"
  using graph Vs_subset subset_E\<^sub>W complete_E\<^sub>W perf_match_exists[OF graph_subset _ even_Vs_E\<^sub>W] 
  by auto 

lemmas match = match[OF perf_match_exists]

lemma subset_M: "M \<subseteq> E"
  using match is_min_matchE2[of E\<^sub>W c M] subset_E\<^sub>W by (auto simp: M_def)

lemma "Vs E\<^sub>W = W" 
  unfolding E\<^sub>W_def2
  sorry

lemma Vs_M_eq_W: "Vs M = W"
  sorry

lemma finite_M: "finite M"
  using finite_E subset_M finite_subset by auto

lemma matching_M: "matching M"
  unfolding M_def using match by (auto simp: is_min_matchE2)

lemma J_eulerian: "is_eulerian (mset_set T + mset_set M)" (is "is_eulerian ?J")
proof (rule is_eulerianI)
  fix v
  assume "v \<in> mVs ?J"
  hence "v \<in> Vs T"
    sorry
  hence "v \<in> W \<or> v \<notin> W"
    using mVs_union by auto
  thus "even' (mdegree ?J v)"
  proof (elim disjE)
    assume "v \<in> W"
    moreover hence "\<not> even' (degree T v)"
      unfolding W_def by auto
    moreover have "degree M v = 1"
      using calculation Vs_M_eq_W degree_matching_in_M[OF matching_M] by auto
    moreover have "mdegree ?J v = degree T v + 1"
      sorry
    ultimately show "even' (mdegree ?J v)"
      sorry
  next
    assume "v \<notin> W"
    moreover hence "even' (degree T v)"
      unfolding W_def using \<open>v \<in> Vs T\<close> by auto
    moreover have "v \<notin> Vs M"
      using calculation Vs_M_eq_W by auto
    moreover have "mdegree ?J v = degree T v"
      sorry
    ultimately show "even' (mdegree ?J v)"
      by auto
  qed
qed

lemma J_vs: "mVs (mset_set T + mset_set M) = Vs E" (is "mVs ?J = Vs E")
proof -
  have "mVs ?J = mVs (mset_set T) \<union> mVs (mset_set M)"
    by (auto simp: mVs_union)
  also have "... = Vs T \<union> Vs M"
    using finite_T finite_M by (auto simp: mVs_mset_set)
  also have "... = Vs E \<union> Vs M"
    using mst_T by (auto simp: is_mstE2)
  also have "... = Vs E"
    using Vs_subset[OF subset_M] by (auto simp: sup_absorb1)
  finally show ?thesis .
qed

lemma J_edges: "set_mset (mset_set T + mset_set M) \<subseteq> E" (is "set_mset ?J \<subseteq> E")
  using subset_T subset_M by (simp add: finite_M finite_T)

lemmas christofides_serdyukov_correctness = J_eulerian J_vs J_edges

end

locale christofides_serdyukov_algo_feasibility =
  hc_of_et E c comp_mst comp_et +
  christofides_serdyukov_algo E c comp_mst comp_et comp_match + 
  christofides_serdyukov_J E c comp_mst comp_et comp_match "comp_mst c E"
  for E :: "'a set set" and c comp_mst and comp_et :: "'a mgraph \<Rightarrow> 'a list" and comp_match
begin

lemmas [simp] = W_def E\<^sub>W_def2 M_def

lemma "is_hc (christofides_serdyukov)"
  apply (simp only: christofides_serdyukov_def Let_def)
  apply (rule hc_of_et_correct, rule eulerian)
  using christofides_serdyukov_correctness by auto

end

subsection \<open>Approximation of \textsc{Christofides-Serdyukov}\<close>

locale christofides_serdyukov_algo_approx =
  hc_of_et +
  christofides_serdyukov_algo
begin

(* TODO *)

lemma christofides_serdyukov_approx:
  assumes "is_mtsp OPT"
  shows "2 * cost_of_path christofides_serdyukov \<le> 3 * cost_of_path OPT" (* ... = 3/2 * ... *)
  sorry

end

end