(* Author: Lukas Koller *)
theory ChristofidesSerdyukov
  imports Main MST TSP Eulerian MinWeightMatching DoubleTree
begin

section \<open>\textsc{Christofides-Serdyukov} Approximation Algorithm for mTSP\<close>

locale christofides_serdyukov_algo = 
  metric_graph_abs E c + 
  mst E c comp_mst + 
  eulerian comp_et +
  min_weight_matching E c 
  for E :: "'a set set" and c comp_mst and comp_et :: "'a mgraph \<Rightarrow> 'a list"
begin

definition christofides_serdyukov where
  "christofides_serdyukov = (
    let T = comp_mst c E;
        W = {v | v. v \<in> Vs T \<and> \<not> even' (degree T v)};
        M = comp_match ({{u,v} | u v. u \<in> W \<and> v \<in> W}) c;
        T' = mset_set T + mset_set M;
        P = comp_et T' in
        hc_of_et P [])"

end

subsection \<open>Feasibility of \textsc{Christofides-Serdyukov}\<close>

context christofides_serdyukov_algo
begin

(* TODO *)

lemma T'_eulerian:
  fixes T W M
  defines "W \<equiv> {v | v. v \<in> Vs T \<and> \<not> even' (degree T v)}"
  defines "M \<equiv> comp_match ({{u,v} | u v. u \<in> W \<and> v \<in> W}) c"
  assumes "is_mst T"
  shows "is_eulerian (mset_set T + mset_set M)"
  sorry

lemma "is_hc (christofides_serdyukov)"
  apply (simp only: christofides_serdyukov_def Let_def)
  apply (rule hc_of_et_correct, rule eulerian)
  sorry

end

subsection \<open>Approximation of \textsc{Christofides-Serdyukov}\<close>

context christofides_serdyukov_algo
begin

(* TODO *)

lemma christofides_serdyukov_approx:
  assumes "is_mtsp OPT"
  shows "2 * cost_of_path christofides_serdyukov \<le> 3 * cost_of_path OPT" (* ... = 3/2 * ... *)
  sorry

end

end