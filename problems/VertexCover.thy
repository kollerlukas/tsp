theory VertexCover
  imports Main tsp.Misc tsp.Berge
begin

definition "is_vc E X \<equiv> (\<forall>e \<in> E. e \<inter> X \<noteq> {}) \<and> X \<subseteq> Vs E"

lemma is_vsI:
  assumes "\<And>e. e \<in> E \<Longrightarrow> e \<inter> X \<noteq> {}" "X \<subseteq> Vs E"
  shows "is_vc E X"
  unfolding is_vc_def using assms by auto

lemma is_vcE:
  assumes "is_vc E X" 
  shows "\<And>e. e \<in> E \<Longrightarrow> e \<inter> X \<noteq> {}" "X \<subseteq> Vs E"
  using assms[unfolded is_vc_def] by auto

definition "is_min_vc E X \<equiv> is_vc E X \<and> (\<forall>X'. is_vc E X' \<longrightarrow> card X \<le> card X')"

lemma is_min_vsI:
  assumes "is_vc E X" "\<And>X'. is_vc E X' \<Longrightarrow> card X \<le> card X'"
  shows "is_min_vc E X"
  unfolding is_min_vc_def using assms by auto

lemma is_min_vcE:
  assumes "is_min_vc E X"
  shows "is_vc E X" "\<And>V'. is_vc E X' \<Longrightarrow> card X \<le> card X'"
  using assms[unfolded is_min_vc_def] by auto

context graph_abs
begin

lemma is_vc_vertexE:
  assumes "is_vc E X" "e \<in> E"
  obtains v where "v \<in> X" "v \<in> e"
proof -
  obtain u v where "e = {u,v}" "u \<noteq> v"
    using assms graph by auto
  moreover have "e \<inter> X \<noteq> {}"
    using assms is_vcE by auto
  ultimately consider "u \<in> X" "u \<in> e" | "v \<in> X" "v \<in> e"
    by auto
  thus ?thesis
    using that by auto
qed

lemma E_subset_covered_edges:
  assumes "is_vc E X"
  shows "E \<subseteq> \<Union> {{e \<in> E. v \<in> e} | v. v \<in> X}"
proof
  fix e
  assume "e \<in> E"
  moreover then obtain v where "v \<in> X" "v \<in> e"
    using assms by (elim is_vc_vertexE)
  ultimately show "e \<in> \<Union> {{e \<in> E. v \<in> e} | v. v \<in> X}"
    by auto
qed

lemma covered_edges_leq_degree:
  assumes "degree E v \<le> enat k"
  shows "card {e \<in> E. v \<in> e} \<le> k"
  using assms[unfolded degree_def2] by (intro card'_leq)

lemma vc_finite: 
  assumes "is_vc E X"
  shows "finite X"
proof (rule finite_subset)
  show "X \<subseteq> Vs E"
    using assms by (elim is_vcE)
  show "finite (Vs E)"
    using graph by auto
qed

lemma card_E_leq_max_degree_card_vc:
  assumes "\<And>v. v \<in> Vs E \<Longrightarrow> degree E v \<le> enat k" "is_vc E X"
  shows "card E \<le> k * card X"
proof -
  have "X \<subseteq> Vs E"
    using assms by (elim is_vcE)
  hence "\<And>v. v \<in> X \<Longrightarrow> card {e \<in> E. v \<in> e} \<le> k"
    using assms by (auto intro: covered_edges_leq_degree) 
  moreover have "\<Union> {{e \<in> E. v \<in> e} | v. v \<in> X} \<subseteq> E"
    by auto
  moreover hence "finite (\<Union> {{e \<in> E. v \<in> e} | v. v \<in> X})"
    using finite_E by (rule finite_subset)
  ultimately have "card E \<le> card (\<Union> {{e \<in> E. v \<in> e} | v. v \<in> X})"
    using assms E_subset_covered_edges by (intro card_mono)
  also have "... \<le> sum card {{e \<in> E. v \<in> e} | v. v \<in> X}"
    by (rule card_Union_le_sum_card)
  also have "... \<le> sum card ((\<lambda>v. {e \<in> E. v \<in> e}) ` X)"
    apply (subst setcompr_eq_image)
    apply simp
    done
  also have "... \<le> sum (card o (\<lambda>v. {e \<in> E. v \<in> e})) X"
    apply (rule sum_image_le)
    using vc_finite[OF \<open>is_vc E X\<close>] apply auto
    done
  also have "... \<le> sum (\<lambda>v. card {e \<in> E. v \<in> e}) X"
    by auto
  also have "... \<le> sum (\<lambda>v. k) X"
    using \<open>\<And>v. v \<in> X \<Longrightarrow> card {e \<in> E. v \<in> e} \<le> k\<close> by (rule sum_mono)
  also have "... = of_nat (card X) * k"
    by (rule sum_constant)
  also have "... = k * card X"
    by auto
  finally show ?thesis .
qed (* TODO: clean up! *)

end

end