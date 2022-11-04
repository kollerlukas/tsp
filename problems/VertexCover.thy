theory VertexCover
  imports Main "../misc/Misc" "../berge/Berge"
begin

definition "is_vc E V \<equiv> (\<forall>e \<in> E. e \<inter> V \<noteq> {})"

lemma is_vsI:
  assumes "\<And>e. e \<in> E \<Longrightarrow> e \<inter> V \<noteq> {}"
  shows "is_vc E V"
  unfolding is_vc_def using assms by auto

lemma is_vcE:
  assumes "is_vc E V"
  shows "\<And>e. e \<in> E \<Longrightarrow> e \<inter> V \<noteq> {}"
  using assms[unfolded is_vc_def] by auto

definition "is_min_vc E V \<equiv> is_vc E V \<and> (\<forall>V'. is_vc E V' \<longrightarrow> card V \<le> card V')"

lemma is_min_vsI:
  assumes "is_vc E V" "\<And>V'. is_vc E V' \<Longrightarrow> card V \<le> card V'"
  shows "is_min_vc E V"
  unfolding is_min_vc_def using assms by auto

lemma is_min_vcE:
  assumes "is_min_vc E V"
  shows "is_vc E V" "\<And>V'. is_vc E V' \<Longrightarrow> card V \<le> card V'"
  using assms[unfolded is_min_vc_def] by auto

end