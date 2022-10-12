(* Author: Lukas Koller *)
theory MultiGraph
  imports Main Misc "berge/Berge" "HOL-Library.Multiset"
begin

type_synonym 'a mgraph = "'a set multiset"

locale mgraph_def =
  fixes E :: "'a set multiset"

abbreviation "mgraph_invar E \<equiv> graph_invar (set_mset E)"

locale mgraph_abs = mgraph_def +
  assumes mgraph: "mgraph_invar E"

definition "mVs E\<^sub>M = Vs (set_mset E\<^sub>M)"

lemma mVs_memberE:
  assumes "v \<in> mVs E"
  obtains e where "v \<in> e" "e \<in># E"
  using assms[unfolded mVs_def] by (auto elim: vs_member_elim)

lemma mVs_mset_set:
  assumes "finite E"
  shows "mVs (mset_set E) = Vs E"
  unfolding mVs_def using assms by (auto simp: finite_set_mset_mset_set)

lemma mVs_subset:
  assumes "E' \<subseteq># E"
  shows "mVs E' \<subseteq> mVs E"
  unfolding mVs_def using assms Vs_subset[OF set_mset_mono, of E' E] by auto

lemma mVs_union: "mVs (A + B) = mVs A \<union> mVs B"
  unfolding mVs_def by (auto simp: Vs_union)

definition "encode_as_graph E\<^sub>M \<equiv> {{(u,i),(v,i)} | u v i. {u,v} \<in># E\<^sub>M \<and> i \<le> count E\<^sub>M {u,v}} 
    \<union> {{(v,i),(v,j)} | v i j. v \<in> mVs E\<^sub>M \<and> i < j \<and> j \<le> Max {count E\<^sub>M {u,v} | u. u \<in> mVs E\<^sub>M}}"

lemma mVs_def2: "mVs E\<^sub>M = fst ` Vs (encode_as_graph E\<^sub>M)"
  sorry

definition "mpath E\<^sub>M P \<equiv> path (encode_as_graph E\<^sub>M) (map (\<lambda>v. (v,1)) P)"

lemma mpath_def2: "mpath E\<^sub>M P \<longleftrightarrow> path (set_mset E\<^sub>M) P"
  sorry

lemma mpath_edges_subset:
  assumes "mpath E P"
  shows "set (edges_of_path P) \<subseteq> set_mset E"
  using path_edges_subset[OF assms[unfolded mpath_def2]] .

lemma mem_mpath_mVs:
  assumes "mpath E P" "v \<in> set P"
  shows "v \<in> mVs E"
  unfolding mVs_def using mem_path_Vs[OF assms[unfolded mpath_def2]] .

lemma mpath_Vs_subset:
  assumes "mpath E P"
  shows "set P \<subseteq> mVs E"
  using mem_mpath_mVs[OF assms] by auto

definition "mdegree E\<^sub>M v \<equiv> degree (encode_as_graph E\<^sub>M) (v,1)"

lemma mdegree_add: "mdegree (E\<^sub>1 + E\<^sub>2) v = mdegree E\<^sub>1 v + mdegree E\<^sub>2 v"
proof -
  have "mdegree (E\<^sub>1 + E\<^sub>2) v = degree (encode_as_graph (E\<^sub>1 + E\<^sub>2)) (v,1)"
    unfolding mdegree_def by auto
  also have "... = card' {e \<in> encode_as_graph (E\<^sub>1 + E\<^sub>2). (v,1) \<in> e}"
    unfolding degree_def2 by auto
  show ?thesis
    sorry
qed

lemma mdegree_eq_degree: "mdegree (mset_set E) v = degree E v"
  sorry

end