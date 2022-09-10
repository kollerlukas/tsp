theory MultiGraph
  imports Main "HOL-Library.Multiset" "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

type_synonym 'a mgraph = "'a set multiset"

(* definition "mgraph_rel E\<^sub>1 E\<^sub>2 \<equiv> (set_mset E\<^sub>1 = set_mset E\<^sub>2)"

quotient_type 'a graph = "'a mgraph" / mgraph_rel
  morphisms Rep_graph Abs_graph
proof (rule equivpI)
  show "reflp mgraph_rel" by (auto simp: reflp_def mgraph_rel_def)
  show "symp mgraph_rel" by (auto simp: symp_def mgraph_rel_def)
  show "transp mgraph_rel" by (auto simp: transp_def mgraph_rel_def)
qed *)

locale mgraph_def =
  fixes E :: "'a set multiset"

abbreviation "mgraph_invar E \<equiv> graph_invar (set_mset E)"

locale mgraph_abs = mgraph_def +
  assumes mgraph: "mgraph_invar E"

definition "mVs E\<^sub>M = Vs (set_mset E\<^sub>M)"

definition "encode_as_graph E\<^sub>M \<equiv> {{(u,i),(v,i)} | u v i. {u,v} \<in># E\<^sub>M \<and> i \<le> count E\<^sub>M {u,v}} 
\<union> {{(v,i),(v,j)} | v i j. v \<in> mVs E\<^sub>M \<and> i < j \<and> j \<le> Max {count E\<^sub>M {u,v} | u. u \<in> mVs E\<^sub>M}}"

lemma mVs_def2: "mVs E\<^sub>M = fst ` Vs (encode_as_graph E\<^sub>M)"
proof
  show "mVs E\<^sub>M \<subseteq> fst ` Vs (encode_as_graph E\<^sub>M)"
  proof
    fix v
    assume "v \<in> mVs E\<^sub>M"
    then obtain e where "v \<in> e" "e \<in> set_mset E\<^sub>M"
      unfolding mVs_def by (auto elim: vs_member_elim)
    then have "e \<in># E\<^sub>M"
      by auto
    moreover then obtain u where "e = {u,v}"
      sorry (* graph_invar E\<^sub>M *)
    ultimately have "{(u,1),(v,1)} \<in> encode_as_graph E\<^sub>M"
      unfolding encode_as_graph_def using count_greater_eq_one_iff[of E\<^sub>M "{u,v}"] by blast
    then have "(v,1) \<in> Vs (encode_as_graph E\<^sub>M)"
      by (auto intro: vs_member_intro)
    then show "v \<in> fst ` Vs (encode_as_graph E\<^sub>M)"
      by force
  qed
next
  show "fst ` Vs (encode_as_graph E\<^sub>M) \<subseteq> mVs E\<^sub>M"
    sorry
qed

definition "mpath E\<^sub>M P \<equiv> path (encode_as_graph E\<^sub>M) (map (\<lambda>v. (v,1)) P)"

lemma mpath_def2: "mpath E\<^sub>M P \<longleftrightarrow> path (set_mset E\<^sub>M) P"
  sorry

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