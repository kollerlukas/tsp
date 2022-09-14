(* Author: Lukas Koller *)
theory Misc
  imports Main "../archive-of-graph-formalizations/Undirected_Graphs/Berge"
begin

text \<open>This theory contains miscellaneous lemmas and theorems.\<close>

section \<open>List Induction Schemas\<close>

(* function just for the induction schema *)
fun list012 where
  "list012 [] = undefined"
| "list012 [v] = undefined"
| "list012 (u#v#P) = list012 (v#P)"

(* function just for the induction schema *)
fun list0123 where
  "list0123 [] = undefined"
| "list0123 [v] = undefined"
| "list0123 [u,v] = undefined"
| "list0123 (u#v#w#P) = list0123 (v#w#P)"

(* function just for the induction schema *)
fun list01234 where
  "list01234 [] = undefined"
| "list01234 [v] = undefined"
| "list01234 [u,v] = undefined"
| "list01234 [u,v,w] = undefined"
| "list01234 (u#v#w#x#P) = list01234 (v#w#x#P)"

section \<open>List Lemmas\<close>

lemma distinct_hd_last_neq: "distinct xs \<Longrightarrow> length xs > 1 \<Longrightarrow> hd xs \<noteq> last xs"
  by (induction xs) auto

lemma rev_hd_last_eq: "xs \<noteq> [] \<Longrightarrow> xs = rev xs \<Longrightarrow> hd xs = last xs"
proof (induction xs rule: list012.induct)
  case (3 x x' xs)
  thus ?case 
    by (metis last_rev)
qed auto

lemma split_hd: 
  assumes "xs \<noteq> []"
  obtains xs' where "xs = hd xs#xs'"
  using assms list.exhaust_sel by blast

lemma split_last:
  assumes "xs \<noteq> []" 
  obtains xs' where "xs = xs' @ [last xs]"
  using assms append_butlast_last_id by metis

lemma last_in_set_tl: "2 \<le> length xs \<Longrightarrow> last xs \<in> set (tl xs)"
  by (induction xs) auto

lemma list_hd_singleton: "length xs = 1 \<Longrightarrow> hd xs = x \<Longrightarrow> xs = [x]"
  by (induction xs) auto

lemma set_tl_subset: "set (tl A) \<subseteq> set A"
  by (induction A) auto

lemma drop_tl: "i > 0 \<Longrightarrow> drop i xs = drop (i - 1) (tl xs)"
  using drop_Suc[of "i-1"] Suc_diff_1[of i] by auto

section \<open>Metric Lemmas\<close>

lemma mult_2: "(x::'b::{ordered_semiring_0,semiring_numeral}) + x = 2 * x"
  by (simp add: semiring_numeral_class.mult_2)

lemma mult_2_mono: "(x::'b::{ordered_semiring_0,semiring_numeral}) \<le> y \<Longrightarrow> 2 * x \<le> 2 * y"
  by (simp add: add_mono semiring_numeral_class.mult_2)

section \<open>Graph Lemmas (Berge)\<close>

lemma path_subset_singleton:
  assumes "path X [v]" "v \<in> Vs X'"
  shows "path X' [v]"
  using assms by (auto intro: path.intros)

lemma path_Vs_subset: 
  assumes "path X P" 
  shows "set P \<subseteq> Vs X"
  using assms mem_path_Vs[of X] by blast

lemma path_drop:
  assumes "path X P"
  shows "path X (drop i P)"
  using assms path_suff[of X "take i P" "drop i P"] append_take_drop_id[of i P] by auto

lemma path_take:
  assumes "path X P"
  shows "path X (take i P)"
  using assms path_pref[of X "take i P" "drop i P"] append_take_drop_id[of i P] by auto

lemma subset_path:
  assumes "path X P" "set (edges_of_path P) \<subseteq> X'" "set P \<subseteq> Vs X'"
  shows "path X' P"
  using assms by (induction P rule: path.induct) (auto intro: path.intros)

lemma path_on_edges:
  assumes "path X P" "length P > 1"
  shows "path (set (edges_of_path P)) P" (is "path ?E\<^sub>P P")
  using assms path_edges_of_path_refl by force

lemma subset_walk:
  assumes "walk_betw X u P v" "set (edges_of_path P) \<subseteq> X'" "set P \<subseteq> Vs X'"
  shows "walk_betw X' u P v"
proof -
  have "path X P" "P \<noteq> []" "hd P = u" "last P = v"
    using assms by (auto elim: walk_between_nonempty_path)
  moreover hence "path X' P" 
    using assms subset_path[of X P X'] by auto
  ultimately show ?thesis
    by (intro nonempty_path_walk_between)
qed

lemma edges_of_path_tl: "edges_of_path (tl P) = tl (edges_of_path P)"
  by (induction P rule: edges_of_path.induct) auto

lemma edges_of_path_prepend_subset: "set (edges_of_path P) \<subseteq> set (edges_of_path (P @ P'))"
  by (induction P rule: edges_of_path.induct) auto

lemma edges_of_path_take_subset: "set (edges_of_path (take i P)) \<subseteq> set (edges_of_path P)"
  using edges_of_path_prepend_subset[of "take i P" "drop i P"] append_take_drop_id by auto

lemma edges_of_path_drop_subset: "set (edges_of_path (drop i P)) \<subseteq> set (edges_of_path P)"
  using edges_of_path_append_subset[of "drop i P" "take i P"] append_take_drop_id by auto

lemma edges_of_path_drop_take_subset: 
  "set (edges_of_path (drop i\<^sub>u (take i\<^sub>v H))) \<subseteq> set (edges_of_path H)"
proof -
  have "set (edges_of_path (drop i\<^sub>u (take i\<^sub>v H))) \<subseteq> set (edges_of_path (take i\<^sub>v H))"
    using edges_of_path_append_subset append_take_drop_id[of i\<^sub>u "take i\<^sub>v H"] by metis
  also have "... \<subseteq> set (edges_of_path H)"
    using edges_of_path_prepend_subset[of "take i\<^sub>v H"] append_take_drop_id[of i\<^sub>v H] by metis
  finally show ?thesis .
qed

lemma edges_of_path_append:
  assumes "P\<^sub>1 \<noteq> []"
  shows "edges_of_path (P\<^sub>1 @ u#P\<^sub>2) = edges_of_path P\<^sub>1 @ [{last P\<^sub>1,u}] @ edges_of_path (u#P\<^sub>2)"
  using assms by (induction P\<^sub>1 rule: list012.induct) auto

lemma walk_of_path:
  assumes "path E P" "i\<^sub>u < i\<^sub>v" "i\<^sub>v < length P"
  shows "walk_betw (set (edges_of_path P)) (P ! i\<^sub>u) (drop i\<^sub>u (take (i\<^sub>v+1) P)) (P ! i\<^sub>v)" 
    (is "walk_betw ?E\<^sub>P ?u ?P' ?v")
proof -
  have "path E ?P'"
    using assms path_drop[OF path_take, of E P i\<^sub>u "i\<^sub>v+1"] by auto
  moreover hence "path (set (edges_of_path ?P')) ?P'"
    using assms path_on_edges[of E ?P'] by auto
  moreover have "set (edges_of_path ?P') \<subseteq> ?E\<^sub>P"
    using edges_of_path_drop_subset[of i\<^sub>u "take (i\<^sub>v+1) P"] 
          edges_of_path_take_subset[of "i\<^sub>v+1" P] by auto
  moreover hence "path ?E\<^sub>P ?P'"
    using calculation path_subset[of "set (edges_of_path ?P')" ?P' ?E\<^sub>P] by auto
  moreover have "?P' \<noteq> []"
    using assms length_take length_drop by auto
  moreover have "hd ?P' = ?u"
      using assms hd_drop_conv_nth[of i\<^sub>u "take (i\<^sub>v+1) P"] nth_take[of i\<^sub>u "i\<^sub>v+1" P] by auto
  moreover have "last ?P' = ?v"
    using assms last_drop[of i\<^sub>u "take (i\<^sub>v+1) P"] last_conv_nth[of "take (i\<^sub>v+1) P"] by force
  ultimately show ?thesis
    by (intro nonempty_path_walk_between) auto
qed

lemma walk_of_pathE:
  assumes "path E P" "i\<^sub>u < i\<^sub>v" "i\<^sub>v < length P"
  obtains P' where "walk_betw (set (edges_of_path P)) (P ! i\<^sub>u) P' (P ! i\<^sub>v)"
  using assms walk_of_path by blast

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

lemma edges_of_path_nil:
  assumes "edges_of_path T = []"
  shows "T = [] \<or> (\<exists>v. T = [v])"
  using assms by (induction T rule: edges_of_path.induct) auto

lemma walk_edges_subset: "walk_betw E u P v \<Longrightarrow> set (edges_of_path P) \<subseteq> E"
  using walk_between_nonempty_path[of E u P v] path_edges_subset by auto

lemma non_inf_degr: "finite E \<Longrightarrow> degree E v \<noteq> \<infinity>"
  unfolding degree_def2 by auto

lemma vs_edges_path_eq:
  assumes "length P \<noteq> 1"
  shows "set P = Vs (set (edges_of_path P))"
  using assms
proof (induction P rule: edges_of_path.induct)
  case (3 u v P)
  show ?case 
  proof 
    show "set (u#v#P) \<subseteq> Vs (set (edges_of_path (u#v#P)))" (is "set (u#v#P) \<subseteq> Vs ?E'")
    proof
      fix w
      assume "w \<in> set (u#v#P)"
      then obtain e where "e \<in> set (edges_of_path (u#v#P))" "w \<in> e"
        using path_vertex_has_edge[of "u#v#P" w] by auto
      then show "w \<in> Vs ?E'"
        by (intro vs_member_intro)
    qed
  next
    show "Vs (set (edges_of_path (u#v#P))) \<subseteq> set (u#v#P)"
      using edges_of_path_Vs[of "u#v#P"] by auto
  qed
qed (auto simp: Vs_def)

lemma walk_on_edges_of_path:
  assumes "walk_betw X u P v" "length P \<noteq> 1"
  shows "walk_betw (set (edges_of_path P)) u P v"
proof (rule subset_walk)
  show "walk_betw X u P v"
    using assms by auto
  show "set (edges_of_path P) \<subseteq> set (edges_of_path P)"
    by auto
  show "set P \<subseteq> Vs (set (edges_of_path P)) "
    using assms vs_edges_path_eq by auto
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

lemma edges_of_vpath_are_vs:
  assumes "\<And>v. P = [v] \<Longrightarrow> v \<in> Vs E" "set (edges_of_path P) \<subseteq> E"
  shows "set P \<subseteq> Vs E"
  using assms
proof (induction P rule: list0123.induct)
  case (3 u v)
  thus ?case 
    by (auto intro: vs_member_intro[of _ "{u,v}" E])
qed auto

context graph_abs
begin

lemma card_vertices_ge2:
  assumes "E \<noteq> {}" 
  shows "card (Vs E) \<ge> 2"
proof -
  obtain u v where "{u,v} \<in> E" "u \<noteq> v"
    using assms graph by force
  then have "{u,v} \<subseteq> Vs E"
    unfolding Vs_def by blast
  then show ?thesis
    using \<open>{u,v} \<in> E\<close> by (metis card_2_iff card_mono graph)
qed

end

lemma degree_edges_of_path_leq_2:
  assumes "distinct P" "length P > 1" "v \<in> set P"
  shows "degree (set (edges_of_path P)) v \<le> 2"
proof -
  have "v = hd P \<or> v = last P \<or> (v \<noteq> hd P \<and> v \<noteq> last P)"
    by auto
  thus ?thesis
  proof (elim disjE)
    assume "v = hd P"
    hence "degree (set (edges_of_path P)) v = 1"
      using assms degree_edges_of_path_hd[of P] by auto
    also have "... \<le> 2"
      using one_le_numeral by blast
    finally show ?thesis by (auto simp: edges_of_path_tl)
  next
    assume "v = last P"
    hence "degree (set (edges_of_path P)) v = 1"
      using assms degree_edges_of_path_last[of P] by auto
    also have "... \<le> 2"
      using one_le_numeral by blast
    finally show ?thesis by (auto simp: edges_of_path_tl)
  next
    assume "v \<noteq> hd P \<and> v \<noteq> last P"
    then show ?thesis
      using assms degree_edges_of_path_ge_2[of P v] by auto
  qed
qed

lemma walk_split:
  assumes "walk_betw X u P v" "u \<noteq> v" "u \<in> E\<^sub>1" "v \<in> E\<^sub>2" "set P \<subseteq> E\<^sub>1 \<union> E\<^sub>2"
  obtains x y where "{x,y} \<in> set (edges_of_path P)" "x \<in> E\<^sub>1" "y \<in> E\<^sub>2"
  using assms by (induction rule: induct_walk_betw) auto

end