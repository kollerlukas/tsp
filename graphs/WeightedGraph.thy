(* Author: Lukas Koller *)
theory WeightedGraph
  imports Main tsp.Misc tsp.Berge tsp.CompleteGraph "HOL-Library.Multiset"
begin

fun cost_of_path where 
  "cost_of_path c [] = 0"
| "cost_of_path c [v] = 0"
| "cost_of_path c (u#v#P) = c u v + cost_of_path c (v#P)"

lemma cost_of_path_short_cut: 
  "cost_of_path c (u#short_cut F (v#P)) = c u v + cost_of_path c (short_cut F (v#P))"
proof -
  obtain P' where [simp]: "short_cut F (v#P) = v#short_cut F P'"
    by (elim short_cut_hdE)
  thus ?thesis by auto
qed

lemma cost_of_path_sum: 
  "cost_of_path (\<lambda>u v. c {u,v}) P = \<Sum>\<^sub># (image_mset c (mset (edges_of_path P)))"
  by (induction P rule: list012.induct) auto

lemma cost_of_path_sum_list: 
  "cost_of_path (\<lambda>u v. c {u,v}) P = sum_list (map c (edges_of_path P))"
  by (induction P rule: list012.induct) auto

lemma cost_of_path_distinct_sum: 
  assumes "distinct (edges_of_path P)" 
  shows "cost_of_path (\<lambda>u v. c {u,v}) P = sum c (set (edges_of_path P))"
  using assms by (auto simp: sum_unfold_sum_mset cost_of_path_sum mset_set_set)

lemma const_cost_of_path:
  assumes "\<And>e. e \<in> set (edges_of_path P) \<Longrightarrow> c e = k" 
  shows "cost_of_path (\<lambda>u v. c {u,v}) P = (length P - 1) * k"
  using assms by (induction P rule: list012.induct) 
    (auto simp: cost_of_path_sum_list edges_of_path_length[symmetric])

lemma cost_of_path_cons: "P \<noteq> [] \<Longrightarrow> cost_of_path c (v#P) = c v (hd P) + cost_of_path c P"
  by (induction P) auto

lemma cost_of_path_eq_cost:
  assumes "\<And>e. e \<in> set (edges_of_path P) \<Longrightarrow> c\<^sub>1 e = c\<^sub>2 e" 
  shows "cost_of_path (\<lambda>u v. c\<^sub>1 {u,v}) P = cost_of_path (\<lambda>u v. c\<^sub>2 {u,v}) P"
  using assms by (induction P rule: list012.induct) auto

lemma cost_of_path_append:
  fixes c :: "'a \<Rightarrow> 'a \<Rightarrow> ('b::ordered_semiring_0)" \<comment> \<open>Needed for associativity.\<close>
  assumes "P\<^sub>1 \<noteq> []" "P\<^sub>2 \<noteq> []" 
  shows "cost_of_path c (P\<^sub>1 @ P\<^sub>2) = cost_of_path c P\<^sub>1 + c (last P\<^sub>1) (hd P\<^sub>2) + cost_of_path c P\<^sub>2"
  using assms by (induction P\<^sub>1 arbitrary: P\<^sub>2 rule: list012.induct) 
    (auto simp: cost_of_path_cons add.assoc)

lemma cost_of_path_append_edge:
  fixes c :: "'a \<Rightarrow> 'a \<Rightarrow> ('b::ordered_semiring_0)" \<comment> \<open>Needed for associativity.\<close>
  shows "cost_of_path c (P @ [u,v]) = cost_of_path c (P @ [u]) + c u v"
  by (induction P rule: list012.induct) (auto simp: cost_of_path_cons add.assoc)

lemma cost_of_path_rev:
  fixes c :: "'a \<Rightarrow> 'a \<Rightarrow> ('b::ordered_semiring_0)" \<comment> \<open>Needed for associativity and commutativity.\<close>
  assumes "\<And>u v. c u v = c v u"
  shows "cost_of_path c (rev P) = cost_of_path c P"
  using assms by (induction P rule: list012.induct) 
    (auto simp add: cost_of_path_append_edge add.commute)

lemma not_hd_snd_rotate_tour_acc: 
  assumes "cost_of_path (\<lambda>x y. if \<not> f x \<and> f y then (1::nat) else 0) xs > 0" 
      (is "cost_of_path ?c xs > 0") and "rotate_tour_acc acc f xs = x#y#xs'"
  shows "\<not> f x" "f y"
  using assms by (induction xs arbitrary: acc rule: list012.induct) (auto split: if_splits)

lemma not_hd_snd_rotate_tour: 
  assumes "cost_of_path (\<lambda>x y. if \<not> f x \<and> f y then (1::nat) else 0) xs > 0" 
      (is "cost_of_path ?c xs > 0") and "rotate_tour f xs = x#y#xs'"
  shows "\<not> f x" "f y"
  using assms(2) not_hd_snd_rotate_tour_acc[OF assms(1), of "[]" x y xs'] by auto

lemma cost_hd_concat_map: 
  assumes "\<And>y. y \<in> set xs \<Longrightarrow> f y \<noteq> [] \<Longrightarrow> c x (hd (f y)) \<le> k" "concat (map f xs) \<noteq> []"
  shows "c x (hd (concat (map f xs))) \<le> k"
  using assms
proof (induction xs)
  case (Cons y xs)
  then show ?case 
    by (cases "f y = []") auto
qed auto

lemma cost_concat_map:
  fixes c :: "'a \<Rightarrow> 'a \<Rightarrow> int"
  assumes "distinct xs"
      and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> f x \<noteq> [] \<Longrightarrow> f y \<noteq> [] \<Longrightarrow> c (last (f x)) (hd (f y)) \<le> k"
  shows "cost_of_path c (concat (map f xs)) \<le> (\<Sum>x\<leftarrow>xs. cost_of_path c (f x)) + (length (tl xs)) * k"
  using assms
proof (induction xs rule: list012.induct)
  case 1
  then show ?case by auto
next
  case (2 v)
  then show ?case by auto
next
  case (3 x y xs)
  let ?fyxs="concat (map f (y#xs))"
  consider "f x = []" | "?fyxs = []" | "f x \<noteq> []" "?fyxs \<noteq> []"
    by auto
  then show ?case 
  proof cases
    assume "f x = []" 
    thus ?thesis
      using 3 by auto
  next
    assume "?fyxs = []"
    hence "cost_of_path c (concat (map f (x#y#xs))) = cost_of_path c (f x @ ?fyxs)"
      by auto
    also have "... = cost_of_path c (f x)"
      by (subst \<open>?fyxs = []\<close>) auto
    also have "... = cost_of_path c (f x) + cost_of_path c ?fyxs"
      by (subst \<open>?fyxs = []\<close>) auto
    also have "... \<le> (\<Sum>x\<leftarrow>(x#y#xs). cost_of_path c (f x)) + (length (tl (x#y#xs))) * k"
      using 3 by auto
    finally show ?thesis .
  next
    assume "f x \<noteq> []" and "?fyxs \<noteq> []"
    hence "cost_of_path c (concat (map f (x#y#xs))) 
      = cost_of_path c (f x) + c (last (f x)) (hd ?fyxs) + cost_of_path c ?fyxs"
      by (auto simp add: cost_of_path_append)
    also have "... \<le> cost_of_path c (f x) + k + cost_of_path c ?fyxs"
      using 3 \<open>f x \<noteq> []\<close> \<open>?fyxs \<noteq> []\<close> cost_hd_concat_map[of "y#xs" f c "last (f x)" k] by auto
    also have "... \<le> (\<Sum>x\<leftarrow>(x#y#xs). cost_of_path c (f x)) + (length (tl (x#y#xs))) * k"
      using 3 by auto
    finally show ?thesis .
  qed
qed

text \<open>Weighted Graph\<close>
locale w_graph_abs = 
  graph_abs E for E :: "'a set set" +
  fixes c :: "'a set \<Rightarrow> 'b::{ordered_semiring_0,semiring_numeral}"
begin

abbreviation "cost_of_path\<^sub>c \<equiv> cost_of_path (\<lambda>u v. c {u,v})"

end

text \<open>Weighted Graph with positive weights\<close>
locale pos_w_graph_abs = 
  w_graph_abs E c for E c +
  assumes costs_positive: "\<And>e. c e > 0"
begin                            

lemma costs_ge_0: "c e \<ge> 0"
  using costs_positive by (simp add: order_less_imp_le)

lemma sum_costs_pos: "sum c A \<ge> 0"
  using costs_ge_0 by (simp add: sum_nonneg)

lemma sum_union_leq:
  assumes "finite A" "finite B"
  shows "sum c (A \<union> B) \<le> sum c A + sum c B"
proof -
  have "sum c (A \<union> B) \<le> sum c (A \<union> B) + sum c (A \<inter> B)"
    using sum_costs_pos add_increasing2 by auto
  also have "...  = sum c A + sum c B"
    using assms sum.union_inter by auto
  finally show ?thesis .
qed

lemma cost_of_path_pos: "cost_of_path\<^sub>c P \<ge> 0"
  by (induction P rule: list012.induct) (auto simp add: costs_ge_0)

lemma cost_of_path_cons_leq: "cost_of_path\<^sub>c P \<le> cost_of_path\<^sub>c (v#P)"
  by (induction P arbitrary: v rule: list012.induct) (auto simp add: costs_ge_0 add_increasing)

lemma cost_of_path_append_leq: "cost_of_path\<^sub>c P \<le> cost_of_path\<^sub>c (P @ [v])"
  by (induction P arbitrary: v rule: list012.induct) (auto simp add: costs_ge_0 add_left_mono)

lemma cost_of_path_leq_sum: "sum c (set (edges_of_path P)) \<le> cost_of_path\<^sub>c P"
proof (induction P rule: list012.induct)
  case (3 u v P)
  have "sum c (set (edges_of_path (u#v#P))) \<le> c {u,v} + sum c (set (edges_of_path (v#P)))"
    using sum_union_leq[of "{{u,v}}" "set (edges_of_path (v#P))"] by auto
  also have "... \<le> cost_of_path\<^sub>c (u#v#P)"
    using "3.IH" by (auto simp add: add_left_mono)
  finally show ?case .
qed auto

lemma cost_of_path_app_edge: "cost_of_path\<^sub>c (P @ [u,v]) = c {u,v} + cost_of_path\<^sub>c (P @ [u])"
  using cost_of_path_append_edge by (auto simp add: add.assoc add.commute add.left_commute)

lemma cost_of_path_rev: "cost_of_path\<^sub>c P = cost_of_path\<^sub>c (rev P)"
  by (auto intro!: cost_of_path_rev[symmetric] simp add: insert_commute)

lemma cost_of_path_rotate: "cost_of_path\<^sub>c (u#P\<^sub>1 @ v#P\<^sub>2 @ [u]) = cost_of_path\<^sub>c (v#P\<^sub>2 @ u#P\<^sub>1 @ [v])" 
  by (auto simp add: cost_of_path_sum mset_edges_of_path_rotate)

end

locale metric_graph_abs = 
  compl_graph_abs E + 
  pos_w_graph_abs E c for E c +
  assumes tri_ineq: "u \<in> Vs E \<Longrightarrow> v \<in> Vs E \<Longrightarrow> w \<in> Vs E \<Longrightarrow> c {u,w} \<le> c {u,v} + c {v,w}"
begin

lemma cost_of_path_cons_tri_ineq:
  assumes "set (u#v#P) \<subseteq> Vs E"
  shows "cost_of_path\<^sub>c (u#P) \<le> cost_of_path\<^sub>c (u#v#P)"
  using assms
proof (induction P)
  case (Cons w P)
  then have "cost_of_path\<^sub>c (u#w#P) \<le> c {u,v} + c {v,w} + cost_of_path\<^sub>c (w#P)"
    using tri_ineq by (auto simp: add_right_mono)
  also have "... = cost_of_path\<^sub>c (u#v#w#P)"
    by (auto simp: add.assoc)
  finally show ?case .
qed (auto simp: costs_ge_0)

lemma cost_of_path_app_tri_ineq:
  assumes "set P\<^sub>1 \<union> set P\<^sub>2 \<union> {w} \<subseteq> Vs E" 
  shows "cost_of_path\<^sub>c (P\<^sub>1 @ P\<^sub>2) \<le> cost_of_path\<^sub>c (P\<^sub>1 @ w#P\<^sub>2)"
  using assms cost_of_path_cons_tri_ineq 
  by (induction P\<^sub>1 rule: list012.induct) (auto simp: add_left_mono cost_of_path_cons_leq)

lemma cost_of_path_short_cut_tri_ineq: 
  assumes "set P \<subseteq> Vs E" 
  shows "cost_of_path\<^sub>c (short_cut E\<^sub>V P) \<le> cost_of_path\<^sub>c P"
  using assms
proof (induction P rule: short_cut.induct)
  case (1 E)
  then show ?case by auto
next
  case (2 E v)
  then show ?case by auto
next
  case (3 E u v P)
  thus ?case 
  proof cases
    assume "{u,v} \<notin> E"
    show ?case
      apply (rule order_trans[of _ "cost_of_path\<^sub>c (u#P)"])
      using \<open>{u,v} \<notin> E\<close> 3 apply auto[1]
      using "3.prems" apply (intro cost_of_path_cons_tri_ineq; auto) 
      done (* TODO: clean up *)
  qed (auto simp: cost_of_path_short_cut add_left_mono)
qed

end

end