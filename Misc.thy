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

lemma remdups_append: "x \<in> set ys \<Longrightarrow> remdups (xs @ x # ys) = remdups (xs @ ys)"
  by (induction xs) auto

subsection \<open>Repeated Elements in Lists\<close>

lemma distinct_distinct_adj: "distinct xs \<Longrightarrow> distinct_adj xs"
  by (simp add: distinct_adj_altdef distinct_tl remdups_adj_distinct)

section \<open>(Finite) Set Lemmas\<close>

lemma set012_split: 
  assumes "finite F"
  obtains x y F' where "F = {} \<or> F = {x} \<or> (F = {x,y} \<union> F' \<and> x \<notin> F' \<and> y \<notin> F' \<and> x \<noteq> y)"
  using assms
proof (induction F rule: finite_induct)
  case insertI1: (insert x F)
  thus ?case 
  proof (induction F rule: finite_induct)
    case insertI2: (insert y F)
    thus ?case 
      using insertI1 by auto
  qed auto
qed auto

text \<open>Induction schema that adds two new elements to a finite set.\<close>
lemma finite2_induct [consumes 1, case_names empty insert insert2]:
  assumes "finite F"
  assumes empty: "P {}"
      and insert: "\<And>x. P {x}"
      and insert2: "\<And>x y F. finite F \<Longrightarrow> x \<notin> F \<Longrightarrow> y \<notin> F \<Longrightarrow> x \<noteq> y \<Longrightarrow> P F \<Longrightarrow> P ({x,y} \<union> F)"
  shows "P F"
  using assms
proof (induction F rule: finite_psubset_induct)
  case (psubset F)
  moreover then obtain x y F' where 
    "F = {} \<or> F = {x} \<or> (F = {x,y} \<union> F' \<and> x \<notin> F' \<and> y \<notin> F' \<and> x \<noteq> y)"
    using set012_split[of F] by metis
  ultimately show ?case 
  proof (elim disjE)
    assume "F = {x,y} \<union> F' \<and> x \<notin> F' \<and> y \<notin> F' \<and> x \<noteq> y"
    then show ?case
      using psubset by fastforce
  qed auto
qed

lemma finite_even_induct [consumes 2, case_names empty insert2]:
  assumes "finite F" "even (card F)"
  assumes empty: "P {}"
      and insert2: "\<And>x y F. finite F \<Longrightarrow> x \<notin> F \<Longrightarrow> y \<notin> F \<Longrightarrow> x \<noteq> y \<Longrightarrow> P F \<Longrightarrow> P ({x,y} \<union> F)"
  shows "P F"
  using assms by (induction F rule: finite2_induct) auto

inductive finite_even :: "'a set \<Rightarrow> bool" where
  fe_empty: "finite_even {}"
| fe_insert2: "finite_even A \<Longrightarrow> a \<notin> A \<Longrightarrow> b \<notin> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> finite_even ({a,b} \<union> A)"

lemma finite_evenI2:
  assumes "finite A" "even (card A)"
  shows "finite_even A"
  using assms
proof (induction A rule: finite_even_induct)
  case (insert2 a b A)
  then show ?case
    by (intro fe_insert2) auto
qed (auto intro: finite_even.intros)
  
lemma finite_even_def2: "finite_even A \<longleftrightarrow> finite A \<and> even (card A)"
proof
  assume "finite_even A"
  then show "finite A \<and> even (card A)"
    by (induction A rule: finite_even.induct) auto
qed (auto simp: finite_evenI2)

section \<open>Metric Lemmas\<close>

lemma mult_2: "(x::'b::{ordered_semiring_0,semiring_numeral}) + x = 2 * x"
  by (simp add: semiring_numeral_class.mult_2)

lemma mult_2_mono: "(x::'b::{ordered_semiring_0,semiring_numeral}) \<le> y \<Longrightarrow> 2 * x \<le> 2 * y"
  by (simp add: add_mono semiring_numeral_class.mult_2)

section \<open>Even Predicate\<close>

text \<open>Even predicate for \<open>enat\<close>\<close>
fun even' :: "enat \<Rightarrow> bool" where
  "even' \<infinity> = False"
| "even' (enat i) = even i"

lemma even_enat_mult2: 
  assumes "i \<noteq> \<infinity>" 
  shows "even' (2 * i)"
proof (cases "2 * i")
  case (enat j)
  thus ?thesis 
    using assms by (auto simp: numeral_eq_enat)
next
  case infinity
  then show ?thesis 
    using assms imult_is_infinity by auto
qed

section \<open>Sum Lemmas\<close>

lemma even_sum_of_odd_vals_iff:
  assumes "finite A" "\<forall>x \<in> A. odd (f x)"
  shows "even (\<Sum>x \<in> A. f x) \<longleftrightarrow> even (card A)"
  using assms by (induction A rule: finite_induct) auto

lemma sum_one_val:
  assumes "finite X" "a \<in> X" "\<And>x. x \<in> X \<Longrightarrow> x \<noteq> a \<Longrightarrow> f x = 0" "f a = 1"
  shows "sum f X = 1"
  using assms
proof (induction X rule: finite_induct)
  case (insert x X)
  show ?case
    using insert
  proof (cases "x = a")
    assume "x = a"
    moreover hence "\<And>x. x \<in> X \<Longrightarrow> f x = 0"
      using insert by fastforce
    ultimately show ?thesis
      using insert by auto
  qed auto
qed auto

lemma sum_two_val:
  assumes "finite X" "a \<in> X" "b \<in> X" "a \<noteq> b" "f a = 1" "f b = 1"
      and "\<And>x. x \<in> X \<Longrightarrow> x \<noteq> a \<Longrightarrow> x \<noteq> b \<Longrightarrow> f x = 0" 
  shows "sum f X = 2"
  using assms
proof (induction X rule: finite_induct)
  case (insert x X)
  have "(x = a \<or> x = b) \<or> (x \<noteq> a \<and> x \<noteq> b)"
    by auto
  then show ?case
  proof (rule disjE)
    assume "x = a \<or> x = b"
    hence "sum f X = 1"
      using insert sum_one_val[of X _ f] by auto
    thus ?thesis
      using insert by fastforce
  next
    assume "x \<noteq> a \<and> x \<noteq> b"
    thus ?thesis
      using insert by auto
  qed
qed auto

lemma finite_sum_add1:
  assumes "finite X" "a \<in> X" "f a = 1 + g a" "\<And>x. x \<in> X \<Longrightarrow> x \<noteq> a \<Longrightarrow> f x = g x"
  shows "sum f X = 1 + sum g X"
  using assms
proof (induction X rule: finite_induct)
  case (insert x X)
  show ?case
  proof cases
    assume [simp]: "x = a"
    hence "sum f X = sum g X"
      using insert sum.cong[of X X f g] by blast
    thus ?case 
      using insert by (auto simp: add.assoc)
  next
    assume "x \<noteq> a"
    hence "sum f (insert x X) = g x + 1 + sum g X"
      using insert by (auto simp: add.assoc)
    also have "... = 1 + g x + sum g X"
      by (auto simp: add.commute)
    also have "... = 1 + sum g (insert x X)"
      using insert by (auto simp: add.assoc)
    finally show ?case .
  qed
qed auto

lemma finite_sum_add2:
  assumes "finite X" "a \<in> X" "b \<in> X" "a \<noteq> b" 
      and "f a = 1 + g a" "f b = 1 + g b" 
      and "\<And>x. x \<in> X \<Longrightarrow> x \<noteq> a \<Longrightarrow> x \<noteq> b \<Longrightarrow> f x = g x"
  shows "sum f X = 2 + sum g X"
  using assms
proof (induction X rule: finite_induct)
  case (insert x X)
  have "(x = a \<or> x = b) \<or> (x \<noteq> a \<and> x \<noteq> b)"
    by auto
  then show ?case
  proof (rule disjE)
    assume "x = a \<or> x = b"
    hence [simp]: "f x = 1 + g x" and [simp]: "sum f X = 1 + sum g X"
      using insert finite_sum_add1[of X _ f g] by auto

    have "sum f (insert x X) = f x + sum f X"
      using insert by auto
    also have "... = 1 + g x + 1 + sum g X"
      using insert by (auto simp: add.assoc)
    also have "... = (1 + 1) + (g x + sum g X)"
      by (metis add.assoc add.commute)
    also have "... = 2 + sum g (insert x X)"
      using insert by (auto simp: add.assoc)
    finally show ?thesis .
  next
    assume "x \<noteq> a \<and> x \<noteq> b"
    thus ?thesis
      using insert group_cancel.add2 by fastforce
  qed
qed auto

(*
  TODO: clean up lemmas \<open>thm finite_sum_add1 finite_sum_add2\<close>. Find more abstract versions.
*)

section \<open>Graph Lemmas (Berge)\<close>

lemma graph_subset:
  assumes "graph_invar E" "E' \<subseteq> E"
  shows "graph_invar E'"
  using assms finite_subset[OF Vs_subset] by auto

lemma Vs_emptyE: 
  assumes graph: "graph_invar E" and "Vs E = {}"
  shows "E = {}"
proof (rule ccontr)
  assume "E \<noteq> {}"
  then obtain e where "e \<in> E"
    by auto
  moreover then obtain u v where "e = {u,v}" "u \<noteq> v"
    using graph by auto
  ultimately have "v \<in> Vs E"
    by (auto intro: vs_member_intro)
  thus "False"
    using assms by auto
qed

lemma Vs_empty_iff: 
  assumes graph: "graph_invar E"
  shows "Vs E = {} \<longleftrightarrow> E = {}"
  using Vs_emptyE[OF graph] by (auto simp: Vs_def)

lemma Vs_empty_empty: "Vs {} = {}"
  using vs_member_elim by force

lemma Vs_union: "Vs (A \<union> B) = Vs A \<union> Vs B"
  unfolding Vs_def by auto

lemma Vs_inter_subset: "Vs (A \<inter> B) \<subseteq> Vs A \<inter> Vs B"
  unfolding Vs_def by auto

lemma Vs_inter_subset1: "Vs (A \<inter> B) \<subseteq> Vs A"
  unfolding Vs_def by auto

lemma Vs_inter_subset2: "Vs (A \<inter> B) \<subseteq> Vs B"
  unfolding Vs_def by auto

lemma Vs_subset_restricted_graph: (* needed in CompleteGraph *)
  fixes V E
  defines "E\<^sub>V \<equiv> {e \<in> E. e \<subseteq> V}"
  shows "Vs E\<^sub>V \<subseteq> V"
proof 
  fix v
  assume "v \<in> Vs E\<^sub>V"
  then obtain e where "e \<in> E\<^sub>V" "v \<in> e"
    by (auto elim: vs_member_elim)
  moreover hence "e \<subseteq> V"
    using assms by auto
  ultimately show "v \<in> V"
    by (auto intro: vs_member_intro)                                         
qed

lemma Vs_inter_disj: 
  assumes "graph_invar E\<^sub>1" "graph_invar E\<^sub>2" "Vs E\<^sub>1 \<inter> Vs E\<^sub>2 = {}" 
  shows "E\<^sub>1 \<inter> E\<^sub>2 = {}"
proof (rule ccontr)
  assume "E\<^sub>1 \<inter> E\<^sub>2 \<noteq> {}"
  then obtain e where "e \<in> E\<^sub>1 \<inter> E\<^sub>2"
    by auto
  moreover then obtain u v where "e = {u,v}"
    using assms by auto
  ultimately have "u \<in> Vs E\<^sub>1" "u \<in> Vs E\<^sub>2"
    by (auto intro: vs_member_intro)
  thus "False"
    using assms by auto
qed

lemma finite_E: "finite (Vs E) \<Longrightarrow> finite E"
  unfolding Vs_def using finite_UnionD by auto

lemma path_distinct_adj:
  assumes "path E P" and graph: "graph_invar E"
  shows "distinct_adj P"
  using assms by (induction P rule: path.induct) auto

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

lemma degree_insert_not_in: "v \<notin> e \<Longrightarrow> degree (insert e E) v = degree E v"
  by (simp add: degree_def)

lemma degree_singleton_edge0: "v \<notin> e \<Longrightarrow> degree {e} v = 0"
  by (auto simp: degree_insert_not_in)

lemma degree_singleton_edge1: "v \<in> e \<Longrightarrow> degree {e} v = 1"
  using one_eSuc by (auto simp: degree_insert[of v e "{}"])

lemmas degree_singleton_edge = degree_singleton_edge0 degree_singleton_edge1

lemma degree_insert_split: "e \<notin> E \<Longrightarrow> degree (insert e E) v = degree E v + degree {e} v"
  using degree_insert plus_1_eSuc 
  by (cases "v \<in> e") (auto simp: degree_insert_not_in degree_singleton_edge)

lemma degree_union:
  assumes "finite E\<^sub>1" "finite E\<^sub>2" "E\<^sub>1 \<inter> E\<^sub>2 = {}"
  shows "degree (E\<^sub>1 \<union> E\<^sub>2) v = degree E\<^sub>1 v + degree E\<^sub>2 v"
  using assms
proof (induction E\<^sub>1 arbitrary: E\<^sub>2 rule: finite_induct)
  case (insert e E\<^sub>1)
  thus ?case
    using degree_insert_split[of e E\<^sub>1] degree_insert_split[of e E\<^sub>2] insert.IH[of "insert e E\<^sub>2"] 
    by auto
qed auto

lemma sum_degree_not_Vs: "sum (degree E) (V - Vs E) = 0"
  using degree_not_Vs[of _ E] by (intro sum.neutral) auto

lemma sum_degree_union:
  assumes "graph_invar E\<^sub>1" "graph_invar E\<^sub>2" "E\<^sub>1 \<inter> E\<^sub>2 = {}"
  shows "sum (degree (E\<^sub>1 \<union> E\<^sub>2)) (Vs (E\<^sub>1 \<union> E\<^sub>2)) = sum (degree E\<^sub>1) (Vs E\<^sub>1) + sum (degree E\<^sub>2) (Vs E\<^sub>2)"
proof -
  have "sum (degree (E\<^sub>1 \<union> E\<^sub>2)) (Vs (E\<^sub>1 \<union> E\<^sub>2)) = sum (degree E\<^sub>1) (Vs E\<^sub>1 \<union> (Vs E\<^sub>2 - Vs E\<^sub>1)) + sum (degree E\<^sub>2) ((Vs E\<^sub>1 - Vs E\<^sub>2) \<union> Vs E\<^sub>2)"
    using assms by (auto simp: Vs_union finite_E degree_union sum.distrib)
  also have "... = sum (degree E\<^sub>1) (Vs E\<^sub>1) + sum (degree E\<^sub>1) (Vs E\<^sub>2 - Vs E\<^sub>1) + sum (degree E\<^sub>2) ((Vs E\<^sub>1 - Vs E\<^sub>2) \<union> Vs E\<^sub>2)"
    using assms by (subst sum.union_disjoint) auto
  also have "... = sum (degree E\<^sub>1) (Vs E\<^sub>1) + sum (degree E\<^sub>2) (Vs E\<^sub>2)"
    using assms by (subst sum.union_disjoint) (auto simp: sum_degree_not_Vs)
  finally show ?thesis .
qed (* TODO: clean up proof! *)

lemma sum_degree_singleton_edge:
  assumes "graph_invar {e}"
  shows "sum (degree {e}) (Vs {e}) = 2"
proof -
  have "sum (degree {e}) (Vs {e}) = 1 + 1"
    using assms by (auto simp: Vs_def sum.insert degree_singleton_edge)
  also have "... = 2"
    using one_add_one .
  finally show ?thesis .
qed

context graph_abs
begin

lemma handshake: "2 * card E = (\<Sum>v \<in> Vs E. degree E v)"
  using finite_E graph
proof (induction E rule: finite_induct)
  case (insert e E)
  moreover have "graph_invar {e}"
    apply (rule graph_subset)
    using insert by blast+
  moreover have "graph_invar E"
    apply (rule graph_subset)
    using insert by blast+
  ultimately have "sum (degree (insert e E)) (Vs (insert e E)) = 2 + sum (degree E) (Vs E)"
    using sum_degree_union[of "{e}"] sum_degree_singleton_edge[OF \<open>graph_invar {e}\<close>] by auto
  also have "... = 2 * card (insert e E)"
    using insert insert.IH[OF \<open>graph_invar E\<close>, symmetric] by (auto simp: numeral_eq_enat)
  finally show ?case by auto
qed (auto simp: Vs_empty_empty sum.empty[of "degree {}"])

lemma sum_degree_even: "even' (\<Sum>v \<in> Vs E. degree E v)"
  using finite_E by (auto simp: handshake[symmetric])

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