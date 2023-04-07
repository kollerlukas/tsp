(* Author: Lukas Koller *)
theory Misc
  imports Main "HOL-Library.Multiset" tsp.Berge
begin

text \<open>This theory contains miscellaneous lemmas and theorems.\<close>

section \<open>List Induction Schemas\<close>

(* function just for the induction schema *)
fun list012 where
  "list012 [] = undefined"
| "list012 [v] = undefined"
| "list012 (u#v#P) = list012 (v#P)"

lemmas list012_induct = list012.induct [case_names Nil Singleton CCons]

(* function just for the induction schema *)
fun list0123 where
  "list0123 [] = undefined"
| "list0123 [v] = undefined"
| "list0123 [u,v] = undefined"
| "list0123 (u#v#w#P) = list0123 (v#w#P)"

lemmas list0123_induct = list0123.induct [case_names Nil Singleton Doubleton CCCons]

(* function just for the induction schema *)
fun list01234 where
  "list01234 [] = undefined"
| "list01234 [v] = undefined"
| "list01234 [u,v] = undefined"
| "list01234 [u,v,w] = undefined"
| "list01234 (u#v#w#x#P) = list01234 (v#w#x#P)"

(* function just for the induction schema *)
fun pair_list where
  "pair_list [] = undefined"
| "pair_list ((x,y)#xs) = pair_list xs"

section \<open>List Lemmas\<close>

lemma hd_singleton: "xs \<noteq> [] \<Longrightarrow> tl xs = [] \<Longrightarrow> xs = [hd xs]"
  by (induction xs) auto

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

lemma set_union_cons: "set (x#xs) = {x} \<union> set xs"
  by auto

lemma set_union_cons_cons: "set (x#y#xs) = {x} \<union> {y} \<union> set xs"
  by auto

lemma hd_last_eq_split:
  assumes "xs \<noteq> []" "hd xs = last xs"
  obtains y where "xs = [y]" | y ys where "xs = y#ys @ [y]"
  using assms
proof (induction xs rule: list012.induct)
  case (3 u v P)
  hence "u#v#P = u#butlast (v#P) @ [u]"
    by (auto simp: append_butlast_last_id)
  thus ?case 
    using 3 by auto
qed auto

lemma hd_last_eq_distinct_set_iff:
  assumes "xs \<noteq> [] \<Longrightarrow> hd xs = last xs"
  shows "distinct (tl xs) \<longleftrightarrow> distinct (butlast xs)"
    and "set (tl xs) = V \<longleftrightarrow> set (butlast xs) = V"
proof -
  consider "xs = []" | y where "xs = [y]" | y ys where "xs = y#ys @ [y]"
    using assms by (auto elim: hd_last_eq_split)
  moreover thus "distinct (tl xs) \<longleftrightarrow> distinct (butlast xs)"
      by cases auto
  ultimately show "set (tl xs) = V \<longleftrightarrow> set (butlast xs) = V"
    by cases auto
qed

lemma list_eq_even_len_gr1:
  assumes "X \<noteq> {}" "even (card X)" "set xs = X"
  shows "length xs > 1"
  using assms by (induction xs rule: list012_induct) auto

lemma set_tl_eq_set:
  assumes "length xs > 1" "distinct (tl xs)" "hd xs = last xs"
  shows "set (tl xs) = set xs"
  using assms by (induction xs rule: list012_induct) auto

lemma list_len_geq2_elim:
  assumes "length xs \<ge> 2"
  obtains x y ys where "xs = x#y#ys"
  using assms by (induction xs rule: list012_induct) auto

lemma list_len_geq2_split_hd_last:
  assumes "length xs \<ge> 2"
  obtains x y ys where "xs = x#ys @ [y]"
  using assms
proof (rule list_len_geq2_elim)
  fix x y ys
  assume "xs = x#y#ys"
  moreover obtain ys' where "y#ys = ys' @ [last (y#ys)]"
    using split_last by blast
  ultimately show ?thesis
    using that by auto
qed

lemma list_split_for_2elems:
  assumes "a \<in> set xs" "b \<in> set xs" "a \<noteq> b"
  obtains xs\<^sub>1 xs\<^sub>2 where "xs = xs\<^sub>1 @ a#xs\<^sub>2" "b \<in> set xs\<^sub>2" | xs\<^sub>1 xs\<^sub>2 where "xs = xs\<^sub>1 @ b#xs\<^sub>2" "a \<in> set xs\<^sub>2"
  using assms 
proof (induction xs arbitrary: a b thesis)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then consider "x = a" "b \<in> set xs" | "x = b" "a \<in> set xs" | "a \<in> set xs" "b \<in> set xs"
    by auto
  thus ?case 
  proof cases
    assume "x = a" "b \<in> set xs"
    thus ?case
      using Cons by fastforce
  next
    assume "x = b" "a \<in> set xs"
    thus ?case
      using Cons by fastforce
  next
    assume "a \<in> set xs" "b \<in> set xs"
    then consider xs\<^sub>1 xs\<^sub>2 where "xs = xs\<^sub>1 @ a#xs\<^sub>2" "b \<in> set xs\<^sub>2"
      | xs\<^sub>1 xs\<^sub>2 where "xs = xs\<^sub>1 @ b#xs\<^sub>2" "a \<in> set xs\<^sub>2"
      using Cons by blast
    thus ?case
    proof cases
      fix xs\<^sub>1 xs\<^sub>2
      assume "xs = xs\<^sub>1 @ a#xs\<^sub>2" "b \<in> set xs\<^sub>2"
      moreover hence "x#xs = (x#xs\<^sub>1) @ a#xs\<^sub>2"
        by auto
      ultimately show ?case
        using Cons by blast
    next
      fix xs\<^sub>1 xs\<^sub>2
      assume "xs = xs\<^sub>1 @ b#xs\<^sub>2" "a \<in> set xs\<^sub>2"
      moreover hence "x#xs = (x#xs\<^sub>1) @ b#xs\<^sub>2"
        by auto
      ultimately show ?case
        using Cons by blast
    qed
  qed
qed

lemma append_tl_butlast_eq:
  assumes "xs \<noteq> []" "ys \<noteq> []" "last xs = x" "hd ys = x"
  shows "xs @ tl ys = butlast xs @ ys"
  using assms by (induction xs rule: list012.induct) auto

lemma map_map: "map (f o g) xs = map f (map g xs)"
  by (induction xs) auto

lemma fold_neq_find:
  assumes "fold f xs a \<noteq> a"
  obtains x where "x \<in> List.set xs" "f x a \<noteq> a"
  using assms 
proof (induction xs arbitrary: a)
  case (Cons x xs)
  then show ?case 
    by (cases "f x a = a") auto
qed auto

lemma fold_enat_min_leq_acc: "fold (\<lambda>x a. min (g x) a) xs (a::enat) \<le> a" (* TODO: less restrictive type *)
proof (induction xs arbitrary: a)
  case (Cons x xs)
  have "fold (\<lambda>x a. min (g x) a) (x#xs) a = fold (\<lambda>x a. min (g x) a) xs (min (g x) a)"
    by auto
  also have "... \<le> min (g x) a"
    using Cons by fastforce
  thus ?case 
    by auto
qed auto

lemma fold_enat_min_leq_member: 
  assumes "x \<in> set xs"
  shows "fold (\<lambda>x a. min (g x) a) xs (a::enat) \<le> min (g x) a"
  using assms
proof (induction xs arbitrary: a rule: list012.induct)
  case 1
  then show ?case by auto
next
  case (2 y)
  then show ?case by auto
next
  case (3 y z xs)
  show ?case
  proof cases
    assume "x = y"
    hence "fold (\<lambda>x a. min (g x) a) (y#z#xs) a = fold (\<lambda>x a. min (g x) a) (z#xs) (min (g x) a)"
      by auto
    also have "... \<le> min (g x) a"
      by (intro fold_enat_min_leq_acc)
    finally show ?thesis .
  next
    assume "x \<noteq> y"
    have "fold (\<lambda>x a. min (g x) a) (y#z#xs) a = fold (\<lambda>x a. min (g x) a) (z#xs) (min (g y) a)"
      by auto
    also have "... \<le> min (g x) (min (g y) a)"
      using \<open>x \<noteq> y\<close> 3 by (intro "3.IH") auto  
    also have "... \<le> min (g x) a"
      using min.cobounded2 min.mono by blast
    finally show ?thesis .
  qed
qed

(* lemma fold_enat_min:
  assumes "(a::enat) < \<infinity>"
  shows "fold (\<lambda>x a. min (g x) a) xs a < \<infinity>" (is "fold ?f xs a < \<infinity>")
  using assms
proof (induction xs arbitrary: a)
  case (Cons x xs)
  thus ?case 
    by (cases "g x") auto
qed auto *)

lemma fold_concat_map: "fold (\<lambda>x a. a @ f x) xs a = a @ concat (map f xs)"
  by (induction xs arbitrary: a) auto

lemma concat_map_disjoint:
  assumes "x \<notin> set xs" "\<And>y. y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> set (f x) \<inter> set (f y) = {}"
  shows "set (f x) \<inter> set (concat (map f xs)) = {}"
  using assms by (induction xs) auto

lemma distinct_concat_map:
  assumes "distinct xs" "\<And>x. x \<in> set xs \<Longrightarrow> distinct (f x)" 
    "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> set (f x) \<inter> set (f y) = {}"
  shows "distinct (concat (map f xs))"
  using assms by (induction xs) (auto intro!: concat_map_disjoint) 

lemma hd_concat_map_elim:
  assumes "\<exists>x \<in> set xs. f x \<noteq> []"
  obtains y where "y \<in> set xs" "f y \<noteq> []" "hd (concat (map f xs)) = hd (f y)"
  using assms
proof (induction xs arbitrary: thesis)
  case (Cons x xs)
  consider "f x = []" | "f x \<noteq> []"
    by auto
  then show ?case
    using Cons by cases auto
qed auto

lemma last_concat_map_elim:
  assumes "\<exists>x \<in> set xs. f x \<noteq> []"
  obtains y where "y \<in> set xs" "f y \<noteq> []" "last (concat (map f xs)) = last (f y)"
proof (rule hd_concat_map_elim)
  show "\<exists>x \<in> set (rev xs). (rev o f) x \<noteq> []"
    using assms by auto
  fix y
  assume "y \<in> set (rev xs)" "(rev o f) y \<noteq> []" 
    "hd (concat (map (rev \<circ> f) (rev xs))) = hd ((rev \<circ> f) y)"
  moreover hence "last (concat (map f xs)) = last (f y)"
    by (simp add: hd_rev[symmetric] rev_concat rev_map)
  ultimately show ?thesis
    using that by auto
qed

lemma last_concat_map:
  assumes "xs \<noteq> []" "\<And>x. x \<in> set xs \<Longrightarrow> f x \<noteq> []"
  shows "last (concat (map f xs)) = last (f (last xs))"
  using assms by (induction xs) auto

lemma concat_filter_empty: "concat (filter (\<lambda>x. x \<noteq> []) xs) = concat xs"
  by (induction xs) auto

lemma concat_map_filter_empty: 
  assumes "\<And>x. \<not> P x \<Longrightarrow> f x = []"
  shows "concat (map f (filter P xs)) = concat (map f xs) "
  using assms by (induction xs) auto

lemma last_filter_non_nil:
  assumes "xs \<noteq> []" "last xs = x" "f x"
  shows "filter f xs \<noteq> [] \<and> last (filter f xs) = x"
  using assms by (induction xs rule: list012_induct) auto

lemma last_filter: "xs \<noteq> [] \<Longrightarrow> last xs = x \<Longrightarrow> f x \<Longrightarrow> last (filter f xs) = x"
  using last_filter_non_nil by fastforce

subsection \<open>Repeated Elements in Lists\<close>

lemma distinct_distinct_adj: "distinct xs \<Longrightarrow> distinct_adj xs"
  by (simp add: distinct_adj_altdef distinct_tl remdups_adj_distinct)

(* lemma card_leq_len_remdups_adj: "card (set xs) \<le> length (remdups_adj xs)"
proof (induction xs rule: remdups_adj.induct)
  case (3 x y xs)
  consider "x = y" | "x \<noteq> y"
    by auto
  thus ?case
  proof cases
    assume "x = y"
    thus ?thesis
      using 3 by auto
  next
    assume "x \<noteq> y"
    hence "set (x#y#xs) = {x} \<union> set (y#xs)"
      by auto
    hence "card (set (x#y#xs)) = card ({x} \<union> set (y#xs))"
      by auto
    also have "... \<le> card {x} + card (set (y#xs))"
      by (intro card_Un_le)
    also have "... \<le> length (remdups_adj ((x#y#xs)))"
      using 3 \<open>x \<noteq> y\<close> by auto
    finally show ?thesis
      by auto
  qed
qed auto

lemma len_remdups_append: "length (remdups_adj xs) \<le> length (remdups_adj (xs @ [x]))"
  by (induction xs rule: remdups_adj.induct) auto

lemma cycle_card_leq_len_remdups_adj: "card (set xs) \<le> length (remdups_adj (xs @ [hd xs]))"
proof -
  have "card (set xs) \<le> length (remdups_adj xs)"
    using card_leq_len_remdups_adj by auto
  also have "... \<le> length (remdups_adj (xs @ [hd xs]))"
    by (intro len_remdups_append)
  finally show ?thesis
    by auto
qed *)

subsection \<open>Even-Indexed Elements in Lists\<close>

fun even_elems :: "'a list \<Rightarrow> 'a list" where
  "even_elems [] = []" 
| "even_elems [x] = [x]" 
| "even_elems (x#y#xs) = x#even_elems xs"

value "even_elems [0::nat,1,2,3,4,5,6,7,8,9,10]"

lemma even_elems_tl: "even_elems (x#xs) = x#even_elems (tl xs)"
  by (induction xs rule: even_elems.induct) auto

lemma even_elems_subset: "set (even_elems xs) \<subseteq> set xs"
  by (induction xs rule: even_elems.induct) auto

lemma even_elems_distinct: "distinct xs \<Longrightarrow> distinct (even_elems xs)"
proof (induction xs rule: even_elems.induct)
  case (3 x y xs)
  hence "distinct (even_elems xs)"
    by auto
  moreover hence "x \<notin> set (even_elems xs)"
    using 3 even_elems_subset by fastforce
  ultimately show ?case 
    by auto
qed auto

lemma even_elems_mset_union: "mset (even_elems (tl xs)) + mset (even_elems xs) = mset xs"
  by (induction xs rule: even_elems.induct) (auto simp: even_elems_tl)

lemma even_elems_butlast: "even (length xs) \<longleftrightarrow> even_elems xs = even_elems (butlast xs)"
  by (induction xs rule: even_elems.induct) auto

lemma even_elem_append:
  assumes "even (length xs)" "even (length ys)"
  shows "even_elems (xs @ ys) = even_elems xs @ even_elems ys"
  using assms by (induction xs arbitrary: ys rule: even_elems.induct) auto

section \<open>(Finite) Set Lemmas\<close>

lemma mem_not_empty: "x \<in> A \<Longrightarrow> A \<noteq> {}"
  by auto

lemma insert_union_subset: "A\<^sub>1 \<union> A\<^sub>2 \<subseteq> B \<Longrightarrow> a \<in> B \<Longrightarrow> insert a A\<^sub>1 \<union> A\<^sub>2 \<subseteq> B"
  by auto

lemma inter_emptyI:
  assumes "\<And>x. x \<in> B \<Longrightarrow> x \<notin> A"
  shows "A \<inter> B = {}"
  using assms by blast

lemma card_neq_1_obtain_mem:
  assumes "card A \<noteq> 1" "a \<in> A"
  obtains b where "b \<in> A" "a \<noteq> b"
proof -
  consider "infinite A" | "card A > 1"
    using assms by (metis One_nat_def Suc_lessI card_gt_0_iff empty_iff)
  thus ?thesis
  proof cases 
    assume "infinite A"
    thus ?thesis
      using that by (metis assms(1) finite.emptyI is_singletonI' is_singleton_altdef)
  next
    assume "card A > 1"
    thus ?thesis
      using assms
      by (metis One_nat_def card.infinite card_le_Suc0_iff_eq leD not_one_less_zero that)
  qed
qed (* TODO: clean up proof! *)

lemma set012_split: 
  assumes "finite F"
  obtains "F = {}"
  | x where "F = {x}"
  | x y F' where "F = {x,y} \<union> F'" "x \<notin> F'" "y \<notin> F'" "x \<noteq> y"
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

lemma set12_split: 
  assumes "finite F" "x \<in> F"
  obtains x where "F = {x}"
  | x y F' where "F = {x,y} \<union> F'" "x \<notin> F'" "y \<notin> F'" "x \<noteq> y"
  using assms by (elim set012_split) auto

text \<open>Induction schema that adds two new elements to a finite set.\<close>
lemma finite2_induct [consumes 1, case_names empty singleton insert2]:
  assumes "finite F"
  assumes empty: "P {}"
      and singleton: "\<And>x. P {x}"
      and insert2: "\<And>x y F. finite F \<Longrightarrow> x \<notin> F \<Longrightarrow> y \<notin> F \<Longrightarrow> x \<noteq> y \<Longrightarrow> P F \<Longrightarrow> P ({x,y} \<union> F)"
  shows "P F"
  using assms
proof (induction F rule: finite_psubset_induct)
  case (psubset F)
  then consider "F = {}" | x where "F = {x}" 
    | x y F' where "F = {x,y} \<union> F'" "x \<notin> F'" "y \<notin> F'" "x \<noteq> y"
    by (elim set012_split)
  thus ?case 
    using psubset
  proof cases
    fix x y F'
    assume "F = {x,y} \<union> F'" "x \<notin> F'" "y \<notin> F'" "x \<noteq> y"
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

lemma finite_even_card:
  assumes "finite X" "x \<notin> X" "y \<notin> X" "x \<noteq> y" 
  shows "even (card ({x,y} \<union> X)) \<longleftrightarrow> even (card X)"
  using assms by auto

lemma finite_even_cardI:
  assumes "finite X" "x \<notin> X" "y \<notin> X" "x \<noteq> y" "even (card ({x,y} \<union> X))"
  shows "even (card X)"
  using assms by auto

lemma finite_even_cardI2:
  assumes "finite X" "x \<notin> X" "y \<notin> X" "x \<noteq> y" "even (card X)"
  shows "even (card ({x,y} \<union> X))"
  using assms by auto

lemma finite_card_geq2: "finite A \<Longrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> A \<and> a \<noteq> b) \<longleftrightarrow> card A \<ge> 2"
  by (induction A rule: finite2_induct) auto

lemma card'_leq: "card' A \<le> enat k \<Longrightarrow> card A \<le> k"
  by (metis card'_finite_enat enat_ile enat_ord_simps(1))

section \<open>Tuple Set Lemmas\<close>

lemma irrefl_subset: "irrefl B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> irrefl A"
  unfolding irrefl_def by auto

section \<open>Metric Lemmas\<close>

lemma mult_2: "(x::'b::{ordered_semiring_0,semiring_numeral}) + x = 2 * x"
  by (simp add: semiring_numeral_class.mult_2)

lemma mult_3: "2 * (x::'b::{ordered_semiring_0,semiring_numeral}) + x = 3 * x"
  by (metis distrib_right mult_numeral_1 numeral_Bit1 numeral_One one_add_one) (* TODO: clean up! *)

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

lemma even'_enat: 
  assumes "even' a"
  obtains a' where "enat a' = a"
  using assms by (cases a) auto

lemma enat_addE:
  assumes "enat c = a + b"
  obtains x y where "enat x = a" "enat y = b"
  by (metis assms not_enat_eq plus_enat_simps)

lemma even'_addI1:
  assumes "even' a" "even' b"
  shows "even' (a + b)"
proof -
  obtain x where "enat x = a"
    using assms by (auto elim: even'_enat)
  moreover hence "even x"
    using assms by auto
  moreover obtain y where "enat y = b"
    using assms by (auto elim: even'_enat)
  moreover hence "even y"
    using assms by auto
  ultimately show ?thesis
    by auto
qed

lemma even'_addI2:
  assumes "\<not> even' a" "a \<noteq> \<infinity>" "\<not> even' b" "b \<noteq> \<infinity>" 
  shows "even' (a + b)"
proof -
  obtain x where "enat x = a"
    using assms by (auto elim: even'_enat)
  moreover hence "odd x"
    using assms by auto
  moreover obtain y where "enat y = b"
    using assms by (auto elim: even'_enat)
  moreover hence "odd y"
    using assms by auto
  ultimately show ?thesis
    by auto
qed

lemma even'_addE1:
  assumes "even' (a + b)" "even' b"
  shows "even' a"
proof -
  obtain c where "enat c = a + b"
    using assms by (auto elim: even'_enat)
  moreover hence "even c"
    using assms by (cases "a+b") auto
  moreover obtain x y where "enat x = a" "enat y = b"
    using assms calculation by (auto elim: enat_addE)
  ultimately show ?thesis
    using assms by auto
qed

lemma even'_addE2:
  assumes "even' (a + b)" "even' a"
  shows "even' b"
proof -
  obtain c where "enat c = a + b"
    using assms by (auto elim: even'_enat)
  moreover hence "even c"
    using assms by (cases "a+b") auto
  moreover obtain x y where "enat x = a" "enat y = b"
    using assms calculation by (auto elim: enat_addE)
  ultimately show ?thesis
    using assms by auto
qed

lemma even'_addE3:
  assumes "even' (a + b)" "\<not> even' b"
  shows "\<not> even' a"
proof -
  obtain c where "enat c = a + b"
    using assms by (auto elim: even'_enat)
  moreover hence "even c"
    using assms by (cases "a+b") auto
  moreover obtain x y where "enat x = a" "enat y = b"
    using assms calculation by (auto elim: enat_addE)
  ultimately show ?thesis
    using assms by auto
qed

lemma even'_addE4:
  assumes "even' (a + b)" "\<not> even' a"
  shows "\<not> even' b"
proof -
  obtain c where "enat c = a + b"
    using assms by (auto elim: even'_enat)
  moreover hence "even c"
    using assms by (cases "a+b") auto
  moreover obtain x y where "enat x = a" "enat y = b"
    using assms calculation by (auto elim: enat_addE)
  ultimately show ?thesis
    using assms by auto
qed

lemma not_even_add1:
  assumes "\<not> even' a" "a \<noteq> \<infinity>"
  shows "even' (a + 1)"
  using assms by (cases a) auto

section \<open>Sum Lemmas\<close>

lemma finite_sum_neq_inf:
  assumes "finite X" "\<And>x. x \<in> X \<Longrightarrow> f x \<noteq> (\<infinity>::enat)"
  shows "sum f X \<noteq> (\<infinity>::enat)"
  using assms by (induction X rule: finite_induct) (auto simp: plus_eq_infty_iff_enat)

lemma even_sum_of_odd_vals_iff:
  assumes "finite X" "\<And>x. x \<in> X \<Longrightarrow> \<not> even' (f x)" "\<And>x. x \<in> X \<Longrightarrow> f x \<noteq> (\<infinity>::enat)"
  shows "even' (sum f X) \<longleftrightarrow> even' (card X)"
  using assms 
proof (induction X rule: finite_induct)
  case (insert x X)
  show ?case 
  proof
    assume "even' (sum f (insert x X))"
    thus "even' (enat (card (insert x X)))"
      using insert by (auto simp: even'_addE4)
  next
    assume "even' (enat (card (insert x X)))"
    hence "\<not> even' (sum f X)"
      using insert by (auto simp: even'_addE4)
    thus "even' (sum f (insert x X))"
      using insert finite_sum_neq_inf[of X f] by (auto simp: even'_addI2)
  qed
qed auto

lemma finite_even_sum:
  assumes "finite X" "\<And>x. x \<in> X \<Longrightarrow> even' (f x)"
  shows "even' (sum f X)"
  using assms by (induction X rule: finite_induct) (auto intro: even'_addI1)

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

lemma sum_list_const: 
  fixes f :: "'a \<Rightarrow> int"
  shows "(\<And>x. x \<in> set xs \<Longrightarrow> f x = k) \<Longrightarrow> (\<Sum>x\<leftarrow>xs. f x) = length xs * k"
  by (induction xs) (auto simp add: int_distrib mult.commute)

lemma sum_const: 
  fixes f :: "'a \<Rightarrow> int"
  assumes "finite X" "\<And>x. x \<in> X \<Longrightarrow> f x = k"
  shows "(\<Sum>x \<in> X. f x) = card X * k"
  using assms by (induction X rule: finite_induct) (auto simp add: int_distrib mult.commute)

(* lemma sum_list_const: 
  fixes f :: "'a \<Rightarrow> int"
  shows "(\<And>x. x \<in> set xs \<Longrightarrow> f x = k) \<Longrightarrow> (\<Sum>x\<leftarrow>xs. f x) = length xs * k"
  by (induction xs) (auto simp add: int_distrib mult.commute)

lemma sum_list_subf:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> g x \<le> f x"
  shows "(\<Sum>x\<leftarrow>xs. (f::'a \<Rightarrow> nat) x - g x) \<le> (\<Sum>x\<leftarrow>xs. f x) - (\<Sum>x\<leftarrow>xs. g x)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  hence "(\<Sum>x\<leftarrow>x#xs. f x - g x) \<le> (\<Sum>x\<leftarrow>xs. f x) - (\<Sum>x\<leftarrow>xs. g x) + f x - g x"
    using Cons by auto
  also have "... \<le> (\<Sum>x\<leftarrow>x#xs. f x) - (\<Sum>x\<leftarrow>x#xs. g x)"
    using Cons by (auto simp add: sum_list_mono)
  finally show ?case
    by auto
qed *)

(* lemma
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> g x \<le> f x"
  shows "(\<Sum>x\<leftarrow>xs. (f::'a \<Rightarrow> nat) x - g x) + (\<Sum>x\<leftarrow>xs. g x) \<le> (\<Sum>x\<leftarrow>xs. f x)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  have "(\<Sum>x\<leftarrow>x#xs. f x - g x) + (\<Sum>x\<leftarrow>x#xs. g x) \<le> (\<Sum>x\<leftarrow>xs. f x - g x) + (f x - g x) + (\<Sum>x\<leftarrow>xs. g x) + g x"
    by auto
  also have "... \<le> (\<Sum>x\<leftarrow>xs. f x - g x) + (\<Sum>x\<leftarrow>xs. g x) + g x + (f x - g x)"
    by auto
  also have "... \<le> (\<Sum>x\<leftarrow>xs. f x) + g x + (f x - g x)"
    using Cons by auto
  also have "... \<le> (\<Sum>x\<leftarrow>xs. f x) + f x"
    by auto
  also have "... \<le> (\<Sum>x\<leftarrow>x#xs. f x)"
    by auto
  finally show ?case
    by auto
qed *)

lemma finite_sum_card:
  assumes "finite X" "\<And>x. x \<in> X \<Longrightarrow> finite (f x)"
      and "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<noteq> y \<Longrightarrow> f x \<inter> f y = {}"
  shows "(\<Sum>x \<in> X. card (f x)) = card (\<Union> (f ` X))"
  using assms
proof (induction X rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert x X)
  hence "f x \<inter> \<Union> (f ` X) = {}"
  proof (induction X rule: finite_induct)
    case (insert y X)
    hence "f x \<inter> \<Union> (f ` (insert y X)) = f x \<inter> \<Union> (insert (f y)  (f ` X))"
      by auto
    also have "... = (f x \<inter> f y) \<union> (f x \<inter> \<Union> (f ` X))"
      by auto
    also have "... = {}"
      using insert by auto
    finally show ?case .
  qed auto
  thus ?case 
    using insert by (auto simp add: card_Un_disjoint)
qed

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

lemma Vs_singleton: "Vs {e} = e"
  unfolding Vs_def by auto

lemma Vs_union: "Vs (A \<union> B) = Vs A \<union> Vs B"
  unfolding Vs_def by auto

lemma Vs_inter_subset: "Vs (A \<inter> B) \<subseteq> Vs A \<inter> Vs B"
  unfolding Vs_def by auto

lemma Vs_inter_subset1: "Vs (A \<inter> B) \<subseteq> Vs A"
  unfolding Vs_def by auto

lemma Vs_inter_subset2: "Vs (A \<inter> B) \<subseteq> Vs B"
  unfolding Vs_def by auto

lemma complete_Vs_subset: "Vs {{u,v} | u v. u \<in> V \<and> v \<in> V \<and> u \<noteq> v} \<subseteq> V"
  by (auto simp: Vs_def)

lemma edge_member_elim:
  assumes "graph_invar E" and "v \<in> e" "e \<in> E"
  obtains u where "e = {u,v}"
proof -
  obtain u' v' where "e = {u',v'}"
    using assms by auto
  then show ?thesis
    using that assms by auto
qed

lemma vs_member_elim2:
  assumes "graph_invar E" and "v \<in> Vs E" 
  obtains u where "{u,v} \<in> E"
proof -
  obtain e where "v \<in> e" "e \<in> E"
    using assms by (auto elim: vs_member_elim)
  moreover then obtain u where "e = {u,v}"
    using assms by (fastforce elim: edge_member_elim)
  ultimately show ?thesis
    using that by auto
qed

lemma Vs_insert: "Vs (insert e E) = e \<union> Vs E"
  unfolding Vs_def by auto

lemma finite_E: "finite (Vs E) \<Longrightarrow> finite E"
  unfolding Vs_def using finite_UnionD by auto

lemma finite_VsI:
  assumes "finite E" "\<And>e. e \<in> E \<Longrightarrow> finite e"
  shows "finite (Vs E)"
  unfolding Vs_def using assms by auto

lemma graph_invarI2: 
  assumes "finite E" "\<And>e. e \<in> E \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<noteq> v" 
  shows "graph_invar E"
  using assms by (auto intro: finite_VsI)

lemma graph_Un:
  assumes "finite A" "\<And>a. a \<in> A \<Longrightarrow> graph_invar a" 
  shows "graph_invar (\<Union> A)"
  using assms
proof (induction A rule: finite_induct)
  case empty
  then show ?case 
    by (auto simp: Vs_empty_empty)
next
  case (insert a A)
  hence "graph_invar (\<Union> A)"
    by (intro insert.IH) fastforce
  moreover have "graph_invar a"
    using insert.prems by blast
  ultimately have "finite (Vs (\<Union> (insert a A)))"
    by (auto simp: Union_insert Vs_union)
  thus ?case 
    using insert.prems by fastforce
qed

lemma vs_not_member: "v \<notin> Vs E \<Longrightarrow> (\<And>e. e \<in> E \<Longrightarrow> v \<notin> e)"
  using vs_member by auto

lemma graph_neq_vertex_aux: 
  assumes "v \<in> Vs E\<^sub>1" "v \<notin> Vs E\<^sub>2" 
  shows "E\<^sub>1 \<noteq> E\<^sub>2"
proof -
  obtain e where "v \<in> e" "e \<in> E\<^sub>1"
    using assms by (elim vs_member_elim)
  moreover have "\<And>e. e \<in> E\<^sub>2 \<Longrightarrow> v \<notin> e"
    using assms(2) by (rule vs_not_member)
  ultimately show ?thesis
    by auto
qed

lemma graph_neq_vertex: 
  assumes "Vs E\<^sub>1 \<noteq> Vs E\<^sub>2" 
  shows "E\<^sub>1 \<noteq> E\<^sub>2"
proof -
  consider v where "v \<in> Vs E\<^sub>1" "v \<notin> Vs E\<^sub>2" | v where "v \<in> Vs E\<^sub>2" "v \<notin> Vs E\<^sub>1"
    using assms by auto
  thus ?thesis
    by (auto intro: graph_neq_vertex_aux)
qed

context graph_abs
begin

lemma finite_vertices: "V \<subseteq> Vs E \<Longrightarrow> finite V"
  using graph finite_subset by auto

end

lemma edge_is_path: "{u,v} \<in> E \<Longrightarrow> path E [u,v]"
  by (auto intro: path.intros)

lemma path_intro2:
  assumes "set (edges_of_path P) \<subseteq> E" "set P \<subseteq> Vs E"
  shows "path E P"
  using assms by (induction P rule: edges_of_path.induct) (auto intro: path.intros)

lemma path_distinct_adj:
  assumes graph: "graph_invar E" 
      and "path E P" 
  shows "distinct_adj P"
  using assms(2) assms(1) by (induction P rule: path.induct) auto

lemma path_subset_singleton:
  assumes "path X [v]" "v \<in> Vs X'"
  shows "path X' [v]"
  using assms by (auto intro: path.intros)

lemma path_cons: "path E (v#P) \<Longrightarrow> path E P"
  by (auto elim: path.cases)

lemma butlast_path_is_path: "path E P \<Longrightarrow> path E (butlast P)"
  by (induction P rule: path.induct) auto

lemma path_Vs_subset: "path X P \<Longrightarrow> set P \<subseteq> Vs X"
  using mem_path_Vs[of X] by blast

lemma path_drop: "path X P \<Longrightarrow> path X (drop i P)"
  using path_suff[of X "take i P" "drop i P"] append_take_drop_id[of i P] by auto

lemma path_take: "path X P \<Longrightarrow> path X (take i P)"
  using path_pref[of X "take i P" "drop i P"] append_take_drop_id[of i P] by auto

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

lemma edges_of_path_butlast: "edges_of_path (butlast P) = butlast (edges_of_path P)"
  by (induction P rule: list0123.induct) auto

lemma edges_of_path_cons_subset: "set (edges_of_path P) \<subseteq> set (edges_of_path (v#P))"
  by (induction P rule: edges_of_path.induct) auto

lemma edge_of_path_subset_of_vpath: "e \<in> set (edges_of_path P) \<Longrightarrow> e \<subseteq> set P"
  by (induction P rule: edges_of_path.induct) auto

abbreviation "even_edges P \<equiv> even_elems (edges_of_path P)"

lemma even_edges_of_path: "even_edges (u#v#P) = {u,v}#even_edges P"
  by (induction P rule: edges_of_path.induct) auto

lemma path_even_edges_subset: "path E P \<Longrightarrow> set (even_edges P) \<subseteq> E"
  using path_edges_subset even_elems_subset by fastforce

lemma Vs_even_edges_subset: "Vs (set (even_edges P)) \<subseteq> set P"
proof -
  have "Vs (set (even_edges P)) \<subseteq> Vs (set (edges_of_path P))"
    by (auto simp: Vs_subset[OF even_elems_subset])
  also have "... \<subseteq> set P"
    by (auto simp: edges_of_path_Vs)
  finally show ?thesis .
qed

lemma Vs_even_edges_eq:
  assumes "even (length P)"
  shows "Vs (set (even_edges P)) = set P"
  using assms
proof (induction P rule: even_elems.induct)
  case (3 u v P)
  have "Vs (set (even_edges (u#v#P))) = Vs ({{u,v}} \<union> set (even_edges P))"
    by (subst even_edges_of_path) auto
  also have "... = Vs {{u,v}} \<union> Vs (set (even_edges P))"
    by (auto simp: Vs_union[symmetric])
  also have "... = set (u#v#P)"
    using 3 by (auto simp: Vs_singleton)
  finally show ?case .
qed (auto simp: Vs_empty_empty)

lemma matching_even_edges:
  assumes "distinct P"
  shows "matching (set (even_edges P))"
  using assms
proof (induction P rule: even_elems.induct)
  case (3 u v P)
  hence "{u,v} \<inter> Vs (set (even_edges P)) = {}"
    using Vs_even_edges_subset by fastforce
  hence "matching (insert {u,v} (set (even_edges P)))"
    using 3 by (auto intro: matching_insert)
  thus ?case 
    by (subst even_edges_of_path) auto
qed (auto simp: matching_def)

lemma Vs_even_edges_permute:
  "odd (length P) \<Longrightarrow> Vs (set (even_edges (u#v#w#P))) = Vs (set (even_edges (w#u#v#P)))"
  by (induction P rule: even_elems.induct) (auto simp: Vs_def Vs_union Vs_union[symmetric])

lemma Vs_even_edges_hd_last_eq:
  assumes "odd (length P)"
  shows "Vs (set (even_edges (x#P))) = Vs (set (even_edges (P @ [x])))"
  using assms
proof (induction P rule: even_elems.induct)
  case (3 u v P)
  hence "Vs (set (even_edges (x#u#v#P))) = Vs (set (even_edges (u#v#x#P)))"
    by (intro Vs_even_edges_permute[symmetric]) auto
  also have "... = Vs {{u,v}} \<union> Vs (set (even_edges (x#P)))"
    by (auto simp: Vs_union[symmetric])
  also have "... = Vs (set ({u,v}#even_edges (P @ [x])))"
    using 3 by (auto simp: Vs_union[symmetric])
  also have "... = Vs (set (even_edges (u#v#P @ [x])))"
    by (auto simp: even_edges_of_path[symmetric])
  finally show ?case by auto
qed (auto simp: insert_commute)

lemma even_edges_mset_union:
  assumes "odd (length P)"
  shows "mset (even_edges (tl P)) + mset (even_edges (butlast P)) = mset (edges_of_path P)" 
  (is "mset ?E\<^sub>1 + mset ?E\<^sub>2 = mset ?E")
proof -
  have "even (length (edges_of_path P))"
    using assms edges_of_path_length by (metis even_diff_nat even_plus_one_iff)
  hence "mset ?E\<^sub>1 + mset ?E\<^sub>2 = mset (even_elems (tl (edges_of_path P))) + mset (even_edges P)"
    by (auto simp: edges_of_path_tl edges_of_path_butlast even_elems_butlast)
  also have "... = mset (edges_of_path P)"
    by (auto simp: even_elems_mset_union)
  finally show ?thesis .
qed

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
  "P\<^sub>1 \<noteq> [] \<Longrightarrow> edges_of_path (P\<^sub>1 @ u#P\<^sub>2) = edges_of_path P\<^sub>1 @ [{last P\<^sub>1,u}] @ edges_of_path (u#P\<^sub>2)"
  by (induction P\<^sub>1 rule: list012.induct) auto

lemma path_is_walk: 
  assumes "path E P" "P \<noteq> []"
  obtains u v where "walk_betw E u P v"
  using assms by (auto intro: nonempty_path_walk_between)

lemma walk_on_path:
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
  using assms walk_on_path by blast

lemma path_swap:
  assumes "P\<^sub>1 \<noteq> []" "P\<^sub>2 \<noteq> []" "path E (P\<^sub>1 @ P\<^sub>2)" "hd P\<^sub>1 = last P\<^sub>2"
  shows "path E (P\<^sub>2 @ tl P\<^sub>1)"
  using assms path_suff[of E P\<^sub>1 P\<^sub>2] path_pref[of E P\<^sub>1 P\<^sub>2] path_concat[of E P\<^sub>2 P\<^sub>1] by auto

lemma path_last_edge: "path E (u#P @ [v]) \<Longrightarrow> {last (u#P),v} \<in> E"
  by (induction P arbitrary: u) auto

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

lemma mset_edges_of_path_rotate:
  "mset (edges_of_path (u#P\<^sub>1 @ v#P\<^sub>2 @ [u])) = mset (edges_of_path (v#P\<^sub>2 @ u#P\<^sub>1 @ [v]))"
  (is "mset (edges_of_path ?P) = mset (edges_of_path ?P')")
proof -
  have "mset (edges_of_path ?P) 
    = mset (edges_of_path (u#P\<^sub>1)) + {#{last (u#P\<^sub>1),v}#} + mset (edges_of_path (v#P\<^sub>2 @ [u]))"
    using edges_of_path_append[of "u#P\<^sub>1" v "P\<^sub>2 @ [u]"] by auto
  also have "... = mset (edges_of_path (u#P\<^sub>1)) + {#{last (u#P\<^sub>1),v}#} 
    + mset (edges_of_path (v#P\<^sub>2)) + {#{last (v#P\<^sub>2),u}#}"
    using edges_of_path_append[of "v#P\<^sub>2" u "[]"] by auto  
  also have 
    "... = mset (edges_of_path (v#P\<^sub>2)) + {#{last (v#P\<^sub>2),u}#} + mset (edges_of_path (u#P\<^sub>1 @ [v]))"
    using edges_of_path_append[of "u#P\<^sub>1" v "[]"] by auto
  also have "... = mset (edges_of_path ?P')"
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

context graph_abs
begin

lemma walk_path_split: (* TODO: remove assumption *)
  assumes (* "graph_invar E" *) "walk_betw E u P u" "v \<in> set P" "u \<noteq> v"
  obtains P\<^sub>1 P\<^sub>2 where "P = u#P\<^sub>1 @ v#P\<^sub>2 @ [u]"
proof -
  have [simp]: "hd P = u" "last P = u" and "P \<noteq> []"
    using assms by (auto elim: nonempty_path_walk_between)
  then obtain P' where "P = u#P'"
    by (auto elim: split_hd)
  moreover hence "P' \<noteq> []"
    using assms by auto
  ultimately obtain P'' where [simp]: "P = u#P'' @ [u]"
    using \<open>last P = u\<close> by (auto elim: split_last[of P'])
  hence "v \<in> set P''"
    using assms by auto
  then obtain P\<^sub>1 P\<^sub>2 where "P = u#P\<^sub>1 @ v#P\<^sub>2 @ [u]"
    using split_list[of v P''] by auto
  thus ?thesis
    using that by auto
qed

lemma walk_rotateE:
  assumes (* "graph_invar E" *)"walk_betw E u P u" "v \<in> set P"
  obtains P' where "walk_betw E v P' v" "set (edges_of_path P) = set (edges_of_path P')"
proof cases
  assume "u = v"
  thus ?thesis 
    using assms that by auto
next
  assume "u \<noteq> v"
  then obtain u P\<^sub>1 P\<^sub>2 where [simp]: "P = u#P\<^sub>1 @ v#P\<^sub>2 @ [u]"
    using assms by (elim walk_path_split) auto
  let ?P'="v#P\<^sub>2 @ u#P\<^sub>1 @ [v]"
  have "path E P"
    using assms by (auto elim: walk_between_nonempty_path)
  moreover hence "walk_betw E v ?P' v"
    using path_rotate by (fastforce intro: nonempty_path_walk_between)
  moreover have "set (edges_of_path P) = set (edges_of_path ?P')"
    using edges_of_path_rotate by fastforce
  ultimately show ?thesis using that by auto
qed

end

lemma walk_transitive2:
  assumes "walk_betw E u P\<^sub>1 v" "walk_betw E v P\<^sub>2 w"
  shows "walk_betw E u (butlast P\<^sub>1 @ P\<^sub>2) w"
  using assms by (subst append_tl_butlast_eq[symmetric, of _ _ v]) (auto intro: walk_transitive)

lemma edges_of_path_nil:
  assumes "edges_of_path T = []"
  obtains "T = []" | v where "T = [v]"
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

lemma walk_split:
  assumes "walk_betw X u P v" "u \<noteq> v" "u \<in> E\<^sub>1" "v \<in> E\<^sub>2" "set P \<subseteq> E\<^sub>1 \<union> E\<^sub>2"
  obtains x y where "{x,y} \<in> set (edges_of_path P)" "x \<in> E\<^sub>1" "y \<in> E\<^sub>2"
  using assms by (induction rule: induct_walk_betw) auto

lemma edges_of_vpath_are_vs:
  assumes "\<And>v. P = [v] \<Longrightarrow> v \<in> Vs E" "set (edges_of_path P) \<subseteq> E"
  shows "set P \<subseteq> Vs E"
  using assms
proof (induction P rule: list0123.induct)
  case (3 u v)
  thus ?case 
    by (auto intro: vs_member_intro[of _ "{u,v}" E])
qed auto

lemma card_vertices_ge2:
  assumes graph: "graph_invar E" and "E \<noteq> {}" 
  shows "card (Vs E) \<ge> 2"
proof -
  obtain u v where "{u,v} \<in> E" "u \<noteq> v"
    using assms graph by force
  then have "{u,v} \<subseteq> Vs E"
    unfolding Vs_def by blast
  then show ?thesis
    using \<open>{u,v} \<in> E\<close> by (metis card_2_iff card_mono graph)
qed

context graph_abs
begin

lemma card_Vs_E_ge2: "E \<noteq> {} \<Longrightarrow> card (Vs E) \<ge> 2"
  using graph by (intro card_vertices_ge2)

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

lemma degree_edges_of_path_hd_leq_1:
  assumes "distinct P"
  shows "degree (set (edges_of_path P)) (hd P) \<le> 1" (is "degree ?E\<^sub>P (hd P) \<le> 1")
  using assms
proof (induction P rule: list012.induct) (* induction just for case distinction *)
  case (3 u v P)
  then show ?case 
    using degree_edges_of_path_hd by fastforce
qed auto

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

lemma even_num_of_odd_degree_vertices: 
  fixes W
  defines "W \<equiv> {v \<in> Vs E. \<not> even' (degree E v)}"
  shows "even (card W)"
proof -
  have "even' (sum (degree E) (Vs E))"
    using finite_E by (auto simp: handshake[symmetric])
  moreover have "finite W" "W \<subseteq> Vs E"
    unfolding W_def using graph by auto
  moreover hence "sum (degree E) (Vs E) = sum (degree E) (Vs E - W) + sum (degree E) W"
    using graph sum.subset_diff by auto
  moreover have "\<And>v. v \<in> Vs E - W \<Longrightarrow> even' (degree E v)"
    unfolding W_def by auto
  moreover hence "even' (sum (degree E) (Vs E - W))"
    using graph by (auto intro: finite_even_sum)
  ultimately have "even' (sum (degree E) W)"
    using even'_addE2 by auto
  moreover have "\<And>v. v \<in> W \<Longrightarrow> \<not> even' (degree E v)"
    unfolding W_def by auto
  moreover have "\<And>v. v \<in> W \<Longrightarrow> degree E v \<noteq> \<infinity>"
    using finite_E non_inf_degr by auto
  ultimately show "even (card W)"
    using even_sum_of_odd_vals_iff[OF \<open>finite W\<close>, of "degree E"] by auto
qed

end

lemma degree_edges_of_path_leq_2:
  assumes "distinct P" "length P > 1" "v \<in> set P"
  shows "degree (set (edges_of_path P)) v \<le> 2"
proof -
  consider "v = hd P" | "v = last P" | "v \<noteq> hd P" "v \<noteq> last P"
    by auto
  thus ?thesis
  proof cases
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
    assume "v \<noteq> hd P" "v \<noteq> last P"
    then show ?thesis
      using assms degree_edges_of_path_ge_2[of P v] by auto
  qed
qed

lemma matching_subset: "matching M \<Longrightarrow> M' \<subseteq> M \<Longrightarrow> matching M'"
  unfolding matching_def by auto

lemma matching_Vs_inter_empty:
  assumes "e \<notin> M" "matching (insert e M)" 
  shows "e \<inter> Vs M = {}"
proof (rule ccontr)
  assume "e \<inter> Vs M \<noteq> {}"
  then obtain v where "v \<in> e" "v \<in> Vs M"
    by auto
  moreover then obtain e' where "v \<in> e'" "e' \<in> M"
    by (auto elim: vs_member_elim)
  ultimately show "False"
    using assms[unfolded matching_def] by auto
qed

subsection \<open>Short-Cutting\<close>

fun short_cut where
  "short_cut E [] = []"
| "short_cut E [v] = [v]"
| "short_cut E (u#v#P) = (if {u,v} \<in> E then u#short_cut E (v#P) else short_cut E (u#P))"

lemma short_cut_hd1: "P \<noteq> [] \<Longrightarrow> hd P = hd (short_cut E P)"
  by (induction P rule: short_cut.induct) auto

lemma short_cut_hd2: "v = hd (short_cut E (v#P))"
  by (auto simp: short_cut_hd1[symmetric])

lemma short_cut_nonnil: "short_cut E (v#P) \<noteq> []"
  by (induction "v#P" arbitrary: v P rule: short_cut.induct) auto

lemma short_cut_hdE: 
  obtains P' where "short_cut E (u#P) = u#short_cut E P'"
proof (induction "u#P" arbitrary: thesis u P rule: short_cut.induct)
  case (2 E v)
  then show ?case 
    by (auto intro: "2.prems"[of "[]"])
next
  case (3 E u v P)
  show ?case 
    apply (cases "{u,v} \<in> E")
    using 3 by auto
qed

lemma short_cut_cons_cons: "{u,v} \<in> E \<Longrightarrow> short_cut E (u#v#P) = u#short_cut E (v#P)"
  by (induction "u#v#P" arbitrary: u v P rule: short_cut.induct) auto

lemma short_cut_butlast: 
  "{u,v} \<in> E \<Longrightarrow> short_cut E (u#butlast (v#P)) = u#short_cut E (butlast (v#P))"
  by (induction P arbitrary: u v) auto

lemma short_cut_hd_not_in_Vs: "u \<notin> Vs E \<Longrightarrow> short_cut E (u#P) = [u]"
  using edges_are_Vs[of u] by (induction "u#P" arbitrary: u P rule : short_cut.induct) auto

lemma last_short_cut_simp: "last (u#short_cut E (v#P)) = last (short_cut E (v#P))"
  using short_cut_nonnil by fastforce

lemma short_cut_subset: "set (short_cut E P) \<subseteq> set P"
  by (induction P rule: short_cut.induct) auto

lemma distinct_short_cut: "distinct P \<Longrightarrow> distinct (short_cut E P)"
proof (induction P rule: short_cut.induct)
  case (3 E u v P)
  thus ?case 
    using short_cut_subset[of _ "v#P"] by auto
qed auto

lemma distinct_tl_short_cut: "distinct (tl P) \<Longrightarrow> distinct (tl (short_cut E P))"
  by (induction P rule: short_cut.induct) (auto simp: distinct_short_cut)

lemma short_cut_Vs_subset: 
  assumes "u \<in> Vs E" 
  shows "set (short_cut E (u#P)) \<subseteq> Vs E"
  using assms
proof (induction "u#P" arbitrary: u P rule: short_cut.induct)
  case (3 E u v P)
  then show ?case 
  proof cases
    assume "{u,v} \<in> E"
    moreover hence "v \<in> Vs E"
      by (auto simp: edges_are_Vs)
    ultimately show ?case
      using "3.hyps"(1) by auto
  qed auto
qed (auto simp: edges_are_Vs)

lemma short_cut_cons_consE:
  assumes "{u,v} \<in> E"
  obtains P' where "short_cut E (u#v#P) = u#v#short_cut E P'"
proof -
  obtain P' where "short_cut E (v#P) = v#short_cut E P'"
    using assms by (auto elim: short_cut_hdE)
  thus ?thesis
    using assms that by auto
qed

lemma short_cut_edges_append:
  assumes "{u,v} \<in> E"
  shows "edges_of_path (short_cut E (u#v#P)) = {u,v}#edges_of_path (short_cut E (v#P))"  
proof -
  obtain P' where "short_cut E (u#v#P) = u#v#short_cut E P'"
    using assms by (auto elim: short_cut_hdE)
  thus ?thesis
    using assms by auto
qed

lemma short_cut_edges: "set (edges_of_path (short_cut E P)) \<subseteq> E"
proof (induction P rule: short_cut.induct)
  case (3 E u v P)
  thus ?case 
  proof cases
    assume "{u,v} \<in> E"
    thus ?thesis
      using 3 by (subst short_cut_edges_append) auto
  qed auto
qed auto

locale graph_abs2 = 
  E\<^sub>1: graph_abs E\<^sub>1 +
  E\<^sub>2: graph_abs E\<^sub>2 for E\<^sub>1 :: "'a set set" and E\<^sub>2 :: "'a set set"
begin

lemma Vs_inter_disj:
  assumes "Vs E\<^sub>1 \<inter> Vs E\<^sub>2 = {}" 
  shows "E\<^sub>1 \<inter> E\<^sub>2 = {}"
proof (rule ccontr)
  assume "E\<^sub>1 \<inter> E\<^sub>2 \<noteq> {}"
  then obtain e where "e \<in> E\<^sub>1 \<inter> E\<^sub>2"
    by auto
  moreover then obtain u v where "e = {u,v}"
    using E\<^sub>1.graph E\<^sub>2.graph by auto
  ultimately have "u \<in> Vs E\<^sub>1" "u \<in> Vs E\<^sub>2"
    by (auto intro: vs_member_intro)
  thus "False"
    using assms by auto
qed

end

locale graph_abs2' = 
  E\<^sub>1: graph_abs E\<^sub>1 +
  E\<^sub>2: graph_abs E\<^sub>2 for E\<^sub>1 :: "'a set set" and E\<^sub>2 :: "'b set set"
begin

end

locale graph_subgraph_abs =
  graph_abs E for E +
  fixes E'
  assumes subset: "E' \<subseteq> E"
begin

lemma graph_E': "graph_invar E'"
  using graph subset finite_subset[OF Vs_subset[of E' E]] by auto

sublocale graph_abs2 E E'
  using graph graph_E' by unfold_locales

end

locale edge_subgraph_abs =
  graph_abs E for E +
  fixes u v
  assumes edge: "{u,v} \<in> E"
begin

sublocale graph_subgraph_abs E "{{u,v}}"
  using edge by unfold_locales simp

end

locale restr_graph_abs =
  graph_abs E for E :: "'a set set" +
  fixes V E\<^sub>V
  defines "E\<^sub>V \<equiv> {e \<in> E. e \<subseteq> V}"
begin

lemma E\<^sub>V_subset: "E\<^sub>V \<subseteq> E"                                  
  unfolding E\<^sub>V_def by auto

sublocale E\<^sub>V: graph_subgraph_abs E E\<^sub>V
  using E\<^sub>V_subset by unfold_locales

lemmas graph_E\<^sub>V = E\<^sub>V.E\<^sub>2.graph

lemma Vs_subset_restr_graph: "Vs E\<^sub>V \<subseteq> V"
proof 
  fix v
  assume "v \<in> Vs E\<^sub>V"
  then obtain e where "e \<in> E\<^sub>V" "v \<in> e"
    by (auto elim: vs_member_elim)
  moreover hence "e \<subseteq> V"
    by (auto simp: E\<^sub>V_def)
  ultimately show "v \<in> V"
    by (auto intro: vs_member_intro)                                         
qed

end

locale path_edges_subgraph_abs = 
  graph_abs E for E +
  fixes P
  assumes path: "path E P"
begin

abbreviation "E\<^sub>P \<equiv> set (edges_of_path P)"

lemma E\<^sub>P_subset: "E\<^sub>P \<subseteq> E"
  using path path_edges_subset by auto

sublocale E\<^sub>P: graph_subgraph_abs E E\<^sub>P
  using E\<^sub>P_subset by unfold_locales

lemmas graph_E\<^sub>P = E\<^sub>P.E\<^sub>2.graph

end

subsection \<open>Rotating Cycles\<close>

(* TODO: connect with cycles defined in problems.MinSpanningTree *)

fun rotate_tour_acc :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rotate_tour_acc acc f (x#y#xs) = 
    (if f x y then x#y#xs @ acc else rotate_tour_acc (acc @ [y]) f (y#xs))"
| "rotate_tour_acc acc f xs = xs @ acc"

lemma edges_of_path_append_singleton: (* move lemma to graph stuff *)
  "xs \<noteq> [] \<Longrightarrow> edges_of_path (xs @ [x]) = edges_of_path xs @ [{last xs,x}]"
  by (induction xs rule: list012.induct) auto

lemma length_rotate_tour_acc: "length (rotate_tour_acc acc f xs) = length acc + length xs"
  by (induction xs arbitrary: acc rule: list012_induct) auto

lemma set_rotate_tour_acc: 
  assumes "hd (xs @ acc) = last (xs @ acc)"
  shows "set xs \<union> set acc = set (rotate_tour_acc acc f xs)"
  using assms
proof (induction xs arbitrary: acc rule: list012_induct)
  case (CCons x y xs)
  hence x_isin: "x \<in> set (y#xs @ acc)"
    using last_in_set[of "y#xs @ acc"] by auto
  thus ?case 
    using "CCons.IH"[of "acc @ [y]"] by (auto split: if_splits)
qed auto

lemma set_tl_rotate_tour_acc: 
  assumes "hd (xs @ acc) = last (xs @ acc)"
  shows "set (tl (xs @ acc)) = set (tl (rotate_tour_acc acc f xs))"
  using assms
proof (induction xs arbitrary: acc rule: list012_induct)
  case (CCons x y xs)
  hence x_isin: "x \<in> set (y#xs @ acc)"
    using last_in_set[of "y#xs @ acc"] by auto
  thus ?case 
    using "CCons.IH"[of "acc @ [y]"] by (auto split: if_splits)
qed auto

lemma edges_of_path_rotate_tour_acc:
  assumes "hd (xs @ acc) = last (xs @ acc)"
  shows "mset (edges_of_path (rotate_tour_acc acc f xs)) = mset (edges_of_path (xs @ acc))"
  using assms
proof (induction xs arbitrary: acc rule: list012_induct)
  case (CCons x y xs)
  thus ?case 
    using edges_of_path_append_singleton[of "y#xs @ acc" y] by (auto split: if_splits)
qed auto

lemma rotate_tour_acc_hd_eq_last:
  "hd (xs @ acc) = last (xs @ acc) \<Longrightarrow> hd (rotate_tour_acc acc f xs) = last (rotate_tour_acc acc f xs)"
  by (induction xs arbitrary: acc rule: list012_induct) auto

lemma distinct_rotate_tour_acc: 
  assumes "hd (xs @ acc) = last (xs @ acc)" "distinct (tl (xs @ acc))" 
  shows "distinct (tl (rotate_tour_acc acc f xs))"
  using assms by (induction xs arbitrary: acc rule: list012_induct) auto

lemma distinct_adj_rotate_tour_acc: 
  assumes "hd (xs @ acc) = last (xs @ acc)" "distinct_adj (xs @ acc)" 
  shows "distinct_adj (rotate_tour_acc acc f xs)"
  using assms 
proof (induction xs arbitrary: acc rule: list012_induct)
  case (CCons x y xs)
  then show ?case 
  proof cases
    assume "\<not> f x y"
    moreover have "distinct_adj (y#xs @ acc @ [y])"
      using CCons distinct_adj_append_iff[of "y#xs @ acc" "[y]"] by auto
    ultimately show ?thesis
      using CCons.IH by auto
  qed auto
qed auto

fun rotate_tour :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rotate_tour f xs = rotate_tour_acc [] f xs"

lemma length_rotate_tour: "length (rotate_tour f T) = length T"
  by (auto simp add: length_rotate_tour_acc)

lemma rotate_tour_non_nil: "xs \<noteq> [] \<Longrightarrow> rotate_tour f xs \<noteq> []"
  using length_rotate_tour length_0_conv by metis

lemma edges_of_path_rotate_tour: 
  "hd xs = last xs \<Longrightarrow> mset (edges_of_path (rotate_tour f xs)) = mset (edges_of_path xs)"
  by (auto simp: edges_of_path_rotate_tour_acc)

lemma rotate_tour_hd_eq_last: "hd xs = last xs \<Longrightarrow> hd (rotate_tour f xs) = last (rotate_tour f xs)"
  by (auto simp: rotate_tour_acc_hd_eq_last)

lemma set_rotate_tour: "hd xs = last xs \<Longrightarrow> set (rotate_tour f xs) = set xs"
  using set_rotate_tour_acc[of xs "[]"] by auto

lemma set_tl_rotate_tour: "hd xs = last xs \<Longrightarrow> set (tl (rotate_tour f xs)) = set (tl xs)"
  using set_tl_rotate_tour_acc[of xs "[]"] by auto

lemma distinct_rotate_tour: "hd xs = last xs \<Longrightarrow> distinct (tl xs) \<Longrightarrow> distinct (tl (rotate_tour f xs))"
  using distinct_rotate_tour_acc[of xs "[]"] by auto

lemma distinct_adj_rotate_tour: "hd xs = last xs \<Longrightarrow> distinct_adj xs \<Longrightarrow> distinct_adj (rotate_tour f xs)"
  using distinct_adj_rotate_tour_acc[of xs "[]"] by auto

end