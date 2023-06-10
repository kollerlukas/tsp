(* Author: Lukas Koller *)
theory MinWeightMatching
  imports Main tsp.Misc tsp.WeightedGraph tsp.CompleteGraph
begin

definition "is_perf_match E M \<equiv> M \<subseteq> E \<and> matching M \<and> Vs M = Vs E"

lemma is_perf_matchI:
  assumes "M \<subseteq> E" "matching M" "Vs M = Vs E"
  shows "is_perf_match E M"
  using assms by (auto simp: is_perf_match_def)

lemma is_perf_matchI2:
  assumes "M \<subseteq> E" "\<And>u. u \<in> Vs E \<Longrightarrow> \<exists>!e \<in> M. u \<in> e"
  shows "is_perf_match E M"
proof -
  have "Vs M = Vs E"
    using assms
  proof (intro equalityI)
    show "Vs E \<subseteq> Vs M"
    proof
      fix v
      assume "v \<in> Vs E"
      then obtain e where "e \<in> M" "v \<in> e"
        using assms by meson
      thus "v \<in> Vs M"
        by (auto intro: vs_member_intro)
    qed
  qed (auto simp: Vs_subset)
  moreover hence "matching M"
    unfolding matching_def2 using assms by auto
  ultimately show ?thesis
    using assms by (intro is_perf_matchI)
qed

lemma is_perf_matchE:
  assumes "is_perf_match E M"
  shows "M \<subseteq> E" "matching M" "Vs M = Vs E"
  using assms[unfolded is_perf_match_def] by auto

lemma extend_perf_match:
  assumes "is_perf_match E M" "u \<notin> Vs E" "v \<notin> Vs E" "{{u,v}} \<union> E \<subseteq> E'" "Vs E' = Vs E \<union> {u,v}"
  shows "is_perf_match E' ({{u,v}} \<union> M)"
proof (rule is_perf_matchI2)
  have "M \<subseteq> E"
    using assms by (auto simp: is_perf_matchE)
  thus "{{u,v}} \<union> M \<subseteq> E'"
    using assms by auto

  show "\<And>w. w \<in> Vs E' \<Longrightarrow> \<exists>!e \<in> {{u,v}} \<union> M. w \<in> e"
  proof -
    fix w
    assume "w \<in> Vs E'"
    then consider "w \<in> {u,v}" | "w \<in> Vs E - {u,v}"
      using assms by auto
    thus "\<exists>!e \<in> {{u,v}} \<union> M. w \<in> e"
    proof cases
      assume "w \<in> {u,v}"
      moreover hence "\<exists>!e \<in> {{u,v}}. w \<in> e"
        by auto
      moreover have "w \<notin> Vs M"
        using assms calculation by (auto simp: is_perf_matchE)
      moreover hence "\<forall>e \<in> M. w \<notin> e"
        using vs_member[of w M] by auto
      ultimately show "\<exists>!e \<in> {{u,v}} \<union> M. w \<in> e"
        by auto
    next
      assume "w \<in> Vs E - {u,v}"
      moreover hence "w \<in> Vs M" "matching M"
        using assms by (auto simp: is_perf_matchE)
      moreover hence "\<exists>!e \<in> M. w \<in> e"
        by (auto simp: matching_def2)
      ultimately show "\<exists>!e \<in> {{u,v}} \<union> M. w \<in> e"
        by auto 
    qed
  qed
qed

lemma restr_graph_compl': 
  "graph_invar E \<Longrightarrow> is_complete E \<Longrightarrow> V \<subseteq> Vs E \<Longrightarrow> is_complete {e \<in> E. e \<subseteq> V}" 
  by (intro restr_compl_graph_abs.E\<^sub>V_complete) unfold_locales (* TODO: clean up lemma!? *)

lemma restr_graph_Vs':
  "graph_invar E \<Longrightarrow> is_complete E \<Longrightarrow> V \<subseteq> Vs E \<Longrightarrow> card V \<noteq> 1 \<Longrightarrow> Vs {e \<in> E. e \<subseteq> V} = V"
  by (intro restr_compl_graph_abs.Vs_E\<^sub>V_eq_V) unfold_locales (* TODO: clean up lemma!? *)

context compl_graph_abs
begin

lemma perf_match_exists: 
  assumes "even (card (Vs E))"
  obtains M where "is_perf_match E M"
proof -
  have "finite (Vs E)" "even (card (Vs E))"
    using graph assms finite_subset[OF Vs_subset] by auto
  thus ?thesis
    using assms graph complete (* restr_graph_compl restr_graph_Vs *) that
  proof (induction "Vs E" arbitrary: E thesis rule: finite_even_induct)
    case empty
    moreover hence "E = {}"
      by (intro Vs_emptyE) auto
    moreover hence "is_perf_match E {}"
      by (auto intro: is_perf_matchI simp: matching_def)
    ultimately show ?case by auto
  next
    case (insert2 u v V)
    have "even (card V)"
      apply (rule finite_even_cardI)
      using insert2 by auto
    moreover have "V \<subseteq> Vs E"
      using insert2 by auto
    moreover hence "V = Vs {e \<in> E. e \<subseteq> V}" (is "V = Vs ?E'")
      using insert2 calculation by (intro restr_graph_Vs'[symmetric]) auto
    moreover have "even (card (Vs ?E'))" 
      using calculation by auto
    moreover have "graph_invar ?E'" 
      apply (rule graph_subset)
      using insert2 by auto
    moreover have "is_complete ?E'"
      using insert2 calculation by (intro restr_graph_compl') 
    ultimately obtain M where "is_perf_match ?E' M"
      using is_completeE[of ?E'] by (elim insert2.hyps(5))
    moreover have "u \<notin> Vs ?E'" "v \<notin> Vs ?E'" "Vs E = Vs ?E' \<union> {u,v}"
      using insert2 by (auto simp: \<open>V = Vs {e \<in> E. e \<subseteq> V}\<close>[symmetric])
    moreover have "u \<in> Vs E" "v \<in> Vs E"
      using insert2 by auto
    moreover hence "{u,v} \<in> E"
      using insert2 by (intro is_completeE)
    moreover hence "{{u,v}} \<union> ?E' \<subseteq> E"
      by auto
    ultimately have "is_perf_match E ({{u,v}} \<union> M)"
      by (intro extend_perf_match)
    thus ?case
      using insert2 by auto
  qed
qed

end

context restr_compl_graph_abs
begin

lemma perf_match_exists: 
  assumes "even (card (Vs E\<^sub>V))"
  obtains M where "is_perf_match E\<^sub>V M"
  apply (rule compl_graph_abs.perf_match_exists[of E\<^sub>V])
  apply unfold_locales
  using graph_E\<^sub>V E\<^sub>V_complete assms that by auto (* TODO: clean up lemma!? *)

end

context compl_graph_abs
begin

lemma restr_perf_match_exists: 
  assumes "V \<subseteq> Vs E" "even (card (Vs {e \<in> E. e \<subseteq> V}))"
  obtains M where "is_perf_match {e \<in> E. e \<subseteq> V} M"
  apply (rule restr_compl_graph_abs.perf_match_exists)
  apply unfold_locales
  using assms that by auto (* TODO: clean up lemma!? *)

end

abbreviation (input) "cost_of_match c M \<equiv> sum c M"

context w_graph_abs
begin

abbreviation "cost_of_match\<^sub>c M \<equiv> sum c M"

end

context pos_w_graph_abs
begin

lemma cost_of_match_sum: "cost_of_match\<^sub>c (set M) \<le> \<Sum>\<^sub># (image_mset c (mset M))"
proof (induction M)
  case (Cons e M)
  thus ?case 
    by (cases "e \<in> set M") (auto simp: add_left_mono insert_absorb add_increasing costs_ge_0)
qed auto

end

definition "is_min_match E c M \<equiv> 
  is_perf_match E M \<and> (\<forall>M'. is_perf_match E M' \<longrightarrow> cost_of_match c M \<le> cost_of_match c M')"

lemma is_min_matchE:
  assumes "is_min_match E c M"
  shows "is_perf_match E M" "\<And>M'. is_perf_match E M' \<Longrightarrow> cost_of_match c M \<le> cost_of_match c M'"
  using assms[unfolded is_min_match_def] by auto

lemma is_min_matchE2:
  assumes "is_min_match E c M"
  shows "M \<subseteq> E" "matching M" "Vs M = Vs E" 
    "\<And>M'. is_perf_match E M' \<Longrightarrow> cost_of_match c M \<le> cost_of_match c M'"
  using is_min_matchE[OF assms] is_perf_matchE[of E M] by auto 

locale min_weight_matching =
  w_graph_abs E c for E :: "'a set set" and c :: "'a set \<Rightarrow> 'b::{ordered_semiring_0,semiring_numeral}" +
  fixes comp_match :: "'a set set \<Rightarrow> ('a set \<Rightarrow> 'b) \<Rightarrow> 'a set set" 
  assumes match: "\<And>E c. (\<exists>M. is_perf_match E M) \<Longrightarrow> is_min_match E c (comp_match E c)"

section \<open>Equivalence to Maximum-Matching\<close>

subsection \<open>Reductions\<close>

text \<open>A problem is defined by a function that characterizes correct solutions to the problem.\<close>
datatype ('a,'b) prob = Prob (is_sol: "'a \<Rightarrow> 'b \<Rightarrow> bool")

text \<open>A function \<open>f\<close> solves a problem \<open>P p\<close>, if for all inputs the function \<open>f\<close> gives a correct result.\<close>
definition "solves P\<^sub>i f \<longleftrightarrow> (\<forall>a. (is_sol P\<^sub>i) a (f a))"

lemma solvesI: "(\<And>a. is_sol P\<^sub>i a (f a)) \<Longrightarrow> solves P\<^sub>i f"
  unfolding solves_def by auto

lemma solvesE: "solves P\<^sub>i f \<Longrightarrow> (\<And>a. is_sol P\<^sub>i a (f a))"
  unfolding solves_def by auto

definition less_eq_prob :: "('a,'b) prob \<Rightarrow> ('c,'d) prob \<Rightarrow> bool" (infix "\<le>\<^sub>R" 80) where
  "P\<^sub>1 \<le>\<^sub>R P\<^sub>2 \<longleftrightarrow> (\<exists>f. (\<forall>g. solves P\<^sub>1 g \<longrightarrow> solves P\<^sub>2 (f g)))"

lemma less_eq_probI:
  assumes "\<exists>f. \<forall>g. solves P\<^sub>1 g \<longrightarrow> solves P\<^sub>2 (f g)"
  shows "P\<^sub>1 \<le>\<^sub>R P\<^sub>2"
  using assms less_eq_prob_def by blast

text \<open>Two problems \<open>P\<^sub>1\<close> and \<open>P\<^sub>2\<close> are equivalent iff \<open>P\<^sub>1 \<le> P\<^sub>2\<close> and \<open>P\<^sub>2 \<le> P\<^sub>1\<close>\<close>
definition eq_prob :: "('a,'b) prob \<Rightarrow> ('a,'b option) prob \<Rightarrow> bool" (infix "=\<^sub>R" 80) where
  "P\<^sub>1 =\<^sub>R P\<^sub>2 \<longleftrightarrow> P\<^sub>1 \<le>\<^sub>R P\<^sub>2 \<and> P\<^sub>2 \<le>\<^sub>R P\<^sub>1"       

lemma eq_probI:
  assumes "P\<^sub>1 \<le>\<^sub>R P\<^sub>2" "P\<^sub>2 \<le>\<^sub>R P\<^sub>1"
  shows "P\<^sub>1 =\<^sub>R P\<^sub>2"
  using assms eq_prob_def by blast

subsection \<open>Maximum Weight Matching\<close>

(* We need to ensure that a matching in a graph is a subset! *)
abbreviation "matching_in \<equiv> \<lambda>E M. M \<subseteq> E \<and> matching M"

definition "is_max_match E c M \<equiv> matching_in E M \<and> (\<forall>M'. matching_in E M' \<longrightarrow> (\<Sum>e\<in>M'. c e) \<le> (\<Sum>e\<in>M. c e))"
                                                                                                                      
abbreviation "P\<^sub>m\<^sub>a\<^sub>x \<equiv> Prob (\<lambda>(E,c) M. graph_invar E \<longrightarrow> is_max_match E c M)"

subsection \<open>Maximum Cardinality Matching\<close>

definition "is_max_card_match E M \<equiv> matching_in E M \<and> (\<forall>M'. matching_in E M' \<longrightarrow> card M' \<le> card M)"
                                                                                                                      
abbreviation "P\<^sub>c\<^sub>a\<^sub>r\<^sub>d \<equiv> Prob (\<lambda>E M. graph_invar E \<longrightarrow> is_max_card_match E M)"

section \<open>Minimum Perfect Weight Matching\<close>

(* abbreviation "perfect_matching \<equiv> \<lambda>(G,c) M. matching_in (G,c) M \<and> Vs M = Vs G"

fun min_weight_perfect_matching :: "'a set set * ('a set \<Rightarrow> int) \<Rightarrow> 'a set set \<Rightarrow> bool" where 
  "min_weight_perfect_matching (G,c) M = (perfect_matching (G,c) M 
    \<and> (\<forall>M'. perfect_matching (G,c) M' \<longrightarrow> (\<Sum>e\<in>M. c e) \<le> (\<Sum>e\<in>M'. c e)))" *)

abbreviation "P\<^sub>m\<^sub>i\<^sub>n \<equiv> Prob (\<lambda>(E,c) M. graph_invar E \<longrightarrow> (case M of 
    Some M \<Rightarrow> is_min_match E c M 
  | None \<Rightarrow> \<nexists>M. is_perf_match E M))"

section \<open>Proof of the Equivalence of Min- & Max-Matching\<close>

lemma matching_subset:
  assumes "matching M" "M' \<subseteq> M"
  shows "matching M'"
  using assms unfolding matching_def by auto

lemma edges_finite: "graph_invar E \<Longrightarrow> finite (Vs E) \<longleftrightarrow> finite E"
  using graph_abs.finite_E graph_abs.intro by auto

lemma matching_card:
  assumes "graph_invar E" "matching_in E M" 
  shows "2 * card M = card (Vs M)"
proof -
  have "Vs M \<subseteq> Vs E"
    using assms Vs_subset by auto
  then have "graph_invar M" "finite (Vs M)"
    using assms graph_subset by auto
  then have "finite M" "matching_in E M"
    using assms edges_finite by auto
  then show ?thesis
  proof (induction M rule: finite.induct)
    case emptyI
    then show ?case 
      using Vs_def card.empty by (metis Union_empty mult_0_right)
  next
    case (insertI M e)
    then have "finite (Vs M)"
      using assms finite_subset[OF Vs_subset[of M E]] by auto
    show ?case 
    proof (cases "e \<in> M")
      case True
      then have "2 * card (insert e M) = 2 * card M"
        by (simp add: insert_absorb)
      also have "... = card (Vs M)"
        using matching_subset insertI by auto
      also have "... = card (Vs (insert e M))"
        using \<open>e \<in> M\<close> by (simp add: insert_absorb)
      finally show ?thesis .
    next
      case False
      have "e \<in> E" "matching M" "matching (insert e M)"
        using insertI matching_subset by auto
      then obtain u v where "e = {u,v}" "u \<noteq> v"
        using assms by auto
      then have "u \<notin> Vs M" "v \<notin> Vs M"
      proof -
        show "u \<notin> Vs M"
        proof (rule ccontr)
          assume "\<not> u \<notin> Vs M"
          then obtain e' where "e' \<in> M" "u \<in> e'"
            using \<open>matching M\<close> matching_def2[of M] by auto
          then have "e \<noteq> e'" "e \<in> insert e M" "e' \<in> insert e M" "e \<inter> e' \<noteq> {}"
            using \<open>e = {u,v}\<close> \<open>e \<notin> M\<close> by auto
          then show "False"
            using \<open>matching (insert e M)\<close> matching_def[of "insert e M"] by auto
        qed

        show "v \<notin> Vs M"
        proof (rule ccontr)
          assume "\<not> v \<notin> Vs M"
          then obtain e' where "e' \<in> M" "v \<in> e'"
            using \<open>matching M\<close> matching_def2[of M] by auto
          then have "e \<noteq> e'" "e \<in> insert e M" "e' \<in> insert e M" "e \<inter> e' \<noteq> {}"
            using \<open>e = {u,v}\<close> \<open>e \<notin> M\<close> by auto
          then show "False"
            using \<open>matching (insert e M)\<close> matching_def[of "insert e M"] by auto
        qed
      qed

      have "Vs {e} = {u,v}"
        using \<open>e={u,v}\<close> Vs_def by (metis cSup_singleton)

      have "Vs M \<union> Vs {e} = Vs (insert e M)"
        using Vs_def by (metis Union_insert cSup_singleton sup_commute)

      have "2 * card (insert e M) = 2 * card M + 2"
        using \<open>e \<notin> M\<close> \<open>finite M\<close> by auto
      also have "... = card (Vs M) + 2"
        using matching_subset insertI by auto
      also have "... = card (Vs M) + card {u,v}"
        using \<open>u \<noteq> v\<close> by auto
      also have "... = card (Vs M \<union> {u,v})"
        using \<open>u \<notin> Vs M\<close> \<open>v \<notin> Vs M\<close> card_Un_disjoint[OF \<open>finite (Vs M)\<close>, of"{u,v}"] by auto
      also have "... = card (Vs M \<union> Vs {e})"
        using \<open>Vs {e} = {u,v}\<close> by auto
      also have "... = card (Vs (insert e M))"
        using \<open>Vs M \<union> Vs {e} = Vs (insert e M)\<close> by auto
      finally show ?thesis .
    qed
  qed
qed

lemma matching_union:
  assumes "matching M1" "matching M2" "Vs M1 \<inter> Vs M2 = {}"
  shows "matching (M1 \<union> M2)"
  using assms unfolding matching_def Vs_def by blast

lemma pairwise_disj_Vs_union:
  assumes "finite M" "Mj\<notin>M" "\<forall>Mi\<in>insert Mj M. \<forall>Mj\<in>insert Mj M. Mi \<noteq> Mj \<longrightarrow> Vs Mi \<inter> Vs Mj = {}" 
  shows "Vs (\<Union> M) \<inter> Vs Mj = {}"
  using assms
proof (induction M rule: finite.induct)
  case emptyI
  then have "Vs (\<Union> {}) = {}"
    using Vs_def by fastforce
  then show ?case by auto
next
  case (insertI M Mi)
  then have "Vs (\<Union> M) \<union> Vs Mi = Vs (\<Union> (insert Mi M))"
    using Vs_def by (metis Sup_insert Un_commute Union_Un_distrib)
  have "Mi \<noteq> Mj"
    using insertI by auto
  then have "(Vs (\<Union> M) \<union> Vs Mi) \<inter> Vs Mj = {}"
    using insertI by auto
  then show ?case 
    using \<open>Vs (\<Union> M) \<union> Vs Mi = Vs (\<Union> (insert Mi M))\<close> by auto
qed

lemma matching_bigunion:
  assumes "finite M" "\<forall>Mi\<in>M.\<forall>Mj\<in>M. Mi \<noteq> Mj \<longrightarrow> Vs Mi \<inter> Vs Mj = {}" "\<forall>Mi\<in>M. matching Mi"
  shows "matching (\<Union> M)"
  using assms
proof (induction M rule: finite.induct)
  case (insertI M Mj)
  then have "matching (\<Union> M)" "matching Mj"
    by auto
  then show ?case 
  proof (cases "Mj\<in>M")
    case True
    then have "\<Union> (insert Mj M) = \<Union> M"
      by auto
    then show ?thesis 
      using insertI by auto
  next
    case False
    then have "matching (\<Union> M)" "matching Mj" "Vs (\<Union> M) \<inter> Vs Mj = {}"
      using insertI pairwise_disj_Vs_union by auto
    have "\<Union> (insert Mj M) = \<Union> M \<union> Mj"
      by blast
    then show ?thesis 
      using matching_union[OF \<open>matching (\<Union> M)\<close> \<open>matching Mj\<close> \<open>Vs (\<Union> M) \<inter> Vs Mj = {}\<close>] by auto
  qed
qed (auto simp: matching_def)

definition f\<^sub>1 :: "('a set set \<times> ('a set \<Rightarrow> int) \<Rightarrow> 'a set set) \<Rightarrow> 'a set set \<times> ('a set \<Rightarrow> int) \<Rightarrow> 'a set set option"
  where "f\<^sub>1 \<equiv> \<lambda>g (E,c). 
    let M = g (E,\<lambda>e. 1 + (\<Sum>e\<in>E. \<bar>c e\<bar>) - c e) in 
      if Vs M = Vs E then Some M else None"

corollary P\<^sub>m\<^sub>a\<^sub>x_leq_P\<^sub>m\<^sub>i\<^sub>n: 
  assumes "solves P\<^sub>m\<^sub>a\<^sub>x g"
  shows "solves P\<^sub>m\<^sub>i\<^sub>n (f\<^sub>1 g)"
proof (rule solvesI)
  fix a
  show "is_sol P\<^sub>m\<^sub>i\<^sub>n a (f\<^sub>1 g a)"
  proof (cases a)
    case (Pair E c)
    then have [simp]: "a = (E,c)" . 
    let ?K="1 + (\<Sum>e\<in>E. \<bar>c e\<bar>)"
    have "0 < ?K"
      by (auto simp: le_imp_0_less)
    let ?c\<^sub>H="\<lambda>e. ?K - c e"
    show ?thesis
    proof (cases "graph_invar E")
      case False
      then show ?thesis by auto
    next
      case True
      then have "graph_abs E"
        by (simp add: graph_abs.intro)
      then have "finite E"
        using graph_abs.finite_E by auto

      let ?M="g (E,?c\<^sub>H)"
      have M_max: "is_max_match E ?c\<^sub>H ?M" and "?M \<subseteq> E"
        using \<open>graph_invar E\<close> \<open>solves P\<^sub>m\<^sub>a\<^sub>x g\<close> by (auto simp: solves_def is_max_match_def)

      text \<open>A maximum weight matching \<open>M\<close> in \<open>(E,c\<^sub>H)\<close> is maximum cardinality matching in \<open>(E,c\<^sub>H)\<close>.\<close>
      moreover have "\<forall>M'. matching_in E M' \<longrightarrow> card M' \<le> card ?M"
      proof (rule ccontr)
        assume "\<not>(\<forall>M'. matching_in E M' \<longrightarrow> card M' \<le> card ?M)"
        then have "\<exists>M'. matching_in E M' \<and> card ?M < card M'"
          by fastforce
        then obtain M' where "matching_in E M'" "card ?M < card M'"
          by auto
        then have "M' \<subseteq> E"
          by auto 
        have "(\<Sum>e\<in>M'. c e) \<le> (\<Sum>e\<in>M'. \<bar>c e\<bar>)"
          by (simp add: sum_mono)
        also have "... \<le> (\<Sum>e\<in>E. \<bar>c e\<bar>)"
          using \<open>finite E\<close> \<open>M' \<subseteq> E\<close> by (auto simp: sum_mono2)
        finally have "(\<Sum>e\<in>M'. c e) < ?K"
          by auto

        have "(\<Sum>e\<in>?M. -c e) \<le> (\<Sum>e\<in>?M. \<bar>c e\<bar>)"
          by (simp add: sum_mono)
        also have "... \<le> (\<Sum>e\<in>E. \<bar>c e\<bar>)"
          using \<open>finite E\<close> \<open>?M \<subseteq> E\<close> by (auto simp: sum_mono2)
        finally have "(\<Sum>e\<in>?M. -c e) < ?K"
          by auto

        have "?M \<union> M' \<subseteq> E"
          using \<open>?M \<subseteq> E\<close> \<open>M' \<subseteq> E\<close> by auto
        have "finite ?M" "finite M'" "finite (?M - M')" "finite (M' - ?M)" "finite (?M \<inter> M')" "finite (?M \<union> M')"
          using \<open>?M \<subseteq> E\<close> \<open>M' \<subseteq> E\<close> \<open>finite E\<close> rev_finite_subset finite_Diff by blast+
        have "(?M - M') \<inter> (M' - ?M) = {}"
          by blast
        have "(?M - M') \<union> (M' - ?M) \<subseteq> ?M \<union> M'"
          by auto

        have "?M = (?M - M') \<union> (?M \<inter> M')" "(?M - M') \<inter> (?M \<inter> M') = {}" "M' = (M' - ?M) \<union> (?M \<inter> M')" "(M' - ?M) \<inter> (?M \<inter> M') = {}"
          by auto

        have "(\<Sum>e\<in>?M. -c e) + (\<Sum>e\<in>M'. c e) = (\<Sum>e\<in>(?M - M') \<union> (?M \<inter> M'). -c e) + (\<Sum>e\<in>(M' - ?M) \<union> (?M \<inter> M'). c e)"
          using \<open>?M = (?M - M') \<union> (?M \<inter> M')\<close> \<open>M' = (M' - ?M) \<union> (?M \<inter> M')\<close> by simp
        also have "... = (\<Sum>e\<in>?M - M'. -c e) + (\<Sum>e\<in>?M \<inter> M'. -c e) + (\<Sum>e\<in>M' - ?M. c e) + (\<Sum>e\<in>?M \<inter> M'. c e)"
          using sum.union_disjoint[OF \<open>finite (?M - M')\<close> \<open>finite (?M \<inter> M')\<close> \<open>(?M - M') \<inter> (?M \<inter> M') = {}\<close>, where g="\<lambda>e. -c e"] 
                sum.union_disjoint[OF \<open>finite (M' - ?M)\<close> \<open>finite (?M \<inter> M')\<close> \<open>(M' - ?M) \<inter> (?M \<inter> M') = {}\<close>, where g="\<lambda>e. c e"]
            by simp
        also have "... = (\<Sum>e\<in>?M - M'. -c e) - (\<Sum>e\<in>?M \<inter> M'. c e) + (\<Sum>e\<in>?M \<inter> M'. c e) + (\<Sum>e\<in>M' - ?M. c e)"
          by (auto simp: sum_negf Int_commute)
        also have "... = (\<Sum>e\<in>?M - M'. -c e) + (\<Sum>e\<in>M' - ?M. c e)"
          by simp
        also have "... \<le> (\<Sum>e\<in>?M - M'. -c e) + (\<Sum>e\<in>M' - ?M. \<bar>c e\<bar>)"
          by (simp add: sum_mono)
        also have "... \<le> (\<Sum>e\<in>?M - M'. \<bar>c e\<bar>) + (\<Sum>e\<in>M' - ?M. \<bar>c e\<bar>)"
          by (simp add: sum_mono)
        also have "... \<le> (\<Sum>e\<in>(?M - M') \<union> (M' - ?M). \<bar>c e\<bar>)"
          using \<open>(?M - M') \<inter> (M' - ?M) = {}\<close> 
                sum_Un[OF \<open>finite (?M - M')\<close> \<open>finite (M' - ?M)\<close>, where f="\<lambda>e. \<bar>c e\<bar>"] by simp
        also have "... \<le> (\<Sum>e\<in>?M \<union> M'. \<bar>c e\<bar>)"
          using \<open>finite (?M \<union> M')\<close> \<open>(?M - M') \<union> (M' - ?M) \<subseteq> ?M \<union> M'\<close> by (auto simp: sum_mono2)
        also have "... \<le> (\<Sum>e\<in>E. \<bar>c e\<bar>)"
          using \<open>finite E\<close> \<open>?M \<union> M' \<subseteq> E\<close> by (auto simp: sum_mono2)
        also have "... < ?K"
          by auto
        finally have "(\<Sum>e\<in>?M. -c e) + (\<Sum>e\<in>M'. c e) < ?K" .

        have "card ?M + 1 \<le> card M'"
          using \<open>card ?M < card M'\<close> by (auto simp: algebra_simps)
        then have "(card ?M + 1) * ?K \<le> card M' * ?K"
          using \<open>0 < ?K\<close> by auto
        then have "card ?M * ?K + ?K \<le> card M' * ?K"
          by (auto simp: algebra_simps)

        have "(\<Sum>e\<in>?M. ?c\<^sub>H e) = card ?M * ?K + (\<Sum>e\<in>?M. -c e)"
          using sum.distrib[where g="\<lambda>e. ?K" and h="\<lambda>e. -c e"] by auto
        also have "... < card ?M * ?K + ?K - (\<Sum>e\<in>M'. c e)"
          using \<open>(\<Sum>e\<in>?M. -c e) + (\<Sum>e\<in>M'. c e) < ?K\<close> by auto
        also have "... \<le> card M' * ?K - (\<Sum>e\<in>M'. c e)"
          using \<open>card ?M * ?K + ?K \<le> card M' * ?K\<close> by simp
        also have "... = (\<Sum>e\<in>M'. ?c\<^sub>H e)"
          using sum.distrib[where g="\<lambda>e. ?K" and h="\<lambda>e. -c e"] by (auto simp: sum_negf)
        finally have "(\<Sum>e\<in>?M. ?c\<^sub>H e) < (\<Sum>e\<in>M'. ?c\<^sub>H e)" .
        moreover have "(\<Sum>e\<in>M'. ?c\<^sub>H e) \<le> (\<Sum>e\<in>?M. ?c\<^sub>H e)"
          using M_max \<open>matching_in E M'\<close> by (auto simp add: is_max_match_def)
        ultimately show "False" by simp
      qed
      ultimately have M_max_card: "is_max_card_match E ?M"
        unfolding is_max_card_match_def by (auto simp add: is_max_match_def)
      then show ?thesis
      proof (cases "(f\<^sub>1 g) a")
        text \<open>If \<open>None\<close> is returned then there is no perfect matching in \<open>E\<close>.\<close>
        case None
        then have "matching_in E ?M"
          using \<open>graph_invar E\<close> \<open>solves P\<^sub>m\<^sub>a\<^sub>x g\<close> by (auto simp: solves_def is_max_match_def)
        then have "Vs ?M \<subseteq> Vs E"
          unfolding Vs_def by auto
        then have "Vs ?M \<subset> Vs E"
          using None by (auto simp add: f\<^sub>1_def)
        then have "card (Vs ?M) < card (Vs E)"
          using \<open>graph_invar E\<close> by (auto simp: psubset_card_mono)

        have "\<forall>M. matching_in E M \<longrightarrow> 2 * card M \<le> 2 * card ?M"
          using M_max_card[unfolded is_max_card_match_def] by auto
        then have "\<forall>M. matching_in E M \<longrightarrow> card (Vs M) \<le> card (Vs ?M)"
          using \<open>matching_in E ?M\<close> by (auto simp: matching_card[OF \<open>graph_invar E\<close>])
        then have "\<forall>M. matching_in E M \<longrightarrow> card (Vs M) < card (Vs E)"
          using \<open>card (Vs ?M) < card (Vs E)\<close> by auto
        then have "\<forall>M. matching_in E M \<longrightarrow> Vs M \<noteq> Vs E"
          by auto
        then have "\<nexists>M. is_perf_match E M"
          unfolding is_perf_match_def by auto
        then show ?thesis
          using None by auto
      next
        case (Some M)
        have "Vs M = Vs E" and [simp]: "M = ?M"
          using Some by (auto simp: f\<^sub>1_def Let_def split: if_splits)
        then have "is_perf_match E M" and M_max: "is_max_match E ?c\<^sub>H M"
          using \<open>graph_invar E\<close> \<open>solves P\<^sub>m\<^sub>a\<^sub>x g\<close> by (auto simp: solves_def is_perf_match_def is_max_match_def)
        then have "matching_in E M" 
          by (auto simp add: is_perf_match_def)

        have "\<forall>M'. is_perf_match E M' \<longrightarrow> (\<Sum>e\<in>M. c e) \<le> (\<Sum>e\<in>M'. c e)"
        proof (rule allI impI)+
          fix M'
          assume "is_perf_match E M'"
          then have "matching_in E M'" 
            unfolding is_perf_match_def by auto
          then have "2 * card M' = card (Vs M')"
            using matching_card[OF \<open>graph_invar E\<close>] by auto
          also have "... = card (Vs E)"
            using \<open>is_perf_match E M'\<close>[unfolded is_perf_match_def] by auto
          also have "... = card (Vs M)"
            using \<open>is_perf_match E M\<close>[unfolded is_perf_match_def] by auto
          also have "... = 2 * card M"
            using \<open>matching_in E M\<close> matching_card[OF \<open>graph_invar E\<close>, symmetric] by auto
          finally have "card M' = card M"
            by auto
          then have "(\<Sum>e\<in>M'. ?K) = (\<Sum>e\<in>M. ?K)"
            by auto
            
          have "matching_in E M'"
            using \<open>is_perf_match E M'\<close>[unfolded is_perf_match_def] by auto
          then have "(\<Sum>e\<in>M'. ?c\<^sub>H e) \<le> (\<Sum>e\<in>M. ?c\<^sub>H e)"
            using M_max[unfolded is_max_match_def] by auto
          then have "(\<Sum>e\<in>M'. ?K) + (\<Sum>e\<in>M'. -c e) \<le> (\<Sum>e\<in>M. ?K) + (\<Sum>e\<in>M. -c e)"
            using sum.distrib[where g="\<lambda>e. ?K" and h="\<lambda>e. -c e"] by auto
          then have "(\<Sum>e\<in>M'. -c e) \<le> (\<Sum>e\<in>M. -c e)"
            using \<open>(\<Sum>e\<in>M'. ?K) = (\<Sum>e\<in>M. ?K)\<close> by auto
          then show "(\<Sum>e\<in>M. c e) \<le> (\<Sum>e\<in>M'. c e)"
            by (auto simp: sum_negf)
        qed
        then have "is_min_match E c M"
          unfolding is_min_match_def using \<open>is_perf_match E M\<close> by auto
        then show ?thesis 
          using \<open>graph_invar E\<close> Some by auto
      qed
    qed
  qed
qed

lemma matching_inj:
  assumes mat: "matching M" and inj: "\<forall>x y. f x = f y \<longrightarrow> x = y"
  shows "matching {{f v, f w} |v w. {v,w}\<in>M}" (is "matching ?M'")
  unfolding matching_def
proof
  fix e1
  assume "e1\<in>?M'"
  then have "\<exists>v1 w1. {v1,w1}\<in>M \<and> {f v1,f w1} = e1"
    by auto
  then obtain v1 w1 where "{v1,w1}\<in>M" "{f v1,f w1} = e1"
    by auto
  show "\<forall>e2 \<in> ?M'. e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {}"
  proof
    fix e2
    assume "e2\<in>?M'"
    then have "\<exists>v2 w2. {v2,w2}\<in>M \<and> {f v2,f w2} = e2"
      by auto
    then obtain v2 w2 where "{v2,w2}\<in>M" "{f v2,f w2} = e2"
      by auto
    show "e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {}"
    proof
      assume "e1 \<noteq> e2"
      then have "(v1 \<noteq> v2 \<or> w1 \<noteq> w2) \<and> (v1 \<noteq> w2 \<or> w1 \<noteq> v2)"
        using doubleton_eq_iff \<open>{f v1,f w1} = e1\<close> \<open>{f v2,f w2} = e2\<close> by auto
      then have "{v1,w1} \<noteq> {v2,w2}"
        using inj by fastforce
      then have "{v1,w1} \<inter> {v2,w2} = {}"
        using \<open>{v1,w1}\<in>M\<close> \<open>{v2,w2}\<in>M\<close> mat
        unfolding matching_def by simp
      then have "{f v1,f w1} \<inter> {f v2,f w2} = {}"
        using inj by blast
      then show "e1 \<inter> e2 = {}"
        using \<open>{f v1,f w1} = e1\<close> \<open>{f v2,f w2} = e2\<close> by auto
    qed
  qed
qed

lemma inj_matching:
  assumes mat: "matching  {{f v, f w} |v w. {v,w}\<in>M}" (is "matching ?M'") 
      and inj: "\<forall>x y. f x = f y \<longrightarrow> x = y"
      and doubleton: "\<forall>e\<in>M. \<exists>v w. e = {v,w} \<and> v\<noteq>w"
  shows "matching M"
proof (rule ccontr)
  assume "\<not> matching M"
  then have "\<exists>e1\<in>M. \<exists>e2\<in>M. e1\<noteq>e2 \<and> e1\<inter>e2\<noteq>{}"
    unfolding matching_def by auto
  then obtain e1 e2 where "e1\<in>M" "e2\<in>M" "e1\<noteq>e2" "e1\<inter>e2\<noteq>{}"
    by auto
  then have "\<exists>v1 w1. e1={v1,w1}" "\<exists>v2 w2. e2={v2,w2}"
    using doubleton by auto
  then obtain v1 w1 v2 w2 where [simp]: "e1={v1,w1}" "e2={v2,w2}"
    by auto
  then have "{f v1,f w1} \<inter> {f v2,f w2}\<noteq>{}"
    using \<open>e1\<inter>e2\<noteq>{}\<close> by blast
  have "{f v1,f w1}\<in>?M'" "{f v2,f w2}\<in>?M'"
    using \<open>e1\<in>M\<close> \<open>e2\<in>M\<close> by auto
  moreover have "{f v1,f w1}\<noteq>{f v2,f w2}"
    using \<open>e1\<noteq>e2\<close> inj by fastforce
  ultimately have "{f v1,f w1} \<inter> {f v2,f w2}={}"
    using mat unfolding matching_def by auto
  then show "False"
    using \<open>{f v1,f w1} \<inter> {f v2,f w2}\<noteq>{}\<close> by auto
qed

lemma matching_pair_iff:
  assumes "\<forall>e\<in>M. \<exists>v w. e = {v,w} \<and> v\<noteq>w"
  shows "matching M \<longleftrightarrow> matching {{(v,k),(w,k)} |v w. {v,w}\<in>M}" (is "_ \<longleftrightarrow> matching ?M'")
proof
  assume "matching M"
  let ?f="\<lambda>v. (v,k)"
  have inj: "\<forall>x y. ?f x = ?f y \<longrightarrow> x = y"
    by auto
  then show "matching ?M'"
    using matching_inj[OF \<open>matching M\<close> inj] by simp
next
  assume "matching ?M'"
  let ?f="\<lambda>v. (v,k)"
  have inj: "\<forall>x y. ?f x = ?f y \<longrightarrow> x = y"
    by auto
  then show "matching M"
    using assms inj_matching[OF \<open>matching ?M'\<close> \<open>\<forall>x y. ?f x = ?f y \<longrightarrow> x = y\<close>] by fastforce
qed

lemma matching_pair_set_iff:
  assumes "\<forall>e\<in>M. \<exists>v w. e = {v,w} \<and> v\<noteq>w" "finite K" "K\<noteq>{}"
  shows "matching M \<longleftrightarrow> matching {{(v,(k::nat)),(w,k)} |v w k. {v,w}\<in>M \<and> k\<in>K}" (is "_ \<longleftrightarrow> matching ?M'")
proof -
  let ?MM="{{{(v,k),(w,k)} |v w. {v,w}\<in>M} |k. k\<in>K}"

  have "finite ?MM"
    using assms by auto

  have "(\<forall>Mk\<in>?MM. matching Mk) \<longleftrightarrow> matching M"
  proof
    assume "\<forall>Mk\<in>?MM. matching Mk"
    obtain Mk k where "Mk={{(v,k),(w,k)} |v w. {v,w}\<in>M}" "k\<in>K" "Mk\<in>?MM"
      using assms by auto
    then have "matching Mk"
      using \<open>\<forall>Mk\<in>?MM. matching Mk\<close> by auto
    then show "matching M"
      using assms matching_pair_iff \<open>Mk={{(v,k),(w,k)} |v w. {v,w}\<in>M}\<close> by fastforce
  next
    assume "matching M"
    show "\<forall>Mk\<in>?MM. matching Mk"
    proof 
      fix Mk
      assume "Mk\<in>?MM"
      then obtain k where "Mk={{(v,k),(w,k)} |v w. {v,w}\<in>M}"
        by auto
      then show "matching Mk"
        using assms matching_pair_iff \<open>matching M\<close> by fastforce
    qed
  qed

  have "\<forall>Mk1\<in>?MM.\<forall>Mk2\<in>?MM. Mk1 \<noteq> Mk2 \<longrightarrow> Vs Mk1 \<inter> Vs Mk2 = {}"
  proof (rule ballI impI)+
    fix Mk1 Mk2
    assume "Mk1\<in>?MM" "Mk2\<in>?MM" "Mk1 \<noteq> Mk2"
    then obtain k1 k2 where "Mk1={{(v,k1),(w,k1)} |v w. {v,w}\<in>M}" "Mk2={{(v,k2),(w,k2)} |v w. {v,w}\<in>M}" "k1\<noteq>k2"
      by auto
    show "Vs Mk1 \<inter> Vs Mk2 = {}"
    proof (rule ccontr)
      assume "Vs Mk1 \<inter> Vs Mk2 \<noteq> {}"
      then obtain v where "v\<in>Vs Mk1" "v\<in>Vs Mk2"
        by auto
      then have "\<exists>e\<in>Mk1. v\<in>e" "\<exists>e\<in>Mk2. v\<in>e"
        by (auto simp: Vs_def)
      then obtain e1 e2 where "v\<in>e1" "e1\<in>Mk1" "v\<in>e2" "e2\<in>Mk2"
        by auto
      then obtain v1 w1 v2 w2 where "{v1,w1}\<in>M" "{v2,w2}\<in>M" 
                                 "e1={(v1,k1),(w1,k1)}" "e2={(v2,k2),(w2,k2)}"
        using \<open>Mk1={{(v,k1),(w,k1)} |v w. {v,w}\<in>M}\<close> \<open>Mk2={{(v,k2),(w,k2)} |v w. {v,w}\<in>M}\<close> by auto
    then have "v\<in>{(v1,k1),(w1,k1)}" "v\<in>{(v2,k2),(w2,k2)}"
      using \<open>v\<in>e1\<close> \<open>v\<in>e2\<close> by auto
    then have "v\<in>{(v1,k1),(w1,k1)} \<inter> {(v2,k2),(w2,k2)}"
      by blast
    then show "False"
      using \<open>k1\<noteq>k2\<close> by auto
    qed
  qed

  have "?M' = \<Union> ?MM"
    by blast

  show ?thesis
  proof
    assume "matching M"
    then have "\<forall>Mk\<in>?MM. matching Mk"
      using \<open>(\<forall>Mk\<in>?MM. matching Mk) \<longleftrightarrow> matching M\<close> by auto
    then show "matching ?M'"
      using \<open>?M' = \<Union> ?MM\<close> matching_bigunion[OF \<open>finite ?MM\<close> \<open>\<forall>Mk1\<in>?MM.\<forall>Mk2\<in>?MM. Mk1 \<noteq> Mk2 \<longrightarrow> Vs Mk1 \<inter> Vs Mk2 = {}\<close>] 
      by auto
  next
    assume "matching ?M'"
    then have "matching (\<Union> ?MM)"
      using \<open>?M' = \<Union> ?MM\<close> by auto
    then have "\<forall>Mk\<in>?MM. matching Mk"
      using matching_subset by auto
    then show "matching M"
      using \<open>(\<forall>Mk\<in>?MM. matching Mk) \<longleftrightarrow> matching M\<close> by auto
  qed
qed

lemma VsH: 
  fixes E
  defines "E\<^sub>H \<equiv> {{(v,i),(w,i)} |v w i. {v,w}\<in>E \<and> i\<in>{1::nat,2}} \<union> {{(v,1::nat),(v,2)} |v. v\<in>Vs E}" (is "E\<^sub>H \<equiv> ?H1 \<union> ?H2")
  assumes "graph_invar E"
  shows "Vs E\<^sub>H = {(v,i)|v i. v\<in>Vs E \<and> i\<in>{1::nat,2}}" (is "Vs E\<^sub>H = ?VsH")
proof
  show "Vs E\<^sub>H \<subseteq> ?VsH"
  proof
    fix x
    assume "x\<in>Vs E\<^sub>H"
    then have "\<exists>e\<in>E\<^sub>H. x\<in>e"
      unfolding Vs_def by auto
    then have "(\<exists>e\<in>?H1. x\<in>e) \<or> (\<exists>e\<in>?H2. x\<in>e)"
      unfolding E\<^sub>H_def using assms by (meson UnE)
    then show "x\<in>?VsH"
    proof
      assume "\<exists>e\<in>?H1. x\<in>e"
      then obtain e where "e\<in>?H1" "x\<in>e"
        by auto
      then obtain v w i where "e={(v,i),(w,i)}" "{v,w}\<in>E" "i\<in>{1::nat,2}"
        by auto
      then have "(x=(v,i) \<and> v\<in>Vs E) \<or> (x=(w,i) \<and> w\<in>Vs E)"
        unfolding Vs_def using \<open>x\<in>e\<close> by auto
      then show "x\<in>?VsH"
        using \<open>i\<in>{1::nat,2}\<close> by blast
    next
      assume "\<exists>e\<in>?H2. x\<in>e"
      then obtain e where "e\<in>?H2" "x\<in>e"
        by auto
      then obtain v where "e={(v,1::nat),(v,2)}" "v\<in>Vs E"
        by auto
      then show "x\<in>?VsH"
        using \<open>x\<in>e\<close> by blast
    qed
  qed
next
  show "?VsH \<subseteq> Vs E\<^sub>H"
  proof
    fix x
    assume "x\<in>?VsH"
    then obtain v i where "v\<in>Vs E" "i\<in>{1::nat,2}" "x=(v,i)"
      by auto
    then have "\<exists>e\<in>E. v\<in>e"
      unfolding Vs_def by auto
    then have "\<exists>v1 w1. {v1,w1}\<in>E \<and> v1\<noteq>w1 \<and> v\<in>{v1,w1}"
      using assms by fastforce
    then have "\<exists>w. {v,w}\<in>E"
      by (metis doubleton_eq_iff insert_iff singleton_iff)
    then obtain w where "{v,w}\<in>E"
      by auto
    then have "{x,(w,i)}\<in>?H1"
      using \<open>x=(v,i)\<close> \<open>i\<in>{1::nat,2}\<close> by auto
    then show "x\<in>Vs E\<^sub>H"
      using assms unfolding Vs_def by auto
  qed
qed

lemma graph_invar_H:
  fixes E
  defines "E\<^sub>H \<equiv> {{(v,i),(w,i)} |v w i. {v,w}\<in>E \<and> i\<in>{(1::nat),2}} \<union> {{(v,1::nat),(v,2)} |v. v\<in>Vs E}" (is "E\<^sub>H \<equiv> ?H1 \<union> ?H2")
  assumes "graph_invar E"
  shows "graph_invar E\<^sub>H"
proof
  show "\<forall>e\<in>E\<^sub>H. \<exists>u v. e = {u,v} \<and> u \<noteq> v"
  proof
    fix e
    assume "e\<in>E\<^sub>H"
    then have "e\<in>?H1 \<or> e\<in>?H2"
      using assms by auto
    then show "\<exists>u v. e = {u, v} \<and> u \<noteq> v"
    proof
      assume "e\<in>?H1"
      then obtain v w i where "e={(v,i),(w,i)}" "{v,w}\<in>E" "i\<in>{(1::nat),2}"
        using assms by auto
      then have "v\<noteq>w"
        using assms by auto
      then have "(v,i)\<noteq>(w,i)"
        by auto
      then show "\<exists>u v. e = {u, v} \<and> u \<noteq> v"
        using \<open>e={(v,i),(w,i)}\<close> by auto
    next
      assume "e\<in>?H2"
      then obtain v where "e={(v,1::nat),(v,2)}" "v\<in>Vs E"
        using assms by auto
      then have "(v,1::nat)\<noteq>(v,2)"
        by auto
      then show "\<exists>u v. e = {u, v} \<and> u \<noteq> v"
        using \<open>e={(v,1::nat),(v,2)}\<close> by blast
    qed
  qed

  show "finite (Vs E\<^sub>H)"
    using assms VsH[of E] by auto
qed

lemma matching_to_perfect_matching:
  fixes E M
  defines "E\<^sub>H \<equiv> {{(v,i),(w,i)} |v w i. {v,w}\<in>E \<and> i\<in>{1::nat,2}} \<union> {{(v,1::nat),(v,2)} |v. v\<in>Vs E}" (is "E\<^sub>H \<equiv> ?H1 \<union> ?H2")
      and "M' \<equiv> {{(v,i),(w,i)}|v w i. {v,w}\<in>M \<and> i\<in>{1::nat,2}} \<union> {{(v,1::nat),(v,2)}|v. v\<in>(Vs E)-(Vs M)}" (is "M' \<equiv> ?M1' \<union> ?M2'")
  assumes "graph_invar E" "matching_in E M" 
  shows "is_perf_match E\<^sub>H M'"
proof (intro is_perf_matchI)
  have "\<forall>e\<in>M. \<exists>v w. e={v,w} \<and> v\<noteq>w" "finite {1::nat,2}" "{1::nat,2} \<noteq> {}"
    using assms by auto
  then have "matching ?M1'"
    using assms matching_pair_set_iff[OF \<open>\<forall>e\<in>M. \<exists>v w. e={v,w} \<and> v\<noteq>w\<close>, of "{1::nat,2}"] by auto
  
  have "matching ?M2'"
  proof (rule ccontr)
    assume "\<not>matching ?M2'"
    then have "\<exists>e\<in>?M2'. \<forall>v w. e={v,w} \<longrightarrow> v=w"
      unfolding matching_def by blast
    then obtain e where "e\<in>?M2'" "\<forall>v w. e={v,w} \<longrightarrow> v=w"
      by auto
    then obtain v where "v\<in>(Vs E)-(Vs M)" "e={(v,1::nat),(v,2)}"
      by blast
    then have "(v,1::nat)=(v,2)"
      using \<open>\<forall>v w. e = {v, w} \<longrightarrow> v = w\<close> by blast
    then show "False"
      by simp
  qed
  
  have "graph_invar E\<^sub>H"
    using assms graph_invar_H[OF \<open>graph_invar E\<close>] by auto

  have "Vs ?M1' \<inter> Vs ?M2' = {}"
  proof (rule ccontr)
    assume "Vs ?M1' \<inter> Vs ?M2' \<noteq> {}"
    then obtain x where "x\<in>Vs ?M1'" "x\<in>Vs ?M2'"
      by blast
    then have "\<exists>!e\<in>?M1'. x\<in>e" "\<exists>!e\<in>?M2'. x\<in>e"
      using \<open>matching ?M1'\<close> matching_def2[of ?M1'] \<open>matching ?M2'\<close> matching_def2[of ?M2'] by auto
    then obtain e where "x\<in>e" "e\<in>?M1'" "e\<in>?M2'"
      by blast
    then obtain v1 w1 i v2 where "{v1,w1}\<in>M" "i\<in>{1::nat,2}" "v2\<in>(Vs E)-(Vs M)" 
                                 "e={(v1,i),(w1,i)}" "e={(v2,1::nat),(v2,2)}"
      by auto
    then have "x\<in>{(v1,i),(w1,i)}" "x\<in>{(v2,1::nat),(v2,2)}"
      using \<open>x\<in>e\<close> by auto
    then have "x\<in>{(v1,i),(w1,i)} \<inter> {(v2,1::nat),(v2,2)}"
      by blast

    have "\<forall>e\<in>M. v2\<notin>e"
      using \<open>v2\<in>(Vs E)-(Vs M)\<close> by blast
    then have "v2\<notin>{v1,w1}"
      using \<open>{v1,w1}\<in>M\<close> by fastforce
    then have "v1\<noteq>v2 \<and> w1\<noteq>v2"
      by blast
    then have "{(v1,i),(w1,i)} \<inter> {(v2,1::nat),(v2,2)} = {}"
      by blast
    then show "False"
      using \<open>x\<in>{(v1,i),(w1,i)} \<inter> {(v2,1::nat),(v2,2)}\<close> by blast
  qed

  have "Vs E\<^sub>H = {(v,i)|v i. v\<in>Vs E \<and> i\<in>{1::nat,2}}" (is "Vs E\<^sub>H = ?VsH")
    using assms VsH[of E] by auto

  show "M' \<subseteq> E\<^sub>H"
  proof
    fix e
    assume "e\<in>M'"
    then have "(\<exists>v w i. {v,w}\<in>M \<and> i\<in>{1::nat,2} \<and> e={(v,i),(w,i)}) \<or> (\<exists>v. v\<in>(Vs E)-(Vs M) \<and> e={(v,1::nat),(v,2)})"
      using assms by auto
    then show "e\<in>E\<^sub>H"
    proof 
      assume "\<exists>v w i. {v,w}\<in>M \<and> i\<in>{1::nat,2} \<and> e={(v,i),(w,i)}"
      then show "e\<in>E\<^sub>H"
        unfolding E\<^sub>H_def using assms by fast
    next
      assume "\<exists>v. v\<in>(Vs E)-(Vs M) \<and> e={(v,1::nat),(v,2)}"
      then show "e\<in>E\<^sub>H"
        using assms by blast
    qed
  qed
  moreover show "matching M'"
  proof -
    have "matching (?M1' \<union> ?M2')"
      using assms \<open>Vs ?M1' \<inter> Vs ?M2' = {}\<close> matching_union[OF \<open>matching ?M1'\<close> \<open>matching ?M2'\<close>] by fastforce
    then show "matching M'"
      using assms by simp 
  qed
  ultimately have "matching_in E\<^sub>H M'"
    by auto
  thus "Vs M' = Vs E\<^sub>H"
  proof -
    have "Vs M' = ?VsH"
    proof
      show "Vs M' \<subseteq> ?VsH"
        using \<open>M' \<subseteq> E\<^sub>H\<close> \<open>Vs E\<^sub>H = ?VsH\<close> Vs_subset[of M' E\<^sub>H] by auto
    next
      show "?VsH \<subseteq> Vs M'"
      proof
        fix x
        assume "x\<in>?VsH"
        then obtain v i where "v\<in>Vs E" "i\<in>{1::nat,2}" "x=(v,i)"
          by auto
        then have "\<exists>e\<in>E. v\<in>e"
          unfolding Vs_def by auto
        then have "\<exists>v1 w1. {v1,w1}\<in>E \<and> v1\<noteq>w1 \<and> v\<in>{v1,w1}"
          using assms by fastforce
        then have "\<exists>w. {v,w}\<in>E"
          by (metis doubleton_eq_iff insert_iff singleton_iff)

        then have "(\<exists>w. {v,w}\<in>M) \<or> v\<in>(Vs E)-(Vs M)"
        proof (cases "v\<in>(Vs E)-(Vs M)")
          case False
          then have "v\<notin>(Vs E)-(Vs M)" "(Vs M)\<subseteq>(Vs E)"
            using assms Union_mono by (auto simp: Vs_def)
          then have "v\<in>Vs M"
            using \<open>v\<in>Vs E\<close> by simp
          then have "\<exists>!e\<in>M. v\<in>e" "\<forall>e\<in>M. \<exists>u v. e={u,v} \<and> u\<noteq>v"
            using assms matching_def2[of M] by auto
          then obtain e where "e\<in>M" "v\<in>e" "\<exists>u v. e={u,v} \<and> u\<noteq>v"
            by auto
          then obtain w where "e={v,w}"
            by auto
          then have "\<exists>w. {v,w}\<in>M"
            using \<open>e\<in>M\<close> by blast
          then show ?thesis 
            by auto
        qed auto
        then show "x\<in>Vs M'"
        proof
          assume "\<exists>w. {v,w}\<in>M"
          then obtain w where "{v,w}\<in>M"
            by auto
          then have "{x,(w,i)}\<in>M'"
            using assms \<open>x=(v,i)\<close> \<open>i\<in>{1::nat,2}\<close> by auto 
          then show ?thesis
            by (auto simp: Vs_def) 
        next
          assume "v\<in>(Vs E)-(Vs M)"
          then have "{(v,1::nat),(v,2)}\<in>M'" "x\<in>{(v,1::nat),(v,2)}"
            using assms \<open>x=(v,i)\<close> \<open>i\<in>{1::nat,2}\<close> by auto
          then show ?thesis
            by (auto simp: Vs_def)
        next
        qed
      qed
    qed
    then show "Vs M' = Vs E\<^sub>H"
      using \<open>Vs E\<^sub>H = ?VsH\<close> by auto
  qed
qed

lemma perfect_matching_to_matching:
  fixes E M'
  defines "E\<^sub>H \<equiv> {{(v,i),(w,i)} |v w i. {v,w}\<in>E \<and> i\<in>{(1::nat),2}} \<union> {{(v,(1::nat)),(v,2)} |v. v\<in>Vs E}"
      and "M \<equiv> {{v,w} |v w. {(v,(1::nat)),(w,1)}\<in>M'}"
  assumes "graph_invar E" "is_perf_match E\<^sub>H M'"
  shows "matching_in E M"
proof -
  have "M \<subseteq> E"
  proof
    fix e
    assume "e\<in>M"
    then have "\<exists>v w. e = {v,w} \<and> {(v,(1::nat)),(w,1)}\<in>M'"
      using assms by fastforce
    then obtain v w where "e = {v,w}" "{(v,(1::nat)),(w,1)}\<in>M'"
      by auto
    then have "(\<exists>v'. {(v,(1::nat)),(w,1)} = {(v',(1::nat)),(v',2)}) 
          \<or> (\<exists>v' w' i. {(v,(1::nat)),(w,1)} = {(v',i),(w',i)} \<and> {v',w'}\<in>E \<and> i\<in>{(1::nat),2})"
      using assms[unfolded is_perf_match_def E\<^sub>H_def] by blast
    then have "\<exists>v' w' i. {(v,(1::nat)),(w,1)} = {(v',i),(w',i)} \<and> {v',w'}\<in>E"
    proof 
      assume "\<exists>v'. {(v,(1::nat)),(w,1)} = {(v',(1::nat)),(v',2)}"
      then obtain v' where "{(v,(1::nat)),(w,1)} = {(v',(1::nat)),(v',2)}"
        by auto
      then have "(v,(1::nat)) = (v',1) \<and> (w,(1::nat)) = (v',2) \<or> (v,(1::nat)) = (v',2) \<and> (w,(1::nat)) = (v',1)"
        using doubleton_eq_iff[of "(v,(1::nat))" "(w,1)" "(v',(1::nat))" "(v',2)"] by simp
      then have "(1::nat) = 2"
        by blast
      then have "False"
        by auto
      then show ?thesis
        by auto
    next
      assume "\<exists>v' w' i. {(v,(1::nat)),(w,1)} = {(v',i),(w',i)} \<and> {v',w'}\<in>E \<and> i\<in>{(1::nat),2}"
      then show ?thesis
        by auto
    qed
    then obtain v' w' i where "{(v,(1::nat)),(w,1)} = {(v',i),(w',i)}" "{v',w'}\<in>E"
      by auto
    then have "(v,(1::nat)) = (v',i) \<and> (w,(1::nat)) = (w',i) \<or> (v,(1::nat)) = (w',i) \<and> (w,(1::nat)) = (v',i)"
      using doubleton_eq_iff[of "(v,(1::nat))" "(w,1)" "(v',i)" "(w',i)"] by simp
    then have "v = v' \<and> w = w' \<or> v = w' \<and> w = v'"
      by blast
    then have "e = {v',w'}"
      using \<open>e = {v,w}\<close> by auto
    then show "e\<in>E"
      using \<open>{v',w'}\<in>E\<close> by auto
  qed
  moreover have "matching M"
  proof -
    have "\<forall>e\<in>M. \<exists>v w. e = {v,w} \<and> v\<noteq>w"
      using \<open>graph_invar E\<close> \<open>M \<subseteq> E\<close> by auto
    
    have "{{(v,(1::nat)),(w,1)} |v w. {v,w}\<in>M} \<subseteq> M'"
    proof
      fix x
      assume "x\<in>{{(v,(1::nat)),(w,1)} |v w. {v,w}\<in>M}"
      then obtain v w where "{v,w}\<in>M" "x={(v,(1::nat)),(w,1)}"
        by auto
      have "\<exists>v' w'. {(v',(1::nat)),(w',1)}\<in>M' \<and> {v,w}={v',w'}"
        using \<open>{v,w}\<in>M\<close> M_def by auto
      then obtain v' w' where "{v,w}={v',w'}" "{(v',(1::nat)),(w',1)}\<in>M'"
        by auto
      then have "x={(v',(1::nat)),(w',1)}"
        using \<open>x={(v,(1::nat)),(w,1)}\<close> by (simp add: doubleton_eq_iff)
      then show "x\<in>M'"
        using \<open>{(v',(1::nat)),(w',1)}\<in>M'\<close> by auto
    qed
    then have "matching {{(v,(1::nat)),(w,1)} |v w. {v,w}\<in>M}"
      using assms[unfolded is_perf_match_def] matching_subset by auto
    then show ?thesis
      using matching_pair_iff[OF \<open>\<forall>e\<in>M. \<exists>v w. e = {v,w} \<and> v\<noteq>w\<close>, of 1, symmetric] by blast
  qed
  ultimately show "matching_in E M"
    by auto
qed

lemma sum_union: "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> (\<Sum>e\<in>A. f e) + (\<Sum>e\<in>B. f e) = (\<Sum>e\<in>A\<union>B. f e)"
  by (simp add: sum.union_disjoint)

text \<open>We construct a new graph \<open>H\<close>, that contains two copies of the graph \<open>E\<close>. The two copies are 
  connected at each vertex.\<close>
definition "E\<^sub>H \<equiv> \<lambda>E. {{(v,i),(w,i)} |v w i. {v,w}\<in>E \<and> i\<in>{(1::nat),2}} \<union> {{(v,(1::nat)),(v,2)} |v. v\<in>Vs E}"

text \<open>We map edges of the graph \<open>H\<close>. \<open>{(v,i),(w,i)} \<in> E(H)\<close> to edges in the graph 
  \<open>E\<close>. \<open>{v,w} \<in> E\<close> with the expression \<open>fst ` e\<close>.\<close>
definition "c\<^sub>H \<equiv> \<lambda>(E,c) e. if fst ` e \<in> E \<and> snd ` e = {1} then -c (fst ` e) else (0::int)"

text \<open>To compute a solution to \<open>?P\<^sub>m\<^sub>a\<^sub>x\<close> we first compute the minimum perfect weight matching 
  \<open>M\<close> in \<open>(?H,?c\<^sub>H)\<close>. The solution to \<open>?P\<^sub>m\<^sub>a\<^sub>x\<close> is obtained by taking the edge \<open>{v,w}\<close> for every 
  edge \<open>{(v,1),(w,1)}\<in>M\<close> \<close>
definition f\<^sub>2 :: "(('a \<times> nat) set set \<times> (('a \<times> nat) set \<Rightarrow> int) \<Rightarrow> ('a \<times> nat) set set option) \<Rightarrow> 'a set set \<times> ('a set \<Rightarrow> int) \<Rightarrow> 'a set set" 
  where "f\<^sub>2 \<equiv> \<lambda>g (E,c). 
    case g (E\<^sub>H E,c\<^sub>H (E,c)) of Some M \<Rightarrow> {{v,w} |v w. {(v,(1::nat)),(w,1)}\<in>M}"

corollary P\<^sub>m\<^sub>i\<^sub>n_leq_P\<^sub>m\<^sub>a\<^sub>x: 
  assumes "solves P\<^sub>m\<^sub>i\<^sub>n g"
  shows "solves P\<^sub>m\<^sub>a\<^sub>x (f\<^sub>2 g)"
proof (rule solvesI)
  fix a
  show "is_sol P\<^sub>m\<^sub>a\<^sub>x a (f\<^sub>2 g a)"
  proof (cases a)
    case (Pair E c)
    then have [simp]: "a = (E,c)" . 
    let ?M="g (E\<^sub>H E,c\<^sub>H (E,c))"
        
    text \<open>We first show there is a perfect matching in \<open>H\<close>.\<close>
    let ?M\<^sub>p\<^sub>e\<^sub>r\<^sub>f\<^sub>e\<^sub>c\<^sub>t="{{(v,(1::nat)),(v,2)} |v. v\<in>Vs E}"
    have "matching_in (E\<^sub>H E) ?M\<^sub>p\<^sub>e\<^sub>r\<^sub>f\<^sub>e\<^sub>c\<^sub>t"
      unfolding matching_def by (auto simp add: E\<^sub>H_def)
    moreover have "Vs ?M\<^sub>p\<^sub>e\<^sub>r\<^sub>f\<^sub>e\<^sub>c\<^sub>t = Vs (E\<^sub>H E)"
    proof
      have "?M\<^sub>p\<^sub>e\<^sub>r\<^sub>f\<^sub>e\<^sub>c\<^sub>t \<subseteq> E\<^sub>H E"
        using \<open>matching_in (E\<^sub>H E) ?M\<^sub>p\<^sub>e\<^sub>r\<^sub>f\<^sub>e\<^sub>c\<^sub>t\<close> by (auto simp add: E\<^sub>H_def)
      then show "Vs ?M\<^sub>p\<^sub>e\<^sub>r\<^sub>f\<^sub>e\<^sub>c\<^sub>t \<subseteq> Vs (E\<^sub>H E)"
        using Vs_subset[of ?M\<^sub>p\<^sub>e\<^sub>r\<^sub>f\<^sub>e\<^sub>c\<^sub>t "E\<^sub>H E"] by (auto simp add: E\<^sub>H_def)
    next
      show "Vs (E\<^sub>H E) \<subseteq> Vs ?M\<^sub>p\<^sub>e\<^sub>r\<^sub>f\<^sub>e\<^sub>c\<^sub>t"
      proof 
        fix x
        assume "x\<in>Vs (E\<^sub>H E)"
        then have "\<exists>v\<in>Vs E. \<exists>i\<in>{1,2}. x=(v,i)"
          unfolding E\<^sub>H_def Vs_def by blast
        then show "x\<in>Vs ?M\<^sub>p\<^sub>e\<^sub>r\<^sub>f\<^sub>e\<^sub>c\<^sub>t"
          by blast
      qed
    qed
    ultimately have M\<^sub>p\<^sub>e\<^sub>r\<^sub>f\<^sub>e\<^sub>c\<^sub>t_is_perfect: "is_perf_match (E\<^sub>H E) ?M\<^sub>p\<^sub>e\<^sub>r\<^sub>f\<^sub>e\<^sub>c\<^sub>t" 
      unfolding is_perf_match_def by (auto simp add: E\<^sub>H_def)
    hence min_matching_ex: "\<exists>M. is_perf_match (E\<^sub>H E) M"
      by auto

    text \<open>We split cases whether the input graph \<open>E\<close> satisfies the graph invariant.\<close>
    show "is_sol P\<^sub>m\<^sub>a\<^sub>x a (f\<^sub>2 g a)"
    proof (cases "graph_invar E")
      case False
      then show ?thesis by auto
    next
      case True

      text \<open>If the graph \<open>E\<close> satisfies the graph invariant, so does the constructed graph \<open>E\<^sub>H E\<close>.\<close>
      have "graph_invar (E\<^sub>H E)"
        using graph_invar_H[OF \<open>graph_invar E\<close>] by (auto simp add: E\<^sub>H_def)

      text \<open>We know there is a perfect matching in \<open>?H (G,c)\<close>, thus there also is a minimum 
        perfect weight matching. Therefore the output of \<open>g\<close> cannot be \<open>None\<close>.\<close>
      have "\<not>?M = None"
      proof
        assume [simp]: "?M = None"
        have "is_sol P\<^sub>m\<^sub>i\<^sub>n (E\<^sub>H E,c\<^sub>H (E,c)) ?M"
          using assms[unfolded solves_def] by (auto simp add: E\<^sub>H_def)
        then have "is_sol P\<^sub>m\<^sub>i\<^sub>n (E\<^sub>H E,c\<^sub>H (E,c)) None"
          by (simp only: \<open>?M = None\<close>)
        then have "\<nexists>M. is_perf_match (E\<^sub>H E) M"
          using \<open>graph_invar (E\<^sub>H E)\<close> by auto
        then show "False"
          using min_matching_ex by blast
      qed
      then have "\<exists>M. ?M = Some M"
        by auto
      then obtain M where [simp]: "?M = Some M"
        by auto

      text \<open>We obtain the facts that the output of \<open>g\<close> is a matching.\<close>
      have "is_sol P\<^sub>m\<^sub>i\<^sub>n (E\<^sub>H E,c\<^sub>H (E,c)) ?M"
        using assms[unfolded solves_def] by (auto simp add: E\<^sub>H_def)
      then have "is_sol P\<^sub>m\<^sub>i\<^sub>n (E\<^sub>H E,c\<^sub>H (E,c)) (Some M)"
        by (simp only: \<open>?M = Some M\<close>)
      then have "is_min_match (E\<^sub>H E) (c\<^sub>H (E,c)) M"
        using \<open>graph_invar (E\<^sub>H E)\<close> by (auto simp add: E\<^sub>H_def)
      then have "is_perf_match (E\<^sub>H E) M"
        by (auto simp add: is_min_match_def)
      then have "matching_in (E\<^sub>H E) M"
        unfolding is_perf_match_def by simp
      then have "matching M" "M \<subseteq> E\<^sub>H E"
        by auto
      then have "finite M"
        using \<open>graph_invar (E\<^sub>H E)\<close> edges_finite[of "E\<^sub>H E"] finite_subset[of M "E\<^sub>H E"] by auto

      let ?M'="(f\<^sub>2 g) (E,c)"
      have "?M' = {{v,w} |v w. {(v,(1::nat)),(w,1)}\<in>M}"
        using \<open>?M = Some M\<close> by (auto simp add: f\<^sub>2_def)
      have "matching_in E ?M'"
        using \<open>is_perf_match (E\<^sub>H E) M\<close> \<open>?M' = {{v,w} |v w. {(v,(1::nat)),(w,1)}\<in>M}\<close> 
          perfect_matching_to_matching[OF \<open>graph_invar E\<close>] by (auto simp add: E\<^sub>H_def)
      text \<open>We show the output of \<open>?f g\<close> is a maximum matching.\<close>
      moreover have "\<forall>M'. matching_in E M' \<longrightarrow> (\<Sum>e\<in>M'. c e) \<le> (\<Sum>e\<in>?M'. c e)"
      proof (rule allI impI)+
        fix M'
        assume "matching_in E M'"
        then have "M' \<subseteq> E"
          by auto
        then have "graph_invar M'"
          using \<open>graph_invar E\<close> finite_subset[OF Vs_subset] by auto
        then have "finite M'" "graph_invar M'"
          using edges_finite[of M'] by auto

        text \<open>We translate the matching \<open>M'\<close> into a perfect matching in \<open>?H (G,c)\<close>.\<close>
        let ?M1''="{{(v,i),(w,i)}|v w i. {v,w}\<in>M' \<and> i\<in>{1::nat,2}}"
        let ?M2''="{{(v,1::nat),(v,2)}|v. v\<in>(Vs E)-(Vs M')}"
        let ?M''="?M1'' \<union> ?M2''"
        have "?M1'' \<inter> ?M2'' = {}"
        proof (rule ccontr)
          assume "?M1'' \<inter> ?M2'' \<noteq> {}"
          then obtain e where "e\<in>?M1''" and "e\<in>?M2''"
            by blast
          then obtain v1 w1 i v2 where "{v1,w1}\<in>M'" "i\<in>{1::nat,2}" "e={(v1,i),(w1,i)}" "v2\<in>(Vs E)-(Vs M')" "e={(v2,1::nat),(v2,2)}"
            by auto
          then have "(v2,1::nat)\<in>{(v1,i),(w1,i)} \<and> (v2,2::nat)\<in>{(v1,i),(w1,i)}"
            by blast
          then show "False"
            by auto
        qed
            
        have "?M1'' \<subseteq> (\<lambda>(e,i). (\<lambda>v. (v,i)) ` e) ` (M' \<times> {1,2})"
        proof
          fix e'
          assume "e' \<in> ?M1''"
          then obtain v w i where "e' = {(v,i),(w,i)}" "{v,w} \<in> M'" "i \<in> {1,2}"
            by blast
          moreover hence "e' = (\<lambda>(e,i). (\<lambda>v. (v,i)) ` e) ({v,w},i)"
            by auto
          ultimately show "e' \<in> (\<lambda>(e,i). (\<lambda>v. (v,i)) ` e) ` (M' \<times> {1,2})"
            by blast
        qed
        moreover have "finite ((\<lambda>(e,i). (\<lambda>v. (v,i)) ` e) ` (M' \<times> {1,2}))"
          using \<open>finite M'\<close> by blast
        ultimately have "finite ?M1''" 
          by (rule finite_subset) 
        have "finite (Vs E - Vs M')"
          using \<open>graph_invar E\<close> by auto
        moreover have "?M2'' = (\<lambda>v. {(v,1),(v,2)}) ` (Vs E - Vs M')"
          by blast
        ultimately have "finite ?M2''"
          by auto

        have "is_perf_match (E\<^sub>H E) ?M''"
          using \<open>matching_in E M'\<close> matching_to_perfect_matching[OF \<open>graph_invar E\<close>] by (auto simp add: E\<^sub>H_def)
        then have "(\<Sum>e\<in>M. (c\<^sub>H (E,c)) e) \<le> (\<Sum>e\<in>?M''. (c\<^sub>H (E,c)) e)"
          using \<open>is_min_match (E\<^sub>H E) (c\<^sub>H (E,c)) M\<close> by (auto simp add: E\<^sub>H_def is_min_match_def)
        then have "-(\<Sum>e\<in>?M''. (c\<^sub>H (E,c)) e) \<le> -(\<Sum>e\<in>M. (c\<^sub>H (E,c)) e)"
          by auto

        have "\<forall>e\<in>{{(v,1::nat),(v,2)}|v. v\<in>(Vs E)-(Vs M')}. (c\<^sub>H (E,c)) e = 0"
          by (auto simp add: c\<^sub>H_def)
        then have "(\<Sum>e\<in>{{(v,1::nat),(v,2)}|v. v\<in>(Vs E)-(Vs M')}. (c\<^sub>H (E,c)) e) = 0"
          by auto

        have "\<forall>e\<in>{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'}. fst ` e\<in>E \<and> snd ` e = {1}"
          using \<open>M' \<subseteq> E\<close> by auto
        then have "\<forall>e\<in>{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'}. (c\<^sub>H (E,c)) e = -c (fst ` e)"
          by (auto simp add: c\<^sub>H_def)

        have "\<forall>e\<in>{{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'}. fst ` e\<in>E \<and> snd ` e = {2}"
          using \<open>M' \<subseteq> E\<close> by auto
        then have "\<forall>e\<in>{{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'}. (c\<^sub>H (E,c)) e = 0"
          by (auto simp add: c\<^sub>H_def)

        have "{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'} \<union> {{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'} = {{(v,i),(w,i)}|v w i. {v,w}\<in>M' \<and> i\<in>{1::nat,2}}"
          by blast
        have "{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'} \<inter> {{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'} = {}"
        proof (rule ccontr)
          assume "{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'} \<inter> {{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'} \<noteq> {}"
          then obtain v w i where "{(v,i),(w,i)}\<in>{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'} \<inter> {{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'}"
            by blast
          then have "i = 1" "i = 2"
            by auto
          then show "False"
            by auto
        qed

        have "\<forall>e\<in>M. snd ` e = {1::nat} \<longrightarrow> fst ` e\<in>E"
        proof (rule ballI impI)+
          fix e
          assume "e\<in>M" "snd ` e = {1::nat}"
          then have "e\<in>{{(v,i), (w,i)} |v w i. {v,w} \<in> E \<and> i\<in>{1::nat,2}} \<or> e\<in>{{(v,1::nat),(v,2)} |v. v \<in> Vs E}"
            using \<open>M \<subseteq> E\<^sub>H E\<close> by (auto simp add: E\<^sub>H_def)
          then show "fst ` e\<in>E"
          proof (rule disjE)
            assume "e\<in>{{(v,i), (w,i)} |v w i. {v,w} \<in> E \<and> i\<in>{1::nat,2}}"
            then show "fst ` e\<in>E"
              by auto
          next
            assume "e\<in>{{(v,1::nat),(v,2)} |v. v \<in> Vs E}"
            then have "snd ` e = {1,2}"
              by auto
            then show "fst ` e\<in>E"
              using \<open>snd ` e = {1::nat}\<close> by auto
          qed
        qed

        have "{e |e. e\<in>M \<and> snd ` e = {1::nat}} \<inter> {e |e. e\<in>M \<and> snd ` e \<noteq> {1::nat}} = {}"
          by blast
        have "{e |e. e\<in>M \<and> snd ` e = {1::nat}} \<union> {e |e. e\<in>M \<and> snd ` e \<noteq> {1::nat}} = M"
          by auto

        have "\<forall>e\<in>{e |e. e\<in>M \<and> snd ` e={1::nat}}. -(c\<^sub>H (E,c)) e = c (fst ` e)"
          using \<open>\<forall>e\<in>M. snd ` e = {1::nat} \<longrightarrow> fst ` e\<in>E\<close> by (auto simp add: c\<^sub>H_def)

        have "{e |e. e\<in>M \<and> snd ` e={1::nat}} = {{(v,(1::nat)),(w,1)} |v w. {(v,(1::nat)),(w,1)}\<in>M}"
        proof
          show "{e |e. e\<in>M \<and> snd ` e={1::nat}} \<subseteq> {{(v,(1::nat)),(w,1)} |v w. {(v,(1::nat)),(w,1)}\<in>M}" (is "?A \<subseteq> ?B")
          proof
            fix e
            assume "e\<in>?A"
            then obtain v w where "e={(v,1::nat),(w,1)}" "e\<in>M"
              using \<open>M \<subseteq> E\<^sub>H E\<close> \<open>graph_invar (E\<^sub>H E)\<close> by (auto simp add: E\<^sub>H_def)
            then show "e\<in>?B"
              by auto
          qed
        next
          show "{{(v,(1::nat)),(w,1)} |v w. {(v,(1::nat)),(w,1)}\<in>M} \<subseteq> {e |e. e\<in>M \<and> snd ` e={1::nat}}"
            by auto
        qed

        have "{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'} \<subseteq> ?M1''" "{{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'} \<subseteq> ?M1''"
          by blast+
        hence "finite {{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'}" "finite {{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'}"
          using finite_subset[OF _ \<open>finite ?M1''\<close>] by auto

        have "finite {e |e. e\<in>M \<and> snd ` e = {1::nat}}" "finite {e |e. e\<in>M \<and> snd ` e \<noteq> {1::nat}}"
          using \<open>finite M\<close> by auto

        have "(\<lambda>e. fst ` e) ` {{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'} = M'"
        proof
          show "M' \<subseteq> (\<lambda>e. fst ` e) ` {{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'}"
          proof
            fix e
            assume "e \<in> M'"
            moreover then obtain v w where "e = {v,w}"
              using \<open>graph_invar M'\<close> by auto
            moreover have "{v,w} = fst ` {(v,1::nat),(w,1)}"
              by auto
            ultimately show "e \<in> (\<lambda>e. fst ` e) ` {{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'}"
              by blast
          qed
       qed auto
       have "inj_on ((`) fst) {{(v,1::nat),(w,1)} |v w. {v,w}\<in>M'}"
         by (intro inj_onI) auto

       have "(\<lambda>e. fst ` e) ` {{(v,(1::nat)),(w,1)} |v w. {(v,(1::nat)),(w,1)}\<in>M} = {{v,w} |v w. {(v,(1::nat)),(w,1)}\<in>M}"
       proof
         show "(\<lambda>e. fst ` e) ` {{(v,(1::nat)),(w,1)} |v w. {(v,(1::nat)),(w,1)}\<in>M} \<subseteq> {{v,w} |v w. {(v,(1::nat)),(w,1)}\<in>M}"
           by fastforce
       next
         show "{{v,w} |v w. {(v,(1::nat)),(w,1)}\<in>M} \<subseteq> (\<lambda>e. fst ` e) ` {{(v,(1::nat)),(w,1)} |v w. {(v,(1::nat)),(w,1)}\<in>M}"
         proof
           fix e
           assume "e \<in> {{v,w} |v w. {(v,(1::nat)),(w,1)}\<in>M}"
           then obtain v w where "e = {v,w}" "{(v,(1::nat)),(w,1)}\<in>M"
             by blast
           moreover hence "e = fst ` {(v,(1::nat)),(w,1)}"
             by auto
           ultimately show "e \<in> (\<lambda>e. fst ` e) ` {{(v,(1::nat)),(w,1)} |v w. {(v,(1::nat)),(w,1)}\<in>M}"
             by blast
          qed
        qed
        have "inj_on ((`) fst) {{(v,1::nat),(w,1)} |v w. {(v,1::nat),(w,1)}\<in>M}"
          by (intro inj_onI) auto

        have "(\<Sum>e\<in>M'. c e) = -(\<Sum>e\<in>M'. -c e)"
          by (simp add: sum_negf)
        also have "... = -(\<Sum>e\<in>(\<lambda>e. fst ` e) ` {{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'}. -c e)"
          using \<open>(\<lambda>e. fst ` e) ` {{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'} = M'\<close> by auto
        also have "... = -(\<Sum>e\<in>{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'}. -c (fst ` e))"
         using \<open>inj_on ((`) fst) {{(v,1::nat),(w,1)} |v w. {v,w}\<in>M'}\<close> by (subst sum.reindex) auto
        also have "... = -(\<Sum>e\<in>{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'}. (c\<^sub>H (E,c)) e)"
          using \<open>\<forall>e\<in>{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'}. (c\<^sub>H (E,c)) e = -c (fst ` e)\<close> by (auto simp add: c\<^sub>H_def)
        also have "... = -(\<Sum>e\<in>{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'}. (c\<^sub>H (E,c)) e)+ 
          -(\<Sum>e\<in>{{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'}. (c\<^sub>H (E,c)) e) + 
          -(\<Sum>e\<in>{{(v,1::nat),(v,2)}|v. v\<in>(Vs E)-(Vs M')}. (c\<^sub>H (E,c)) e)"
          using \<open>\<forall>e\<in>{{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'}. (c\<^sub>H (E,c)) e = 0\<close> \<open>(\<Sum>e\<in>{{(v,1::nat),(v,2)}|v. v\<in>(Vs E)-(Vs M')}. (c\<^sub>H (E,c)) e) = 0\<close> by auto 
        also have "... = -(\<Sum>e\<in>{{(v,i),(w,i)}|v w i. {v,w}\<in>M' \<and> i\<in>{1::nat,2}}. (c\<^sub>H (E,c)) e)+ 
          -(\<Sum>e\<in>{{(v,1::nat),(v,2)}|v. v\<in>(Vs E)-(Vs M')}. (c\<^sub>H (E,c)) e)"
          using \<open>{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'} \<union> {{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'} = {{(v,i),(w,i)}|v w i. {v,w}\<in>M' \<and> i\<in>{1::nat,2}}\<close> 
            sum.union_disjoint[OF \<open>finite {{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'}\<close> \<open>finite {{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'}\<close> 
              \<open>{{(v,1::nat),(w,1)}|v w. {v,w}\<in>M'} \<inter> {{(v,2::nat),(w,2)}|v w. {v,w}\<in>M'} = {}\<close>, of "c\<^sub>H (E,c)"] by auto
        also have "... = -(\<Sum>e\<in>?M''. (c\<^sub>H (E,c)) e)"
          using sum.union_disjoint[OF \<open>finite ?M1''\<close> \<open>finite ?M2''\<close> \<open>?M1'' \<inter> ?M2'' = {}\<close>, of "c\<^sub>H (E,c)"] by auto
        also have "... \<le> -(\<Sum>e\<in>M. (c\<^sub>H (E,c)) e)"
          using \<open>is_perf_match (E\<^sub>H E) ?M''\<close> \<open>is_min_match (E\<^sub>H E) (c\<^sub>H (E,c)) M\<close> by (auto simp add: is_min_match_def)
        also have "... \<le> (\<Sum>e\<in>M. -(c\<^sub>H (E,c)) e)"
          by (simp add: sum_negf)
        also have "... = (\<Sum>e\<in>{e |e. e\<in>M \<and> snd ` e = {1::nat}}\<union>{e |e. e\<in>M \<and> snd ` e \<noteq> {1::nat}}. -(c\<^sub>H (E,c)) e)"
          using \<open>{e |e. e\<in>M \<and> snd ` e = {1::nat}} \<union> {e |e. e\<in>M \<and> snd ` e \<noteq> {1::nat}} = M\<close> by auto
        also have "... = (\<Sum>e\<in>{e |e. e\<in>M \<and> snd ` e={1::nat}}. -(c\<^sub>H (E,c)) e) + (\<Sum>e\<in>{e |e. e\<in>M \<and> snd ` e\<noteq>{1::nat}}. -(c\<^sub>H (E,c)) e)"
          using sum.union_disjoint[OF \<open>finite {e |e. e\<in>M \<and> snd ` e = {1::nat}}\<close> 
              \<open>finite {e |e. e\<in>M \<and> snd ` e \<noteq> {1::nat}}\<close> 
                \<open>{e |e. e\<in>M \<and> snd ` e = {1::nat}} \<inter> {e |e. e\<in>M \<and> snd ` e \<noteq> {1::nat}} = {}\<close>, of "-(c\<^sub>H (E,c))"]
          by auto
        also have "... = (\<Sum>e\<in>{e |e. e\<in>M \<and> snd ` e={1::nat}}. c (fst ` e)) + (\<Sum>e\<in>{e |e. e\<in>M \<and> snd ` e\<noteq>{1::nat}}. 0)"
          using \<open>\<forall>e\<in>M. snd ` e = {1::nat} \<longrightarrow> fst ` e\<in>E\<close> by (auto simp add: c\<^sub>H_def)
        also have "... = (\<Sum>e\<in>{e |e. e\<in>M \<and> snd ` e={1::nat}}. c (fst ` e))"
          by auto
        also have "... = (\<Sum>e\<in>{{(v,(1::nat)),(w,1)} |v w. {(v,(1::nat)),(w,1)}\<in>M}. c (fst ` e))"
          using \<open>{e |e. e\<in>M \<and> snd ` e={1::nat}} = {{(v,(1::nat)),(w,1)} |v w. {(v,(1::nat)),(w,1)}\<in>M}\<close> by auto
        also have "... = (\<Sum>e\<in>(\<lambda>e. fst ` e) ` {{(v,(1::nat)),(w,1)} |v w. {(v,(1::nat)),(w,1)}\<in>M}. c e)"
          using \<open>inj_on ((`) fst) {{(v,1::nat),(w,1)} |v w. {(v,1::nat),(w,1)}\<in>M}\<close> by (subst sum.reindex) auto
        also have "... = (\<Sum>e\<in>{{v,w} |v w. {(v,(1::nat)),(w,1)}\<in>M}. c e)"
          using \<open>(\<lambda>e. fst ` e) ` {{(v,(1::nat)),(w,1)} |v w. {(v,(1::nat)),(w,1)}\<in>M} = {{v,w} |v w. {(v,(1::nat)),(w,1)}\<in>M}\<close> by auto
        also have "... = (\<Sum>e\<in>?M'. c e)"
          using \<open>?M' = {{v,w} |v w. {(v,(1::nat)),(w,1)}\<in>M}\<close> by auto
        finally show "(\<Sum>e\<in>M'. c e) \<le> (\<Sum>e\<in>?M'. c e)" by simp
      qed
      ultimately have "is_max_match E c ?M'"
        unfolding is_max_match_def by auto
      then show "is_sol P\<^sub>m\<^sub>a\<^sub>x a (f\<^sub>2 g a)" 
        using \<open>graph_invar E\<close> by auto
    qed
  qed
qed

end