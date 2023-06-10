theory HamiltonianCycle
  imports Main tsp.Misc tsp.MinSpanningTree
begin

section \<open>Hamiltonian cycle\<close>
definition "is_hc E H \<equiv> (H \<noteq> [] \<longrightarrow> (\<exists>v. walk_betw E v H v)) \<and> set (tl H) = Vs E \<and> distinct (tl H)"

lemma is_hcI:
  assumes "H \<noteq> [] \<Longrightarrow> (\<exists>v. walk_betw E v H v)" "Vs E = set (tl H)" "distinct (tl H)"
  shows "is_hc E H"
  unfolding is_hc_def using assms by auto

lemma is_hcE:
  assumes "is_hc E H"
  shows "H \<noteq> [] \<Longrightarrow> (\<exists>v. walk_betw E v H v)" "Vs E = set (tl H)" "distinct (tl H)"
  using assms[unfolded is_hc_def] by auto

lemma is_hcE_nil:
  assumes "is_hc E []"
  shows "Vs E = {}"
  using assms[unfolded is_hc_def] by auto

lemma is_hcE_nonnil:
  assumes "is_hc E H" "H \<noteq> []"
  obtains v where "walk_betw E v H v" "set (tl H) = Vs E" "distinct (tl H)"
  using assms[unfolded is_hc_def] by auto

lemma is_hc_path: "is_hc E H \<Longrightarrow> path E H"
  by (cases H) (auto intro: path.intros elim: is_hcE_nonnil)

lemma hc_vs_set:
  assumes "is_hc E H"
  shows "set H = Vs E"
  using assms
proof cases
  assume "H \<noteq> []"
  hence "hd H \<in> set (tl H)"
    using assms[unfolded is_hc_def walk_betw_def] by (metis hd_in_set mem_path_Vs)
  hence "set H = set (tl H)"
    using hd_Cons_tl[OF \<open>H \<noteq> []\<close>] insert_absorb[of "hd H" "set (tl H)"] set_simps by metis
  also have "... = Vs E"
    using assms \<open>H \<noteq> []\<close> by (auto elim: is_hcE_nonnil[of E H])
  finally show ?thesis .
qed (auto simp: is_hcE_nil)

lemma is_hcI_nil: "Vs E = {} \<Longrightarrow> is_hc E []"
  unfolding is_hc_def by auto

lemma hc_length:
  assumes "is_hc E H" "H \<noteq> []"
  shows "length H = card (Vs E) + 1"
proof -
  have "length H = 1 + length (tl H)"
    using assms hd_Cons_tl[of H] by auto
  also have "... = card (Vs E) + 1"
    using assms distinct_card[of "tl H"] by (auto elim: is_hcE_nonnil)
  finally show ?thesis .
qed

lemma hc_edges_subset: 
  assumes "is_hc E H"
  shows "set (edges_of_path H) \<subseteq> E"
proof cases
  assume "H \<noteq> []"
  then obtain v where "walk_betw E v H v"
    using assms by (auto elim: is_hcE_nonnil)
  thus ?thesis
    using walk_edges_subset by fastforce
qed auto

lemma hc_walk_betw1:
  assumes "is_hc E H" "i\<^sub>u < i\<^sub>v" "i\<^sub>v < length H"
  shows "walk_betw E (H ! i\<^sub>u) (drop i\<^sub>u (take (i\<^sub>v+1) H)) (H ! i\<^sub>v)" (is "walk_betw E ?u ?P ?v")
proof (rule walk_subset[OF _ walk_on_path])
  show "i\<^sub>u < i\<^sub>v" "i\<^sub>v < length H"
    using assms by auto
  show "path E H"
    using assms by (auto elim: is_hcE_nonnil walk_between_nonempty_path)
  thus "set (edges_of_path H) \<subseteq> E"
    using path_edges_subset by auto
qed

context graph_abs
begin

lemma hc_nil_iff2: 
  assumes hc: "is_hc E H" 
  shows "E = {} \<longleftrightarrow> H = []"
  using hc_vs_set[OF hc] Vs_empty_iff[OF graph] by auto

lemma hc_non_nil_length_gr2:
  assumes "is_hc E H" "H \<noteq> []"
  shows "length H > 2"
proof (rule ccontr)
  assume "\<not> length H > 2"
  hence "card (Vs E) < 2"
    using assms card_length[of "tl H"] by (auto simp: is_hcE)
  thus "False"
    using assms hc_nil_iff2[of H] card_Vs_E_ge2 by auto
qed

lemma walk_betw_vv_set_tl_eq: 
  assumes "H \<noteq> []" "walk_betw E v H v" "set H = Vs E" 
  shows "set (tl H) = Vs E"
proof -
  have "E \<noteq> {}"
    using assms by (auto simp: Vs_def)
  hence "2 \<le> length H"
    using assms card_Vs_E_ge2 card_length[of H] by auto
  hence "hd H \<in> set (tl H)"
    using assms[unfolded walk_betw_def] last_in_set_tl[of H] by auto
  hence "set (tl H) = set H"
    using hd_Cons_tl[OF \<open>H \<noteq> []\<close>] insert_absorb[of "hd H" "set (tl H)"] set_simps by metis
  also have "... = Vs E"
    using assms by (auto elim: is_hcE_nonnil) 
  finally show ?thesis .
qed (* TODO: simplify proof with \<open>Misc.set_tl_eq_set\<close> *)

lemma is_hcI_nonnil: 
  "H \<noteq> [] \<Longrightarrow> walk_betw E v H v \<Longrightarrow> set H = Vs E \<Longrightarrow> distinct (tl H) \<Longrightarrow> is_hc E H"
  unfolding is_hc_def using walk_betw_vv_set_tl_eq by auto

lemma hc_nil_iff: "E = {} \<longleftrightarrow> is_hc E []"
proof -
  have "E = {} \<longleftrightarrow> path E [] \<and> set [] = Vs E"
    unfolding Vs_def using graph by force
  also have "... \<longleftrightarrow> is_hc E []"
    by (auto intro: is_hcI_nil simp: is_hcE_nil)
  finally show ?thesis .
qed

lemma hc_edges_nil: "is_hc E H \<Longrightarrow> edges_of_path H = [] \<Longrightarrow> H = []"
  using edges_of_path_nil hc_non_nil_length_gr2 by fastforce

lemma hc_edges_length:
  assumes "is_hc E H"
  shows "length (edges_of_path H) = card (Vs E)"
  using assms
proof (induction H)
  case Nil
  thus ?case 
    using hc_nil_iff2[of "[]"] by (simp add: Vs_def)
next
  case (Cons v H)
  thus ?case 
    apply (subst edges_of_path_length)
    apply (subst hc_length)
    apply auto
    done
qed

lemma is_hc_def2: "is_hc E H \<longleftrightarrow> (H \<noteq> [] \<longrightarrow> is_cycle E H) \<and> set (tl H) = Vs E \<and> distinct (tl H)"
  oops 
(* TODO: 
  Definition for \<open>is_hc\<close> with \<open>is_cycle\<close>. 
  Does not hold! counterexample: graph with 2 vertices 
*)

(* lemma is_hc_def2: "is_hc E H \<and> length (edges_of_path H) \<ge> 3 \<longleftrightarrow> is_cycle E H \<and> set (tl H) = Vs E"
proof (cases H)
  case (Cons u tlH)
  show ?thesis 
  proof 
    assume assm: "is_hc E H \<and> length (edges_of_path H) \<ge> 3"
    hence "H \<noteq> [] \<Longrightarrow> (\<exists>v. walk_betw E v H v)" and vs: "Vs E = set (tl H)" and "distinct (tl H)"
      by (auto elim!: is_hcE)
    moreover then obtain v where walk: "walk_betw E v H v"
      using Cons by auto
    ultimately have "is_simple H"
      using walk_distinct_tl_equiv_butlast[of E v H] by (intro is_simpleI) auto
    hence "is_cycle E H"
      using assm walk by (intro is_cycleI) auto
    thus "is_cycle E H \<and> set (tl H) = Vs E"
      using vs by blast
  next
    assume "is_cycle E H \<and> set (tl H) = Vs E"
    moreover then obtain v where "is_simple H" "walk_betw E v H v" "length (edges_of_path H) \<ge> 3"
      using Cons by (auto elim!: is_cycleE)
    moreover hence "distinct (tl H) \<and> distinct (butlast H)"
      by (auto elim!: is_simpleE)
    ultimately show "is_hc E H \<and> length (edges_of_path H) \<ge> 3"
      by (auto intro!: is_hcI)
  qed
qed (auto simp add: is_hc_def is_cycle_def) *)

lemma hc_split:
  assumes "is_hc E H"
  obtains "H = []" | v P where "H = v#P @ [v]"
  using that
proof cases
  assume "H \<noteq> []"
  moreover hence "hd H = last H"
    using assms by (auto elim: is_hcE_nonnil simp: walk_between_nonempty_path)
  ultimately consider v where "H = [v]" | v P where "H = v#P @ [v]"
    using hd_last_eq_split[of H] by auto
  thus ?thesis
    using that hc_non_nil_length_gr2[OF assms \<open>H \<noteq> []\<close>] by cases auto
qed auto

lemma hc_distinct_butlast:
  assumes hc: "is_hc E H"
  shows "distinct (butlast H)"
  using hc_split[OF hc] assms by cases (auto elim: is_hcE_nonnil)

lemma hc_set_butlast:
  assumes hc: "is_hc E H" and "H \<noteq> []"
  shows "set (butlast H) = Vs E"
  using hc_split[OF hc] assms is_hcE_nonnil[OF hc] by cases auto

end

section \<open>Hamiltonian path\<close>
definition "is_hp E u P v \<equiv> walk_betw E u P v \<and> set P = Vs E \<and> distinct P"
(* TODO: connect definitions of Hamiltonian Path and Hamiltonian cycle. *)

lemma is_hpI:
  assumes "walk_betw E u P v" "set P = Vs E" "distinct P"
  shows "is_hp E u P v"
  unfolding is_hp_def using assms by auto 

lemma is_hpE:
  assumes "is_hp E u P v"
  shows "walk_betw E u P v" "set P = Vs E" "distinct P"
  using assms[unfolded is_hp_def] by auto

lemma hp_subset: "E \<subseteq> E' \<Longrightarrow> Vs E = Vs E' \<Longrightarrow> is_hp E u P v \<Longrightarrow> is_hp E' u P v"
  unfolding is_hp_def using walk_subset by metis

lemma hp_rev: "is_hp E u P v \<Longrightarrow> is_hp E v (rev P) u"
  unfolding is_hp_def using walk_symmetric by fastforce

lemma hp_append:
  assumes "is_hp E\<^sub>1 u P\<^sub>1 v" "is_hp E\<^sub>2 w P\<^sub>2 x" "Vs E\<^sub>1 \<inter> Vs E\<^sub>2 = {}"
  shows "is_hp (insert {v,w} E\<^sub>1 \<union> E\<^sub>2) u (P\<^sub>1 @ P\<^sub>2) x"
proof (intro is_hpI)
  have walk1: "walk_betw E\<^sub>1 u P\<^sub>1 v" and vs1: "set P\<^sub>1 = Vs E\<^sub>1"
    using assms(1) by (elim is_hpE)+
  moreover hence "last P\<^sub>1 = v" "P\<^sub>1 \<noteq> []"
    by (auto elim: walk_between_nonempty_path)
  ultimately have "v \<in> Vs E\<^sub>1"
    using walk_in_Vs by auto

  have walk2: "walk_betw E\<^sub>2 w P\<^sub>2 x" and vs2: "set P\<^sub>2 = Vs E\<^sub>2"
    using assms(2) by (elim is_hpE)+
  moreover hence "hd P\<^sub>2 = w" "P\<^sub>2 \<noteq> []"
    by (auto elim: walk_between_nonempty_path)
  ultimately have [simp]: "w#tl P\<^sub>2 = P\<^sub>2" and "w \<in> Vs E\<^sub>2"
    using walk_in_Vs by auto

  have "Vs (insert {v,w} E\<^sub>1 \<union> E\<^sub>2) = Vs (E\<^sub>1 \<union> E\<^sub>2)"
    using \<open>v \<in> Vs E\<^sub>1\<close> \<open>w \<in> Vs E\<^sub>2\<close> by (auto simp: Vs_def)
  show "set (P\<^sub>1 @ P\<^sub>2) = Vs (insert {v,w} E\<^sub>1 \<union> E\<^sub>2)"
    apply (subst \<open>Vs (insert {v,w} E\<^sub>1 \<union> E\<^sub>2) = Vs (E\<^sub>1 \<union> E\<^sub>2)\<close>)
    apply (subst Vs_union)
    using vs1 vs2 apply auto
    done

  have "walk_betw (insert {v,w} E\<^sub>1 \<union> E\<^sub>2) u P\<^sub>1 v"
    apply (rule walk_subset[of E\<^sub>1])
    using walk1 apply auto
    done
  moreover have "walk_betw (insert {v,w} E\<^sub>1 \<union> E\<^sub>2) v [v,w] w"
    by (intro nonempty_path_walk_between) (auto intro: path.intros)
  ultimately have "walk_betw (insert {v,w} E\<^sub>1 \<union> E\<^sub>2) u (P\<^sub>1 @ tl [v,w]) w"
    by (rule walk_transitive)
  moreover have "walk_betw (insert {v,w} E\<^sub>1 \<union> E\<^sub>2) w P\<^sub>2 x"
    apply (rule walk_subset[of E\<^sub>2])
    using walk2 apply auto
    done
  ultimately have "walk_betw (insert {v,w} E\<^sub>1 \<union> E\<^sub>2) u ((P\<^sub>1 @ tl [v,w]) @ tl P\<^sub>2) x"
    by (rule walk_transitive)
  thus "walk_betw (insert {v,w} E\<^sub>1 \<union> E\<^sub>2) u ((P\<^sub>1 @ P\<^sub>2)) x"
    by auto

  have "set P\<^sub>1 \<inter> set P\<^sub>2 = {}"
    using vs1 vs2 assms(3) by auto
  moreover have "distinct P\<^sub>1" "distinct P\<^sub>2"
    using assms(1,2) by (auto elim: is_hpE)
  ultimately show "distinct (P\<^sub>1 @ P\<^sub>2)"
    by auto
qed (* TODO: clean up! *)

lemma hc_of_hp:
  assumes "is_hp E u P v" "{u,v} \<in> E"
  shows "is_hc E (v#P)" (is "is_hc E ?P'")
proof (intro is_hcI)
  have "walk_betw E u P v"
    using assms by (elim is_hpE)  
  moreover have "walk_betw E v [v,u] u"
    using assms by (intro nonempty_path_walk_between) (auto simp: insert_commute)
  ultimately have "walk_betw E v (butlast [v,u] @ P) v"
    by (intro walk_transitive2)
  thus "?P' \<noteq> [] \<Longrightarrow> \<exists>w. walk_betw E w ?P' w"
    by auto

  have "set P = Vs E" "distinct P"
    using assms by (elim is_hpE)+
  thus "Vs E = set (tl ?P')" "distinct (tl ?P')"
    by auto
qed

end

