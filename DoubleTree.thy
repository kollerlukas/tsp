theory DoubleTree
  imports TSP MST
begin

context graph_abs_compl
begin

section \<open>\textsc{DoubleTree} Approximation Algorithm for TSP\<close>

text \<open>directed edges\<close>
definition "diE X = {(u,v) | u v. {u,v}\<in>X}"

lemma diE_iff: "(u,v) \<in> diE X \<longleftrightarrow> {u,v} \<in> X"
  unfolding diE_def by auto

text \<open>Vertices of directed graph\<close>
definition "diVs X = (fst ` X) \<union> (snd ` X)"

lemma diVs_member: "v \<in> diVs X \<longleftrightarrow> (\<exists>u. (u,v) \<in> X \<or> (v,u) \<in> X)"
  unfolding diVs_def by force

lemma diVs_nil: "X = {} \<longleftrightarrow> diVs X = {}"
  unfolding diVs_def by blast

lemma diVs_tour_nil: "P = [] \<longleftrightarrow> diVs (set P) = {}"
  unfolding diVs_def by blast

lemma diVs_Cons: "diVs (set ((u,v)#P)) = {u,v} \<union> diVs (set P)"
  unfolding diVs_def by auto

text \<open>directed tour\<close>
inductive ditour :: "('a * 'a) set \<Rightarrow> ('a * 'a) list \<Rightarrow> bool" where
  ditour0: "ditour X []" |
  ditour1: "e \<in> X \<Longrightarrow> ditour X [e]" |
  ditour2: "(u,v) \<in> X \<Longrightarrow> ditour X ((v,w)#T) \<Longrightarrow> ditour X ((u,v)#(v,w)#T)"

lemma ditour_Cons: "ditour X (e#P) \<Longrightarrow> ditour X P"
proof (induction P)
  case (Cons e' P)
  then show ?case using ditour.cases by fastforce
qed (auto intro: ditour0)

lemma ditour_edges_subset: "ditour E' T \<Longrightarrow> set T \<subseteq> E'"
  by (induction E' T rule: ditour.induct) auto

lemma ditour_ball_edges: "ditour (diE E) T \<Longrightarrow> (u,v) \<in> set T \<Longrightarrow> {u,v} \<in> E"
  using ditour_edges_subset diE_iff by fastforce

lemma ditour_consec_vertices: "ditour X (e\<^sub>1#e\<^sub>2#P) \<Longrightarrow> snd e\<^sub>1 = fst e\<^sub>2"
  using ditour.cases by fastforce

text \<open>Eulerian Tour\<close>
definition "is_et P \<equiv> 
  ditour (diE E) P \<and> fst (hd P) = snd (last P) \<and> (\<forall>e\<in>diE E. \<exists>!i. i < length P \<and> P ! i = e)"

lemma et_distinct:
  assumes "is_et P"
  shows "distinct P"
proof -
  have "\<forall>i<length P. \<forall>j<length P. i \<noteq> j \<longrightarrow> P ! i \<noteq> P ! j"
  proof (rule allI impI)+
    fix i j
    assume "i < length P" "j < length P" "i \<noteq> j"
    then have "P ! i \<in> diE E" "P ! j \<in> diE E"
      using assms[unfolded is_et_def] ditour_edges_subset[of "diE E" P] by auto
    then show "P ! i \<noteq> P ! j"
      using assms[unfolded is_et_def] \<open>i \<noteq> j\<close> \<open>i < length P\<close> \<open>j < length P\<close> by blast
  qed
  then show "distinct P"
    using distinct_conv_nth by auto
qed

lemma et_vertices:
  assumes "is_et P"
  shows "diVs (set P) = Vs E"
proof
  show "diVs (set P) \<subseteq> Vs E"
  proof
    fix v
    assume "v \<in> diVs (set P)"
    then obtain u where "(u,v) \<in> set P \<or> (v,u) \<in> set P"
      using diVs_member[of v "set P"] by auto
    then have "{u,v} \<in> E"
      using assms[unfolded is_et_def] ditour_ball_edges by (metis insert_commute)
    then show "v \<in> Vs E"
      unfolding Vs_def by auto
  qed
next
  show "Vs E \<subseteq> diVs (set P)"
  proof
    fix v
    assume "v \<in> Vs E"
    then obtain e where "v \<in> e" "e \<in> E"
      using vs_member[of v E] by auto
    then obtain u where "e={u,v}"
      using graph by fastforce
    then have "(u,v) \<in> diE E"
      using \<open>e \<in> E\<close> diE_iff[of u v E] by auto
    then have "\<exists>!i. i < length P \<and> P ! i = (u,v)"
      using assms[unfolded is_et_def] by auto
    then have "(u,v) \<in> set P"
      using nth_mem by fastforce
    then show "v \<in> diVs (set P)"
      using diVs_member[of v "set P"] by auto
  qed
qed

lemma et_nil_iff:
  assumes "is_et P"
  shows "P = [] \<longleftrightarrow> E = {}"
  using assms graph diVs_tour_nil[of P] et_vertices[unfolded Vs_def, of P] by blast

text \<open>Eulerian tour of 'double'-Tree starting at vertex \<open>u\<close>\<close>
function et_of_dT :: "'a \<Rightarrow> ('a * 'a) set \<Rightarrow> ('a * 'a) list" where
  "et_of_dT u X = (
    if X = {} then []
    else let v = SOME v. (u,v)\<in>X in (u,v)#et_of_dT v (X-{(u,v)}))"
  by pat_completeness auto
termination et_of_dT
  apply (relation "measure (\<lambda>(u,Es). card Es)")
  apply auto
  sorry

find_theorems "?A = (SOME x. ?P x)"

lemma et_of_dT_ditour:
  assumes "finite X" "u \<in> diVs X" (* X has to be eulerian *)
  shows "ditour X (et_of_dT u X)"
  using assms
proof (induction X arbitrary: u rule: finite.induct)
  case emptyI
  then show ?case
    using diVs_nil by (metis empty_iff)
next
  case (insertI X e)
  then show ?case 
    sorry
qed

lemma et_of_dT_correct:
  assumes "finite X" "u \<in> diVs X"
  shows "is_et (et_of_dT u X)"
  sorry

text \<open>Hamiltonian Cycle of Eulerian Tour\<close>
fun hc_of_et :: "('a * 'a) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "hc_of_et [] H = H"
| "hc_of_et [(u,v)] H = v#(if u\<in>set H then H else u#H)"
| "hc_of_et ((u,v)#P) H = (if u\<in>set H then hc_of_et P H else hc_of_et P (u#H))"

lemma hc_of_et_vertices_aux: 
  assumes "ditour X P"
  shows "set (hc_of_et P H) = diVs (set P) \<union> set H"
  using assms
proof (induction P H rule: hc_of_et.induct)
  case (3 u v e P H)
  then obtain v' w where "e = (v',w)"
    by (meson old.prod.exhaust)
  then have "e = (v,w)"
    using "3.prems" ditour_consec_vertices[of X "(u,v)" e P] by auto

  have "set (hc_of_et ((u,v)#e#P) H) = diVs (set (e#P)) \<union> {u} \<union> set (u#H)"
    using ditour_Cons[OF "3.prems"] "3.IH" by auto
  also have "... = diVs (set ((u,v)#e#P)) \<union> set H"
    using \<open>e = (v,w)\<close> diVs_Cons[of v w P] diVs_Cons[of u v "(v,w)#P"] by auto 
  finally show ?case .
qed (auto simp: diVs_def)

lemma hc_of_et_vertices:
  assumes "is_et P"
  shows "set (hc_of_et P []) = Vs E"
  using assms hc_of_et_vertices_aux et_vertices by (auto simp: is_et_def)

lemma hc_of_et_path: "is_et P \<Longrightarrow> path E (hc_of_et P [])"
  using hc_of_et_vertices complete_path by auto

lemma hc_of_et_distinct: 
  assumes "distinct H" 
  shows "distinct (tl (hc_of_et P H))"
  using assms by (induction P H rule: hc_of_et.induct) (auto simp: distinct_tl)

lemma hc_of_et_hd:
  assumes "P \<noteq> []"
  shows "hd (hc_of_et P H) = snd (last P)"
  using assms by (induction P H rule: hc_of_et.induct) auto

lemma hc_of_et_last_H_notnil: "H \<noteq> [] \<Longrightarrow> last H = last (hc_of_et P H)"
  by (induction P H rule: hc_of_et.induct) auto

lemma hc_of_et_last:
  assumes "P \<noteq> []"
  shows "last (hc_of_et P []) = fst (hd P)"
  using assms hc_of_et_last_H_notnil 
  by (induction P "[]::'a list" rule: hc_of_et.induct) auto
  (* induction only for case-distinction *)

lemma hc_of_et_hd_last_eq: 
  assumes "is_et P" "P \<noteq> []" "H = hc_of_et P []" 
  shows "hd H = last H"
  using assms[unfolded is_et_def] hc_of_et_hd hc_of_et_last by auto

lemma hc_of_et_correct:
  assumes "is_et P"
  shows "is_hc (hc_of_et P [])"
proof (cases "P = []")
  case True
  then show ?thesis 
    using et_nil_iff[OF assms] hc_nil_iff by auto
next
  case False
  then show ?thesis 
    unfolding is_hc_def 
    using assms hc_of_et_path hc_of_et_vertices hc_of_et_distinct hc_of_et_hd_last_eq by auto
qed

fun double_tree :: "('a set \<Rightarrow> int) \<Rightarrow> 'a list" where
  "double_tree c = (
    let T = kruskal c;
        u = SOME u. u\<in>Vs T;
        P = et_of_dT u (diE T) in
        hc_of_et P [])"

text \<open>Feasibility of \textsc{DoubleTree}\<close>
lemma "is_hc (double_tree c)"
proof -
  let ?T="kruskal c"

  show ?thesis
    using hc_of_et_correct[OF et_of_dT_correct, of "diE ?T"]
    sorry
qed

text \<open>Approximation of \textsc{DoubleTree}\<close>

(* lemma
  shows "cost_of_path c (hc_of_et P H) \<le> cost_of_path c P"
  sorry *)

lemma dT_mst_approx:
  assumes "is_mst c T"
  shows "cost_of_path c (double_tree c) \<le> 2*(\<Sum>e\<in>T. c e)"
  sorry

lemma st_of_hc:
  assumes "is_hc H" "E' = set (edges_of_path H)" "e \<in> E'"
  shows "is_st (E' - {e})"
  sorry

lemma mst_mtsp_approx:
  assumes "is_mst c T" "is_mtsp c OPT"
  shows "(\<Sum>e\<in>T. c e) \<le> cost_of_path c OPT"
proof (cases "OPT = []")
  case True
  then have "E = {}"
    using assms[unfolded is_mtsp_def is_tsp_def] hc_nil_iff by auto
  then have "T = {}"
    using assms[unfolded is_mst_def is_st_def] by auto
  then show ?thesis 
    using \<open>OPT = []\<close> by auto
next
  let ?E\<^sub>O\<^sub>P\<^sub>T="set (edges_of_path OPT)"
  case False
  then obtain e where "e \<in> ?E\<^sub>O\<^sub>P\<^sub>T"
    sorry
  then have "is_st (?E\<^sub>O\<^sub>P\<^sub>T - {e})"
    using assms[unfolded is_mtsp_def is_tsp_def] st_of_hc[of OPT] by auto
  then have "(\<Sum>e\<in>T. c e) \<le> (\<Sum>e\<in>(?E\<^sub>O\<^sub>P\<^sub>T - {e}). c e)"
    using assms[unfolded is_mst_def] by auto
  also have "... \<le> cost_of_path c OPT"
    using cost_of_path_sum[of c OPT] by (auto simp: sum_diff1_nat)
  finally show ?thesis .
qed

lemma dT_approx:
  assumes "is_mtsp c OPT"
  shows "cost_of_path c (double_tree c) \<le> 2 * cost_of_path c OPT"
  using assms dT_mst_approx[OF kruskal_mst, of c] mst_mtsp_approx[OF kruskal_mst assms] by auto

end

end