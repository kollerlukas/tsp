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

lemma diVs_eq_Vs: "diVs (diE X) = Vs X"
  unfolding diVs_def diE_def Vs_def sorry

text \<open>directed tour\<close>
inductive ditour :: "('a * 'a) set \<Rightarrow> ('a * 'a) list \<Rightarrow> bool" where
  ditour0: "ditour X []" |
  ditour1: "e \<in> X \<Longrightarrow> ditour X [e]" |
  ditour2: "(u,v) \<in> X \<Longrightarrow> ditour X ((v,w)#T) \<Longrightarrow> ditour X ((u,v)#(v,w)#T)"

lemma ditour_edges_subset: "ditour E' T \<Longrightarrow> set T \<subseteq> E'"
  by (induction E' T rule: ditour.induct) auto

lemma ditour_ball_edges: "ditour (diE E) T \<Longrightarrow> (u,v) \<in> set T \<Longrightarrow> {u,v} \<in> E"
  using ditour_edges_subset diE_iff by fastforce

text \<open>Eulerian Tour\<close>
definition "is_et P \<equiv> ditour (diE E) P \<and> fst (hd P) = snd (last P) \<and> (\<forall>e\<in>diE E. \<exists>!i. i < length P \<and> P ! i = e)"

lemma et_distinct:
  assumes "is_et P"
  shows "distinct P"
  sorry

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

lemma et_of_dT_correct:
  assumes "finite X" "u \<in> diVs X"
  shows "is_et (et_of_dT u X)"
  sorry

text \<open>Hamiltonian Cycle of Eulerian Tour\<close>
fun hc_of_et :: "('a * 'a) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "hc_of_et [] H = H"
| "hc_of_et [(u,v)] H = v#(if u\<in>set H then H else u#H)"
| "hc_of_et ((u,v)#P) H = (if u\<in>set H then hc_of_et P H else hc_of_et P (u#H))"

lemma hc_of_et_distinct: 
  assumes "distinct H" 
  shows "distinct (tl (hc_of_et P H))"
  using assms by (induction P H rule: hc_of_et.induct) (auto simp: distinct_tl)

lemma hc_of_et_hd:
  assumes "P \<noteq> []"
  shows "hd (hc_of_et P H) = snd (last P)"
  using assms by (induction P H rule: hc_of_et.induct) auto

lemma hc_of_et_last:
  assumes "P \<noteq> []"
  shows "last (hc_of_et P H) = fst (hd P)"
  sorry

lemma hc_of_et_hd_last_eq: 
  assumes "is_et P" "H = hc_of_et P []" 
  shows "hd H = last H"
  sorry

lemma hc_of_et_vertices: 
  shows "set (hc_of_et P H) = diVs (set P) \<union> set H"
proof (induction P H rule: hc_of_et.induct)
  case (1 H)
  then show ?case 
    by (auto simp: diVs_def)
next
  case (2 u v H)
  then show ?case 
    by (auto simp: diVs_def)
next
  case (3 u v e P H)
  then have "u\<in>set H \<or> u\<notin>set H"
    by auto
  then show ?case 
    sorry
qed 

lemma 
  assumes "is_et P" "H = hc_of_et P []" 
  shows "set H = Vs E"
  using assms hc_of_et_vertices[of P "[]"] diVs_eq_Vs
  sorry

lemma hc_of_et_correct:
  assumes "is_et P"
  shows "is_hc (hc_of_et P [])"
  sorry

fun double_tree :: "('a set \<Rightarrow> int) \<Rightarrow> 'a list" where
  "double_tree c = (
    let T = kruskal c;
        u = SOME u. u\<in>Vs T;
        P = et_of_dT u (diE T) in
        hc_of_et P [])"

text \<open>Feasibility of \textsc{DoubleTree}\<close>
lemma "is_hc (double_tree c)"
proof -
  show ?thesis
    using hc_of_et_correct[OF et_of_dT_correct]
    sorry
qed

text \<open>Approximation of \textsc{DoubleTree}\<close>
lemma 
  assumes "is_mtsp c OPT"
  shows "cost_of_path c (double_tree c) \<le> 2 * cost_of_path c OPT"
  sorry

end

end