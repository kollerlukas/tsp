theory VC4_to_mTSP_Poly_old
  imports Main tsp.Misc tsp.Berge tsp.CompleteGraph tsp.TravelingSalesman tsp.VertexCover
begin

(* OLD, NOT NEEDED; TODO: remove *)

text \<open>This theory formalizes a L-Reduction from Minimum-Vertex-Cover (VC4), with max. degree 4, 
to metric-Traveling-Salesman (mTSP).\<close>

(* All edges are undirected, but are represent by tuples to more easily write executable functions. *)

text \<open>The function \<open>f\<close> translates from VC4 to mTSP. Let \<open>E\<close> be an instance of VC4 then \<open>f E\<close> is an 
instance of mTSP.\<close>

text \<open>
({u,v},u,1) --- ({u,v},u,5) --- ({u,v},v,2)
     |                               |
({u,v},u,3) --- ({u,v},u,6) --- ({u,v},v,4)
     |                               |
({u,v},u,4) --- ({u,v},v,6) --- ({u,v},v,3)
     |                               |
({u,v},u,2) --- ({u,v},v,5) --- ({u,v},v,1)
\<close>

definition "H\<^sub>e u v \<equiv> (let e = {u,v} in 
  {{(e,u,1::nat),(e,u,3)},
  {(e,u,1),(e,u,5)},
  {(e,u,2),(e,u,4)},
  {(e,u,2),(e,v,5)},
  {(e,u,3),(e,u,4)},
  {(e,u,3),(e,u,6)},
  {(e,u,4),(e,v,6)},

  {(e,v,1::nat),(e,v,3)},
  {(e,v,1),(e,v,5)},
  {(e,v,2),(e,v,4)},
  {(e,v,2),(e,u,5)},
  {(e,v,3),(e,v,4)},
  {(e,v,3),(e,v,6)},
  {(e,v,4),(e,u,6)}})"

(* definition "H\<^sub>e u v \<equiv> (let e = {u,v} in 
  {{(e,u,1::nat),(e,u,2)},
  {(e,u,1),(e,u,6)},
  {(e,u,2),(e,u,3)},
  {(e,u,3),(e,u,4)},
  {(e,u,4),(e,u,5)},
  {(e,u,4),(e,v,4)},
  {(e,u,5),(e,u,6)},
  {(e,u,6),(e,v,6)},

  {(e,v,1),(e,v,2)},
  {(e,v,1),(e,v,6)},
  {(e,v,2),(e,v,3)},
  {(e,v,3),(e,v,4)},
  {(e,v,4),(e,v,5)},
  {(e,v,5),(e,v,6)}})" *)

abbreviation "H E \<equiv> \<Union> {H\<^sub>e u v | u v. {u,v} \<in> E}"

definition "f E \<equiv> (let V\<^sub>H = Vs (H E) in complete_graph V\<^sub>H)"

fun dist\<^sub>H\<^sub>e :: "('a set \<times> 'a \<times> nat) \<Rightarrow> ('a set \<times> 'a \<times> nat) \<Rightarrow> nat option" where
  "dist\<^sub>H\<^sub>e (e\<^sub>u,u,i) (e\<^sub>v,v,j) = undefined" (* TODO: Do I need the distance? Or just set it to \<ge> 12 *)

fun c\<^sub>H :: "'a set set \<Rightarrow> ('a set \<times> 'a \<times> nat) set \<Rightarrow> nat" where
  "c\<^sub>H E e = 
  (if \<exists>u v. {u,v} \<in> E \<and> e \<in> H\<^sub>e u v then 1 
  else if \<exists>u v. {u,v} \<in> E \<and> e \<subseteq> Vs (H\<^sub>e u v) then 12
  else if \<exists>v e\<^sub>1 e\<^sub>2 i j. e = {(e\<^sub>1,v,i),(e\<^sub>2,v,j)} \<and> e\<^sub>1 \<noteq> e\<^sub>2 then 4
  else 5)"

text \<open>The function \<open>g\<close> translates a feasible solution of mTSP to a feasible solution of VC4. Let \<open>E\<close> 
be an instance of VC4 and let \<open>T\<close> be a feasible solution (Hamiltonian cycle) of \<open>f E\<close> then \<open>g (f E)\<close> 
is a feasible solution of \<open>E\<close> (vertex cover).\<close>

fun g :: "('a set \<times> 'a \<times> nat) list \<Rightarrow> 'a list" where
  "g es = undefined" (* TODO *)

(* ----- auxiliary lemmas ----- *)

lemma finite_H\<^sub>e: "finite (H\<^sub>e u v)"
  unfolding H\<^sub>e_def Let_def by auto

lemma finite_Vs_H\<^sub>e: "finite (Vs (H\<^sub>e u v))"
  unfolding Vs_def H\<^sub>e_def Let_def by auto

lemma H\<^sub>e_symmetric: "H\<^sub>e u v = H\<^sub>e v u"
  unfolding H\<^sub>e_def Let_def by (simp add: insert_commute)

lemma Vs_H\<^sub>e_member_fst_edge: "(e,v',i) \<in> Vs (H\<^sub>e u v) \<Longrightarrow> e = {u,v}"
  unfolding H\<^sub>e_def Let_def Vs_def by auto

lemma graph_H\<^sub>e_aux1:
  assumes "u \<noteq> v" "e \<in> H\<^sub>e u v"
  obtains x y where "e = {x,y}" "x \<noteq> y"
  using assms[unfolded H\<^sub>e_def Let_def] by auto

lemma graph_H\<^sub>e_aux2: "u \<noteq> v \<Longrightarrow> (\<forall>e \<in> H\<^sub>e u v. \<exists>x y. e = {x,y} \<and> x \<noteq> y)"
  using graph_H\<^sub>e_aux1 by metis

lemma graph_H\<^sub>e: 
  assumes "u \<noteq> v" 
  shows "graph_invar (H\<^sub>e u v)"
  using graph_H\<^sub>e_aux2[OF assms(1)] finite_Vs_H\<^sub>e by fastforce

lemma complete_f: "is_complete (f E)"
  unfolding f_def Let_def by (rule complete_graph_is_complete)

lemma H_union: "H (E\<^sub>1 \<union> E\<^sub>2) = H E\<^sub>1 \<union> H E\<^sub>2"
  by blast

lemma Vs_H_union: "Vs (H (E\<^sub>1 \<union> E\<^sub>2)) = Vs (H E\<^sub>1) \<union> Vs (H E\<^sub>2)"
  by (simp only: H_union) (intro Vs_union)

lemma f_union: "f E\<^sub>1 \<union> f E\<^sub>2 \<subseteq> f (E\<^sub>1 \<union> E\<^sub>2)"
  by (simp only: f_def Let_def Vs_H_union) (intro complete_graph_union)

lemma f_insert_union:
  assumes "u \<noteq> v" "u \<in> Vs (f E\<^sub>1)" "v \<in> Vs (f E\<^sub>2)"
  shows "insert {u,v} (f E\<^sub>1) \<union> (f E\<^sub>2) \<subseteq> f (E\<^sub>1 \<union> E\<^sub>2)"
proof (intro insert_union_subset)
  show "f E\<^sub>1 \<union> f E\<^sub>2 \<subseteq> f (E\<^sub>1 \<union> E\<^sub>2)"
    by (rule f_union)

  have "u \<in> Vs (H E\<^sub>1)" "v \<in> Vs (H E\<^sub>2)"
    using assms(2,3)[unfolded f_def Let_def] complete_graph_Vs_subset by fastforce+
  moreover have "Vs (H E\<^sub>1) \<subseteq> Vs (H (E\<^sub>1 \<union> E\<^sub>2))" "Vs (H E\<^sub>2) \<subseteq> Vs (H (E\<^sub>1 \<union> E\<^sub>2))"
    using Vs_H_union[of E\<^sub>1 E\<^sub>2] by blast+
  ultimately have "u \<in> Vs (H (E\<^sub>1 \<union> E\<^sub>2))" "v \<in> Vs (H (E\<^sub>1 \<union> E\<^sub>2))"
    by auto
  thus "{u,v} \<in> f (E\<^sub>1 \<union> E\<^sub>2)"
    using assms(1) unfolding f_def Let_def by (intro complete_graph_memberI)
qed

context graph_abs
begin

lemma Vs_H\<^sub>e_subset: "{u,v} \<in> E \<Longrightarrow> Vs (H\<^sub>e u v) \<subseteq> Vs (H E)"
  by (intro Vs_subset) auto

lemma H\<^sub>e_subset_f: 
  assumes "{u,v} \<in> E"
  shows "H\<^sub>e u v \<subseteq> f E"
  unfolding f_def Let_def
proof (intro graph_abs.subset_complete_graph; unfold_locales)
  show "graph_invar (H\<^sub>e u v)"
    using graph assms by (intro graph_H\<^sub>e) auto
  show "Vs (H\<^sub>e u v) \<subseteq> Vs (\<Union> {H\<^sub>e u v |u v. {u,v} \<in> E})"
    using assms by (intro Vs_H\<^sub>e_subset)
qed

lemma Vs_fE_member_fst_edge: 
  assumes "({u,v},x,k) \<in> Vs (f E)" 
  shows "{u,v} \<in> E"
proof -
  have "({u,v},x,k) \<in> Vs (H E)"
    using assms[unfolded f_def Let_def] using complete_graph_Vs_subset by fastforce
  then obtain e' where "e' \<in> H E" "({u,v},x,k) \<in> e'"
    by (elim vs_member_elim)
  moreover then obtain u' v' where "e' \<in> H\<^sub>e u' v'" "{u',v'} \<in> E"
    by auto
  ultimately have "({u,v},x,k) \<in> Vs (H\<^sub>e u' v')"
    by (intro vs_member_intro)
  hence "{u,v} = {u',v'}"
    by (simp add: Vs_H\<^sub>e_member_fst_edge)
  thus "{u,v} \<in> E"
    using \<open>{u',v'} \<in> E\<close> by auto
qed

lemma Vs_fE_member_iff: "({u,v},v,1) \<in> Vs (f E) \<longleftrightarrow> {u,v} \<in> E"
proof
  assume "({u,v},v,1) \<in> Vs (f E)"
  thus "{u,v} \<in> E"
    by (rule Vs_fE_member_fst_edge)
next
  assume "{u,v} \<in> E"
  moreover hence "{({u,v},v,1),({u,v},v,3)} \<in> H\<^sub>e u v"
    unfolding H\<^sub>e_def by (auto simp: Let_def)
  moreover hence "({u,v},v,1) \<in> Vs (H\<^sub>e u v)"
    by (intro vs_member_intro) auto
  ultimately show "({u,v},v,1) \<in> Vs (f E)"
    using Vs_subset[OF H\<^sub>e_subset_f] by auto
qed

lemma finite_union_H\<^sub>e_aux: "finite {H\<^sub>e u v | u v. {u,v} \<in> E}"
  using finite_E graph
proof (induction E)
  case (insert e E)
  moreover have "graph_invar E"
    using insert(4) by (rule graph_subset) auto
  moreover obtain u v where [simp]: "e = {u,v}"
    using insert by auto
  moreover have "{H\<^sub>e u v |u v. {u,v} \<in> insert e E} = {H\<^sub>e u v |u v. {u,v} \<in> E} \<union> {H\<^sub>e u v}"
    by (auto simp: doubleton_eq_iff H\<^sub>e_symmetric)
  ultimately show ?case 
    by auto
qed auto

lemma finite_union_H\<^sub>e: "finite (H E)"
  by (rule finite_Union) (auto intro: finite_union_H\<^sub>e_aux finite_H\<^sub>e)

lemma finite_Vs_union_H\<^sub>e: "finite (Vs (H E))"
  unfolding Vs_def using finite_union_H\<^sub>e by (rule finite_Union) (auto simp: H\<^sub>e_def Let_def)

lemma graph_H': "graph_invar (H E)"
proof (intro graph_Un)
  show "finite {H\<^sub>e u v |u v. {u,v} \<in> E}"
    by (rule finite_union_H\<^sub>e_aux)
  fix a
  assume "a \<in> {H\<^sub>e u v |u v. {u,v} \<in> E}"
  then obtain u v where "a = H\<^sub>e u v" and "{u,v} \<in> E"
    by auto
  moreover hence "u \<noteq> v"
    using graph by auto
  ultimately show "graph_invar a"
    by (simp only: \<open>a = H\<^sub>e u v\<close>; intro graph_H\<^sub>e)
qed

lemma finite_fE: "finite (f E)"
  unfolding f_def Let_def using finite_Vs_union_H\<^sub>e by (rule finite_complete_graph)

lemma graph_fE: "graph_invar (f E)"
  unfolding f_def Let_def using finite_Vs_union_H\<^sub>e by (rule graph_complete_graph)

thm card_vertices_ge2

lemma card_Vs_H': "card (Vs (H E)) \<noteq> 1"
  sorry

lemma Vs_f_eq_Vs_H': "Vs (f E) = Vs (H E)"
  unfolding f_def Let_def using card_Vs_H' by (intro Vs_complete_graph_eq_V)

lemma split_vertex_fE:
  assumes "v' \<in> Vs (f E)"
  obtains e u k where "v' = (e,u,k)" "u \<in> e" "e \<in> E"
proof -
  have "v' \<in> Vs (H E)"
    using assms Vs_f_eq_Vs_H' by auto
  then obtain e' where "v' \<in> e'" "e' \<in> (H E)"
    by (elim vs_member_elim)
  moreover then obtain u v where "e' \<in> H\<^sub>e u v" "{u,v} \<in> E"
    by auto
  moreover then obtain u\<^sub>1 u\<^sub>2 k\<^sub>1 k\<^sub>2 where "e' = {({u,v},u\<^sub>1,k\<^sub>1),({u,v},u\<^sub>2,k\<^sub>2)}" 
    "u\<^sub>1 \<in> {u,v}" "u\<^sub>2 \<in> {u,v}"
    unfolding H\<^sub>e_def Let_def by auto
  ultimately consider "v' = ({u,v},u\<^sub>1,k\<^sub>1)" "u\<^sub>1 \<in> {u,v}" "{u,v} \<in> E" 
    | "v' = ({u,v},u\<^sub>2,k\<^sub>2)" "u\<^sub>2 \<in> {u,v}" "{u,v} \<in> E"
    by auto
  thus ?thesis
    using that by cases auto
qed (* see Vs_fE_member_iff *)

text \<open>There is a Hamiltonian path from \<open>({u,v},u,1)\<close> to \<open>({u,v},u,2)\<close> in \<open>H\<^sub>e u v\<close>.\<close>

lemma hp_in_H\<^sub>e_1:
  assumes "{u,v} \<in> E"
  obtains P where "is_hp (H\<^sub>e u v) ({u,v},u,1) P ({u,v},u,2)" "cost_of_path (c\<^sub>H E) P = 11"
proof -
  let ?e="{u,v}"
  let ?P="[(?e,u,1),(?e,u,5),(?e,v,2),(?e,v,4),(?e,u,6),(?e,u,3),
    (?e,u,4),(?e,v,6),(?e,v,3),(?e,v,1),(?e,v,5),(?e,u,2)]"
  have "u \<noteq> v"
    using assms graph by auto
  moreover hence "path (H\<^sub>e u v) ?P"
    by (auto simp: Vs_def H\<^sub>e_def Let_def doubleton_eq_iff)
  ultimately have "is_hp (H\<^sub>e u v) (?e,u,1) ?P (?e,u,2)"
    by (intro is_hpI)
      (auto intro: nonempty_path_walk_between simp: Vs_def H\<^sub>e_def Let_def doubleton_eq_iff)
  moreover have "\<And>e. e \<in> set (edges_of_path ?P) \<Longrightarrow> (c\<^sub>H E) e = 1"
    using assms path_ball_edges[OF \<open>path (H\<^sub>e u v) ?P\<close>] by (simp only: c\<^sub>H.simps) auto
  moreover hence "cost_of_path (c\<^sub>H E) ?P = 11 * 1"
    by (subst const_cost_of_path) simp+
  ultimately show ?thesis
    using that by auto
qed

end 

context graph_abs2
begin

lemma f_inj_aux: 
  assumes "e \<in> E\<^sub>1" "e \<notin> E\<^sub>2" 
  shows "f E\<^sub>1 \<noteq> f E\<^sub>2"
proof -
  obtain u v where "e = {u,v}" "u \<noteq> v"
    using assms E\<^sub>1.graph by auto
  hence "({u,v},v,1) \<in> Vs (f E\<^sub>1)" "({u,v},v,1) \<notin> Vs (f E\<^sub>2)"
    using assms E\<^sub>1.Vs_fE_member_iff E\<^sub>2.Vs_fE_member_iff by auto
  hence "Vs (f E\<^sub>1) \<noteq> Vs (f E\<^sub>2)"
    by auto
  thus ?thesis
    by (intro graph_neq_vertex)
qed

lemma f_inj: 
  assumes "E\<^sub>1 \<noteq> E\<^sub>2" 
  shows "f E\<^sub>1 \<noteq> f E\<^sub>2"
proof -
  consider e where "e \<in> E\<^sub>1" "e \<notin> E\<^sub>2" | e where "e \<in> E\<^sub>2" "e \<notin> E\<^sub>1"
    using assms by auto
  thus ?thesis
  proof cases
    fix e
    assume "e \<in> E\<^sub>1" "e \<notin> E\<^sub>2"
    moreover then obtain u v where "e = {u,v}" "u \<noteq> v"
      using E\<^sub>1.graph by auto
    ultimately have "({u,v},v,1) \<in> Vs (f E\<^sub>1)" "({u,v},v,1) \<notin> Vs (f E\<^sub>2)"
      using assms E\<^sub>1.Vs_fE_member_iff E\<^sub>2.Vs_fE_member_iff by auto
    hence "Vs (f E\<^sub>1) \<noteq> Vs (f E\<^sub>2)"
      by auto
    thus ?thesis
      by (intro graph_neq_vertex)
  next
    fix e
    assume "e \<notin> E\<^sub>1" "e \<in> E\<^sub>2"
    moreover then obtain u v where "e = {u,v}" "u \<noteq> v"
      using E\<^sub>2.graph by auto
    ultimately have "({u,v},v,1) \<notin> Vs (f E\<^sub>1)" "({u,v},v,1) \<in> Vs (f E\<^sub>2)"
      using assms E\<^sub>1.Vs_fE_member_iff E\<^sub>2.Vs_fE_member_iff by auto
    hence "Vs (f E\<^sub>1) \<noteq> Vs (f E\<^sub>2)"
      by auto
    thus ?thesis
      by (intro graph_neq_vertex)
  qed
qed

end

context edge_subgraph_abs
begin

lemma hp_in_fuv:
  assumes "is_hp (H\<^sub>e u v) x P y"
  shows "is_hp (f {{u,v}}) x P y"
proof -
  have "H\<^sub>e u v \<subseteq> f {{u,v}}"
    by (intro E\<^sub>2.H\<^sub>e_subset_f) auto
  moreover have "Vs (H\<^sub>e u v) = Vs (f {{u,v}})"
    by (subst E\<^sub>2.Vs_f_eq_Vs_H'; rule arg_cong[of _ _ Vs]) (auto simp: doubleton_eq_iff H\<^sub>e_symmetric)
  ultimately show ?thesis
    using assms by (rule hp_subset)
qed

lemma hp_in_H\<^sub>e_1':
  obtains P where "is_hp (f {{u,v}}) ({u,v},u,1) P ({u,v},u,2)" "cost_of_path (c\<^sub>H E) P = 11"
proof -
  obtain P where "is_hp (H\<^sub>e u v) ({u,v},u,1) P ({u,v},u,2)" "cost_of_path (c\<^sub>H E) P = 11"
    using edge by (elim hp_in_H\<^sub>e_1)
  thus ?thesis
    apply (intro that)
    apply (rule hp_in_fuv)
    apply auto
    done
qed

end

context graph_abs
begin

lemma hp_in_H\<^sub>e_1':                      
  assumes "{u,v} \<in> E"
  obtains P where "is_hp (f {{u,v}}) ({u,v},u,1) P ({u,v},u,2)" "cost_of_path (c\<^sub>H E) P = 11"
  apply (rule edge_subgraph_abs.hp_in_H\<^sub>e_1')
  using assms by unfold_locales

end

(* text \<open>There is a Hamiltonian path from \<open>({u,v},u,3)\<close> to \<open>({u,v},v,3)\<close> in \<open>H\<^sub>e u v\<close>.\<close>

context graph_abs
begin

lemma hp_in_H\<^sub>e_2:
  assumes "{u,v} \<in> E"
  obtains P where "is_hp (H\<^sub>e u v) ({u,v},u,3) P ({u,v},v,3)" "cost_of_path (c\<^sub>H E) P = 11"
proof -
  let ?e="{u,v}"
  let ?P="[(?e,u,3),(?e,u,2),(?e,u,1),(?e,u,6),(?e,u,5),(?e,u,4),
    (?e,v,4),(?e,v,5),(?e,v,6),(?e,v,1),(?e,v,2),(?e,v,3)]"
  have "u \<noteq> v"
    using assms graph by auto
  moreover hence "path (H\<^sub>e u v) ?P"
    by (auto simp: Vs_def H\<^sub>e_def Let_def doubleton_eq_iff)
  ultimately have "is_hp (H\<^sub>e u v) (?e,u,3) ?P (?e,v,3)"
    by (intro is_hpI) 
      (auto intro: nonempty_path_walk_between simp: Vs_def H\<^sub>e_def Let_def doubleton_eq_iff)
  moreover have "\<And>e. e \<in> set (edges_of_path ?P) \<Longrightarrow> (c\<^sub>H E) e = 1"
    using assms path_ball_edges[OF \<open>path (H\<^sub>e u v) ?P\<close>] by (simp only: c\<^sub>H.simps) auto
  moreover hence "cost_of_path (c\<^sub>H E) ?P = 11 * 1"
    by (subst const_cost_of_path) simp+
  ultimately show ?thesis
    using that by auto
qed

end 

context edge_subgraph_abs
begin

lemma hp_in_H\<^sub>e_2':
  obtains P where "is_hp (f {{u,v}}) ({u,v},u,3) P ({u,v},v,3)" "cost_of_path (c\<^sub>H E) P = 11"
proof -
  obtain P where "is_hp (H\<^sub>e u v) ({u,v},u,3) P ({u,v},v,3)" "cost_of_path (c\<^sub>H E) P = 11"
    using edge by (elim hp_in_H\<^sub>e_2)
  thus ?thesis
    apply (intro that)
    apply (rule hp_in_fuv)
    apply auto
    done
qed

end

context graph_abs
begin

lemma hp_in_H\<^sub>e_2':
  assumes "{u,v} \<in> E"
  obtains P where "is_hp (f {{u,v}}) ({u,v},u,3) P ({u,v},v,3)" "cost_of_path (c\<^sub>H E) P = 11"
  apply (rule edge_subgraph_abs.hp_in_H\<^sub>e_2')
  using assms by unfold_locales

lemma "\<And>P. \<not> is_hp (H\<^sub>e u v) (e,u,1) P (e,u,3)"
  sorry (* TODO: How to proof this? *)

lemma "\<And>P. \<not> is_hp (H\<^sub>e u v) (e,u,3) P (e,u,1)"
  sorry (* TODO: How to proof this? *)

end *)

locale graph_abs2_edge = 
  graph_abs2 E "{{u,v}}" for E u v +
  assumes "u \<noteq> v"
begin

lemma Vs_f_inter_empty:
  assumes "{u,v} \<notin> E" (is "?e \<notin> E")
  shows "Vs (f E) \<inter> Vs (f {?e}) = {}"
proof (rule inter_emptyI)
  fix v'
  assume "v' \<in> Vs (f {?e})"
  then obtain e u k where "v' = (?e,u,k)" "u \<in> e"
    by (elim E\<^sub>2.split_vertex_fE) auto
  thus "v' \<notin> Vs (f E)"
    using assms E\<^sub>1.split_vertex_fE by auto
qed

end

context graph_abs
begin

lemma Vs_fE_inter_empty:
  assumes "u \<noteq> v" and "{u,v} \<notin> E" (is "?e \<notin> E")
  shows "Vs (f E) \<inter> Vs (f {?e}) = {}"
  using assms by (intro graph_abs2_edge.Vs_f_inter_empty; unfold_locales) (auto simp: Vs_def)

end

(* locale hp_on_partition_aux = 
  graph_abs E\<^sub>x for E\<^sub>x +
  fixes x u v w P
  assumes E\<^sub>x_not_empty: "E\<^sub>x \<noteq> {}" 
    and e_notin_E\<^sub>x: "{x,u} \<notin> E\<^sub>x" 
    and x_neq_u: "x \<noteq> u"

    and hp_in_fE\<^sub>x: "is_hp (f E\<^sub>x) ({x,v},x,1) P ({x,w},x,2)" 
    and cost_of_hp_in_fE\<^sub>x: "cost_of_path (c\<^sub>H E\<^sub>x) P = 11 * card E\<^sub>x + 4 * (card E\<^sub>x - 1)"
begin

lemma graph_xu: "graph_invar {{x,u}}"
  using x_neq_u by (auto simp: Vs_def)

sublocale xu: graph_abs "{{x,u}}"
  using graph_xu by unfold_locales

lemma graph_Ex_xu: "graph_invar (insert {x,u} E\<^sub>x)"
proof -
  have "graph_invar (\<Union> {{{x,u}}, E\<^sub>x})"
    using graph graph_xu by (intro graph_Un) auto
  thus ?thesis
    by auto
qed

sublocale Ex_xu: graph_abs "insert {x,u} E\<^sub>x"
  using graph_Ex_xu by unfold_locales

lemma hp_in_fe: 
  obtains P' where "is_hp (f {{x,u}}) ({x,u},x,1) P' ({x,u},x,2)" 
    and "cost_of_path (c\<^sub>H {{x,u}}) P' = 11"
  by (rule xu.hp_in_H\<^sub>e_1') auto

lemma Vs_f_union_subset: 
  "Vs (f (insert {x,u} E\<^sub>x)) \<subseteq> Vs (insert {({x,w},x,2),({x,u},x,1)} (f E\<^sub>x) \<union> f {{x,u}})" 
  (is "_ \<subseteq> Vs ?fE'")
proof
  fix v'
  assume "v' \<in> Vs (f (insert {x,u} E\<^sub>x))"
  hence "v' \<in> Vs (H (insert {x,u} E\<^sub>x))"
    using Ex_xu.Vs_f_eq_Vs_H' by auto
  then obtain e where "v' \<in> e" "e \<in> H (insert {x,u} E\<^sub>x)"
    by (elim vs_member_elim)
  then obtain v w where "{v,w} \<in> insert {x,u} E\<^sub>x" "e \<in> H\<^sub>e v w" 
    by auto
  then consider "{v,w} = {x,u}" | "{v,w} \<in> E\<^sub>x"
    by auto
  thus "v' \<in> Vs ?fE'"
  proof cases
    assume "{v,w} = {x,u}"
    hence "e \<in> H\<^sub>e x u"
      using \<open>e \<in> H\<^sub>e v w\<close> by (auto simp: H\<^sub>e_symmetric doubleton_eq_iff)
    hence "v' \<in> Vs (H {{x,u}})"
      using \<open>v' \<in> e\<close> by (intro vs_member_intro) auto
    hence "v' \<in> Vs (f {{x,u}})"
      using xu.Vs_f_eq_Vs_H' by auto
    moreover have "Vs (f {{x,u}}) \<subseteq> Vs ?fE'"
      by (subst Vs_union) simp
    ultimately show ?thesis
      by auto
  next
    assume "{v,w} \<in> E\<^sub>x"
    hence "e \<in> H E\<^sub>x"
      using \<open>e \<in> H\<^sub>e v w\<close> by auto
    hence "v' \<in> Vs (H E\<^sub>x)"
      using \<open>v' \<in> e\<close> by (intro vs_member_intro) auto
    hence "v' \<in> Vs (f E\<^sub>x)"
      using Vs_f_eq_Vs_H' by auto
    moreover have "Vs (f E\<^sub>x) \<subseteq> Vs ?fE'"
      apply (subst(7) insert_is_Un)
      apply (subst Vs_union) 
      apply (subst Vs_union) 
      apply auto
      done
    ultimately show ?thesis
      by auto
  qed
qed

lemma IH_step_app: 
  assumes "is_hp (f {{x,u}}) ({x,u},x,1) P' ({x,u},x,2)"
  shows "is_hp (f (insert {x,u} E\<^sub>x)) ({x,v},x,1) (P @ P') ({x,u},x,2)" 
proof (rule hp_subset)
  let ?fE'="insert {({x,w},x,2),({x,u},x,1)} (f E\<^sub>x) \<union> f {{x,u}}"

  have "walk_betw (f {{x,u}}) ({x,u},x,1) P' ({x,u},x,2)"
    using assms by (elim is_hpE)
  moreover have "walk_betw (f E\<^sub>x) ({x,v},x,1) P ({x,w},x,2)"
    using hp_in_fE\<^sub>x by (elim is_hpE)
  moreover hence "({x,w},x,2) \<in> Vs (f E\<^sub>x)"
    by auto
  moreover hence "{x,w} \<in> E\<^sub>x"
    by (auto elim: split_vertex_fE)
  moreover hence "({x,w},x,2) \<noteq> ({x,u},x,1)"
    using e_notin_E\<^sub>x by auto
  ultimately show "?fE' \<subseteq> f (insert {x,u} E\<^sub>x)"
    apply (subst insert_is_Un[of "{x,u}" E\<^sub>x])
    apply (subst Un_commute[of "{{x,u}}" E\<^sub>x])
    apply (intro f_insert_union)
    apply auto
    done
  hence "Vs ?fE' \<subseteq> Vs (f (insert {x,u} E\<^sub>x))"
    by (intro Vs_subset)
  moreover have "Vs (f (insert {x,u} E\<^sub>x)) \<subseteq> Vs ?fE'"
    by (intro Vs_f_union_subset)
  ultimately show "Vs ?fE' = Vs (f (insert {x,u} E\<^sub>x))"
    by auto

  show "is_hp ?fE' ({x,v},x,1) (P @ P') ({x,u},x,2)"
  proof (rule hp_append)
    show "is_hp (f E\<^sub>x) ({x,v},x,1) P ({x,w},x,2)"
      by (rule hp_in_fE\<^sub>x)

    show "is_hp (f {{x,u}}) ({x,u},x,1) P' ({x,u},x,2)"
      by (rule assms(1))

    show "Vs (f E\<^sub>x) \<inter> Vs (f {{x,u}}) = {}" 
      using e_notin_E\<^sub>x x_neq_u by (intro Vs_fE_inter_empty)
  qed
qed

lemma IH_step_cost:
  assumes "P' \<noteq> []" "cost_of_path (c\<^sub>H {{x,u}}) P' = 11"
  shows "cost_of_path (c\<^sub>H (insert {x,u} E\<^sub>x)) (P @ P')
    = 11 * card (insert {x,u} E\<^sub>x) + 4 * (card (insert {x,u} E\<^sub>x) - 1)"
proof -
  let ?c="c\<^sub>H (insert {x,u} E\<^sub>x)"

  have "cost_of_path ?c P = 11 * card E\<^sub>x + 4 * (card E\<^sub>x - 1)"
    thm cost_of_hp_in_fE\<^sub>x cost_of_path_eq_cost
    sorry

  have "?c {last P, hd P'} = 4"
    sorry

  have "cost_of_path ?c P' = 11"
    thm assms
    thm cost_of_path_eq_cost
    sorry

  have "card E\<^sub>x \<ge> 1"
    using E\<^sub>x_not_empty finite_E card_0_eq by fastforce 
  moreover hence "card (insert {x,u} E\<^sub>x) - 1 = card E\<^sub>x"
    using finite_E e_notin_E\<^sub>x by auto
  ultimately have "card (insert {x,u} E\<^sub>x) > 1"
    by auto

  have "walk_betw (f E\<^sub>x) ({x,v},x,1) P ({x,w},x,2)"
    using hp_in_fE\<^sub>x by (elim is_hpE)
  hence "P \<noteq> []"
    by (elim walk_between_nonempty_path)
  hence "cost_of_path ?c (P @ P') = 
    cost_of_path ?c P + ?c {last P, hd P'} + cost_of_path ?c P'"
    using assms (1) by (rule cost_of_path_append)
  also have "... = 11 * card E\<^sub>x + 4 * (card E\<^sub>x - 1) + 4 + 11"
    by (simp only: \<open>cost_of_path ?c P = 11 * card E\<^sub>x + 4 * (card E\<^sub>x - 1)\<close> 
        \<open>?c {last P, hd P'} = 4\<close> \<open>cost_of_path ?c P' = 11\<close>)
  also have "... = 11 * (card E\<^sub>x + 1) + 4 * card E\<^sub>x"
    using \<open>card E\<^sub>x \<ge> 1\<close> by auto
  also have "... = 11 * card (insert {x,u} E\<^sub>x) + 4 * (card (insert {x,u} E\<^sub>x) - 1)"
    using \<open>card (insert {x,u} E\<^sub>x) - 1 = card E\<^sub>x\<close> \<open>card (insert {x,u} E\<^sub>x) > 1\<close> by auto
  finally show ?thesis .
qed

lemma IH_step:
  obtains P' where "is_hp (f (insert {x,u} E\<^sub>x)) ({x,v},x,1) P' ({x,u},x,2)"
    and "cost_of_path (c\<^sub>H (insert {x,u} E\<^sub>x)) P' 
      = 11 * card (insert {x,u} E\<^sub>x) + 4 * (card (insert {x,u} E\<^sub>x) - 1)"
proof -
  obtain P' where hp_P': "is_hp (f {{x,u}}) ({x,u},x,1) P' ({x,u},x,2)"
    and "cost_of_path (c\<^sub>H {{x,u}}) P' = 11"
    by (elim hp_in_fe)
  moreover hence "walk_betw (f {{x,u}}) ({x,u},x,1) P' ({x,u},x,2)"
    by (elim is_hpE)
  moreover hence "P' \<noteq> []"
    by (elim walk_between_nonempty_path)
  ultimately show ?thesis
    using IH_step_app IH_step_cost 
    apply (intro that) 
    apply auto
    done
qed

end

locale graph_abs_vertex =
  graph_abs E for E +
  fixes x E\<^sub>x
  assumes E\<^sub>x_subset: "E\<^sub>x \<subseteq> {e \<in> E. x \<in> e}"
begin

lemma E\<^sub>x_subset_E: "E\<^sub>x \<subseteq> E"
  using E\<^sub>x_subset by auto

sublocale graph_subgraph_abs E E\<^sub>x
  using E\<^sub>x_subset_E by unfold_locales

lemma hp_on_E\<^sub>x:
  assumes "E\<^sub>x \<noteq> {}"
  obtains u P v where "is_hp (f E\<^sub>x) ({x,u},x,1) P ({x,v},x,2)" 
    "cost_of_path (c\<^sub>H E\<^sub>x) P = 11 * card E\<^sub>x + 4 * (card E\<^sub>x - 1)"
  using finite_subset[OF E\<^sub>x_subset_E finite_E] assms E\<^sub>x_subset E\<^sub>2.graph
proof (induction E\<^sub>x arbitrary: thesis rule: finite_ne_induct)
  case (singleton e)
  then obtain u where [simp]: "e = {x,u}" and "x \<noteq> u"
    by auto
  hence "graph_abs {e}" "{x,u} \<in> {e}"
    by unfold_locales (auto simp: doubleton_eq_iff Vs_def)
  then obtain P where "is_hp (f {e}) ({x,u},x,1) P ({x,u},x,2)" "cost_of_path (c\<^sub>H {e}) P = 11"
    by (rule graph_abs.hp_in_H\<^sub>e_1') auto
  moreover hence "cost_of_path (c\<^sub>H {e}) P = 11 * card {e} + 4 * (card {e} - 1)"
    by auto
  ultimately show ?case 
    by (intro singleton(1))
next
  case (insert e E\<^sub>x)

  obtain u where [simp]: "e = {x,u}" and "x \<noteq> u"
    using insert(6,7) by (auto simp: doubleton_eq_iff)

  moreover have "graph_invar E\<^sub>x"
    using insert(7) by (rule graph_subset) auto
  ultimately obtain v P w where "is_hp (f E\<^sub>x) ({x,v},x,1) P ({x,w},x,2)" 
    "cost_of_path (c\<^sub>H E\<^sub>x) P = 11 * card E\<^sub>x + 4 * (card E\<^sub>x - 1)"
    using insert 
    apply (elim insert.IH) 
    apply unfold_locales
    apply auto
    done
  hence "hp_on_partition_aux E\<^sub>x x u v w P"
    using \<open>graph_invar E\<^sub>x\<close> insert(2,3) \<open>x \<noteq> u\<close>
    apply unfold_locales
    apply simp+
    done
  then obtain P' where "is_hp (f (insert e E\<^sub>x)) ({x,v},x,1) P' ({x,u},x,2)" and 
      "cost_of_path (c\<^sub>H (insert e E\<^sub>x)) P' = 11 * card (insert e E\<^sub>x) + 4 * (card (insert e E\<^sub>x) - 1)"
    apply (simp only: \<open>e = {x,u}\<close>)
    apply (elim hp_on_partition_aux.IH_step)
    apply auto
    done
  thus ?case 
    apply (intro insert(5))
    apply blast+
    done
qed

end *)

lemma hp_on_E\<^sub>x:
  assumes "finite E\<^sub>x" "E\<^sub>x \<noteq> {}" and "\<And>e. e \<in> E\<^sub>x \<Longrightarrow> x \<in> e" "graph_invar E\<^sub>x"
  obtains u P v where "is_hp (f E\<^sub>x) ({x,u},x,1) P ({x,v},x,2)" 
    "cost_of_path (c\<^sub>H E\<^sub>x) P = 11 * card E\<^sub>x + 4 * (card E\<^sub>x - 1)"
  using assms 
proof (induction E\<^sub>x arbitrary: thesis rule: finite_ne_induct)
  case (singleton e)
  then obtain u where [simp]: "e = {x,u}" and "x \<noteq> u"
    by auto
  hence "graph_abs {e}"
    by unfold_locales (auto simp: doubleton_eq_iff Vs_def)
  then obtain P where "is_hp (f {e}) (e,x,1) P (e,x,2)" "cost_of_path (c\<^sub>H {e}) P = 11"
    by (rule graph_abs.hp_in_H\<^sub>e_1') auto
  moreover hence "cost_of_path (c\<^sub>H {e}) P = 11 * card {e} + 4 * (card {e} - 1)"
    by auto
  ultimately show ?case 
    by (intro singleton(1)) simp
next
  case (insert e E\<^sub>x)
  obtain u where [simp]: "e = {x,u}" and x_neq_u: "x \<noteq> u"
    using insert(6,7) by (auto simp: doubleton_eq_iff)
  hence graph_e: "graph_abs {e}"
    by unfold_locales (auto simp: doubleton_eq_iff Vs_def)
  then obtain P' where hp_P': "is_hp (f {e}) (e,x,1) P' (e,x,2)" 
    and cost_P': "cost_of_path (c\<^sub>H {e}) P' = 11"
    by (rule graph_abs.hp_in_H\<^sub>e_1') auto
  moreover have graph_E\<^sub>x: "graph_invar E\<^sub>x"
    using insert(7) by (rule graph_subset) auto
  ultimately obtain v P w where hp_P: "is_hp (f E\<^sub>x) ({x,v},x,1) P ({x,w},x,2)" 
    and cost_P: "cost_of_path (c\<^sub>H E\<^sub>x) P = 11 * card E\<^sub>x + 4 * (card E\<^sub>x - 1)"
    using insert by (elim insert.IH) auto

  let ?eE\<^sub>x="insert e E\<^sub>x"
  let ?fE'="insert {({x,w},x,2),(e,x,1)} (f E\<^sub>x) \<union> f {e}"

  have "is_hp (f ?eE\<^sub>x) ({x,v},x,1) (P @ P') (e,x,2)"
  proof (rule hp_subset)
    have "walk_betw (f {e}) (e,x,1) P' (e,x,2)"
      using hp_P' by (elim is_hpE)
    moreover have "walk_betw (f E\<^sub>x) ({x,v},x,1) P ({x,w},x,2)"
      using hp_P by (elim is_hpE)
    moreover hence "({x,w},x,2) \<in> Vs (f E\<^sub>x)"
      by auto
    moreover hence "{x,w} \<in> E\<^sub>x"
      using graph_E\<^sub>x by (intro graph_abs.Vs_fE_member_fst_edge; unfold_locales) auto
    moreover hence "({x,w},x,2) \<noteq> (e,x,1)"
      using insert(3) by auto
    ultimately show "?fE' \<subseteq> f ?eE\<^sub>x"
      apply (subst insert_is_Un[of e E\<^sub>x])
      apply (subst Un_commute[of "{e}" E\<^sub>x])
      apply (intro f_insert_union)
        apply auto
      done
    hence "Vs ?fE' \<subseteq> Vs (f ?eE\<^sub>x)"
      by (intro Vs_subset)
    moreover have "Vs (f ?eE\<^sub>x) \<subseteq> Vs ?fE'"
    proof
      fix v'
      assume "v' \<in> Vs (f ?eE\<^sub>x)"
      hence "v' \<in> Vs (H ?eE\<^sub>x)"
        apply (subst graph_abs.Vs_f_eq_Vs_H'[symmetric])
        using insert(7) apply unfold_locales
        apply auto 
        done
      then obtain e' where "v' \<in> e'" "e' \<in> H ?eE\<^sub>x"
        by (elim vs_member_elim)
      then obtain v w where "{v,w} \<in> ?eE\<^sub>x" "e' \<in> H\<^sub>e v w" 
        by auto
      then consider "{v,w} = {x,u}" | "{v,w} \<in> E\<^sub>x"
        by auto
      thus "v' \<in> Vs ?fE'"
      proof cases
        assume "{v,w} = {x,u}"
        hence "e' \<in> H\<^sub>e x u"
          using \<open>e' \<in> H\<^sub>e v w\<close> by (auto simp: H\<^sub>e_symmetric doubleton_eq_iff)
        hence "v' \<in> Vs (H {{x,u}})"
          using \<open>v' \<in> e'\<close> by (intro vs_member_intro) auto
        hence "v' \<in> Vs (f {e})"
          using graph_e by (auto simp: graph_abs.Vs_f_eq_Vs_H')
        moreover have "Vs (f {{x,u}}) \<subseteq> Vs ?fE'"
          by (subst Vs_union) simp
        ultimately show ?thesis
          by auto
      next
        assume "{v,w} \<in> E\<^sub>x"
        hence "e' \<in> H E\<^sub>x"
          using \<open>e' \<in> H\<^sub>e v w\<close> by auto
        hence "v' \<in> Vs (H E\<^sub>x)"
          using \<open>v' \<in> e'\<close> by (intro vs_member_intro) auto
        hence "v' \<in> Vs (f E\<^sub>x)"
          apply (subst graph_abs.Vs_f_eq_Vs_H')
          using graph_E\<^sub>x apply unfold_locales by auto
        moreover have "Vs (f E\<^sub>x) \<subseteq> Vs ?fE'"
          apply (subst(5) insert_is_Un)
          apply (subst Vs_union) 
          apply (subst Vs_union) 
          apply auto
          done
        ultimately show ?thesis
          by auto
      qed
    qed
    ultimately show "Vs ?fE' = Vs (f ?eE\<^sub>x)"
      by auto

    show "is_hp ?fE' ({x,v},x,1) (P @ P') (e,x,2)"
      using hp_P hp_P'
      apply (rule hp_append)
      apply simp
      using graph_E\<^sub>x insert(3) x_neq_u 
      apply (intro graph_abs.Vs_fE_inter_empty)
      apply unfold_locales
      apply auto
      done
  qed
  moreover have "cost_of_path (c\<^sub>H ?eE\<^sub>x) (P @ P') = 11 * card ?eE\<^sub>x + 4 * (card ?eE\<^sub>x - 1)"
    sorry (* TODO: need executable graph-model! *)
  ultimately show ?case 
    apply (intro insert(5))
    apply simp
    apply blast
    done
qed

context graph_abs
begin

lemma hp_on_E\<^sub>x:
  assumes "E\<^sub>x \<noteq> {}" and E\<^sub>x_subset_E: "E\<^sub>x \<subseteq> {e \<in> E. x \<in> e}"
  obtains u P v where "is_hp (f E\<^sub>x) ({x,u},x,1) P ({x,v},x,2)" 
    "cost_of_path (c\<^sub>H E\<^sub>x) P = 11 * card E\<^sub>x + 4 * (card E\<^sub>x - 1)"
proof (rule hp_on_E\<^sub>x)
  show "finite E\<^sub>x"
    using assms finite_E by (intro finite_subset[OF E\<^sub>x_subset_E]) auto
  show "E\<^sub>x \<noteq> {}" "\<And>e. e \<in> E\<^sub>x \<Longrightarrow> x \<in> e"
    using assms by auto
  show "graph_invar E\<^sub>x"
    using graph apply (rule graph_subset) using assms by auto
qed

lemma
  assumes "is_vc E X"
  obtains T where "is_hc (H E) T" "cost_of_path (c\<^sub>H E) T = 15 * card E + card X"
proof cases
  assume "E = {}"
  show ?thesis
    sorry
next
  assume "E \<noteq> {}" (* TODO: How do I obtain a partition of E? \<rightarrow> executable graph model! *)
  show ?thesis
    sorry
qed

lemma
  assumes opt_vc: "is_min_vc E OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "is_tsp (H E) (c\<^sub>H E) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path (c\<^sub>H E) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 15 * card E + card OPT\<^sub>V\<^sub>C"
  sorry

lemma
  assumes "is_hc (H E) T"
  obtains u P v where "is_hp (H E) u P v" "cost_of_path (c\<^sub>H E) P \<le> 0"
  sorry (* TODO: How do I formalize: contains a Hamiltonian path of each subgraph H\<^sub>e? *)

lemma
  assumes "is_hc (H E) T" "cost_of_path (c\<^sub>H E) T = 15 * card E + k"
  obtains X where "is_vc E X" "card x = k"
  sorry

end

(* ----- 1st condition for a L-reduction ----- *)

text \<open>\<open>(H,c\<^sub>H)\<close> is an instance of mTSP.\<close>
lemma "is_complete (H E)"
  sorry

lemma "(c\<^sub>H E) e \<ge> 0"
  sorry

lemma 
  assumes "u \<in> Vs (H E)" "v \<in> Vs (H E)" "w \<in> Vs (H E)" 
  shows "(c\<^sub>H E) {u,w} \<le> (c\<^sub>H E) {u,v} + (c\<^sub>H E) {v,w}"
  sorry

lemma l_reduction1:
  assumes opt_vc: "is_min_vc E OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "is_tsp (f E) (c\<^sub>H E) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path (c\<^sub>H E) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * card OPT\<^sub>V\<^sub>C" (is "?c' OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> ?\<alpha> * ?c OPT\<^sub>V\<^sub>C")
  sorry

(* ----- 2nd condition for a L-reduction ----- *)

text \<open>The function \<open>g\<close> maps a feasible solution of mTSP to a feasible solution of VC4.\<close>
lemma
  assumes "is_hc H T"
  shows "is_vc E (set (g T))"
  sorry

lemma l_reduction2:
  assumes opt_vc: "is_min_vc E OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "is_tsp H c\<^sub>H OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P" 
      and "is_hc H T"
  shows "\<bar> int (card (set (g T))) - int (card OPT\<^sub>V\<^sub>C) \<bar> 
    \<le> 1 * \<bar> int (cost_of_path c\<^sub>H T) - int (cost_of_path c\<^sub>H OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P) \<bar>"
    (is "\<bar> ?c (set (g T)) - ?c OPT\<^sub>V\<^sub>C \<bar> \<le> ?\<beta> * \<bar> ?c' T - ?c' OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<bar>")
  sorry

(* ----- executable refinement ----- *)

(* TODO *)

end