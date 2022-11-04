theory VC4_to_mTSP_Poly
  imports Main "../misc/Misc" "../berge/Berge" "../graphs/CompleteGraph" "../problems/TSP" 
    "../problems/VertexCover" 
begin

text \<open>This theory formalizes a L-Reduction from Minimum-Vertex-Cover (VC4), with max. degree 4, 
to metric-Traveling-Salesman (mTSP).\<close>

(* All edges are undirected, but are represent by tuples to more easily write executable functions. *)

text \<open>The function \<open>f\<close> translates from VC4 to mTSP. Let \<open>E\<close> be an instance of VC4 then \<open>f E\<close> is an 
instance of mTSP.\<close>

definition "H\<^sub>e u v \<equiv> (let e = {u,v} in 
  {{(e,u,1),(e,u,2)},
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
  {(e,v,5),(e,v,6)}})"

fun f :: "'a set set \<Rightarrow> ('a set \<times> 'a \<times> nat) set set" where (* H := f E *)
  "f E = (let V\<^sub>H = Vs (\<Union> {H\<^sub>e u v | u v. {u,v} \<in> E}) in {{u,v} | u v. u \<in> V\<^sub>H \<and> v \<in> V\<^sub>H})"

fun dist\<^sub>H\<^sub>e :: "('a set \<times> 'a \<times> nat) \<Rightarrow> ('a set \<times> 'a \<times> nat \<times> nat) \<Rightarrow> nat option" where
  "dist\<^sub>H\<^sub>e (e\<^sub>u,u,i) (e\<^sub>v,v,j) = undefined" (* TODO: Do I need the distance? Or just set it to \<ge> 12 *)

fun c\<^sub>H :: "'a set set \<Rightarrow> ('a set \<times> 'a \<times> nat) set \<Rightarrow> nat" where
  "c\<^sub>H E e = 
  (if \<exists>u v. {u,v} \<in> E \<and> e \<in> H\<^sub>e u v then 1 
  else if \<exists>u v. {u,v} \<in> E \<and> e \<subseteq> Vs (H\<^sub>e u v) then 12
  else if \<exists>e\<^sub>u u i e\<^sub>v v j. e = {(e\<^sub>u,u,i),(e\<^sub>v,v,j)} \<and> e\<^sub>u \<noteq> e\<^sub>v \<and> u = v then 4
  else 5)"

text \<open>The function \<open>g\<close> translates a feasible solution of mTSP to a feasible solution of VC4. Let \<open>E\<close> 
be an instance of VC4 and let \<open>H\<close> be a feasible solution (Hamiltonian cycle) of \<open>f E\<close> then \<open>g (f E)\<close> 
is a feasible solution of \<open>E\<close> (vertex cover).\<close>

fun g_aux :: "'a \<Rightarrow> ('a set \<times> 'a \<times> nat) list \<Rightarrow> 'a list" where
  "g_aux v [] = []"
| "g_aux v ((e\<^sub>u,u,i)#es) = (if v \<in> e\<^sub>u then g_aux v es else v#g_aux u es)"

fun g :: "('a set \<times> 'a \<times> nat) list \<Rightarrow> 'a list" where
  "g [] = []"
| "g ((e\<^sub>u,u,i)#es) = g_aux u es"

text \<open>Hamiltonian path\<close>
abbreviation "is_hp E P \<equiv> (P \<noteq> [] \<longrightarrow> (\<exists>u v. walk_betw E u P v)) \<and> set P = Vs E \<and> distinct P"

(* ----- auxiliary lemmas ----- *)

context graph_abs
begin

lemma graph_H: "graph_invar (f E)"
  sorry

sublocale H: graph_abs "f E"
  using graph_H apply unfold_locales oops

definition "H \<equiv> f E"

lemma "is_complete H"
  sorry

end

lemma
  fixes x E\<^sub>x
  assumes "E\<^sub>x = {{x,y} | y. {x,y} \<in> E}"
  shows "False"
  sorry

lemma
  assumes "is_vc E X"
  obtains T where "is_hc H T" "cost_of_path (c\<^sub>H E) T = 15 * card E + card X"
  sorry

lemma
  assumes "is_hc H T"
  obtains T' where "is_hp H T'" "cost_of_path (c\<^sub>H E) T' \<le> 0"
  sorry

lemma
  assumes "is_hc H T" "cost_of_path (c\<^sub>H E) T = 15 * card E + k"
  obtains X where "is_vc E X" "card x = k"
  sorry

lemma
  assumes opt_vc: "is_min_vc E OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "is_tsp H (c\<^sub>H E) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path (c\<^sub>H E) OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P = 15 * card E + card OPT\<^sub>V\<^sub>C"
  sorry

(* ----- 1st condition for a L-reduction ----- *)

text \<open>\<open>(H,c\<^sub>H)\<close> is an instance of mTSP.\<close>
lemma "is_complete H"
  unfolding H_def by (auto intro: compl_graph_is_complete)

lemma "c\<^sub>H e \<ge> 0"
  sorry

lemma l_reduction1:
  assumes opt_vc: "is_min_vc E OPT\<^sub>V\<^sub>C" 
      and opt_mtsp: "is_tsp H c\<^sub>H OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P"
  shows "cost_of_path c\<^sub>H OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> 61 * card OPT\<^sub>V\<^sub>C" (is "?c' OPT\<^sub>m\<^sub>T\<^sub>S\<^sub>P \<le> ?\<alpha> * ?c OPT\<^sub>V\<^sub>C")
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

text \<open>The function \<open>f\<close> translates from VC4 to mTSP. Let \<open>E\<close> be an instance of VC4 then \<open>f E\<close> is an 
instance of mTSP.\<close>

definition "H\<^sub>e e \<equiv> (case e of (u,v) \<Rightarrow> undefined)"

abbreviation "enum6 e\<^sub>v \<equiv> 
  (let (e,v) = e\<^sub>v in [(e,v,1),(e,v,2),(e,v,3),(e,v,4),(e,v,5),(e,v,6)])"

fun f :: "('a \<times> 'a) list \<Rightarrow> ('a set \<times> 'a \<times> nat) set list" where
  "f es = 
    (let vs = remdups (map (\<lambda>(u,v). ({u,v},u)) es @ map (\<lambda>(u,v). ({u,v},v)) es) 
    in compl_graph (fold (\<lambda>v vs. enum6 v @ vs) vs []))"

fun dist\<^sub>H\<^sub>e :: "('a set \<times> 'a \<times> nat) \<Rightarrow> ('a set \<times> 'a \<times> nat \<times> nat) \<Rightarrow> enat" where
  "dist\<^sub>H\<^sub>e (e\<^sub>u,u,i) (e\<^sub>v,v,j) = undefined" (* TODO: Do I need the distance? Or just set it to \<ge> 12 *)

fun c\<^sub>H' :: "('a set \<times> 'a \<times> nat) \<Rightarrow> ('a set \<times> 'a \<times> nat) \<Rightarrow> nat" where
  "c\<^sub>H' e = undefined"

fun c\<^sub>H :: "('a set \<times> 'a \<times> nat) set \<Rightarrow> nat" where
  "c\<^sub>H e = undefined"

text \<open>The function \<open>g\<close> translates a feasible solution of mTSP to a feasible solution of VC4. Let \<open>E\<close> 
be an instance of VC4 and let \<open>H\<close> be a feasible solution (Hamiltonian cycle) of \<open>f E\<close> then \<open>g (f E)\<close> 
is a feasible solution of \<open>E\<close> (vertex cover).\<close>

fun g_aux :: "'a \<Rightarrow> ('a set \<times> 'a \<times> nat) list \<Rightarrow> 'a list" where
  "g_aux v [] = []"
| "g_aux v ((e\<^sub>u,u,i)#es) = (if v \<in> e\<^sub>u then g_aux v es else v#g_aux u es)"

fun g :: "('a set \<times> 'a \<times> nat) list \<Rightarrow> 'a list" where
  "g [] = []"
| "g ((e\<^sub>u,u,i)#es) = g_aux u es"

abbreviation "uedge \<equiv> \<lambda>(u,v). {u,v}"

fun cost_of_path' where 
  "cost_of_path' c [] = 0"
| "cost_of_path' c [v] = 0"
| "cost_of_path' c (u#v#P) = c (u,v) + cost_of_path' c (v#P)"

lemma "cost_of_path c P = cost_of_path' (c o uedge) P"
  by (induction P rule: list012.induct) auto

locale graph_abs_edge_list =
  graph_abs E for E +
  fixes Es :: "('a \<times> 'a) list"
  assumes distinct_Es: "distinct (map uedge Es)" 
      and set_Es: "set (map uedge Es) = E"
  (* 
    TODO: 
    How to assume that a graph \<open>'a set set\<close> can be converted into a list of directed edges \<open>('a \<times> 'a) list\<close>? 
  *)
begin

lemma "H = set (f Es)"
  sorry

end

end