(* Author: Lukas Koller *)
theory GraphAdjList
  imports GraphAdjMap_Specs
begin

section \<open>List Implementation for Sets\<close>

type_synonym 'a lset = "'a list"

definition lset_empty :: "'a lset" ("\<emptyset>\<^sub>l") where [simp]: "lset_empty = []"

fun lset_delete :: "'a \<Rightarrow> 'a lset \<Rightarrow> 'a lset" where
  "lset_delete a as = filter (\<lambda>x. a \<noteq> x) as"

fun lset_insert :: "'a \<Rightarrow> 'a lset \<Rightarrow> 'a lset" where
  "lset_insert a as = List.insert a as"

fun lset_isin :: "'a lset \<Rightarrow> 'a \<Rightarrow> bool" where
  "lset_isin as a = (filter (\<lambda>x. a = x) as \<noteq> [])"

fun lset_set :: "'a lset \<Rightarrow> 'a set" where
  "lset_set as = set as"

fun lset_invar :: "'a lset \<Rightarrow> bool" where
  "lset_invar as = distinct as"

fun lset_inter :: "'a lset \<Rightarrow> 'a lset \<Rightarrow> 'a lset" where 
  "lset_inter as bs = filter (\<lambda>a. lset_isin bs a) as"

fun lset_diff :: "'a lset \<Rightarrow> 'a lset \<Rightarrow> 'a lset" where 
  "lset_diff as bs = filter (\<lambda>a. \<not> lset_isin bs a) as"

fun lset_union :: "'a lset \<Rightarrow> 'a lset \<Rightarrow> 'a lset" where 
  "lset_union as bs = as @ lset_diff bs as"

lemma lset_empty: "lset_set lset_empty = {}"
  by auto

lemma lset_isin: "lset_invar s \<Longrightarrow> lset_isin s x = (x \<in> lset_set s)"
  by (induction s) auto

lemma lset_insert: "lset_invar s \<Longrightarrow> lset_set (lset_insert x s) = lset_set s \<union> {x}"
  by auto

lemma lset_delete: "lset_invar s \<Longrightarrow> lset_set (lset_delete x s) = lset_set s - {x}"
  by (induction s) auto

lemma lset_invar_empty: "lset_invar lset_empty"
  by auto

lemma lset_invar_insert: "lset_invar s \<Longrightarrow> lset_invar (lset_insert x s)"
  by auto

lemma lset_invar_delete: "lset_invar s \<Longrightarrow> lset_invar (lset_delete x s)"
  by auto

lemma lset_inter: 
  "lset_invar s1 \<Longrightarrow> lset_invar s2 \<Longrightarrow> lset_set (lset_inter s1 s2) = lset_set s1 \<inter> lset_set s2"
proof (induction s1 arbitrary: s2)
  case (Cons a as)
  then show ?case
    using lset_isin by (cases "lset_isin s2 a") fastforce+
qed auto

lemma lset_diff: 
  "lset_invar s1 \<Longrightarrow> lset_invar s2 \<Longrightarrow> lset_set (lset_diff s1 s2) = lset_set s1 - lset_set s2"
proof (induction s1 arbitrary: s2)
  case (Cons a as)
  then show ?case
    using lset_isin by (cases "lset_isin s2 a") fastforce+
qed auto

lemma lset_union: 
  "lset_invar s1 \<Longrightarrow> lset_invar s2 \<Longrightarrow> lset_set (lset_union s1 s2) = lset_set s1 \<union> lset_set s2"
  using lset_diff by auto

lemma lset_invar_inter: "lset_invar s1 \<Longrightarrow> lset_invar s2 \<Longrightarrow> lset_invar (lset_inter s1 s2)"
  by auto

lemma lset_invar_diff: "lset_invar s1 \<Longrightarrow> lset_invar s2 \<Longrightarrow> lset_invar (lset_diff s1 s2)"
  by auto

lemma lset_invar_union: "lset_invar s1 \<Longrightarrow> lset_invar s2 \<Longrightarrow> lset_invar (lset_union s1 s2)"
  using lset_diff lset_invar_diff by auto

lemmas lset_specs = lset_empty lset_isin lset_insert lset_delete lset_invar_empty lset_invar_insert 
  lset_invar_delete

interpretation lset: Set lset_empty lset_insert lset_delete lset_isin lset_set lset_invar
  using lset_specs by unfold_locales

lemmas lset2_specs = lset_union lset_inter lset_diff lset_invar_union lset_invar_inter 
  lset_invar_diff
                     
interpretation lset2: Set2 lset_empty lset_delete lset_isin lset_set lset_invar lset_insert 
  lset_union lset_inter lset_diff
  using lset2_specs by unfold_locales

section \<open>List implementation for Maps\<close>

type_synonym ('a,'b) lmap = "('a \<times> 'b) list"

definition lmap_empty :: "('a,'b) lmap" where [simp]: "lmap_empty = []"

fun lmap_delete :: "'a \<Rightarrow> ('a,'b) lmap \<Rightarrow> ('a,'b) lmap" where
  "lmap_delete a M = filter (\<lambda>(x,y). a \<noteq> x) M"

fun lmap_update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) lmap \<Rightarrow> ('a,'b) lmap" where
  "lmap_update a b M = (a,b)#lmap_delete a M"

fun lmap_lookup :: "('a,'b) lmap \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "lmap_lookup [] a = None"
| "lmap_lookup ((x,y)#M) a = (if a = x then Some y else lmap_lookup M a)"

fun lmap_invar :: "('a,'b) lmap \<Rightarrow> bool" where
  "lmap_invar M = distinct (map fst M)"

lemma lmap_empty: "lmap_lookup lmap_empty = (\<lambda>_. None)"
  unfolding lmap_empty_def by auto

lemma lmap_delete: "lmap_invar M \<Longrightarrow> lmap_lookup (lmap_delete a M) = (lmap_lookup M) (a := None)"
  by (induction M) auto

lemma lmap_update: 
  "lmap_invar M \<Longrightarrow> lmap_lookup (lmap_update a b M) = (lmap_lookup M) (a := Some b)"
  by (auto simp add: lmap_delete simp del: lmap_delete.simps)

lemma lmap_invar_empty: "lmap_invar lmap_empty"            
  by auto

lemma lmap_invar_update: "lmap_invar M \<Longrightarrow> lmap_invar (lmap_update a b M)"
  by (induction M) auto

lemma lmap_invar_delete: "lmap_invar M \<Longrightarrow> lmap_invar (lmap_delete a M)"
  by (induction M) auto

lemmas lmap_specs = lmap_empty lmap_update lmap_delete lmap_invar_empty lmap_invar_update 
  lmap_invar_delete

interpretation list_map: Map lmap_empty lmap_update lmap_delete lmap_lookup lmap_invar
  using lmap_specs by unfold_locales

section \<open>Graph Implementation with Adjacency-Lists\<close>

interpretation ugraph_adj_list: ugraph_adj_map_by_linorder 
  lmap_empty lmap_update lmap_delete lmap_lookup lmap_invar
  lset_empty lset_insert lset_delete lset_isin lset_set lset_invar lset_union lset_inter lset_diff
  by unfold_locales

notation ugraph_adj_list.ugraph_adj_map_invar ("ugraph'_adj'_list'_invar")
notation ugraph_adj_list.rep ("rep'_uedge")
notation ugraph_adj_list.neighborhood ("\<N>")

lemma isin_lmap_lookup:
  assumes "lmap_invar G" 
  shows "lmap_lookup G u = Some Nu \<longleftrightarrow> (u,Nu) \<in> set G" 
  using assms 
proof (induction G rule: pair_list.induct)
  case (2 v Nv G)
  thus ?case
    by (cases "u = v") force+
qed auto

lemma isin_lmap_neighborhood:
  assumes "ugraph_adj_list_invar G" "(u,Nu) \<in> set G" 
  shows "\<N> G u = Nu"
  unfolding ugraph_adj_list.neighborhood_def
  using assms by (auto simp add: iffD2[OF isin_lmap_lookup])

lemma lmap_unique_assoc:
  assumes "lmap_invar G" "(u,Nu) \<in> set G" "(v,Nv) \<in> set G" "u = v"
  shows "(u,Nu) = (v,Nv)"
proof
  have "lmap_lookup G u = Some Nu" "lmap_lookup G u = Some Nv"
    using assms by (auto intro!: iffD2[OF isin_lmap_lookup])
  thus "u = v \<and> Nu = Nv"
    using assms by auto
qed

end