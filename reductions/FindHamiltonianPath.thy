(* Author: Lukas Koller *)
theory FindHamiltonianPath
  imports GraphAdjList
begin

fun extend_path where
  "extend_path Es [] = []"
| "extend_path Es p = (case lmap_lookup Es (hd p) of 
    None \<Rightarrow> []
  | Some N \<Rightarrow> map (\<lambda>x. x#p) (filter (\<lambda>u. u \<notin> set p) N))"

fun vertex_dist_paths where
  "vertex_dist_paths Es ks ps = fold (\<lambda>k ps. concat (map (extend_path Es) ps)) ks ps"

lemma prepend_path_lookup:
  assumes "ugraph_adj_list_invar Es" "\<And>u v. lset_isin (\<N> Es v) u \<Longrightarrow> lset_isin (\<N> Es u) v"
  shows "length p' > 1 \<and> ugraph_adj_list.path_betw Es u p' w \<longleftrightarrow> 
    (\<exists>p v N. p' = u#p \<and> ugraph_adj_list.path_betw Es v p w \<and> lmap_lookup Es (hd p) = Some N \<and> u \<in> set N)"
proof
  assume "length p' > 1 \<and> ugraph_adj_list.path_betw Es u p' w"
  hence "ugraph_adj_list.path_betw Es u p' w" "length p' > 1"
    by auto
  then obtain p v where "p' = u#p" "ugraph_adj_list.path_betw Es v p w" "lset_isin (\<N> Es u) v"
    by (elim ugraph_adj_list.path_betw.cases[of Es u _ w]) auto
  moreover hence "lset_isin (\<N> Es (hd p)) u" 
    using assms ugraph_adj_list.hd_path_betw by blast
  moreover hence"lmap_lookup Es (hd p) = Some (\<N> Es (hd p))" and "u \<in> lset_set (\<N> Es (hd p))"
    using assms ugraph_adj_list.lookup_non_empty_neighborhood lset.set_specs(2)[of "\<N> Es (hd p)"] by blast+
  moreover hence "u \<in> set (\<N> Es (hd p))"
    by auto
  ultimately show "\<exists>p v N. p' = u#p \<and> ugraph_adj_list.path_betw Es v p w \<and> lmap_lookup Es (hd p) = Some N \<and> u \<in> set N"
    by blast
next
  assume "\<exists>p v N. p' = u#p \<and> ugraph_adj_list.path_betw Es v p w \<and> lmap_lookup Es (hd p) = Some N \<and> u \<in> set N"
  then obtain p v N where [simp]: "p' = u#p" and "ugraph_adj_list.path_betw Es v p w" 
    and "lmap_lookup Es (hd p) = Some N" "u \<in> set N"
    by auto
  moreover hence len_p': "length p' > 1" and "hd p = v" and "u \<in> lset_set (\<N> Es v)"
    unfolding ugraph_adj_list.neighborhood_def using ugraph_adj_list.path_non_nil 
      by (auto simp add: ugraph_adj_list.hd_path_betw)
  moreover hence "lset_isin (\<N> Es v) u"
    using assms lset.set_specs(2)[of "\<N> Es v"] by blast
  ultimately have "ugraph_adj_list.path_betw Es u (u#p) w"
    using assms by (intro ugraph_adj_list.path_betw.intros) blast+
  hence "ugraph_adj_list.path_betw Es u p' w"
    by auto
  thus "length p' > 1 \<and> ugraph_adj_list.path_betw Es u p' w"
    using assms len_p' by blast
qed

lemma isin_extend_path_iff:
  assumes "ugraph_adj_list_invar Es"
  shows "distinct p \<and> p' \<in> set (extend_path Es p) \<longleftrightarrow> 
    (\<exists>u N. p \<noteq> [] \<and> p' = u#p \<and> distinct p' \<and> lmap_lookup Es (hd p) = Some N \<and> u \<in> set N)"
proof
  assume "distinct p \<and> p' \<in> set (extend_path Es p)"
  moreover then obtain u N where "p \<noteq> []" "p' = u#p" "lmap_lookup Es (hd p) = Some N" 
    and "u#p \<in> set (map (\<lambda>x. x#p) (filter (\<lambda>u. u \<notin> set p) N))"
    by (cases p; cases "lmap_lookup Es (hd p)") auto
  moreover hence "u \<in> set N" "distinct (u#p)"
    using assms calculation by auto
  ultimately show "\<exists>u N. p \<noteq> [] \<and> p' = u#p \<and> distinct p' \<and> lmap_lookup Es (hd p) = Some N \<and> u \<in> set N"
    by auto
next
  assume "\<exists>u N. p \<noteq> [] \<and> p' = u#p \<and> distinct p' \<and> lmap_lookup Es (hd p) = Some N \<and> u \<in> set N"
  then obtain u N where "p \<noteq> []" "p' = u#p" "distinct (u#p)" "lmap_lookup Es (hd p) = Some N" "u \<in> set N"
    by auto
  moreover hence "p' \<in> set (map (\<lambda>x. x#p) (filter (\<lambda>u. u \<notin> set p) N))"
    by auto
  ultimately show "distinct p \<and> p' \<in> set (extend_path Es p)"
    using assms by (cases p; cases "lmap_lookup Es (hd p)") auto
qed

lemma vertex_dist_paths_are_dist_paths:
  assumes "ugraph_adj_list_invar Es" "\<And>u v. lset_isin (\<N> Es v) u \<Longrightarrow> lset_isin (\<N> Es u) v"
      and "l > 0"
      and "\<And>p. p \<in> set ps \<longleftrightarrow> distinct p \<and> length p = l \<and> (\<exists>v w. ugraph_adj_list.path_betw Es v p w)"
  shows "p \<in> set (vertex_dist_paths Es ks ps) \<longleftrightarrow> 
    (\<exists>u v. distinct p \<and> length p = l + length ks \<and> ugraph_adj_list.path_betw Es u p v)"
  using assms
proof (induction ks arbitrary: l ps)
  case Nil
  thus ?case 
    by auto
next
  case (Cons k ks)
  let ?ps'="concat (map (extend_path Es) ps)"
  have "\<And>p'. p' \<in> set ?ps' 
    \<longleftrightarrow> distinct p' \<and> length p' = l + 1 \<and> (\<exists>u w. ugraph_adj_list.path_betw Es u p' w)"
  proof
    fix p'
    assume "p' \<in> set ?ps'"
    then obtain p where "p \<in> set ps" "p' \<in> set (extend_path Es p)"
      by auto
    moreover hence "distinct p \<and> length p = l \<and> (\<exists>v w. ugraph_adj_list.path_betw Es v p w)"
      using Cons by blast
    moreover then obtain v w where "distinct p" and [simp]: "length p = l" 
      and path_p: "ugraph_adj_list.path_betw Es v p w"
      by auto
    ultimately have "\<exists>u N. p \<noteq> [] \<and> p' = u#p \<and> distinct p' \<and> lmap_lookup Es (hd p) = Some N \<and> u \<in> set N"
      using Cons isin_extend_path_iff by blast 
    then obtain u N where "p \<noteq> []" "p' = u#p" "distinct p'" "lmap_lookup Es (hd p) = Some N" "u \<in> set N"
      by auto
    moreover hence "ugraph_adj_list.path_betw Es u p' w"
      using assms path_p prepend_path_lookup[of Es p' u w] by blast
    ultimately show "distinct p' \<and> length p' = l + 1 \<and> (\<exists>u w. ugraph_adj_list.path_betw Es u p' w)"
      by auto
  next
    fix p' 
    assume "distinct p' \<and> length p' = l + 1 \<and> (\<exists>u w. ugraph_adj_list.path_betw Es u p' w)"
    then obtain u w where dist_p': "distinct p'" and len_p': "length p' = l + 1" 
      and "ugraph_adj_list.path_betw Es u p' w"
      by auto
    moreover hence "length p' > 1"
      using Cons by linarith
    ultimately obtain p v N where 
      "p' = u#p \<and> ugraph_adj_list.path_betw Es v p w \<and> lmap_lookup Es (hd p) = Some N \<and> u \<in> set N"
      using assms prepend_path_lookup[of Es p' u w] by blast
    hence [simp]: "p' = u#p" and path_p: "ugraph_adj_list.path_betw Es v p w" 
      and "lmap_lookup Es (hd p) = Some N" "u \<in> set N"
      by auto
    hence "distinct p \<and> p' \<in> set (extend_path Es p)"
      using assms dist_p' ugraph_adj_list.path_non_nil by (intro iffD2[OF isin_extend_path_iff]) blast+
    moreover hence "distinct p \<and> length p = l \<and> (\<exists>v w. ugraph_adj_list.path_betw Es v p w)"
      using path_p len_p' by auto 
    moreover hence "p \<in> set ps"
      using Cons by blast
    ultimately show "p' \<in> set ?ps'"
      by auto
  qed
  moreover have "l + 1 > 0"
    by auto
  ultimately have "p \<in> set (vertex_dist_paths Es ks ?ps') 
    \<longleftrightarrow> (\<exists>u v. distinct p \<and> length p = (l + 1) + length ks \<and> ugraph_adj_list.path_betw Es u p v)"
    using Cons.IH[OF assms(1-2), of "l + 1" ?ps'] by fastforce
  moreover hence "(l + 1) + length ks = l + length (k#ks)"
    by auto
  ultimately show ?case 
    by fastforce
qed

abbreviation "He_lgraph \<equiv> [
  (1::nat,[3::nat,4]), \<comment> \<open>1 \<mapsto> (e,u,1)\<close>
  (2,[9,11]), \<comment> \<open>2 \<mapsto> (e,u,2)\<close>
  (3,[1,8]), \<comment> \<open>3 \<mapsto> (e,u,3)\<close>
  (4,[1,11,12]), \<comment> \<open>4 \<mapsto> (e,u,4)\<close>
  (5,[8,10,12]), \<comment> \<open>5 \<mapsto> (e,u,5)\<close>
  (6,[10,11]), \<comment> \<open>6 \<mapsto> (e,u,6)\<close>
  (7,[9,10]), \<comment> \<open>7 \<mapsto> (e,v,1)\<close>
  (8,[3,5]), \<comment> \<open>8 \<mapsto> (e,v,2)\<close>
  (9,[7,2]), \<comment> \<open>9 \<mapsto> (e,v,3)\<close>
  (10,[7,5,6]), \<comment> \<open>10 \<mapsto> (e,v,4)\<close>
  (11,[2,4,6]), \<comment> \<open>11 \<mapsto> (e,v,5)\<close>
  (12,[4,5]) \<comment> \<open>12 \<mapsto> (e,v,6)\<close>
]"

abbreviation "He_vertices \<equiv> map nat [1::nat..12]"

value "vertex_dist_paths He_lgraph [1..11] (map (\<lambda>x. [x]) He_vertices)"

lemma map_invar_He: "lmap_invar He_lgraph"
  by simp

lemma neigborhood_invar_He: "lset_invar (\<N> He_lgraph v)"
  unfolding ugraph_adj_list.neighborhood_def by simp

lemma neigborhood_irrefl: "\<not> lset_isin (\<N> He_lgraph v) v"
  unfolding ugraph_adj_list.neighborhood_def by simp

lemma neigborhood_sym: "lset_isin (\<N> He_lgraph u) v \<Longrightarrow> lset_isin (\<N> He_lgraph v) u"
  unfolding ugraph_adj_list.neighborhood_def sorry

lemma finite_uedges_He: "finite (ugraph_adj_list.uedges He_lgraph)"
  unfolding ugraph_adj_list.uedges_def2 ugraph_adj_list.neighborhood_def sorry

lemma invar_He: "ugraph_adj_list_invar He_lgraph"
  using map_invar_He neigborhood_invar_He neigborhood_irrefl neigborhood_sym finite_uedges_He by blast

lemma He_vertices: "set He_vertices = ugraph_adj_list.vertices He_lgraph"
  sorry

lemma all_singleton_paths:
  defines "vs \<equiv> map (\<lambda>x. [x]) He_vertices"
  shows "p \<in> set vs \<longleftrightarrow> distinct p \<and> length p = 1 \<and> (\<exists>v w. ugraph_adj_list.path_betw He_lgraph v p w)"
proof
  assume "p \<in> set vs"
  then obtain v where "p = [v]" "v \<in> ugraph_adj_list.vertices He_lgraph"
    unfolding vs_def using He_vertices by auto
  moreover hence "ugraph_adj_list.path_betw He_lgraph v [v] v"
    by (intro ugraph_adj_list.path_betw.intros)
  ultimately show "distinct p \<and> length p = 1 \<and> (\<exists>v w. ugraph_adj_list.path_betw He_lgraph v p w)"
    by auto
next
  assume "distinct p \<and> length p = 1 \<and> (\<exists>v w. ugraph_adj_list.path_betw He_lgraph v p w)"
  moreover then obtain v w where "ugraph_adj_list.path_betw He_lgraph v p w" and "p \<noteq> []" "hd p = v"
    using ugraph_adj_list.hd_path_betw ugraph_adj_list.path_non_nil by blast 
  ultimately have "p = [v]" "v \<in> ugraph_adj_list.vertices He_lgraph"
    using ugraph_adj_list.path_vertices list_hd_singleton hd_in_set by fastforce+
  thus "p \<in> set vs"
    unfolding vs_def using He_vertices by auto
qed

lemma He_sym:
  assumes "lset_isin (\<N> He_lgraph v) u"
  shows "lset_isin (\<N> He_lgraph u) v"
  sorry

lemma 
  assumes "ugraph_adj_list.path_betw He_lgraph u p v" "distinct p" "length p = 12"
  obtains "hd p = 6" "last p = 1" 
    | "hd p = 2" "last p = 1" 
    | "hd p = 12" "last p = 2" 
    | "hd p = 1" "last p = 2" 
    | "hd p = 12" "last p = 6" 
    | "hd p = 1" "last p = 6" 
    | "hd p = 12" "last p = 6" 
    | "hd p = 8" "last p = 6" 
    | "hd p = 12" "last p = 7" 
    | "hd p = 8" "last p = 7" 
    | "hd p = 6" "last p = 8" 
    | "hd p = 7" "last p = 8" 
    | "hd p = 6" "last p = 12" 
    | "hd p = 7" "last p = 12" 
    | "hd p = 6" "last p = 12" 
    | "hd p = 2" "last p = 12"
proof -
  let ?ks="[1..11]"
  let ?vs="map (\<lambda>x. [x]) He_vertices"
  have "length p = 1 + length ?ks"
    using assms by auto
  hence "p \<in> set (vertex_dist_paths He_lgraph ?ks ?vs)"
    using assms vertex_dist_paths_are_dist_paths[OF invar_He He_sym _ all_singleton_paths, of p ?ks] 
    by auto
  moreover have "vertex_dist_paths He_lgraph ?ks ?vs = [
    [6,10,7,9,2,11,4,12,5,8,3,1],
    [2,9,7,10,6,11,4,12,5,8,3,1],
    [12,5,8,3,1,4,11,6,10,7,9,2],
    [1,3,8,5,12,4,11,6,10,7,9,2],
    [12,5,8,3,1,4,11,2,9,7,10,6],
    [1,3,8,5,12,4,11,2,9,7,10,6],
    [12,4,1,3,8,5,10,7,9,2,11,6],
    [8,3,1,4,12,5,10,7,9,2,11,6],
    [12,4,1,3,8,5,10,6,11,2,9,7],
    [8,3,1,4,12,5,10,6,11,2,9,7],
    [6,11,2,9,7,10,5,12,4,1,3,8],
    [7,9,2,11,6,10,5,12,4,1,3,8],
    [6,11,2,9,7,10,5,8,3,1,4,12],
    [7,9,2,11,6,10,5,8,3,1,4,12],
    [6,10,7,9,2,11,4,1,3,8,5,12],
    [2,9,7,10,6,11,4,1,3,8,5,12]]"
    by eval
  ultimately consider "p = [6,10,7,9,2,11,4,12,5,8,3,1]" 
    | "p = [2,9,7,10,6,11,4,12,5,8,3,1]" 
    | "p = [12,5,8,3,1,4,11,6,10,7,9,2]" 
    | "p = [1,3,8,5,12,4,11,6,10,7,9,2]" 
    | "p = [12,5,8,3,1,4,11,2,9,7,10,6]" 
    | "p = [1,3,8,5,12,4,11,2,9,7,10,6]" 
    | "p = [12,4,1,3,8,5,10,7,9,2,11,6]" 
    | "p = [8,3,1,4,12,5,10,7,9,2,11,6]" 
    | "p = [12,4,1,3,8,5,10,6,11,2,9,7]" 
    | "p = [8,3,1,4,12,5,10,6,11,2,9,7]" 
    | "p = [6,11,2,9,7,10,5,12,4,1,3,8]" 
    | "p = [7,9,2,11,6,10,5,12,4,1,3,8]" 
    | "p = [6,11,2,9,7,10,5,8,3,1,4,12]" 
    | "p = [7,9,2,11,6,10,5,8,3,1,4,12]" 
    | "p = [6,10,7,9,2,11,4,1,3,8,5,12]" 
    | "p = [2,9,7,10,6,11,4,1,3,8,5,12]"
    by fastforce
  thus ?thesis
    using that by cases auto
qed

end