theory FindHamiltonianPath
  imports GraphAdjList
begin

type_synonym 'v lgraph = "('v ,'v lset) lmap"

abbreviation "He_lgraph \<equiv> [
  ((''u'',1::nat),[(''u'',3::nat),(''u'',4::nat)]),
  ((''u'',2::nat),[(''v'',3::nat),(''v'',5::nat)]),
  ((''u'',3::nat),[(''u'',1::nat),(''v'',2::nat)]),
  ((''u'',4::nat),[(''u'',1::nat),(''v'',5::nat),(''v'',6::nat)]),
  ((''u'',5::nat),[(''v'',2::nat),(''v'',4::nat),(''v'',6::nat)]),
  ((''u'',6::nat),[(''v'',4::nat),(''v'',5::nat)]),
  ((''v'',1::nat),[(''v'',3::nat),(''v'',4::nat)]),
  ((''v'',2::nat),[(''u'',3::nat),(''u'',5::nat)]),
  ((''v'',3::nat),[(''v'',1::nat),(''u'',2::nat)]),
  ((''v'',4::nat),[(''v'',1::nat),(''u'',5::nat),(''u'',6::nat)]),
  ((''v'',5::nat),[(''u'',2::nat),(''u'',4::nat),(''u'',6::nat)]),
  ((''v'',6::nat),[(''u'',4::nat),(''u'',5::nat)])
]"

abbreviation "He_vertices \<equiv> 
  [(''u'',1::nat),(''u'',2::nat),(''u'',3::nat),(''u'',4::nat),(''u'',5::nat),(''u'',6::nat),
  (''v'',1::nat),(''v'',2::nat),(''v'',3::nat),(''v'',4::nat),(''v'',5::nat),(''v'',6::nat)]"

fun extend_path where
  "extend_path Es [] = []"
| "extend_path Es p = (case lmap_lookup Es (last p) of 
    None \<Rightarrow> []
  | Some N \<Rightarrow> map (\<lambda>x. p @ [x]) (filter (Not o (lset_isin p)) N))"

fun vertex_dist_paths where
  "vertex_dist_paths Es (k::nat) vs = fold (\<lambda>k ps. concat (map (extend_path He_lgraph) ps)) [1..k] (map (\<lambda>x. [x]) vs)"

value "vertex_dist_paths He_lgraph 11 He_vertices"

value "map (\<lambda>xs. (hd xs,last xs)) (vertex_dist_paths He_lgraph 11 He_vertices)"

end