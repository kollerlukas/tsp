(* Author: Lukas Koller *)
theory Select
  imports Main "HOL-Data_Structures.Set_Specs"
begin

locale select = Set_by_Ordered S for S +
  fixes pick
  assumes pick: "isin S (pick S)"

end