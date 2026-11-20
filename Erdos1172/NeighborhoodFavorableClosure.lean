/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.NeighborhoodMixedBlocks

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172NeighborhoodFavorableClosure

open Erdos1172NeighborhoodCode Erdos1172NeighborhoodIdeal Erdos1172NeighborhoodIdealCore Erdos1172NeighborhoodDerivedIdeal Erdos1172NeighborhoodMixedBlocks Erdos1172BHTAsymmetricEndpointFavorableOrder

abbrev Part2Targets (G H : SimpleGraph Erdos1172NeighborhoodCode.W3) : Prop :=
  OrdinalRamsey.HasCliqueOfType G (ω_ 2 + ω_ 1) ∨
    OrdinalRamsey.HasCliqueOfType H (ω_ 2 + ω)

/-- A mixed positive earlier ideal and a later positive favorable word
construct all fields of the previously conditional favorable endpoint. -/
theorem part2Targets_of_two_cuts (hCH : CH)
    {r : Code ↪ Erdos1172NeighborhoodCode.W3}
    (G H : SimpleGraph Erdos1172NeighborhoodCode.W3) (hcompl : IsCompl G H)
    {a b : Erdos1172NeighborhoodCode.W3} (ha : GoodCut r G H a)
    (hb : GoodCut r G H b) (hab : a < b)
    (word : List Bool) (hred : true ∈ word) (hblue : false ∈ word)
    (rows : Set Erdos1172NeighborhoodCode.W3) (hrows : rows ⊆ Set.Iio a)
    (hpositive : ¬DerivedSmall r G H word a rows)
    (hfuture : ¬DerivedSmall r G H [false, true] b (Set.Iio b)) :
    Part2Targets G H := by
  obtain ⟨blocks, hlater, hcross⟩ := exists_mixed_blocks hb false true (Set.Iio b)
    hfuture Set.Subset.rfl a hab
  let data : FavorableEndpointData G H := {
    rows := rows
    blocks := fun i => (blocks i).points
    smallness := derivedSmallness word ha
    rows_positive := hpositive
    block_red := fun i => (blocks i).clique
    block_type := fun i => (blocks i).type_eq
    blocks_ordered := fun hij x hx y hy => (hcross _ _ hij x hx y hy).1
    distinct_blocks_blue := by
      intro i j hij x hx y hy
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact (hcross _ _ hij x hx y hy).2
      · exact (hcross _ _ hji y hy x hx).2.symm
    rows_before_blocks := fun x hx i y hy => (hrows hx).trans (hlater i y hy)
    red_core := fun s hs hp => by
      simpa only [colorGraph, ↓reduceIte] using
        exists_core_of_derived_positive word ha s (hs.trans hrows) hp true hred
    blue_core := fun s hs hp => by
      simpa only [colorGraph, Bool.false_eq_true, ↓reduceIte] using
        exists_core_of_derived_positive word ha s (hs.trans hrows) hp false hblue }
  exact part2Targets_of_favorableEndpoint hCH G H hcompl data

/-- In a counterexample with a mixed positive earlier cut, all later good
cuts have an improper favorable-word ideal. -/
theorem favorable_small_of_no_targets (hCH : CH)
    {r : Code ↪ Erdos1172NeighborhoodCode.W3}
    (G H : SimpleGraph Erdos1172NeighborhoodCode.W3) (hcompl : IsCompl G H)
    (hno : ¬Part2Targets G H) {a b : Erdos1172NeighborhoodCode.W3}
    (ha : GoodCut r G H a) (hb : GoodCut r G H b) (hab : a < b)
    (word : List Bool) (hred : true ∈ word) (hblue : false ∈ word)
    (rows : Set Erdos1172NeighborhoodCode.W3) (hrows : rows ⊆ Set.Iio a)
    (hpositive : ¬DerivedSmall r G H word a rows) :
    DerivedSmall r G H [false, true] b (Set.Iio b) := by
  by_contra h
  exact hno (part2Targets_of_two_cuts hCH G H hcompl ha hb hab word hred hblue
    rows hrows hpositive h)

end Erdos1172NeighborhoodFavorableClosure
