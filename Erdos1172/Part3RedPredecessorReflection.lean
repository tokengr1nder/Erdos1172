/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CoreObjectIdealCore
public import Erdos1172.Part3TwoSuccessorBootstrap

@[expose] public section

/-!
# Stationary reflection of positive red predecessors

The absence of a source-sized blue clique makes the red predecessors of
every fixed stationary source positive on a club. This applies to the
enlarged algebra naming whole blocks. No large red core is assumed.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RedPredecessorReflection

open Erdos1172Part3CoreObjectCode Erdos1172Part3CoreObjectIdeal
open Erdos1172Part3NeighborhoodCode (W2 cof_W2 alephZero_lt_cof_W2)
open Erdos1172Part3RedCoreIdeal (mk_eq_alephTwo_of_isCofinal)
open OrdinalRamsey (HasCliqueOfType)
open Erdos1172Part3TwoSuccessorBootstrap (isCofinal_of_stationary)

theorem stationaryPressingDown : Set.StationaryPressingDown W2 := by
  have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
    convert Cardinal.isRegular_aleph_add_one 1 using 1
    norm_num
  change Set.StationaryPressingDown ((ω_ 2 : Ordinal.{0}).ToType)
  rw [← Cardinal.ord_aleph]
  exact Set.stationaryPressingDown_ord (ℵ_ 2) hreg
    (Cardinal.aleph0_lt_aleph.mpr (by norm_num))

theorem exists_club_red_predecessor_positive
    (r : Code ↪ W2) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hblue : ¬HasCliqueOfType H (ω_ 2)) (source : Set W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, a ∈ source →
      ¬Small r G H a ((source ∩ Set.Iio a) ∩ {x | G.Adj x a}) := by
  classical
  let bad : Set W2 := {a | a ∈ source ∧
    Small r G H a ((source ∩ Set.Iio a) ∩ {x | G.Adj x a})}
  have hnonstat : ¬IsStationary bad := by
    intro hstat
    let chosen (a : W2) : Code :=
      if h : a ∈ bad then h.2.choose else SmallUnionCode.empty
    have chosen_spec (a : W2) (ha : a ∈ bad) :
        r (chosen a) < a ∧ a ∉ eval G H (chosen a) ∧
          ((source ∩ Set.Iio a) ∩ {x | G.Adj x a}) ⊆ eval G H (chosen a) := by
      simpa only [chosen, dif_pos ha] using ha.2.choose_spec
    obtain ⟨value, hfiber⟩ := stationaryPressingDown bad (fun a => r (chosen a))
      hstat (fun a ha => (chosen_spec a ha).1)
    let fiber : Set W2 := {a | a ∈ bad ∧ r (chosen a) = value}
    have hclique : H.IsClique fiber := by
      intro x hx y hy hxy
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      refine ⟨hxy, ?_⟩
      have hcode : chosen x = chosen y := r.injective (hx.2.trans hy.2.symm)
      intro hred
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · have hmem := (chosen_spec y hy.1).2.2 ⟨⟨hx.1.1, hlt⟩, hred⟩
        rw [← hcode] at hmem
        exact (chosen_spec x hx.1).2.1 hmem
      · have hmem := (chosen_spec x hx.1).2.2 ⟨⟨hy.1.1, hgt⟩, hred.symm⟩
        rw [hcode] at hmem
        exact (chosen_spec y hy.1).2.1 hmem
    exact hblue ⟨fiber, hclique,
      Erdos1172Part3Failure.typeLT_eq_omegaTwo_of_mk_eq
        (mk_eq_alephTwo_of_isCofinal (isCofinal_of_stationary hfiber))⟩
  obtain ⟨club, hclub, hdisjoint⟩ := not_isStationary_iff.mp hnonstat
  refine ⟨club, hclub, ?_⟩
  intro a hac has hsmall
  exact Set.disjoint_left.mp hdisjoint ⟨has, hsmall⟩ hac

/-- The blue bound needed by Problem 1172 suffices for the reflection. -/
theorem exists_club_red_predecessor_positive_of_no_blue_target
    (r : Code ↪ W2) (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) (source : Set W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, a ∈ source →
      ¬Small r G H a ((source ∩ Set.Iio a) ∩ {x | G.Adj x a}) := by
  apply exists_club_red_predecessor_positive r G H hcompl _ source
  rintro ⟨s, hs, ht⟩
  obtain ⟨t, hts, htt⟩ := Ordinal.exists_subset_typeLT_eq s
    (show (ω_ 1 : Ordinal.{0}) + 2 ≤ typeLT s by
      rw [ht]
      exact Erdos1172Part3RedCoreDerivedIdeal.blue_target_le_omegaTwo)
  exact hblue ⟨t, hs.subset hts, htt⟩

end Erdos1172Part3RedPredecessorReflection
