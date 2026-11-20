/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalNonstationaryPressingDown
public import Erdos1172.Part4InternalIncreasingEnumeration

@[expose] public section

/-!
# Internal clubs are stationary and admit increasing omega-one sequences

The binary intersection construction proves that a club meets every
internally named club, hence is positive for the constructed nonstationary
ideal. Its resulting omega-two cardinal size supplies an actual increasing
omega-one injection into that same club. No external enumeration or
additional stationarity premise is used.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosClubs

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosNonstationary ErdosPartition ErdosIncreasingPartial

theorem club_stationary {C : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HC : Γ ≤ club omegaTwo C) :
    Γ ≤ positive omegaTwo nonstationaryIdeal C := by
  apply stationary_of_meets_clubs (club_subset HC)
  apply le_iInf
  intro D
  rw [← deduction]
  obtain ⟨x, Hx⟩ := exists_mem_club
    (club_binary_inter (inf_le_left.trans HCH) (inf_le_left.trans HC)
      (show Γ ⊓ club omegaTwo D ≤ club omegaTwo D from inf_le_right))
  have Hparts := mem_binary_inter_iff.mp Hx
  exact le_iSup_of_le x (le_inf Hparts.1 Hparts.2)

theorem omegaTwo_injects_club {C : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HC : Γ ≤ club omegaTwo C) :
    Γ ≤ injects_into omegaTwo C :=
  stationary_injects_omegaTwo HCH (club_stationary HCH HC)

theorem omegaOne_injects_club {C : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HC : Γ ≤ club omegaTwo C) :
    Γ ≤ injects_into omegaOne C :=
  injects_into_trans
    (injects_into_of_subset (subset_of_mem_Ord omegaOne_mem_omegaTwo omegaTwo_Ord))
    (omegaTwo_injects_club HCH HC)

/-- The map is an actual supported internal injection into C, with
increasingness and an initial image proved by the enumeration theorem. -/
theorem exists_increasing_omegaOne_in_club {C : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HC : Γ ≤ club omegaTwo C) :
    ∃ f : bSet 𝔹, Γ ≤ is_injective_function omegaOne C f ⊓
      (increasingOn omegaOne f ⊓ rangeInitial omegaOne C f) :=
  exists_increasing_injection omegaTwo_Ord (club_subset HC) omegaOne_initial
    (omegaOne_injects_club HCH HC)

theorem increasing_omegaOne_in_club_value {C : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HC : Γ ≤ club omegaTwo C) :
    Γ ≤ ⨆ f, is_injective_function omegaOne C f ⊓
      (increasingOn omegaOne f ⊓ rangeInitial omegaOne C f) := by
  obtain ⟨f, Hf⟩ := exists_increasing_omegaOne_in_club HCH HC
  exact le_iSup_of_le f Hf

end bSet.ErdosClubs
