/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalClubLarge
public import Erdos1172.Part4InternalCountablyBoundedSup

@[expose] public section

/-!
The actual set of countably bounded predecessors of omega-two meets every
internal club. An increasing omega-one chain through the club supplies a
countably bounded supremum still below omega-two. Internal countable
boundedness of omega-one remains explicit and is discharged by the existing
row-ideal assumptions, not by ground-model regularity.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosStationaryEndpoints

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosClubs ErdosIdeal ErdosNonstationary
open ErdosOmegaOneIdealBounded ErdosCountablyBoundedSup ErdosCountableImage
open ErdosPartition ErdosSimultaneousRowChoice

theorem increasingSup_mem_omegaTwo {C f : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HC : Γ ≤ C ⊆ᴮ omegaTwo)
    (Hf : Γ ≤ is_injective_function omegaOne C f) :
    Γ ≤ increasingSup C f ∈ᴮ omegaTwo :=
  ErdosOmegaTwoBounded.union_mem_omegaTwo HCH (subset_trans' image_subset HC)
    (image_injects_into_ordinal (is_func'_of_is_function (Hf.trans inf_le_left))
      injects_into_refl omegaOne_Ord)

theorem exists_countablyBounded_mem_club {C : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ countablyBounded omegaOne)
    (HC : Γ ≤ club omegaTwo C) :
    ∃ L : bSet 𝔹, Γ ≤ L ∈ᴮ C ⊓ countablyBounded L := by
  obtain ⟨f, Hf⟩ := exists_increasing_omegaOne_in_club HCH HC
  have Hfunction := Hf.trans inf_le_left
  have Hincreasing := Hf.trans (inf_le_right.trans inf_le_left)
  have Hsub := club_subset HC
  have HL := increasingSup_mem_omegaTwo HCH Hsub Hfunction
  refine ⟨increasingSup C f, le_inf ?_ ?_⟩
  · exact closedIn_apply (club_closed HC) HL
      (increasingSup_nonempty HB (Hfunction.trans inf_le_left) Hincreasing)
      (increasingSup_cofinal HB (Hfunction.trans inf_le_left) Hincreasing)
  · exact countablyBounded_increasingSup HB Hsub (Hfunction.trans inf_le_left) Hincreasing

def stationaryEndpoints : bSet 𝔹 :=
  comprehend countablyBounded omegaTwo

theorem mem_stationaryEndpoints_iff {L : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ L ∈ᴮ stationaryEndpoints ↔
      Γ ≤ L ∈ᴮ omegaTwo ∧ Γ ≤ countablyBounded L :=
  ErdosRelationGraph.mem_comprehend_and countablyBounded_ext

theorem stationaryEndpoints_subset {Γ : 𝔹} :
    Γ ≤ stationaryEndpoints ⊆ᴮ omegaTwo :=
  comprehend_subset (ϕ := countablyBounded) omegaTwo

theorem stationaryEndpoints_stationary {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ countablyBounded omegaOne) :
    Γ ≤ positive omegaTwo nonstationaryIdeal stationaryEndpoints := by
  apply stationary_of_meets_clubs stationaryEndpoints_subset
  apply le_iInf
  intro C
  rw [← deduction]
  have HC : Γ ⊓ club omegaTwo C ≤ club omegaTwo C := inf_le_right
  obtain ⟨L, HL⟩ := exists_countablyBounded_mem_club
    (inf_le_left.trans HCH) (inf_le_left.trans HB) HC
  have HE := mem_stationaryEndpoints_iff.mpr
    ⟨mem_of_mem_subset (club_subset HC) (HL.trans inf_le_left), HL.trans inf_le_right⟩
  exact le_iSup_of_le L (le_inf HE (HL.trans inf_le_left))

theorem stationaryEndpoints_injects_omegaTwo {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ countablyBounded omegaOne) :
    Γ ≤ injects_into omegaTwo stationaryEndpoints :=
  stationary_injects_omegaTwo HCH (stationaryEndpoints_stationary HCH HB)

theorem stationaryEndpoints_of_rowIdeals {S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Hrows : Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J)) :
    Γ ≤ positive omegaTwo nonstationaryIdeal stationaryEndpoints :=
  stationaryEndpoints_stationary HCH (countablyBounded_of_rowIdeals Hrows)

end bSet.ErdosStationaryEndpoints
