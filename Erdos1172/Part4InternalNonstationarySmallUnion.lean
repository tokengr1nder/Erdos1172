/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalNonstationaryIdeal
public import Erdos1172.Part4InternalClubIntersection

@[expose] public section

/-!
# Internally small unions of nonstationary names

Bounded internal choice constructs a supported function assigning an
avoiding club to every member of the given arbitrary name family. The
actual indexed club intersection avoids its union. Consequently the
constructed nonstationary ideal is closed under internally omega-one-small
unions under CH, including the empty family. Countable closure follows
without any external enumeration or supplied coherent club choices.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosNonstationary

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosClubs ErdosIndexedIntersection

/-- Every internally named family of nonstationary sets has one actual
supported function selecting avoiding clubs, at the same condition. -/
theorem exists_avoiding_club_selector {T : bSet 𝔹} {Γ : 𝔹}
    (HT : Γ ≤ T ⊆ᴮ nonstationaryIdeal) :
    ∃ F : bSet 𝔹, Γ ≤ is_function T (bv_powerset omegaTwo) F ⊓
      ⨅ A, ⨅ C, _root_.imp (A ∈ᴮ T ⊓ pair A C ∈ᴮ F)
        (club omegaTwo C ⊓ A ⊆ᴮ difference omegaTwo C) := by
  apply ErdosSmallFiberBound.exists_selector_of_pointwise
    (P := fun A C => club omegaTwo C ⊓ A ⊆ᴮ difference omegaTwo C)
    (fun _ => B_ext_inf B_ext_const B_ext_subset_left)
    (fun A => avoidingClub_ext A)
  apply le_iInf
  intro A
  rw [← deduction]
  obtain ⟨C, HC⟩ := exists_avoiding_club
    (mem_of_mem_subset (inf_le_left.trans HT) (show Γ ⊓ A ∈ᴮ T ≤ A ∈ᴮ T from inf_le_right))
  exact le_iSup_of_le C (le_inf (mem_powerset_iff.mpr (club_subset (HC.trans inf_le_left))) HC)

/-- Unions of arbitrary internally omega-one-small families of members
remain in the actual nonstationary ideal. -/
theorem nonstationaryIdeal_small_union {T : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HT : Γ ≤ T ⊆ᴮ nonstationaryIdeal)
    (Hsmall : Γ ≤ injects_into T omegaOne) :
    Γ ≤ bv_union T ∈ᴮ nonstationaryIdeal := by
  obtain ⟨F, HF⟩ := exists_avoiding_club_selector HT
  have Hweak := is_func'_of_is_function (HF.trans inf_le_left)
  have Hclubs : Γ ≤ ⨅ A, ⨅ C, _root_.imp (A ∈ᴮ T ⊓ pair A C ∈ᴮ F) (club omegaTwo C) := by
    apply le_iInf
    intro A
    apply le_iInf
    intro C
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans ((HF.trans inf_le_right).trans
      ((iInf_le _ A).trans (iInf_le _ C)))) inf_le_right).trans bv_imp_elim).trans inf_le_left
  have Hclub := club_indexedIntersection HCH Hweak Hsmall Hclubs
  apply mem_nonstationaryIdeal_of_club Hclub
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ bv_union T
  obtain ⟨A, HA⟩ := exists_convert
    (mem_bv_union_iff.mp (show Δ ≤ x ∈ᴮ bv_union T from inf_le_right))
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have Hcex : Δ ≤ ⨆ C, C ∈ᴮ bv_powerset omegaTwo ⊓ pair A C ∈ᴮ F :=
    (le_inf (inf_le_left.trans ((Hweak.trans inf_le_right).trans (iInf_le _ A)))
      (HA.trans inf_le_left)).trans bv_imp_elim
  obtain ⟨C, HC⟩ := exists_convert Hcex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Havoid : Δ ≤ A ⊆ᴮ difference omegaTwo C :=
    ((le_inf (inf_le_left.trans ((HF.trans inf_le_right).trans
      ((iInf_le _ A).trans (iInf_le _ C))))
      (le_inf (HA.trans inf_le_left) (HC.trans inf_le_right))).trans bv_imp_elim).trans inf_le_right
  have Hx := mem_of_mem_subset Havoid (HA.trans inf_le_right)
  rw [mem_difference] at Hx
  rw [mem_difference]
  refine le_inf (Hx.trans inf_le_left) ?_
  rw [← imp_bot, ← deduction]
  have Hsub : Δ ⊓ x ∈ᴮ indexedIntersection omegaTwo F T ≤
      indexedIntersection omegaTwo F T ⊆ᴮ C :=
    indexedIntersection_subset_value (inf_le_left.trans (HA.trans inf_le_left))
      (inf_le_left.trans (HC.trans inf_le_right))
  exact bv_absurd _ (mem_of_mem_subset Hsub inf_le_right)
    (inf_le_left.trans (Hx.trans inf_le_right))

end bSet.ErdosNonstationary
