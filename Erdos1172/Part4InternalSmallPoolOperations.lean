/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOrdinalPointHull
public import Erdos1172.Part4InternalSmallFamilyUnion

@[expose] public section

/-!
# Small unions and a globally bounded ordinal growth operation

The clipped successor is defined on every name and always lies in the
powerset of omega-two. On small point pools it is exactly the successor
of their ordinal closure. Thus it contains that closure as a point and
grows strictly, without requiring boundedness of arbitrary past inputs.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSmallPoolOperations

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosCountablePast ErdosOrdinalPointHull
open ErdosLargeDifference ErdosPartialInjection

theorem binary_union_congr {A B C D : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A =ᴮ B) (HC : Γ ≤ C =ᴮ D) :
    Γ ≤ binary_union A C =ᴮ binary_union B D := by
  unfold binary_union
  exact B_congr_bv_union (bv_trans (B_congr_insert1_left HA)
    (B_congr_insert1_right (B_congr_insert1_left HC)))

theorem past_congr : B_congr (past : bSet 𝔹 → bSet 𝔹) := by
  intro A B Γ H
  exact binary_union_congr H (B_congr_bv_union H)

theorem subset_binary_union_left {A B : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ A ⊆ᴮ binary_union A B := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, mem_binary_union]
  exact inf_le_right.trans le_sup_left

theorem subset_binary_union_right {A B : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ B ⊆ᴮ binary_union A B := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, mem_binary_union]
  exact inf_le_right.trans le_sup_right

theorem binary_union_subset {A B K : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ K) (HB : Γ ≤ B ⊆ᴮ K) :
    Γ ≤ binary_union A B ⊆ᴮ K := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, mem_binary_union, inf_sup_left]
  exact sup_le (mem_of_mem_subset (inf_le_left.trans HA) inf_le_right)
    (mem_of_mem_subset (inf_le_left.trans HB) inf_le_right)

/-- No common ambient set is needed for the finite small-union bound. -/
theorem binary_union_injects_omegaOne {A B : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HA : Γ ≤ injects_into A omegaOne)
    (HB : Γ ≤ injects_into B omegaOne) :
    Γ ≤ injects_into (binary_union A B) omegaOne := by
  have Hnot : Γ ≤ (injects_into omegaTwo (binary_union A B))ᶜ := by
    rw [← imp_bot, ← deduction]
    let Δ := Γ ⊓ injects_into omegaTwo (binary_union A B)
    have Hlarge : Δ ≤ injects_into omegaTwo (difference (binary_union A B) A) :=
      omegaTwo_injects_difference (inf_le_left.trans HCH) inf_le_right
        (inf_le_left.trans HA)
    have Hsub : Δ ≤ difference (binary_union A B) A ⊆ᴮ B := by
      rw [subset_unfold']
      apply le_iInf
      intro x
      rw [← deduction, mem_difference, mem_binary_union, inf_sup_right, inf_sup_left]
      apply sup_le
      · exact (bv_absurd _ (inf_le_right.trans inf_le_left)
          (inf_le_right.trans inf_le_right)).trans bot_le
      · exact inf_le_right.trans inf_le_left
    exact bv_absurd _ (injects_into_trans Hlarge
      (injects_into_trans (injects_into_of_subset Hsub) (inf_le_left.trans HB)))
      omegaTwo_not_injects
  apply (le_inf le_rfl
    (omegaTwo_cardinal_dichotomy (S := binary_union A B) (Γ := Γ))).trans
  rw [inf_sup_left]
  exact sup_le inf_le_right
    ((bv_absurd _ inf_le_right (inf_le_left.trans Hnot)).trans bot_le)

theorem succ_injects_omegaOne {A : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HA : Γ ≤ injects_into A omegaOne) :
    Γ ≤ injects_into (succ A) omegaOne :=
  bv_rw' (ϕ := fun X => injects_into X omegaOne) succ_eq_binary_union
    (h_congr := B_ext_injects_into_left)
    (H_new := binary_union_injects_omegaOne HCH (singleton_injects_omegaOne A) HA)

def ordinalGrow (P : bSet 𝔹) : bSet 𝔹 := succ (past P) ∩ᴮ omegaTwo

theorem ordinalGrow_congr : B_congr (ordinalGrow : bSet 𝔹 → bSet 𝔹) := by
  intro P Q Γ H
  exact B_congr_binary_inter_left (B_congr_succ (past_congr H))

theorem ordinalGrow_subset {P : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ordinalGrow P ⊆ᴮ omegaTwo := binary_inter_subset_right

theorem subset_ordinalGrow {P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ P ⊆ᴮ omegaTwo) : Γ ≤ P ⊆ᴮ ordinalGrow P :=
  subset_binary_inter_iff.mpr ⟨subset_trans' subset_past subset_succ, HP⟩

/-- Clipping does not change the successor on a genuinely small pool. -/
theorem ordinalGrow_eq_succ_past {P : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HP : Γ ≤ P ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into P omegaOne) :
    Γ ≤ ordinalGrow P =ᴮ succ (past P) := by
  have Hsub : Γ ≤ succ (past P) ⊆ᴮ omegaTwo :=
    Ord.succ_le_of_lt omegaTwo_Ord (past_mem_omegaTwo HCH HP Hsmall)
  apply mem_ext
  · apply le_iInf
    intro x
    rw [← deduction]
    exact (mem_binary_inter_iff.mp
      (show Γ ⊓ x ∈ᴮ ordinalGrow P ≤ x ∈ᴮ ordinalGrow P from inf_le_right)).1
  · apply le_iInf
    intro x
    rw [← deduction]
    exact mem_binary_inter_iff.mpr
      ⟨inf_le_right, mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right⟩

theorem past_mem_ordinalGrow {P : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HP : Γ ≤ P ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into P omegaOne) : Γ ≤ past P ∈ᴮ ordinalGrow P := by
  apply mem_binary_inter_iff.mpr
  refine ⟨?_, past_mem_omegaTwo HCH HP Hsmall⟩
  change Γ ≤ past P ∈ᴮ insert (past P) (past P)
  rw [mem_insert1]
  exact bv_refl.trans le_sup_left

theorem ordinalGrow_Ord {P : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HP : Γ ≤ P ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into P omegaOne) : Γ ≤ Ord (ordinalGrow P) :=
  bv_rw' (ϕ := Ord) (ordinalGrow_eq_succ_past HCH HP Hsmall)
    (h_congr := B_ext_Ord) (H_new := Ord_succ (past_Ord_of_subset omegaTwo_Ord HP))

theorem ordinalGrow_injects_omegaOne {P : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HP : Γ ≤ P ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into P omegaOne) :
    Γ ≤ injects_into (ordinalGrow P) omegaOne :=
  injects_into_trans (injects_into_of_subset binary_inter_subset_left)
    (succ_injects_omegaOne HCH (past_injects_omegaOne HCH HP Hsmall))

end bSet.ErdosSmallPoolOperations
