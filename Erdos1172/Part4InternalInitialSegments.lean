/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Flypitch4.BvmExtras2

@[expose] public section

/-!
# Arbitrary internal ordinal initial segments and their unions

A transitive subset of an internal ordinal is an internal ordinal, hence is
either equal to its bound or a member of that bound. Unions of families of
such initial segments remain initial segments. Every family and every
ordinal here is an arbitrary Boolean-valued name under the stated condition.

The ordinal dichotomy and preservation of transitivity by union reuse the
existing `Ord.le_iff_lt_or_eq` and `transitive_union` theorems.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosInitialSegments

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem Ord_of_transitive_subset {κ A : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HA : Γ ≤ A ⊆ᴮ κ)
    (Htrans : Γ ≤ is_transitive A) : Γ ≤ Ord A := by
  refine le_inf (le_inf (epsilon_trichotomy_of_sub_Ord A ?_) (epsilon_wf_of_sub_Ord A)) Htrans
  apply le_iInf
  intro x
  rw [← deduction]
  exact Ord_of_mem_Ord
    (mem_of_mem_subset (inf_le_left.trans HA) inf_le_right)
    (inf_le_left.trans Hκ)

/-- The disjunction is Boolean-valued, not an external choice of branch. -/
theorem eq_or_mem_of_ordinal_subset {α κ : bSet 𝔹} {Γ : 𝔹}
    (Hα : Γ ≤ Ord α) (Hκ : Γ ≤ Ord κ) (Hsub : Γ ≤ α ⊆ᴮ κ) :
    Γ ≤ (α =ᴮ κ) ⊔ (α ∈ᴮ κ) := by
  simpa only [sup_comm] using (Ord.le_iff_lt_or_eq Hα Hκ).mp Hsub

theorem union_subset_of_members_subset {F κ : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ ⨅ A : bSet 𝔹, _root_.imp (A ∈ᴮ F) (A ⊆ᴮ κ)) :
    Γ ≤ bv_union F ⊆ᴮ κ := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  have Hmem : Γ ⊓ (x ∈ᴮ bv_union F) ≤
      ⨆ A : bSet 𝔹, (A ∈ᴮ F) ⊓ (x ∈ᴮ A) :=
    mem_bv_union_iff.mp inf_le_right
  obtain ⟨A, HA⟩ := exists_convert Hmem (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have Hsub : Γ ⊓ (x ∈ᴮ bv_union F) ≤ A ⊆ᴮ κ :=
    (le_inf (inf_le_left.trans (HF.trans (iInf_le _ A))) (HA.trans inf_le_left)).trans bv_imp_elim
  exact mem_of_mem_subset Hsub (HA.trans inf_le_right)

theorem union_transitive_of_ordinal_members {F : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ ⨅ A : bSet 𝔹, _root_.imp (A ∈ᴮ F) (Ord A)) :
    Γ ≤ is_transitive (bv_union F) := by
  apply transitive_union
  apply le_iInf
  intro A
  rw [← deduction]
  have Hord : Γ ⊓ (A ∈ᴮ F) ≤ Ord A :=
    (le_inf (inf_le_left.trans (HF.trans (iInf_le _ A))) inf_le_right).trans bv_imp_elim
  exact Hord.trans inf_le_right

theorem union_transitive_subset {F κ : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ ⨅ A : bSet 𝔹, _root_.imp (A ∈ᴮ F) (is_transitive A ⊓ A ⊆ᴮ κ)) :
    Γ ≤ is_transitive (bv_union F) ⊓ (bv_union F ⊆ᴮ κ) := by
  refine le_inf ?_ ?_
  · apply transitive_union
    apply le_iInf
    intro A
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans (HF.trans (iInf_le _ A))) inf_le_right).trans
      bv_imp_elim).trans inf_le_left
  · apply union_subset_of_members_subset
    apply le_iInf
    intro A
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans (HF.trans (iInf_le _ A))) inf_le_right).trans
      bv_imp_elim).trans inf_le_right

theorem union_Ord_of_ordinal_subsets {F κ : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ)
    (HF : Γ ≤ ⨅ A : bSet 𝔹, _root_.imp (A ∈ᴮ F) (Ord A ⊓ A ⊆ᴮ κ)) :
    Γ ≤ Ord (bv_union F) := by
  have Htrans : Γ ≤ is_transitive (bv_union F) ⊓ (bv_union F ⊆ᴮ κ) := by
    apply union_transitive_subset
    apply le_iInf
    intro A
    rw [← deduction]
    have HA : Γ ⊓ (A ∈ᴮ F) ≤ Ord A ⊓ (A ⊆ᴮ κ) :=
      (le_inf (inf_le_left.trans (HF.trans (iInf_le _ A))) inf_le_right).trans bv_imp_elim
    exact le_inf (HA.trans (inf_le_left.trans inf_le_right)) (HA.trans inf_le_right)
  exact Ord_of_transitive_subset Hκ (Htrans.trans inf_le_right) (Htrans.trans inf_le_left)

/-- The union of any family of ordinal initial segments stays inside the
bound and is itself either the entire bound or one of its members. -/
theorem union_initialSegment {F κ : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ)
    (HF : Γ ≤ ⨅ A : bSet 𝔹, _root_.imp (A ∈ᴮ F) (Ord A ⊓ A ⊆ᴮ κ)) :
    Γ ≤ Ord (bv_union F) ⊓ ((bv_union F ⊆ᴮ κ) ⊓ ((bv_union F =ᴮ κ) ⊔ (bv_union F ∈ᴮ κ))) := by
  have Hord : Γ ≤ Ord (bv_union F) := union_Ord_of_ordinal_subsets Hκ HF
  have Hsub : Γ ≤ bv_union F ⊆ᴮ κ := by
    apply union_subset_of_members_subset
    apply le_iInf
    intro A
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans (HF.trans (iInf_le _ A))) inf_le_right).trans
      bv_imp_elim).trans inf_le_right
  exact le_inf Hord (le_inf Hsub (eq_or_mem_of_ordinal_subset Hord Hκ Hsub))

end bSet.ErdosInitialSegments
