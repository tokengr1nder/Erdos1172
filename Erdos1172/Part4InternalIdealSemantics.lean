/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Flypitch4.BvmExtras

@[expose] public section

/-!
# Arbitrary-name finite ideal semantics

An ideal is an internal family of subsets, with empty-set membership,
downward closure and binary-union closure. Properness is separate. The core
closure lemmas hold under arbitrary Boolean conditions and for arbitrary
names. They do not assert existence, normality, density or a partition result.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIdeal

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def downwardClosed (I : bSet 𝔹) : 𝔹 :=
  ⨅ X, ⨅ Y, _root_.imp ((X ⊆ᴮ Y) ⊓ (Y ∈ᴮ I)) (X ∈ᴮ I)

def unionClosed (I : bSet 𝔹) : 𝔹 :=
  ⨅ X, ⨅ Y, _root_.imp ((X ∈ᴮ I) ⊓ (Y ∈ᴮ I)) (binary_union X Y ∈ᴮ I)

def isIdeal (κ I : bSet 𝔹) : 𝔹 :=
  (I ⊆ᴮ bv_powerset κ) ⊓
    (((∅ : bSet 𝔹) ∈ᴮ I) ⊓ (downwardClosed I ⊓ unionClosed I))

def properIdeal (κ I : bSet 𝔹) : 𝔹 :=
  isIdeal κ I ⊓ (κ ∈ᴮ I)ᶜ

def positive (κ I X : bSet 𝔹) : 𝔹 :=
  (X ⊆ᴮ κ) ⊓ (X ∈ᴮ I)ᶜ

theorem downwardClosed_of_isIdeal {κ I : bSet 𝔹} {Γ : 𝔹}
    (HI : Γ ≤ isIdeal κ I) : Γ ≤ downwardClosed I :=
  HI.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))

theorem unionClosed_of_isIdeal {κ I : bSet 𝔹} {Γ : 𝔹}
    (HI : Γ ≤ isIdeal κ I) : Γ ≤ unionClosed I :=
  HI.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))

theorem empty_small_of_isIdeal {κ I : bSet 𝔹} {Γ : 𝔹}
    (HI : Γ ≤ isIdeal κ I) : Γ ≤ (∅ : bSet 𝔹) ∈ᴮ I :=
  HI.trans (inf_le_right.trans inf_le_left)

theorem small_of_subset {I X Y : bSet 𝔹} {Γ : 𝔹}
    (Hdown : Γ ≤ downwardClosed I) (HY : Γ ≤ Y ∈ᴮ I)
    (Hsub : Γ ≤ X ⊆ᴮ Y) : Γ ≤ X ∈ᴮ I :=
  (le_inf (Hdown.trans ((iInf_le _ X).trans (iInf_le _ Y))) (le_inf Hsub HY)).trans bv_imp_elim

theorem small_union {I X Y : bSet 𝔹} {Γ : 𝔹}
    (Hunion : Γ ≤ unionClosed I) (HX : Γ ≤ X ∈ᴮ I)
    (HY : Γ ≤ Y ∈ᴮ I) : Γ ≤ binary_union X Y ∈ᴮ I :=
  (le_inf (Hunion.trans ((iInf_le _ X).trans (iInf_le _ Y))) (le_inf HX HY)).trans bv_imp_elim

theorem base_positive_of_properIdeal {κ I : bSet 𝔹} {Γ : 𝔹}
    (HI : Γ ≤ properIdeal κ I) : Γ ≤ positive κ I κ :=
  le_inf subset_self (HI.trans inf_le_right)

theorem small_of_subset_union {κ I X Y Z : bSet 𝔹} {Γ : 𝔹}
    (HI : Γ ≤ isIdeal κ I) (HY : Γ ≤ Y ∈ᴮ I) (HZ : Γ ≤ Z ∈ᴮ I)
    (Hcover : Γ ≤ X ⊆ᴮ binary_union Y Z) : Γ ≤ X ∈ᴮ I :=
  small_of_subset (downwardClosed_of_isIdeal HI)
    (small_union (unionClosed_of_isIdeal HI) HY HZ) Hcover

/-- A subset of `X` representing internal set difference. -/
def difference (X Y : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun z => (z ∈ᴮ Y)ᶜ) X

theorem difference_subset {X Y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ difference X Y ⊆ᴮ X :=
  comprehend_subset (ϕ := fun z => (z ∈ᴮ Y)ᶜ) (Γ := Γ) X

theorem mem_difference (X Y z : bSet 𝔹) : z ∈ᴮ difference X Y = (z ∈ᴮ X) ⊓ (z ∈ᴮ Y)ᶜ := by
  have Hext : B_ext (fun w : bSet 𝔹 => (w ∈ᴮ Y)ᶜ) :=
    B_ext_neg (h := B_ext_mem_left)
  apply le_antisymm
  · have H := (mem_comprehend_iff₂ (fun w => (w ∈ᴮ Y)ᶜ) X Hext).mp
      (le_refl (z ∈ᴮ difference X Y))
    apply H.trans
    apply iSup_le
    intro w
    have Heq : w ∈ᴮ X ⊓ (z =ᴮ w ⊓ (w ∈ᴮ Y)ᶜ) ≤ z =ᴮ w := inf_le_right.trans inf_le_left
    exact le_inf
      (bv_rw' Heq (h_congr := B_ext_mem_left) (H_new := inf_le_left))
      (bv_rw' Heq (h_congr := Hext) (H_new := inf_le_right.trans inf_le_right))
  · apply (mem_comprehend_iff₂ (fun w => (w ∈ᴮ Y)ᶜ) X Hext).mpr
    apply le_iSup_of_le z
    exact le_inf inf_le_left (le_inf bv_refl inf_le_right)

theorem mem_binary_union (X Y z : bSet 𝔹) : z ∈ᴮ binary_union X Y = (z ∈ᴮ X) ⊔ (z ∈ᴮ Y) := by
  have Hpair (w : bSet 𝔹) : w ∈ᴮ ({X, Y} : bSet 𝔹) = (w =ᴮ X) ⊔ (w =ᴮ Y) := by
    have Hempty : w ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by
      rw [mem_unfold]
      exact exists_over_empty _
    rw [mem_insert1, mem_singleton_bSet, Hempty, sup_bot_eq]
  apply le_antisymm
  · have H := (mem_bv_union_iff (u := ({X, Y} : bSet 𝔹))).mp (le_refl (z ∈ᴮ binary_union X Y))
    apply H.trans
    apply iSup_le
    intro w
    rw [Hpair, inf_sup_right]
    exact sup_le (subst_congr_mem_right.trans le_sup_left)
      (subst_congr_mem_right.trans le_sup_right)
  · apply sup_le
    · apply (mem_bv_union_iff (u := ({X, Y} : bSet 𝔹))).mpr
      apply le_iSup_of_le X
      exact le_inf (by rw [Hpair]; exact bv_refl.trans le_sup_left) le_rfl
    · apply (mem_bv_union_iff (u := ({X, Y} : bSet 𝔹))).mpr
      apply le_iSup_of_le Y
      exact le_inf (by rw [Hpair]; exact bv_refl.trans le_sup_right) le_rfl

theorem subset_difference_union {X Y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ X ⊆ᴮ binary_union (difference X Y) Y := by
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction, mem_binary_union, mem_difference]
  have Hcover : z ∈ᴮ X ≤ (z ∈ᴮ X ⊓ (z ∈ᴮ Y)ᶜ) ⊔ z ∈ᴮ Y := by
    calc
      z ∈ᴮ X = (z ∈ᴮ X ⊓ (z ∈ᴮ Y)ᶜ) ⊔ (z ∈ᴮ X ⊓ z ∈ᴮ Y) := by
        rw [← inf_sup_left, compl_sup_eq_top, inf_top_eq]
      _ ≤ (z ∈ᴮ X ⊓ (z ∈ᴮ Y)ᶜ) ⊔ z ∈ᴮ Y := sup_le_sup_left inf_le_right _
  exact inf_le_right.trans Hcover

/-- Removing any small set leaves a positive set. This is the basic internal
centering step used when finitely many small obstructions are discarded. -/
theorem positive_difference_of_small {κ I X Y : bSet 𝔹} {Γ : 𝔹}
    (HI : Γ ≤ isIdeal κ I) (HX : Γ ≤ positive κ I X)
    (HY : Γ ≤ Y ∈ᴮ I) : Γ ≤ positive κ I (difference X Y) := by
  refine le_inf (subset_trans' difference_subset (HX.trans inf_le_left)) ?_
  apply le_neg_of_inf_eq_bot
  apply bot_unique
  have Hsmall : (difference X Y ∈ᴮ I) ⊓ Γ ≤ X ∈ᴮ I :=
    small_of_subset_union (inf_le_right.trans HI) inf_le_left
      (inf_le_right.trans HY) subset_difference_union
  exact (le_inf Hsmall (inf_le_right.trans (HX.trans inf_le_right))).trans inf_compl_eq_bot.le

end bSet.ErdosIdeal
