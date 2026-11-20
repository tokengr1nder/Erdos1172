/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIndexedIntersection
public import Erdos1172.Part4InternalPartitionGraph

@[expose] public section

/-!
Internally countable intersections of co-large sets remain co-large.
The countable family is an arbitrary internal name, its actual value image
and difference image form the loss family, and countable closure makes the
actual loss union small. Weak total-functional graphs suffice, so a graph
on a larger domain may be reused on a countable internal prefix.
No CH, normality, dense basis, or external enumeration is needed.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosColargeIntersection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosIdeal ErdosIndexedIntersection ErdosCountablyCentered ErdosPartition

/-- A subset of the base whose relative complement belongs to the ideal. -/
def colarge (κ J A : bSet 𝔹) : 𝔹 :=
  A ⊆ᴮ κ ⊓ difference κ A ∈ᴮ J

/-- If deleting L leaves a subset of A, then the complement of A is
contained in L. This is an arbitrary-name Boolean set identity. -/
theorem complement_subset_of_remainder_subset {κ L A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ difference κ L ⊆ᴮ A) :
    Γ ≤ difference κ A ⊆ᴮ L := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ difference κ A
  have Hx : Δ ≤ x ∈ᴮ κ ⊓ (x ∈ᴮ A)ᶜ := by
    rw [← mem_difference]
    exact inf_le_right
  change Δ ≤ x ∈ᴮ L
  rw [← compl_compl (x ∈ᴮ L), ← imp_bot, ← deduction]
  have Hrem : Δ ⊓ (x ∈ᴮ L)ᶜ ≤ x ∈ᴮ difference κ L := by
    rw [mem_difference]
    exact le_inf (inf_le_left.trans (Hx.trans inf_le_left)) inf_le_right
  exact bv_absurd _
    (mem_of_mem_subset (inf_le_left.trans (inf_le_left.trans H)) Hrem)
    (inf_le_left.trans (Hx.trans inf_le_right))

/-- The concrete remainder lies in the actual indexed intersection.
Only weak functionality on the guarded domain is required. -/
theorem commonRemainder_subset_indexedIntersection {κ T F : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_func' T (bv_powerset κ) F) :
    Γ ≤ commonRemainder κ (lossFamily κ (image T (bv_powerset κ) F)) ⊆ᴮ
      indexedIntersection κ F T := by
  apply subset_indexedIntersection commonRemainder_subset
  apply le_iInf
  intro t
  apply le_iInf
  intro A
  rw [← deduction]
  let Δ := Γ ⊓ (t ∈ᴮ T ⊓ pair t A ∈ᴮ F)
  have Ht : Δ ≤ t ∈ᴮ T := inf_le_right.trans inf_le_left
  have Hpair : Δ ≤ pair t A ∈ᴮ F := inf_le_right.trans inf_le_right
  have Hcod : Δ ≤ A ∈ᴮ bv_powerset κ :=
    value_mem_codomain (inf_le_left.trans HF) Ht Hpair
  have Him : Δ ≤ A ∈ᴮ image T (bv_powerset κ) F := mem_image Hpair Ht Hcod
  exact commonRemainder_subset_of_loss_mem (difference_mem_lossFamily Him)

/-- The complement of the actual indexed intersection is small whenever
the internally countable guarded values have small complements. The ideal
need not be proper for this closure theorem, and empty domains are allowed. -/
theorem indexedIntersection_complement_small {κ J T F : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (Hclosure : Γ ≤ countableClosure J)
    (HF : Γ ≤ is_func' T (bv_powerset κ) F)
    (HT : Γ ≤ injects_into T bSet.omega)
    (Hvalues : Γ ≤ ⨅ t, ⨅ A,
      _root_.imp (t ∈ᴮ T ⊓ pair t A ∈ᴮ F) (difference κ A ∈ᴮ J)) :
    Γ ≤ difference κ (indexedIntersection κ F T) ∈ᴮ J := by
  let V := image T (bv_powerset κ) F
  let L := lossFamily κ V
  have HVcount : Γ ≤ injects_into V bSet.omega :=
    ErdosCountableImage.image_countable HF HT
  have HVsmall : Γ ≤ ⨅ A, _root_.imp (A ∈ᴮ V) (difference κ A ∈ᴮ J) :=
    commonLoss_image_small (U := T) Hvalues subset_self
  have HLsmall : Γ ≤ bv_union L ∈ᴮ J :=
    countable_union_small Hclosure (lossFamily_countable HVcount)
      (lossFamily_subset_ideal HVsmall)
  have Hcover : Γ ≤ difference κ (indexedIntersection κ F T) ⊆ᴮ bv_union L :=
    complement_subset_of_remainder_subset (commonRemainder_subset_indexedIntersection HF)
  exact small_of_subset (downwardClosed_of_isIdeal HJ) HLsmall Hcover

theorem indexedIntersection_colarge {κ J T F : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (Hclosure : Γ ≤ countableClosure J)
    (HF : Γ ≤ is_func' T (bv_powerset κ) F)
    (HT : Γ ≤ injects_into T bSet.omega)
    (Hvalues : Γ ≤ ⨅ t, ⨅ A,
      _root_.imp (t ∈ᴮ T ⊓ pair t A ∈ᴮ F) (difference κ A ∈ᴮ J)) :
    Γ ≤ colarge κ J (indexedIntersection κ F T) :=
  le_inf indexedIntersection_subset
    (indexedIntersection_complement_small HJ Hclosure HF HT Hvalues)

/-- The usual co-large-values predicate also implies the complement-only
premise; powerset support is already supplied by the weak function. -/
theorem indexedIntersection_colarge_of_colarge_values {κ J T F : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (Hclosure : Γ ≤ countableClosure J)
    (HF : Γ ≤ is_func' T (bv_powerset κ) F)
    (HT : Γ ≤ injects_into T bSet.omega)
    (Hvalues : Γ ≤ ⨅ t, ⨅ A,
      _root_.imp (t ∈ᴮ T ⊓ pair t A ∈ᴮ F) (colarge κ J A)) :
    Γ ≤ colarge κ J (indexedIntersection κ F T) := by
  apply indexedIntersection_colarge HJ Hclosure HF HT
  apply le_iInf
  intro t
  apply le_iInf
  intro A
  rw [← deduction]
  have HA : Γ ⊓ (t ∈ᴮ T ⊓ pair t A ∈ᴮ F) ≤ colarge κ J A :=
    (le_inf (inf_le_left.trans
      (Hvalues.trans ((iInf_le _ t).trans (iInf_le _ A)))) inf_le_right).trans bv_imp_elim
  exact HA.trans inf_le_right

/-- The complement after an additional removal is covered by the original
complement and the removed set. No containment of the removed set is needed. -/
theorem complement_difference_subset_union {κ A L : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ difference κ (difference A L) ⊆ᴮ binary_union (difference κ A) L := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, mem_difference, mem_difference, mem_binary_union, mem_difference,
    compl_inf, compl_compl, inf_sup_left]
  exact inf_le_right.trans
    (sup_le le_sup_left (inf_le_right.trans le_sup_right))

/-- Removing any ideal-small set preserves co-largeness. -/
theorem colarge_difference_of_small {κ J A L : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (HA : Γ ≤ colarge κ J A)
    (HL : Γ ≤ L ∈ᴮ J) : Γ ≤ colarge κ J (difference A L) :=
  le_inf (subset_trans' difference_subset (HA.trans inf_le_left))
    (small_of_subset_union HJ (HA.trans inf_le_right) HL complement_difference_subset_union)

/-- Properness makes every co-large set positive; it is not needed for
the preceding complement-closure and removal theorems. -/
theorem colarge_positive {κ J A : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal κ J) (HA : Γ ≤ colarge κ J A) :
    Γ ≤ positive κ J A := by
  refine le_inf (HA.trans inf_le_left) ?_
  rw [← imp_bot, ← deduction]
  have Hsmall : Γ ⊓ A ∈ᴮ J ≤ κ ∈ᴮ J :=
    small_of_subset_union (inf_le_left.trans (HJ.trans inf_le_left))
      (inf_le_left.trans (HA.trans inf_le_right)) inf_le_right subset_difference_union
  exact bv_absurd _ Hsmall (inf_le_left.trans (HJ.trans inf_le_right))

theorem positive_not_empty {κ J A : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (HA : Γ ≤ positive κ J A) :
    Γ ≤ (A =ᴮ (∅ : bSet 𝔹))ᶜ := by
  rw [← imp_bot, ← deduction]
  have Hsmall : Γ ⊓ A =ᴮ (∅ : bSet 𝔹) ≤ A ∈ᴮ J :=
    bv_rw' (x := A) (y := (∅ : bSet 𝔹)) (ϕ := fun X => X ∈ᴮ J)
      inf_le_right (h_congr := B_ext_mem_left)
      (H_new := empty_small_of_isIdeal (inf_le_left.trans HJ))
  exact bv_absurd _ Hsmall (inf_le_left.trans (HA.trans inf_le_right))

/-- Fullness produces an actual internal member at the original Boolean
condition, not an external or checked-ground representative. -/
theorem exists_mem_of_positive {κ J A : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (HA : Γ ≤ positive κ J A) :
    ∃ x : bSet 𝔹, Γ ≤ x ∈ᴮ A :=
  exists_convert (nonempty_iff_exists_mem.mp (positive_not_empty HJ HA)) B_ext_mem_left

theorem exists_mem_of_colarge {κ J A : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal κ J) (HA : Γ ≤ colarge κ J A) :
    ∃ x : bSet 𝔹, Γ ≤ x ∈ᴮ A :=
  exists_mem_of_positive (HJ.trans inf_le_left) (colarge_positive HJ HA)

end bSet.ErdosColargeIntersection
