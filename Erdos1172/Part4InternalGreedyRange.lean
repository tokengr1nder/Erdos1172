/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalGreedyIncreasing
public import Erdos1172.Part4InternalIncreasingSelfMap
public import Erdos1172.Part4InternalClosurePoints

@[expose] public section

/-!
Normality makes the actual least-choice graph's range co-large. On the
constructed seed/diagonal/closure common set, each ordinal is admissible
at its own stage. Leastness and the nondecreasing law force a fixed point.
The final theorem constructs the full function and proves its co-large
range; neither the function nor its successful range is a premise.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosGreedyPartial

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosRowCandidates ErdosOrdinalLeast
open ErdosColargeIntersection ErdosDiagonalIntersection ErdosClosurePoints

private theorem mem_of_not_mem_complement {κ A x : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ κ) (Hnot : Γ ≤ (x ∈ᴮ difference κ A)ᶜ) : Γ ≤ x ∈ᴮ A := by
  rw [← compl_compl (x ∈ᴮ A), ← imp_bot, ← deduction]
  have Hbad : Γ ⊓ (x ∈ᴮ A)ᶜ ≤ x ∈ᴮ difference κ A := by
    rw [mem_difference]
    exact le_inf (inf_le_left.trans Hx) inf_le_right
  exact bv_absurd _ Hbad (inf_le_left.trans Hnot)

theorem colarge_of_subset {κ J A B : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (HA : Γ ≤ colarge κ J A)
    (HAB : Γ ≤ A ⊆ᴮ B) (HB : Γ ≤ B ⊆ᴮ κ) : Γ ≤ colarge κ J B := by
  refine le_inf HB (small_of_subset (downwardClosed_of_isIdeal HJ) (HA.trans inf_le_right) ?_)
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, mem_difference, mem_difference]
  refine le_inf (inf_le_right.trans inf_le_left) ?_
  rw [← imp_bot (a := x ∈ᴮ A), ← deduction]
  exact bv_absurd _
    (mem_of_mem_subset (inf_le_left.trans (inf_le_left.trans HAB)) inf_le_right)
    (inf_le_left.trans (inf_le_right.trans inf_le_right))

/-- A point in the seed and both constructed diagonal sets is its own
stage's least admissible value. This is equality of internal names. -/
theorem fixedPoint_of_mem_diagonal_closure {seed F f x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f)
    (Hlaw : Γ ≤ greedyLaw seed F f) (Hseed : Γ ≤ x ∈ᴮ seed)
    (Hdiag : Γ ≤ x ∈ᴮ diagonalCommon omegaOne F)
    (Hclosed : Γ ≤ x ∈ᴮ closurePoints f) : Γ ≤ pair x x ∈ᴮ f := by
  have Hxω : Γ ≤ x ∈ᴮ omegaOne := mem_of_mem_subset difference_subset Hdiag
  have Hprefix : Γ ≤ is_func' x omegaOne f :=
    is_func'_subset_of_is_func' Hf (subset_of_mem_Ord Hxω omegaOne_Ord)
  have Hlegal : Γ ≤ rowAdmissible x seed F f x := by
    refine le_inf Hxω (le_inf Hseed (le_inf ?_ ?_))
    · apply le_iInf
      intro j
      apply le_iInf
      intro A
      rw [← deduction]
      have Hjx : Γ ⊓ (j ∈ᴮ x ⊓ pair j A ∈ᴮ F) ≤ j ∈ᴮ x := inf_le_right.trans inf_le_left
      exact diagonalCommon_mem_value (inf_le_left.trans Hdiag)
        (mem_of_mem_Ord Hjx (inf_le_left.trans Hxω) omegaOne_Ord) Hjx
        (inf_le_right.trans inf_le_right)
    · apply le_iInf
      intro j
      apply le_iInf
      intro v
      rw [← deduction]
      have Hjx : Γ ⊓ (j ∈ᴮ x ⊓ pair j v ∈ᴮ f) ≤ j ∈ᴮ x := inf_le_right.trans inf_le_left
      exact closurePoints_apply (inf_le_left.trans Hclosed)
        (mem_of_mem_Ord Hjx (inf_le_left.trans Hxω) omegaOne_Ord) Hjx
        (inf_le_right.trans inf_le_right)
  have Hcandidate : Γ ≤ x ∈ᴮ rowCandidates x seed F f := (mem_rowCandidates_iff Hprefix).mpr Hlegal
  have Hex : Γ ≤ ⨆ v, v ∈ᴮ omegaOne ⊓ pair x v ∈ᴮ f :=
    (le_inf ((Hf.trans inf_le_right).trans (iInf_le _ x)) Hxω).trans bv_imp_elim
  obtain ⟨v, Hv⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hleast := leastIn_apply (greedyLaw_apply Hlaw (Hv.trans inf_le_right)) Hcandidate
  have Hvsub : Γ ≤ v ⊆ᴮ x :=
    (Ord.le_iff_lt_or_eq (Ord_of_mem_Ord (Hv.trans inf_le_left) omegaOne_Ord)
      (Ord_of_mem_Ord Hxω omegaOne_Ord)).mpr (by simpa only [sup_comm] using Hleast)
  have Hxsub : Γ ≤ x ⊆ᴮ v := ErdosIncreasingSelfMap.index_subset_value omegaOne_Ord
    Hf (increasingOn_of_greedyLaw Hf Hlaw) Hxω (Hv.trans inf_le_right)
  have Heq : Γ ≤ v =ᴮ x := by
    rw [eq_iff_subset_subset]
    exact le_inf Hvsub Hxsub
  exact bv_rw'' (ϕ := fun z => pair x z ∈ᴮ f) Heq (Hv.trans inf_le_right)
    B_ext_pair_mem_right

/-- The actual range of any full least-choice graph is co-large under the
explicit normal ideal hypotheses. No supplied club or common-range set is
needed; the proof constructs a co-large set of fixed points. -/
theorem greedy_range_colarge {J seed F f : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hnormal : Γ ≤ diagonalClosure omegaOne J)
    (Hseed : Γ ≤ colarge omegaOne J seed)
    (HF : Γ ≤ is_func' omegaOne (bv_powerset omegaOne) F)
    (Hvalues : Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ omegaOne ⊓ pair i A ∈ᴮ F)
      (difference omegaOne A ∈ᴮ J))
    (Hf : Γ ≤ is_func' omegaOne omegaOne f) (Hlaw : Γ ≤ greedyLaw seed F f) :
    Γ ≤ colarge omegaOne J (image omegaOne omegaOne f) := by
  let D := diagonalCommon omegaOne F
  let C := closurePoints f
  let G := difference seed (binary_union (difference omegaOne D) (difference omegaOne C))
  have HD : Γ ≤ colarge omegaOne J D := diagonalCommon_colarge HJ Hnormal HF Hvalues
  have HC : Γ ≤ colarge omegaOne J C := closurePoints_colarge HJ Habsorb Hclosure Hnormal Hf
  have HG : Γ ≤ colarge omegaOne J G := colarge_difference_of_small HJ Hseed
    (small_union (unionClosed_of_isIdeal HJ) (HD.trans inf_le_right) (HC.trans inf_le_right))
  apply colarge_of_subset HJ HG ?_ image_subset
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ G
  have Hx : Δ ≤ x ∈ᴮ seed ⊓ ((x ∈ᴮ difference omegaOne D)ᶜ ⊓ (x ∈ᴮ difference omegaOne C)ᶜ) := by
    simpa only [G, mem_difference, mem_binary_union, compl_sup] using
      (show Δ ≤ x ∈ᴮ G from inf_le_right)
  have Hxω : Δ ≤ x ∈ᴮ omegaOne :=
    mem_of_mem_subset (inf_le_left.trans (Hseed.trans inf_le_left)) (Hx.trans inf_le_left)
  have Hfixed : Δ ≤ pair x x ∈ᴮ f := fixedPoint_of_mem_diagonal_closure
    (inf_le_left.trans Hf) (inf_le_left.trans Hlaw) (Hx.trans inf_le_left)
    (mem_of_not_mem_complement Hxω (Hx.trans (inf_le_right.trans inf_le_left)))
    (mem_of_not_mem_complement Hxω (Hx.trans (inf_le_right.trans inf_le_right)))
  exact mem_image Hfixed Hxω Hxω

end bSet.ErdosGreedyPartial
