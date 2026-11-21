/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalActiveInverse
public import Erdos1172.Part4InternalFusionMaskedTailCross

@[expose] public section

/-!
# Co-large ranges for least-choice rows activated after their birth

Only active earlier coordinates constrain a new value. Consequently the
inactive prefix need not be increasing and may consist entirely of zero.
An actual total active-inverse selector replaces the invalid global
increasing-selfmap argument. On the seed, section diagonal, and closure
points of both the row and its inverse, past the birth ordinal, leastness
forces a fixed point. This constructs a co-large subset of the actual
active range, not a separately assumed positive mask.

The final wrapper identifies that range with the existing actual
coordinate mask. Its least-candidate and section hypotheses remain
explicit structural graph laws, to be derived from a successful fusion.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBirthGreedyRange

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosRowCandidates ErdosOrdinalLeast
open ErdosColargeIntersection ErdosDiagonalIntersection ErdosClosurePoints
open ErdosCountablePast ErdosIncreasingTail ErdosGreedyPartial ErdosActiveInverse
open ErdosFusionRowCandidates ErdosFusionMaskedTail ErdosSimultaneousTraces

def birthGreedyLaw (ν seed F f : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ v, _root_.imp ((ν ∈ᴮ i ⊓ i ∈ᴮ omegaOne) ⊓ pair i v ∈ᴮ f)
    (leastIn (rowCandidates (activatedStages i ν) seed F f) v)

theorem birthGreedyLaw_apply {ν seed F f i v : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ birthGreedyLaw ν seed F f)
    (Hνi : Γ ≤ ν ∈ᴮ i) (Hi : Γ ≤ i ∈ᴮ omegaOne)
    (Hiv : Γ ≤ pair i v ∈ᴮ f) :
    Γ ≤ leastIn (rowCandidates (activatedStages i ν) seed F f) v :=
  (le_inf (H.trans ((iInf_le _ i).trans (iInf_le _ v)))
    (le_inf (le_inf Hνi Hi) Hiv)).trans bv_imp_elim

theorem birth_rowAdmissible {ν seed F f i v : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f)
    (Hlaw : Γ ≤ birthGreedyLaw ν seed F f)
    (Hνi : Γ ≤ ν ∈ᴮ i) (Hi : Γ ≤ i ∈ᴮ omegaOne)
    (Hiv : Γ ≤ pair i v ∈ᴮ f) :
    Γ ≤ rowAdmissible (activatedStages i ν) seed F f v :=
  (mem_rowCandidates_iff (is_func'_subset_of_is_func' Hf
    (subset_trans' activatedStages_subset (subset_of_mem_Ord Hi omegaOne_Ord)))).mp
    (leastIn_mem (birthGreedyLaw_apply Hlaw Hνi Hi Hiv))

/-- Increasingness is derived only on the actual active domain. Failed
intermediate block choices do not remove any of these recorded stages. -/
theorem active_increasing_of_birthGreedyLaw {ν seed F f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f)
    (Hlaw : Γ ≤ birthGreedyLaw ν seed F f) :
    Γ ≤ increasingOn (activatedStages omegaOne ν) f := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((i ∈ᴮ activatedStages omegaOne ν ⊓
    j ∈ᴮ activatedStages omegaOne ν) ⊓ i ∈ᴮ j) ⊓
    (pair i x ∈ᴮ f ⊓ pair j y ∈ᴮ f))
  have Hi := mem_activatedStages_iff.mp (show Δ ≤ i ∈ᴮ activatedStages omegaOne ν from
      inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
  have Hj := mem_activatedStages_iff.mp (show Δ ≤ j ∈ᴮ activatedStages omegaOne ν from
      inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  have Hlegal := birth_rowAdmissible (inf_le_left.trans Hf) (inf_le_left.trans Hlaw)
    Hj.2 Hj.1 (show Δ ≤ pair j y ∈ᴮ f from
      inf_le_right.trans (inf_le_right.trans inf_le_right))
  have Hprevious := Hlegal.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  exact (le_inf (Hprevious.trans ((iInf_le _ i).trans (iInf_le _ x)))
    (le_inf (mem_activatedStages_iff.mpr
      ⟨inf_le_right.trans (inf_le_left.trans inf_le_right), Hi.2⟩)
      (inf_le_right.trans (inf_le_right.trans inf_le_left)))).trans bv_imp_elim

/-- A good point past the birth is an actual fixed point of the original
row. The inverse closure condition, not a false all-stage monotonicity
law, supplies the reverse inequality. -/
theorem birth_fixedPoint_of_diagonal_closures
    {ν seed F f g x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f)
    (Hlaw : Γ ≤ birthGreedyLaw ν seed F f)
    (Hg : Γ ≤ is_function omegaOne omegaOne g)
    (Hglaw : Γ ≤ activeInverseLaw ν f g)
    (Hνx : Γ ≤ ν ∈ᴮ x) (Hseed : Γ ≤ x ∈ᴮ seed)
    (Hdiag : Γ ≤ x ∈ᴮ diagonalCommon omegaOne F)
    (Hclosedf : Γ ≤ x ∈ᴮ closurePoints f)
    (Hclosedg : Γ ≤ x ∈ᴮ closurePoints g) : Γ ≤ pair x x ∈ᴮ f := by
  have Hx : Γ ≤ x ∈ᴮ omegaOne := mem_of_mem_subset difference_subset Hdiag
  have Hprefix : Γ ≤ is_func' (activatedStages x ν) omegaOne f :=
    is_func'_subset_of_is_func' Hf
      (subset_trans' activatedStages_subset (subset_of_mem_Ord Hx omegaOne_Ord))
  have Hlegal : Γ ≤ rowAdmissible (activatedStages x ν) seed F f x := by
    refine le_inf Hx (le_inf Hseed (le_inf ?_ ?_))
    · apply le_iInf
      intro j
      apply le_iInf
      intro A
      rw [← deduction]
      have Hjx := (mem_activatedStages_iff.mp
        (show Γ ⊓ (j ∈ᴮ activatedStages x ν ⊓ pair j A ∈ᴮ F) ≤
          j ∈ᴮ activatedStages x ν from inf_le_right.trans inf_le_left)).1
      exact diagonalCommon_mem_value (inf_le_left.trans Hdiag)
        (mem_of_mem_Ord Hjx (inf_le_left.trans Hx) omegaOne_Ord) Hjx
        (inf_le_right.trans inf_le_right)
    · apply le_iInf
      intro j
      apply le_iInf
      intro v
      rw [← deduction]
      have Hjx := (mem_activatedStages_iff.mp
        (show Γ ⊓ (j ∈ᴮ activatedStages x ν ⊓ pair j v ∈ᴮ f) ≤
          j ∈ᴮ activatedStages x ν from inf_le_right.trans inf_le_left)).1
      exact closurePoints_apply (inf_le_left.trans Hclosedf)
        (mem_of_mem_Ord Hjx (inf_le_left.trans Hx) omegaOne_Ord) Hjx
        (inf_le_right.trans inf_le_right)
  have Hcandidate := (mem_rowCandidates_iff Hprefix).mpr Hlegal
  have Hex : Γ ≤ ⨆ v, v ∈ᴮ omegaOne ⊓ pair x v ∈ᴮ f :=
    (le_inf ((Hf.trans inf_le_right).trans (iInf_le _ x)) Hx).trans bv_imp_elim
  obtain ⟨v, Hv⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hleast := leastIn_apply (birthGreedyLaw_apply Hlaw Hνx Hx (Hv.trans inf_le_right)) Hcandidate
  have Hvsub : Γ ≤ v ⊆ᴮ x :=
    (Ord.le_iff_lt_or_eq (Ord_of_mem_Ord (Hv.trans inf_le_left) omegaOne_Ord)
      (Ord_of_mem_Ord Hx omegaOne_Ord)).mpr (by simpa only [sup_comm] using Hleast)
  have Hxsub : Γ ≤ x ⊆ᴮ v := active_index_subset_value_of_inverse_closure
    Hg Hglaw (active_increasing_of_birthGreedyLaw Hf Hlaw) Hx Hνx
    (Hv.trans inf_le_left) (Hv.trans inf_le_right) Hclosedg
  have Heq : Γ ≤ v =ᴮ x := by
    rw [eq_iff_subset_subset]
    exact le_inf Hvsub Hxsub
  exact mem_congr (pair_congr bv_refl Heq) bv_refl (Hv.trans inf_le_right)

private theorem mem_of_not_mem_relative_complement {κ A x : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ κ) (Hnot : Γ ≤ (x ∈ᴮ difference κ A)ᶜ) : Γ ≤ x ∈ᴮ A := by
  rw [← compl_compl (x ∈ᴮ A), ← imp_bot, ← deduction]
  have Hbad : Γ ⊓ (x ∈ᴮ A)ᶜ ≤ x ∈ᴮ difference κ A := by
    rw [mem_difference]
    exact le_inf (inf_le_left.trans Hx) inf_le_right
  exact bv_absurd _ Hbad (inf_le_left.trans Hnot)

/-- Normality makes the actual birth-guarded range co-large. No
co-largeness, positivity, or fixed points of the range are hypotheses. -/
theorem birth_greedy_range_colarge {J ν seed F f : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hnormal : Γ ≤ diagonalClosure omegaOne J)
    (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (Hseed : Γ ≤ colarge omegaOne J seed)
    (HF : Γ ≤ is_func' omegaOne (bv_powerset omegaOne) F)
    (Hvalues : Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ omegaOne ⊓ pair i A ∈ᴮ F)
      (difference omegaOne A ∈ᴮ J))
    (Hf : Γ ≤ is_func' omegaOne omegaOne f)
    (Hlaw : Γ ≤ birthGreedyLaw ν seed F f) :
    Γ ≤ colarge omegaOne J (image (activatedStages omegaOne ν) omegaOne f) := by
  obtain ⟨g, Hg⟩ := exists_active_inverse ν f (Γ := Γ)
  let D := diagonalCommon omegaOne F
  let C := closurePoints f
  let K := closurePoints g
  let G := difference seed (binary_union (difference omegaOne D)
    (binary_union (difference omegaOne C)
      (binary_union (difference omegaOne K) (past ({ν} : bSet 𝔹)))))
  have HD : Γ ≤ colarge omegaOne J D := diagonalCommon_colarge HJ Hnormal HF Hvalues
  have HC : Γ ≤ colarge omegaOne J C := closurePoints_colarge HJ Habsorb Hclosure Hnormal Hf
  have HK : Γ ≤ colarge omegaOne J K := closurePoints_colarge HJ Habsorb Hclosure Hnormal
    (is_func'_of_is_function (Hg.trans inf_le_left))
  have HG : Γ ≤ colarge omegaOne J G := colarge_difference_of_small HJ Hseed
    (small_union (unionClosed_of_isIdeal HJ) (HD.trans inf_le_right)
      (small_union (unionClosed_of_isIdeal HJ) (HC.trans inf_le_right)
        (small_union (unionClosed_of_isIdeal HJ) (HK.trans inf_le_right)
          (singleton_past_small HJ Habsorb Hclosure Hν))))
  apply colarge_of_subset HJ HG ?_ image_subset
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ G
  have Hx : Δ ≤ x ∈ᴮ seed ⊓ ((x ∈ᴮ difference omegaOne D)ᶜ ⊓
      ((x ∈ᴮ difference omegaOne C)ᶜ ⊓
        ((x ∈ᴮ difference omegaOne K)ᶜ ⊓ (x ∈ᴮ past ({ν} : bSet 𝔹))ᶜ))) := by
    simpa only [G, mem_difference, mem_binary_union, compl_sup] using
      (show Δ ≤ x ∈ᴮ G from inf_le_right)
  have Hxω : Δ ≤ x ∈ᴮ omegaOne :=
    mem_of_mem_subset (inf_le_left.trans (Hseed.trans inf_le_left)) (Hx.trans inf_le_left)
  have Hνx : Δ ≤ ν ∈ᴮ x := value_above_of_not_mem_singleton_past
    (inf_le_left.trans Hν) Hxω
    (Hx.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))))
  have Hfixed := birth_fixedPoint_of_diagonal_closures
    (inf_le_left.trans Hf) (inf_le_left.trans Hlaw)
    (inf_le_left.trans (Hg.trans inf_le_left)) (inf_le_left.trans (Hg.trans inf_le_right))
    Hνx (Hx.trans inf_le_left)
    (mem_of_not_mem_relative_complement Hxω (Hx.trans (inf_le_right.trans inf_le_left)))
    (mem_of_not_mem_relative_complement Hxω
      (Hx.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))))
    (mem_of_not_mem_relative_complement Hxω
      (Hx.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))))
  exact mem_image Hfixed (mem_activatedStages_iff.mpr ⟨Hxω, Hνx⟩) Hxω

/-- Exact identification of the mask with the active image of the
original decoded row. This equality needs no function or run premise. -/
theorem activeMask_eq_row_image {X ν : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ activeMask X ν =ᴮ
      image (activatedStages omegaOne ν) omegaOne (rowHistory omegaOne X ν) := by
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv : Γ ⊓ v ∈ᴮ activeMask X ν ≤ v ∈ᴮ activeMask X ν := inf_le_right
    obtain ⟨ξ, Hξ, Hνξ, Hpair⟩ := activeMask_witness Hv
    have Hvω := (mem_activeMask_iff.mp Hv).1
    exact mem_image (mem_rowHistory_iff.mpr ⟨Hξ, Hvω, Hpair⟩)
      (mem_activatedStages_iff.mpr ⟨Hξ, Hνξ⟩) Hvω
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_image_iff.mp
      (show Γ ⊓ v ∈ᴮ image (activatedStages omegaOne ν) omegaOne
        (rowHistory omegaOne X ν) ≤ v ∈ᴮ image (activatedStages omegaOne ν)
        omegaOne (rowHistory omegaOne X ν) from inf_le_right)
    obtain ⟨ξ, Hξ⟩ := exists_convert Hv.2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    have Hactive := mem_activatedStages_iff.mp (Hξ.trans inf_le_left)
    exact mem_activeMask_of_coordinate Hactive.1 Hactive.2 Hv.1
      (rowHistory_apply (Hξ.trans inf_le_right))

/-- The concrete fusion mask is co-large once its actual row obeys the
displayed birth-guarded least law. The same full coordinate graph is used;
it is not re-enumerated or assumed increasing before birth. -/
theorem activeMask_colarge_of_birthGreedyLaw {J ν seed F X : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hnormal : Γ ≤ diagonalClosure omegaOne J)
    (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (Hseed : Γ ≤ colarge omegaOne J seed)
    (HF : Γ ≤ is_func' omegaOne (bv_powerset omegaOne) F)
    (Hvalues : Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ omegaOne ⊓ pair i A ∈ᴮ F)
      (difference omegaOne A ∈ᴮ J))
    (HX : Γ ≤ is_func' (prod omegaOne omegaOne) omegaOne X)
    (Hlaw : Γ ≤ birthGreedyLaw ν seed F (rowHistory omegaOne X ν)) :
    Γ ≤ colarge omegaOne J (activeMask X ν) := by
  have Hrange := birth_greedy_range_colarge HJ Habsorb Hclosure Hnormal Hν Hseed HF Hvalues
    (is_func'_of_is_function (rowHistory_is_function HX Hν)) Hlaw
  have Heq := activeMask_eq_row_image (X := X) (ν := ν) (Γ := Γ)
  rw [eq_iff_subset_subset] at Heq
  exact colarge_of_subset HJ Hrange (Heq.trans inf_le_right) activeMask_subset

end bSet.ErdosBirthGreedyRange
