/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountablyBoundedSup

@[expose] public section

/-!
# Capturing an internal countable subset at one stage of a chain

An actual increasing omega-one-indexed family of sets captures every
internally countable subset of its union at one actual stage. The proof
constructs a membership-stage selector, bounds its countable image using
the explicit countablyBounded premise, and uses the value at that bound.
The set of all possible witnessing stages is not claimed countable.
Empty subsets and mixed names are included at the original condition.
No selector-closed hull, rank, CH, or external transfinite sequence is
assumed or constructed here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableChainCapture

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosOmegaOneIdealBounded ErdosCountablyBoundedSup
open ErdosCountableImage ErdosSmallFamilyUnion ErdosSmallFiberBound

def increasingFamily (F : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ j, ⨅ A, ⨅ B, _root_.imp
    ((i ∈ᴮ omegaOne ⊓ j ∈ᴮ omegaOne) ⊓
      (i ∈ᴮ j ⊓ (pair i A ∈ᴮ F ⊓ pair j B ∈ᴮ F))) (A ⊆ᴮ B)

theorem increasingFamily_apply {F i j A B : bSet 𝔹} {Γ : 𝔹}
    (Hinc : Γ ≤ increasingFamily F)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hj : Γ ≤ j ∈ᴮ omegaOne)
    (Hij : Γ ≤ i ∈ᴮ j) (HiA : Γ ≤ pair i A ∈ᴮ F) (HjB : Γ ≤ pair j B ∈ᴮ F) :
    Γ ≤ A ⊆ᴮ B :=
  (le_inf (Hinc.trans ((iInf_le _ i).trans
    ((iInf_le _ j).trans ((iInf_le _ A).trans (iInf_le _ B)))))
    (le_inf (le_inf Hi Hj) (le_inf Hij (le_inf HiA HjB)))).trans bv_imp_elim

def stageContains (F t i : bSet 𝔹) : 𝔹 :=
  ⨆ A, pair i A ∈ᴮ F ⊓ t ∈ᴮ A

theorem stageContains_ext_member (F i : bSet 𝔹) :
    B_ext (fun t => stageContains F t i) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_left)

theorem stageContains_ext_stage (F t : bSet 𝔹) : B_ext (stageContains F t) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const)

theorem stageContains_witness {F t i : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ stageContains F t i) :
    ∃ A : bSet 𝔹, Γ ≤ pair i A ∈ᴮ F ⊓ t ∈ᴮ A :=
  exists_convert H (B_ext_inf B_ext_pair_mem_right B_ext_mem_right)

/-- Select one actual witnessing stage per member. The union is the
bounded image union, so this needs no functionality premise on F. -/
theorem exists_membership_stage_selector {κ F T : bSet 𝔹} {Γ : 𝔹}
    (HT : Γ ≤ T ⊆ᴮ bv_union (image omegaOne (bv_powerset κ) F)) :
    ∃ h : bSet 𝔹, Γ ≤ is_function T omegaOne h ⊓
      (⨅ t, ⨅ i, _root_.imp (t ∈ᴮ T ⊓ pair t i ∈ᴮ h) (stageContains F t i)) := by
  have Hpoint : Γ ≤ ⨅ t, _root_.imp (t ∈ᴮ T) (⨆ i, i ∈ᴮ omegaOne ⊓ stageContains F t i) := by
    apply le_iInf
    intro t
    rw [← deduction]
    have Ht : Γ ⊓ t ∈ᴮ T ≤ t ∈ᴮ bv_union (image omegaOne (bv_powerset κ) F) :=
      mem_of_mem_subset (inf_le_left.trans HT) inf_le_right
    obtain ⟨i, A, Hdata⟩ := exists_indexed_union_witness Ht
    exact le_iSup_of_le i (le_inf (Hdata.trans (inf_le_left.trans inf_le_left))
      (le_iSup_of_le A (le_inf (Hdata.trans (inf_le_left.trans inf_le_right))
        (Hdata.trans inf_le_right))))
  exact exists_selector_of_pointwise (stageContains_ext_member F) (stageContains_ext_stage F) Hpoint

/-- A countable subset of the union is contained in one actual value of
the family. Countable boundedness also handles the empty selector image,
and totality provides the value at the resulting stage. -/
theorem exists_family_value_containing_countable
    {κ F T : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (HF : Γ ≤ is_function omegaOne (bv_powerset κ) F)
    (Hinc : Γ ≤ increasingFamily F)
    (HT : Γ ≤ T ⊆ᴮ bv_union (image omegaOne (bv_powerset κ) F))
    (Hcount : Γ ≤ injects_into T bSet.omega) :
    ∃ j A : bSet 𝔹, Γ ≤ j ∈ᴮ omegaOne ⊓ (pair j A ∈ᴮ F ⊓ T ⊆ᴮ A) := by
  obtain ⟨h, Hh⟩ := exists_membership_stage_selector HT
  have Hhfunc : Γ ≤ is_function T omegaOne h := Hh.trans inf_le_left
  have HimageCount : Γ ≤ injects_into (image T omegaOne h) bSet.omega :=
    image_countable (is_func'_of_is_function Hhfunc) Hcount
  obtain ⟨j, Hj⟩ := exists_bound_of_countablyBounded HB image_subset HimageCount
  have HexA : Γ ≤ ⨆ A, A ∈ᴮ bv_powerset κ ⊓ pair j A ∈ᴮ F :=
    (le_inf ((is_total_of_is_function HF).trans (iInf_le _ j))
      (Hj.trans inf_le_left)).trans bv_imp_elim
  obtain ⟨A, HA⟩ := exists_convert HexA (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  refine ⟨j, A, le_inf (Hj.trans inf_le_left) (le_inf (HA.trans inf_le_right) ?_)⟩
  rw [subset_unfold']
  apply le_iInf
  intro t
  rw [← deduction]
  let Δ := Γ ⊓ t ∈ᴮ T
  have Hexi : Δ ≤ ⨆ i, i ∈ᴮ omegaOne ⊓ pair t i ∈ᴮ h :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function Hhfunc).trans (iInf_le _ t)))
      (show Δ ≤ t ∈ᴮ T from inf_le_right)).trans bv_imp_elim
  obtain ⟨i, Hi⟩ := exists_convert Hexi (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hstage : Δ ≤ stageContains F t i :=
    (le_inf (inf_le_left.trans ((Hh.trans inf_le_right).trans
      ((iInf_le _ t).trans (iInf_le _ i))))
      (le_inf (show Δ ≤ t ∈ᴮ T from inf_le_right) (Hi.trans inf_le_right))).trans bv_imp_elim
  obtain ⟨B, HBvalue⟩ := stageContains_witness Hstage
  have Him : Δ ≤ i ∈ᴮ image T omegaOne h :=
    mem_image (Hi.trans inf_le_right) (show Δ ≤ t ∈ᴮ T from inf_le_right)
      (Hi.trans inf_le_left)
  have Hij : Δ ≤ i ∈ᴮ j := mem_of_mem_subset (inf_le_left.trans (Hj.trans inf_le_right)) Him
  have HBA : Δ ≤ B ⊆ᴮ A := increasingFamily_apply (inf_le_left.trans Hinc)
    (Hi.trans inf_le_left) (inf_le_left.trans (Hj.trans inf_le_left)) Hij
    (HBvalue.trans inf_le_left) (inf_le_left.trans (HA.trans inf_le_right))
  exact mem_of_mem_subset HBA (HBvalue.trans inf_le_right)

end bSet.ErdosCountableChainCapture
