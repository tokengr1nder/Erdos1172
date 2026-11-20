/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRunLocalStep

@[expose] public section

/-!
# The actual fusion run stays inside the same closed hull

Internal ordinal invariant induction establishes that every whole block
output is empty or in the fixed object pool, and that every block point
and every stored active point lies in the fixed cut. The earlier active
countability theorem discharges selector-domain cardinality; no pool
invariant, row legality, ideal law, or successful run is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRunPoolInvariant

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosClosedSelectorHull
open ErdosFusionEntrySpace ErdosFusionRun ErdosFusionRunCountable ErdosFusionRunLocalStep
open ErdosFusionHistories ErdosBoundedFunctionValue ErdosCountableChoicePoolStep
open ErdosImageRecursionInvariant ErdosBoundedImageRecursion ErdosTaggedPrefix

def poolState (B P q : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ A, ⨅ Z, ⨅ U, _root_.imp (q =ᴮ pair i (entry A Z U))
    (A ⊆ᴮ P ⊓ ((A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B) ⊓ U ⊆ᴮ P))

theorem poolState_ext (B P : bSet 𝔹) : B_ext (poolState B P) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_bv_eq_left) (h₂ := B_ext_const)))))

theorem poolState_apply {B P i A Z U : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ poolState B P (pair i (entry A Z U))) :
    Γ ≤ A ⊆ᴮ P ⊓ ((A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B) ⊓ U ⊆ᴮ P) :=
  (le_inf (H.trans ((iInf_le _ i).trans ((iInf_le _ A).trans
    ((iInf_le _ Z).trans (iInf_le _ U))))) bv_refl).trans bv_imp_elim

theorem poolState_of_entry {B P i A Z U : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ P) (Hcase : Γ ≤ A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B)
    (HU : Γ ≤ U ⊆ᴮ P) : Γ ≤ poolState B P (pair i (entry A Z U)) := by
  apply le_iInf
  intro j
  apply le_iInf
  intro C
  apply le_iInf
  intro W
  apply le_iInf
  intro V
  rw [← deduction]
  let Δ := Γ ⊓ pair i (entry A Z U) =ᴮ pair j (entry C W V)
  have HAC : Δ ≤ A =ᴮ C := eq_of_eq_pair_left' (eq_of_eq_pair_right' inf_le_right)
  have HUV : Δ ≤ U =ᴮ V :=
    eq_of_eq_pair_right' (eq_of_eq_pair_right' (eq_of_eq_pair_right' inf_le_right))
  exact le_inf (bv_rw'' HAC (inf_le_left.trans HA) B_ext_subset_left)
    (le_inf (bv_rw'' (ϕ := fun X => X =ᴮ (∅ : bSet 𝔹) ⊔ X ∈ᴮ B)
      HAC (inf_le_left.trans Hcase) (B_ext_sup (h₁ := B_ext_bv_eq_left) (h₂ := B_ext_mem_left)))
      (bv_rw'' HUV (inf_le_left.trans HU) B_ext_subset_left))

theorem blockHistory_poolValues_of_allGood {B P ξ T : bSet 𝔹} {Γ : 𝔹}
    (Hgood : Γ ≤ allGood (poolState B P) T) :
    Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ ξ ⊓ pair i A ∈ᴮ blockHistory T)
      (A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro A
  rw [← deduction]
  obtain ⟨Z, U, Hentry⟩ := blockHistory_witness
    (show Γ ⊓ (i ∈ᴮ ξ ⊓ pair i A ∈ᴮ blockHistory T) ≤ pair i A ∈ᴮ blockHistory T from
      inf_le_right.trans inf_le_right)
  exact (poolState_apply (allGood_apply (inf_le_left.trans Hgood) Hentry)).trans
    (inf_le_right.trans inf_le_left)

theorem activeFamily_poolValues_of_allGood {B P ξ T : bSet 𝔹} {Γ : 𝔹}
    (Hgood : Γ ≤ allGood (poolState B P) T) :
    Γ ≤ ⨅ i, ⨅ U, _root_.imp (i ∈ᴮ ξ ⊓ pair i U ∈ᴮ activeFamily T) (U ⊆ᴮ P) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro U
  rw [← deduction]
  obtain ⟨A, Z, Hentry⟩ := activeFamily_witness
    (show Γ ⊓ (i ∈ᴮ ξ ⊓ pair i U ∈ᴮ activeFamily T) ≤ pair i U ∈ᴮ activeFamily T from
      inf_le_right.trans inf_le_right)
  exact (poolState_apply (allGood_apply (inf_le_left.trans Hgood) Hentry)).trans
    (inf_le_right.trans inf_le_right)

theorem fusion_pool_invariant_step
    {color : Bool} {R E F top Run B P : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ imageRecInvariantStep omegaOne runSpace
      (fun i T => pair i (nextEntry color R E F top i T)) Run (poolState B P) := by
  apply le_iInf
  intro i
  rw [← deduction]
  let Δ := Γ ⊓ (i ∈ᴮ omegaOne ⊓ allGood (poolState B P) (image i runSpace Run))
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hi : Δ ≤ i ∈ᴮ omegaOne := inf_le_right.trans inf_le_left
  let T := taggedPrefix i omegaOne entrySpace Run
  have HT : Δ ≤ is_function i entrySpace T :=
    fusion_prefix_is_function (HΔ.trans HRun) (HΔ.trans Hlaw) (subset_of_mem_Ord Hi omegaOne_Ord)
  have Hgood : Δ ≤ allGood (poolState B P) T := inf_le_right.trans inf_le_right
  have Hobjects := blockHistory_poolValues_of_allGood (ξ := i) Hgood
  have Hprevious := activeFamily_poolValues_of_allGood (ξ := i) Hgood
  have HA := nextBlock_in_closedHull_of_prefix (top := top)
    (HΔ.trans HE) (HΔ.trans HElaw) (HΔ.trans HF) Hi HT
    (fusion_prefix_countableValues (HΔ.trans HE) (HΔ.trans HElaw)
      (HΔ.trans HRun) (HΔ.trans Hlaw)) (HΔ.trans Hhull) Hobjects Hprevious
  have HU := nextActive_subset_closedHull_of_prefix (top := top)
    (HΔ.trans HE) (HΔ.trans HElaw) Hi HT (HΔ.trans Hhull) Hobjects Hprevious
  exact poolState_of_entry (HA.trans inf_le_left) (HA.trans inf_le_right) HU

/-- The entire actual run satisfies the fixed-pool invariant. This is
the conclusion of internal ordinal induction, not an input invariant. -/
theorem fusion_run_allPool
    {color : Bool} {R E F top Run B P : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ allGood (poolState B P) (image omegaOne runSpace Run) :=
  image_allGood_of_imageRecLaw omegaOne_Ord HRun Hlaw (poolState_ext B P)
    (fusion_pool_invariant_step HE HElaw HF Hhull HRun Hlaw)

theorem fusion_run_entry_in_pool
    {color : Bool} {R E F top Run B P i A Z U : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hpair : Γ ≤ pair i (pair i (entry A Z U)) ∈ᴮ Run) :
    Γ ≤ A ⊆ᴮ P ⊓ ((A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B) ⊓ U ⊆ᴮ P) :=
  poolState_apply (good_of_imageRecLaw_pair omegaOne_Ord HRun Hlaw (poolState_ext B P)
    (fusion_pool_invariant_step HE HElaw HF Hhull HRun Hlaw) Hpair)

theorem fusion_prefix_allPool
    {color : Bool} {R E F top Run B P ξ : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ allGood (poolState B P) (taggedPrefix ξ omegaOne entrySpace Run) := by
  apply le_iInf
  intro q
  rw [← deduction]
  let Δ := Γ ⊓ q ∈ᴮ taggedPrefix ξ omegaOne entrySpace Run
  obtain ⟨i, Hi⟩ := exists_convert (mem_image_iff.mp
    (show Δ ≤ q ∈ᴮ taggedPrefix ξ omegaOne entrySpace Run from inf_le_right)).2
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact allGood_apply (inf_le_left.trans (fusion_run_allPool HE HElaw HF Hhull HRun Hlaw))
    (mem_image (Hi.trans inf_le_right)
      (mem_domain_of_is_function (Hi.trans inf_le_right) (inf_le_left.trans HRun))
      (mem_codomain_of_is_function (Hi.trans inf_le_right) (inf_le_left.trans HRun)))

theorem fusion_prefix_poolValues
    {color : Bool} {R E F top Run B P ξ : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ ⨅ i, ⨅ A, _root_.imp
      (i ∈ᴮ ξ ⊓ pair i A ∈ᴮ blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
      (A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B) :=
  blockHistory_poolValues_of_allGood (fusion_prefix_allPool HE HElaw HF Hhull HRun Hlaw)

theorem fusion_prefix_active_poolValues
    {color : Bool} {R E F top Run B P ξ : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ ⨅ i, ⨅ U, _root_.imp
      (i ∈ᴮ ξ ⊓ pair i U ∈ᴮ activeFamily (taggedPrefix ξ omegaOne entrySpace Run)) (U ⊆ᴮ P) :=
  activeFamily_poolValues_of_allGood (fusion_prefix_allPool HE HElaw HF Hhull HRun Hlaw)

theorem fusion_prefix_earlierHistory_subset_pool
    {color : Bool} {R E F top Run B P ξ : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ earlierHistory color R ξ (blockHistory (taggedPrefix ξ omegaOne entrySpace Run)) ⊆ᴮ B :=
  earlierHistory_subset_pool_of_values (fusion_prefix_poolValues HE HElaw HF Hhull HRun Hlaw)

theorem fusion_prefix_successful_block_mem_pool
    {color : Bool} {R E F top Run B P ξ ν : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne)
    (Hactive : Γ ≤ ν ∈ᴮ successfulRows color R ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))) :
    Γ ≤ blockValue (blockHistory (taggedPrefix ξ omegaOne entrySpace Run)) ν ∈ᴮ B := by
  have Hparts := mem_successfulRows_iff.mp Hactive
  have HBlocks := blockHistory_is_function (subset_of_mem_Ord Hξ omegaOne_Ord)
    (fusion_prefix_is_function HRun Hlaw (subset_of_mem_Ord Hξ omegaOne_Ord))
  exact mem_of_mem_subset (fusion_prefix_earlierHistory_subset_pool HE HElaw HF Hhull HRun Hlaw)
    (earlierHistory_mem_of_pair HBlocks (graphValue_pair_mem HBlocks Hparts.1) Hparts.2)

end bSet.ErdosFusionRunPoolInvariant
