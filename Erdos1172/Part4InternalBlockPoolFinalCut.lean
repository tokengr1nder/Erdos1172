/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockPoolOrdinalStages
public import Erdos1172.Part4InternalBlockPoolFinalClosure
public import Erdos1172.Part4InternalCountablyBoundedSup

@[expose] public section

/-!
# The actual final ordinal cut of the selector-pool run

The final point aggregate is the union of the actual ordinal stage
values. Its already proved cardinal bound places that ordinal strictly
inside omega-two. Every internally countable subset is captured at one
stage, and a strictly later stage puts that capturing ordinal inside the
final aggregate. This supplies a strict bound at the original condition,
including for the empty subset.

The countable boundedness of omega-one remains an explicit premise.
All whole points of the final object pool are contained in this cut;
neither a successful block selection nor a completed fusion is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockPoolFinalCut

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBlockSelector ErdosCountableChoicePoolStep
open ErdosBlockPoolRecursion ErdosBlockPoolSmallInvariant ErdosBlockPoolRunIncreasing
open ErdosBlockPoolOrdinalStages ErdosBlockPoolFinalClosure ErdosBoundedImageRecursion
open ErdosPoolAggregation ErdosInitialSegments ErdosOrdinalPointHull ErdosCountablePast
open ErdosOmegaOneIdealBounded ErdosCountablyBoundedSup ErdosBlockPoolUpdate

theorem finalPoints_Ord {color : Bool} {R J E S F Run : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ Ord (finalPoints color R Run) := by
  have Hmembers : Γ ≤ ⨅ P, _root_.imp
      (P ∈ᴮ image omegaOne (bv_powerset omegaTwo) (pointFamily HRun))
      (Ord P ⊓ P ⊆ᴮ omegaTwo) := by
    apply le_iInf
    intro P
    rw [← deduction]
    let Δ := Γ ⊓ P ∈ᴮ image omegaOne (bv_powerset omegaTwo) (pointFamily HRun)
    have Hmem := mem_image_iff.mp
      (show Δ ≤ P ∈ᴮ image omegaOne (bv_powerset omegaTwo) (pointFamily HRun) from
        inf_le_right)
    obtain ⟨i, Hi⟩ := exists_convert Hmem.2
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    obtain ⟨B, HB⟩ := pointFamily_witness HRun (Hi.trans inf_le_right)
    exact le_inf (pool_run_pair_ordinal (inf_le_left.trans HCH)
      (inf_le_left.trans HF) (inf_le_left.trans Hlaw) (inf_le_left.trans HRun)
      (inf_le_left.trans Hrec) HB) (mem_powerset_iff.mp Hmem.1)
  exact bv_rw' (ϕ := Ord) (finalPoints_eq_coordinate_union HRun)
    (h_congr := B_ext_Ord)
    (H_new := union_Ord_of_ordinal_subsets omegaTwo_Ord Hmembers)

theorem finalPoints_mem_omegaTwo {color : Bool} {R J E S F Run : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ finalPoints color R Run ∈ᴮ omegaTwo := by
  have Hord := finalPoints_Ord HCH HF Hlaw HRun Hrec
  have Hsmall : Γ ≤ injects_into (finalPoints color R Run) omegaOne :=
    (pool_final_aggregates_small HCH HF Hlaw HRun Hrec).trans inf_le_right
  have Hpast : Γ ≤ past (finalPoints color R Run) ∈ᴮ omegaTwo :=
    past_mem_omegaTwo HCH aggregateRight_subset Hsmall
  have Hcases := eq_or_mem_of_ordinal_subset Hord
    (Ord_of_mem_Ord Hpast omegaTwo_Ord) subset_past
  apply (le_inf le_rfl Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact mem_congr (bv_symm inf_le_right) bv_refl (inf_le_left.trans Hpast)
  · exact mem_of_mem_Ord inf_le_right (inf_le_left.trans Hpast) omegaTwo_Ord

/-- A later actual stage puts each stage ordinal inside the final union,
rather than merely proving that it is a subset of the final union. -/
theorem pointFamily_value_mem_finalPoints
    {color : Bool} {R J E S F Run i P : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne) (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run)
    (Hpair : Γ ≤ pair i P ∈ᴮ pointFamily HRun) :
    Γ ≤ P ∈ᴮ finalPoints color R Run := by
  have Hi : Γ ≤ i ∈ᴮ omegaOne :=
    mem_domain_of_is_function Hpair (pointFamily_is_function HRun)
  obtain ⟨j, Hj⟩ := exists_above_of_countablyBounded HB Hi
  have Hex : Γ ≤ ⨆ Q, Q ∈ᴮ bv_powerset omegaTwo ⊓ pair j Q ∈ᴮ pointFamily HRun :=
    (le_inf ((is_total_of_is_function (pointFamily_is_function HRun)).trans (iInf_le _ j))
      (Hj.trans inf_le_left)).trans bv_imp_elim
  obtain ⟨Q, HQ⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  obtain ⟨B, HBi⟩ := pointFamily_witness HRun Hpair
  obtain ⟨C, HCj⟩ := pointFamily_witness HRun (HQ.trans inf_le_right)
  have HPQ : Γ ≤ P ∈ᴮ Q :=
    pool_run_points_strict_mono HCH HF Hlaw HRun Hrec (Hj.trans inf_le_right) HBi HCj
  have Hunion : Γ ≤ P ∈ᴮ bv_union
      (image omegaOne (bv_powerset omegaTwo) (pointFamily HRun)) :=
    mem_bv_union_iff.mpr (le_iSup_of_le Q
      (le_inf (mem_image (HQ.trans inf_le_right) (Hj.trans inf_le_left)
        (HQ.trans inf_le_left)) HPQ))
  exact mem_congr bv_refl (bv_symm (finalPoints_eq_coordinate_union HRun)) Hunion

theorem finalPoints_countablyBounded
    {color : Bool} {R J E S F Run : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne) (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ countablyBounded (finalPoints color R Run) := by
  apply le_iInf
  intro T
  rw [← deduction]
  obtain ⟨i, P, HiP⟩ := exists_point_history_stage (inf_le_left.trans HB)
    (inf_le_left.trans HRun) (inf_le_left.trans Hrec)
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
  exact le_iSup_of_le P (le_inf
    (pointFamily_value_mem_finalPoints (inf_le_left.trans HB) (inf_le_left.trans HCH)
      (inf_le_left.trans HF) (inf_le_left.trans Hlaw) (inf_le_left.trans HRun)
      (inf_le_left.trans Hrec) (HiP.trans (inf_le_right.trans inf_le_left)))
    (HiP.trans (inf_le_right.trans inf_le_right)))

/-- Every point of every final whole block is in the final point pool.
This containment alone requires only the actual recursion equations. -/
theorem finalObjects_points_subset
    {color : Bool} {R F Run : bSet 𝔹} {Γ : 𝔹}
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ bv_union (finalObjects color R Run) ⊆ᴮ finalPoints color R Run := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ bv_union (finalObjects color R Run)
  obtain ⟨A, HA⟩ := exists_convert (mem_bv_union_iff.mp
    (show Δ ≤ x ∈ᴮ bv_union (finalObjects color R Run) from inf_le_right))
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  obtain ⟨B, P, Hstate, HB, HP, HAB⟩ := aggregateLeft_witness (HA.trans inf_le_left)
  obtain ⟨i, Hi⟩ := exists_convert (mem_image_iff.mp Hstate).2
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have HxB : Δ ≤ x ∈ᴮ bv_union B :=
    mem_bv_union_iff.mpr (le_iSup_of_le A (le_inf HAB (HA.trans inf_le_right)))
  have HxP : Δ ≤ x ∈ᴮ P :=
    mem_of_mem_subset (pool_run_pair_blockPoints_subset (inf_le_left.trans Hrec)
      (Hi.trans inf_le_right)) HxB
  exact mem_aggregateRight_of_pair Hstate HB HP HxP

end bSet.ErdosBlockPoolFinalCut
