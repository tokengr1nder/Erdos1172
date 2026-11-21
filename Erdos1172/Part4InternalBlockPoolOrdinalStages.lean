/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockPoolSmallInvariant

@[expose] public section

/-!
# Ordinal point pools in the actual selector-pool recursion

The established smallness invariant makes the clipped update an actual
ordinal successor at each stage. Its predecessor marker is a member of
the new point pool. Every earlier point pool is an ordinal contained in
that marker, hence is itself a member of the later pool.

The object component is kept as whole block objects: the union of those
objects is contained in the same stage's point component. No increasing
chain, ordinal-state invariant, or successful selector output is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockPoolOrdinalStages

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBlockSelector ErdosCountableChoicePoolStep
open ErdosPoolAggregation ErdosBlockPoolUpdate ErdosBlockPoolRecursion
open ErdosBlockPoolSmallInvariant ErdosImageRecursionInvariant ErdosBoundedImageRecursion
open ErdosCountablePast ErdosOrdinalPointHull ErdosSmallPoolOperations ErdosInitialSegments

/-- The already proved invariant holds on every actual restricted image,
even without a bound on the restriction name. -/
theorem pool_prefix_allSmall {color : Bool} {R J E S F Run i : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R) (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ allGood smallState (image i (stateSpace color R) Run) := by
  have Hgood := pool_run_allSmall HCH HF Hlaw HRun Hrec
  apply le_iInf
  intro q
  rw [← deduction]
  let Δ := Γ ⊓ q ∈ᴮ image i (stateSpace color R) Run
  obtain ⟨j, Hj⟩ := exists_convert ((mem_image_iff.mp
    (show Δ ≤ q ∈ᴮ image i (stateSpace color R) Run from inf_le_right)).2)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hpair : Δ ≤ pair j q ∈ᴮ Run := Hj.trans inf_le_right
  have Hfull : Δ ≤ q ∈ᴮ image omegaOne (stateSpace color R) Run :=
    mem_image Hpair (mem_domain_of_is_function Hpair (inf_le_left.trans HRun))
      (mem_codomain_of_is_function Hpair (inf_le_left.trans HRun))
  exact allGood_apply (inf_le_left.trans Hgood) Hfull

/-- The concrete input of the ordinal-growth update is small at every
actual stage. This is derived from the recursion invariant. -/
theorem pool_prefix_pointInput_small
    {color : Bool} {R J E S F Run i : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R) (fun _ T => poolUpdate color R F T) Run)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) :
    Γ ≤ injects_into (pointInput
      (priorObjects color R (image i (stateSpace color R) Run))
      (priorPoints color R (image i (stateSpace color R) Run)) F) omegaOne := by
  have Hagg := aggregates_small HCH image_subset (prefix_image_small HRun Hi)
    (pool_prefix_allSmall HCH HF Hlaw HRun Hrec (i := i))
  exact (update_small HCH (Hagg.trans inf_le_left) (Hagg.trans inf_le_right)
    HF Hlaw aggregateLeft_subset aggregateRight_subset).trans (inf_le_right.trans inf_le_left)

/-- Both ordinalness and the actual predecessor marker belong to the
same stage value of the same run. -/
theorem pool_run_pair_ordinal_and_growth
    {color : Bool} {R J E S F Run i B P : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R) (fun _ T => poolUpdate color R F T) Run)
    (Hpair : Γ ≤ pair i (pair B P) ∈ᴮ Run) :
    Γ ≤ Ord P ⊓ past (pointInput
      (priorObjects color R (image i (stateSpace color R) Run))
      (priorPoints color R (image i (stateSpace color R) Run)) F) ∈ᴮ P := by
  have Hinput := pool_prefix_pointInput_small HCH HF Hlaw HRun Hrec
    (mem_domain_of_is_function Hpair HRun)
  have Hnext := update_ordinal_and_growth (color := color) (R := R)
    HCH aggregateLeft_subset aggregateRight_subset Hinput
  have Heq := (pool_recursion_entry Hrec Hpair).trans inf_le_right
  exact le_inf
    (bv_rw' (ϕ := Ord) Heq (h_congr := B_ext_Ord) (H_new := Hnext.trans inf_le_left))
    (bv_rw' (ϕ := fun Q => past (pointInput
      (priorObjects color R (image i (stateSpace color R) Run))
      (priorPoints color R (image i (stateSpace color R) Run)) F) ∈ᴮ Q)
      Heq (h_congr := B_ext_mem_right) (H_new := Hnext.trans inf_le_right))

theorem pool_run_pair_ordinal
    {color : Bool} {R J E S F Run i B P : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R) (fun _ T => poolUpdate color R F T) Run)
    (Hpair : Γ ≤ pair i (pair B P) ∈ᴮ Run) : Γ ≤ Ord P :=
  (pool_run_pair_ordinal_and_growth HCH HF Hlaw HRun Hrec Hpair).trans inf_le_left

/-- Whole objects are retained: their actual point union is contained in
the point pool of this same stage. No cardinal hypotheses are needed. -/
theorem pool_run_pair_blockPoints_subset
    {color : Bool} {R F Run i B P : bSet 𝔹} {Γ : 𝔹}
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R) (fun _ T => poolUpdate color R F T) Run)
    (Hpair : Γ ≤ pair i (pair B P) ∈ᴮ Run) : Γ ≤ bv_union B ⊆ᴮ P := by
  have Hentry := pool_recursion_entry Hrec Hpair
  have Hnext : Γ ≤ bv_union (nextObjects color R
      (priorObjects color R (image i (stateSpace color R) Run))
      (priorPoints color R (image i (stateSpace color R) Run)) F) ⊆ᴮ
    nextPoints (priorObjects color R (image i (stateSpace color R) Run))
      (priorPoints color R (image i (stateSpace color R) Run)) F :=
    nextBlockPoints_subset_nextPoints aggregateLeft_subset aggregateRight_subset
  exact subset_trans'
    (subset_trans' (subset_of_eq (B_congr_bv_union (Hentry.trans inf_le_left))) Hnext)
    (subset_of_eq (bv_symm (Hentry.trans inf_le_right)))

/-- Strict ordinal growth is derived from the concrete marker in the
later update, not postulated as a chain invariant. -/
theorem pool_run_points_strict_mono
    {color : Bool} {R J E S F Run j i B P C Q : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R) (fun _ T => poolUpdate color R F T) Run)
    (Hji : Γ ≤ j ∈ᴮ i)
    (Hjpair : Γ ≤ pair j (pair B P) ∈ᴮ Run)
    (Hipair : Γ ≤ pair i (pair C Q) ∈ᴮ Run) : Γ ≤ P ∈ᴮ Q := by
  let T := image i (stateSpace color R) Run
  let U := pointInput (priorObjects color R T) (priorPoints color R T) F
  have Hpast : Γ ≤ pair B P ∈ᴮ T := mem_image Hjpair Hji (mem_codomain_of_is_function Hjpair HRun)
  have HPprior : Γ ≤ P ⊆ᴮ priorPoints color R T := right_subset_aggregate image_subset Hpast
  have HPmarker : Γ ≤ P ⊆ᴮ past U :=
    subset_trans' (subset_trans' HPprior subset_binary_union_left) subset_past
  have HPord : Γ ≤ Ord P := pool_run_pair_ordinal HCH HF Hlaw HRun Hrec Hjpair
  have Hnew := pool_run_pair_ordinal_and_growth HCH HF Hlaw HRun Hrec Hipair
  have HQord : Γ ≤ Ord Q := Hnew.trans inf_le_left
  have Hmarker : Γ ≤ past U ∈ᴮ Q := Hnew.trans inf_le_right
  have Hcases := eq_or_mem_of_ordinal_subset HPord (Ord_of_mem_Ord Hmarker HQord) HPmarker
  apply (le_inf le_rfl Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact mem_congr (bv_symm inf_le_right) bv_refl (inf_le_left.trans Hmarker)
  · exact mem_of_mem_Ord inf_le_right (inf_le_left.trans Hmarker) (inf_le_left.trans HQord)

end bSet.ErdosBlockPoolOrdinalStages
