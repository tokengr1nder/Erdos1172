/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRun
public import Erdos1172.Part4InternalFusionRunCountable
public import Erdos1172.Part4InternalClosedSelectorHull
public import Erdos1172.Part4InternalBlockSelector

@[expose] public section

/-!
# Genuine selector inputs and closed-hull preservation at one fusion step

An actual countable prefix and internally countable earlier active values
put both computed histories in the fixed selector's real domain. Hence
the bounded evaluator is the value of that same selector, including its
exact candidate-or-empty alternative. No input-domain premise is assumed.

Guarded earlier block-pool membership and earlier active-point bounds
also place these histories inside a supplied constructed closed hull.
Its literal selector closure then preserves the whole selected object
and all its points. These are local induction implications, not a proof
that every entry of the full run already satisfies the induction laws.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRunLocalStep

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBoundedFunctionValue
open ErdosFusionHistories ErdosFusionActiveHistory ErdosFusionEntrySpace ErdosFusionRun
open ErdosCountableFamilyUnion ErdosCountableSubsetCodes ErdosCountableChoicePoolStep
open ErdosBlockCandidate ErdosBlockSelector ErdosClosedSelectorHull ErdosRelationGraph

theorem earlierHistory_countable_of_prefix
    {color : Bool} {R ξ T : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T) :
    Γ ≤ injects_into (earlierHistory color R ξ (blockHistory T)) bSet.omega :=
  earlierHistory_countable (blockHistory_is_function (subset_of_mem_Ord Hξ omegaOne_Ord) HT)
    (omegaOne_member_injects Hξ)

theorem nextActive_countable_of_prefix
    {color : Bool} {R E top ξ T : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hvalues : Γ ≤ countableValues ξ (activeFamily T)) :
    Γ ≤ injects_into (nextActive color R E top ξ T) bSet.omega :=
  activeHistory_countable
    (is_func'_of_is_function (activeFamily_is_function (subset_of_mem_Ord Hξ omegaOne_Ord) HT))
    Hvalues HE HElaw nextIndices_is_function (subset_of_mem_Ord Hξ omegaOne_Ord)
    (omegaOne_member_injects Hξ)

/-- Domain membership is proved from the actual countable histories,
including when the prefix or its successful block subfamily is empty. -/
theorem selector_input_mem_of_prefix
    {color : Bool} {R E top ξ T : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hvalues : Γ ≤ countableValues ξ (activeFamily T)) :
    Γ ≤ pair (earlierHistory color R ξ (blockHistory T)) (nextActive color R E top ξ T) ∈ᴮ
      choicePoolDomain (blockObjects color R) omegaTwo :=
  mem_choicePoolDomain_iff.mpr
    ⟨⟨earlierHistory_subset, earlierHistory_countable_of_prefix Hξ HT⟩,
      ⟨nextActive_subset, nextActive_countable_of_prefix HE HElaw Hξ HT Hvalues⟩⟩

/-- This is the original fixed selector graph, not a newly selected
function on the local history domain. -/
theorem nextBlock_pair_of_prefix
    {color : Bool} {R E F top ξ T : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hvalues : Γ ≤ countableValues ξ (activeFamily T)) :
    Γ ≤ pair (pair (earlierHistory color R ξ (blockHistory T)) (nextActive color R E top ξ T))
      (nextBlock color R E F top ξ T) ∈ᴮ F :=
  graphValue_pair_mem HF (selector_input_mem_of_prefix HE HElaw Hξ HT Hvalues)

theorem nextBlock_candidate_or_empty_of_prefix
    {color : Bool} {R J E S F top ξ T : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hvalues : Γ ≤ countableValues ξ (activeFamily T)) :
    Γ ≤ blockCandidate color R J E S (earlierHistory color R ξ (blockHistory T))
      (nextActive color R E top ξ T) (nextBlock color R E F top ξ T) ⊔
      nextBlock color R E F top ξ T =ᴮ (∅ : bSet 𝔹) :=
  selected_candidate_or_empty HF HFlaw (nextBlock_pair_of_prefix HE HElaw HF Hξ HT Hvalues)

theorem nextBlock_candidate_of_nonempty_of_prefix
    {color : Bool} {R J E S F top ξ T : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hvalues : Γ ≤ countableValues ξ (activeFamily T))
    (Hnonempty : Γ ≤ (nextBlock color R E F top ξ T =ᴮ (∅ : bSet 𝔹))ᶜ) :
    Γ ≤ blockCandidate color R J E S (earlierHistory color R ξ (blockHistory T))
      (nextActive color R E top ξ T) (nextBlock color R E F top ξ T) :=
  selected_candidate_of_nonempty HF HFlaw
    (nextBlock_pair_of_prefix HE HElaw HF Hξ HT Hvalues) Hnonempty

theorem nextBlock_empty_iff_no_candidate_of_prefix
    {color : Bool} {R J E S F top ξ T : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hvalues : Γ ≤ countableValues ξ (activeFamily T)) :
    (Γ ≤ nextBlock color R E F top ξ T =ᴮ (∅ : bSet 𝔹)) ↔
      Γ ≤ (⨆ A, blockCandidate color R J E S (earlierHistory color R ξ (blockHistory T))
        (nextActive color R E top ξ T) A)ᶜ :=
  selected_empty_iff_no_candidate HF HFlaw
    (nextBlock_pair_of_prefix HE HElaw HF Hξ HT Hvalues)

/-- Only successful earlier values enter the whole-object history. The
Boolean empty-or-pool induction law therefore bounds that entire history. -/
theorem earlierHistory_subset_pool_of_values
    {color : Bool} {R ξ Blocks B : bSet 𝔹} {Γ : 𝔹}
    (Hvalues : Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ ξ ⊓ pair i A ∈ᴮ Blocks)
      (A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B)) :
    Γ ≤ earlierHistory color R ξ Blocks ⊆ᴮ B := by
  rw [subset_unfold']
  apply le_iInf
  intro A
  rw [← deduction]
  let Δ := Γ ⊓ A ∈ᴮ earlierHistory color R ξ Blocks
  have HA := (mem_comprehend_and B_ext_mem_left).mp
    (show Δ ≤ A ∈ᴮ earlierHistory color R ξ Blocks from inf_le_right)
  obtain ⟨i, Hi⟩ := exists_convert (mem_image_iff.mp HA.1).2
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hcases : Δ ≤ A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B :=
    (le_inf (inf_le_left.trans (Hvalues.trans ((iInf_le _ i).trans (iInf_le _ A)))) Hi).trans
      bv_imp_elim
  apply (le_inf (le_refl Δ) Hcases).trans
  rw [inf_sup_left]
  exact sup_le
    ((bv_absurd _ inf_le_right (inf_le_left.trans (blockObject_nonempty HA.2))).trans bot_le)
    inf_le_right

theorem nextActive_subset_closedHull_of_prefix
    {color : Bool} {R E F top ξ T B P : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (Hobjects : Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ ξ ⊓ pair i A ∈ᴮ blockHistory T)
      (A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B))
    (Hprevious : Γ ≤ ⨅ i, ⨅ U, _root_.imp (i ∈ᴮ ξ ⊓ pair i U ∈ᴮ activeFamily T)
      (U ⊆ᴮ P)) : Γ ≤ nextActive color R E top ξ T ⊆ᴮ P :=
  activeHistory_subset_of_pool HE HElaw
    (blockHistory_is_function (subset_of_mem_Ord Hξ omegaOne_Ord) HT)
    nextIndices_is_function (subset_of_mem_Ord Hξ omegaOne_Ord)
    (earlierHistory_subset_pool_of_values Hobjects)
    (Hhull.trans (inf_le_right.trans (inf_le_right.trans
      (inf_le_right.trans (inf_le_right.trans inf_le_left)))))
    (previousActive_subset_of_values Hprevious)

/-- Both actual histories are internally countable subsets of the local
whole-object and point pools; no restricted-selector function is invented. -/
theorem selector_input_mem_closedHull_of_prefix
    {color : Bool} {R E F top ξ T B P : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hvalues : Γ ≤ countableValues ξ (activeFamily T))
    (Hhull : Γ ≤ closedHullData color R F B P)
    (Hobjects : Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ ξ ⊓ pair i A ∈ᴮ blockHistory T)
      (A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B))
    (Hprevious : Γ ≤ ⨅ i, ⨅ U, _root_.imp (i ∈ᴮ ξ ⊓ pair i U ∈ᴮ activeFamily T)
      (U ⊆ᴮ P)) :
    Γ ≤ pair (earlierHistory color R ξ (blockHistory T)) (nextActive color R E top ξ T) ∈ᴮ
      choicePoolDomain B P :=
  mem_choicePoolDomain_iff.mpr
    ⟨⟨earlierHistory_subset_pool_of_values Hobjects, earlierHistory_countable_of_prefix Hξ HT⟩,
      ⟨nextActive_subset_closedHull_of_prefix HE HElaw Hξ HT Hhull Hobjects Hprevious,
        nextActive_countable_of_prefix HE HElaw Hξ HT Hvalues⟩⟩

/-- The computed next object is empty or belongs to the same whole-block
pool, and its entire point set lies in the same ordinal cut. All premises
about earlier stages are displayed local induction hypotheses. -/
theorem nextBlock_in_closedHull_of_prefix
    {color : Bool} {R E F top ξ T B P : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (HT : Γ ≤ is_function ξ entrySpace T)
    (Hvalues : Γ ≤ countableValues ξ (activeFamily T))
    (Hhull : Γ ≤ closedHullData color R F B P)
    (Hobjects : Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ ξ ⊓ pair i A ∈ᴮ blockHistory T)
      (A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B))
    (Hprevious : Γ ≤ ⨅ i, ⨅ U, _root_.imp (i ∈ᴮ ξ ⊓ pair i U ∈ᴮ activeFamily T)
      (U ⊆ᴮ P)) :
    Γ ≤ nextBlock color R E F top ξ T ⊆ᴮ P ⊓
      (nextBlock color R E F top ξ T =ᴮ (∅ : bSet 𝔹) ⊔
        nextBlock color R E F top ξ T ∈ᴮ B) := by
  have Hinput := mem_choicePoolDomain_iff.mp
    (selector_input_mem_closedHull_of_prefix (top := top)
      HE HElaw Hξ HT Hvalues Hhull Hobjects Hprevious)
  exact selectorClosed_apply
    (Hhull.trans (inf_le_right.trans (inf_le_right.trans
      (inf_le_right.trans (inf_le_right.trans inf_le_right)))))
    (mem_countableSubsets_iff.mpr Hinput.1) (mem_countableSubsets_iff.mpr Hinput.2)
    (nextBlock_pair_of_prefix HE HElaw HF Hξ HT Hvalues)

/-- The established actual-run countability invariant discharges the
local countable-values premise at every internal stage. -/
theorem fusion_run_nextBlock_pair
    {color : Bool} {R E F top Run ξ : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) :
    Γ ≤ pair (pair
      (earlierHistory color R ξ
        (blockHistory (ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run)))
      (nextActive color R E top ξ (ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run)))
      (nextBlock color R E F top ξ (ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run))
      ∈ᴮ F :=
  nextBlock_pair_of_prefix HE HElaw HF Hξ
    (fusion_prefix_is_function HRun Hlaw (subset_of_mem_Ord Hξ omegaOne_Ord))
    (ErdosFusionRunCountable.fusion_prefix_countableValues HE HElaw HRun Hlaw)

theorem fusion_run_nextBlock_candidate_or_empty
    {color : Bool} {R J E S F top Run ξ : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) :
    Γ ≤ blockCandidate color R J E S
      (earlierHistory color R ξ
        (blockHistory (ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run)))
      (nextActive color R E top ξ (ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run))
      (nextBlock color R E F top ξ (ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run)) ⊔
      nextBlock color R E F top ξ (ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run)
        =ᴮ (∅ : bSet 𝔹) :=
  selected_candidate_or_empty HF HFlaw (fusion_run_nextBlock_pair HE HElaw HF HRun Hlaw Hξ)

theorem fusion_run_nextBlock_empty_iff_no_candidate
    {color : Bool} {R J E S F top Run ξ : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) :
    (Γ ≤ nextBlock color R E F top ξ (ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run)
      =ᴮ (∅ : bSet 𝔹)) ↔
      Γ ≤ (⨆ A, blockCandidate color R J E S
        (earlierHistory color R ξ
          (blockHistory (ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run)))
        (nextActive color R E top ξ (ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run))
        A)ᶜ :=
  selected_empty_iff_no_candidate HF HFlaw
    (fusion_run_nextBlock_pair HE HElaw HF HRun Hlaw Hξ)

/-- Every actually stored output satisfies the full candidate law or is
the empty failure value. Both its stored active set and its whole block
are transported from the genuine next-entry equation. -/
theorem fusion_run_stored_block_candidate_or_empty
    {color : Bool} {R J E S F top Run ξ A Z U : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hpair : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run) :
    Γ ≤ blockCandidate color R J E S
      (earlierHistory color R ξ
        (blockHistory (ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run))) U A ⊔
      A =ᴮ (∅ : bSet 𝔹) := by
  let T := ErdosTaggedPrefix.taggedPrefix ξ omegaOne entrySpace Run
  let Earlier := earlierHistory color R ξ (blockHistory T)
  have Hentry := fusion_run_entry_eq Hlaw Hpair
  have Hcomputed := fusion_run_nextBlock_candidate_or_empty HE HElaw HF HFlaw HRun Hlaw
    (mem_domain_of_is_function Hpair HRun)
  have HA : Γ ≤ blockCandidate color R J E S Earlier (nextActive color R E top ξ T) A ⊔
      A =ᴮ (∅ : bSet 𝔹) :=
    bv_rw' (ϕ := fun B => blockCandidate color R J E S Earlier
      (nextActive color R E top ξ T) B ⊔ B =ᴮ (∅ : bSet 𝔹))
      (eq_of_eq_pair_left' Hentry)
      (h_congr := B_ext_sup
        (h₁ := blockCandidate_ext_object color R J E S Earlier (nextActive color R E top ξ T))
        (h₂ := B_ext_bv_eq_left)) (H_new := Hcomputed)
  exact bv_rw' (ϕ := fun V => blockCandidate color R J E S Earlier V A ⊔
    A =ᴮ (∅ : bSet 𝔹))
    (eq_of_eq_pair_right' (eq_of_eq_pair_right' Hentry))
    (h_congr := B_ext_sup (h₁ := blockCandidate_ext_active color R J E S Earlier A)
      (h₂ := B_ext_const)) (H_new := HA)

end bSet.ErdosFusionRunLocalStep
