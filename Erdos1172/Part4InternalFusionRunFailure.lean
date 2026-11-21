/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRunTerminalInvariant
public import Erdos1172.Part4InternalBlockSelectorFailure

@[expose] public section

/-!
# The exact failed selector input of an actual fusion entry

The stored block and active set are identified with the actual update
through the run equation. Pool preservation and internal countability
prove that the whole-object history and stored active set belong to the
same local selector domain. An empty stored block is therefore an empty
output of the same fixed selector at those exact inputs. The established
terminal invariant supplies the final clause of a failed terminal label.

No validity, countability, terminal adjacency, least failure, or success
invariant is supplied as a premise.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRunFailure

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosCanonicalBlocks ErdosBlockSelector
open ErdosCountableChoicePoolStep ErdosClosedSelectorHull ErdosClosedPoolFuture
open ErdosFusionHistories ErdosFusionEntrySpace ErdosFusionRun ErdosTaggedPrefix
open ErdosFusionRunCountable ErdosFusionRunLocalStep ErdosFusionRunPoolInvariant
open ErdosFusionRunTerminalInvariant ErdosBlockSelectorFailure

/-- This pair belongs to the original fixed selector graph. Both its
input active set and its output are the actual stored entry components. -/
theorem fusion_run_stored_selector_pair
    {color : Bool} {R E F top Run ξ A Z U : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run) :
    Γ ≤ pair (pair
      (earlierHistory color R ξ (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))) U) A
      ∈ᴮ F := by
  let T := taggedPrefix ξ omegaOne entrySpace Run
  have Hentryeq := fusion_run_entry_eq Hlaw Hentry
  have HA : Γ ≤ A =ᴮ nextBlock color R E F top ξ T := eq_of_eq_pair_left' Hentryeq
  have HU : Γ ≤ U =ᴮ nextActive color R E top ξ T :=
    eq_of_eq_pair_right' (eq_of_eq_pair_right' Hentryeq)
  exact mem_congr (bv_symm (pair_congr (pair_congr bv_refl HU) HA)) bv_refl
    (fusion_run_nextBlock_pair HE HElaw HF HRun Hlaw (mem_domain_of_is_function Hentry HRun))

/-- Domain validity is derived from the actual run. In particular,
the stored active set retains points chosen at the current failed stage. -/
theorem fusion_run_stored_input_mem_closedHull
    {color : Bool} {R E F top Run B P ξ A Z U : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run) :
    Γ ≤ pair (earlierHistory color R ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))) U ∈ᴮ choicePoolDomain B P := by
  have Hξ := mem_domain_of_is_function Hentry HRun
  have Hpool := fusion_run_entry_in_pool HE HElaw HF Hhull HRun Hlaw Hentry
  exact mem_choicePoolDomain_iff.mpr
    ⟨⟨fusion_prefix_earlierHistory_subset_pool HE HElaw HF Hhull HRun Hlaw,
      earlierHistory_countable_of_prefix Hξ
        (fusion_prefix_is_function HRun Hlaw (subset_of_mem_Ord Hξ omegaOne_Ord))⟩,
     ⟨Hpool.trans (inf_le_right.trans inf_le_right),
      fusion_run_active_countable HE HElaw HRun Hlaw Hentry⟩⟩

/-- The exact three-part integrand of `allTerminalFailures`, with the
actual strict-prefix whole objects and actual stored active point set. -/
theorem fusion_run_failed_input
    {color : Bool} {R J E S F B P Y top Run ξ A Z U : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (Hseeds : Γ ≤ poolSeedLaw color R J E B Y) (Htop : Γ ≤ top ∈ᴮ Y)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run)
    (Hempty : Γ ≤ A =ᴮ (∅ : bSet 𝔹)) :
    Γ ≤ pair (earlierHistory color R ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))) U ∈ᴮ choicePoolDomain B P ⊓
      (pair (pair (earlierHistory color R ξ
        (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))) U) (∅ : bSet 𝔹) ∈ᴮ F ⊓
        activeTerminalEdges color R U top) :=
  le_inf (fusion_run_stored_input_mem_closedHull HE HElaw HF Hhull HRun Hlaw Hentry)
    (le_inf (mem_congr (pair_congr bv_refl Hempty) bv_refl
      (fusion_run_stored_selector_pair HE HElaw HF HRun Hlaw Hentry))
      (fusion_run_active_terminal HJ Habsorb Hclosure HE HElaw HF HFlaw Hhull Hseeds Htop
        HRun Hlaw Hentry))

end bSet.ErdosFusionRunFailure
