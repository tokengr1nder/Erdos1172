/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockCandidateExistence
public import Erdos1172.Part4InternalBlockSelector

@[expose] public section

/-!
# A selector for tails extending whole omega-one-small block families

The input is an arbitrary subset of the fixed block-object space, not a
countable selector input. On genuinely omega-one-small inputs, candidate
existence is proved with the original large future and empty active set.
The single bounded fallback selector is therefore successful there.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableTailSelector

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis ErdosCanonicalBlocks
open ErdosBlockCandidate ErdosBlockCandidateExistence ErdosBoundedFallbackChoice

def tailSelectorLaw (color : Bool) (R J E S G : bSet 𝔹) : 𝔹 :=
  fallbackFamilyLaw (bv_powerset (blockObjects color R)) (bv_powerset omegaTwo)
    (fun Earlier A => blockCandidate color R J E S Earlier ∅ A) ∅ G

/-- A property proved for the constructed selector below, not an
additional existence premise of the final tail construction. -/
def smallTailCandidates (color : Bool) (R J E S G : bSet 𝔹) : 𝔹 :=
  ⨅ Earlier, ⨅ A, _root_.imp
    (injects_into Earlier omegaOne ⊓ pair Earlier A ∈ᴮ G)
    (blockCandidate color R J E S Earlier ∅ A)

theorem exists_tail_selector (color : Bool) (R J E S : bSet 𝔹) (Γ : 𝔹) :
    ∃ G : bSet 𝔹, Γ ≤
      is_function (bv_powerset (blockObjects color R)) (bv_powerset omegaTwo) G ⊓
      tailSelectorLaw color R J E S G := by
  exact exists_fallback_selector
    (fun A => blockCandidate_ext_earlier color R J E S ∅ A)
    (fun Earlier => blockCandidate_ext_object color R J E S Earlier ∅)
    (mem_powerset_iff.mpr empty_subset)

theorem activeCompatible_empty {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ activeCompatible color R ∅ S := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  exact (bot_of_mem_empty (inf_le_right.trans inf_le_left)).trans bot_le

theorem smallTailCandidates_apply {color : Bool}
    {R J E S G Earlier A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ smallTailCandidates color R J E S G)
    (Hsmall : Γ ≤ injects_into Earlier omegaOne)
    (Hpair : Γ ≤ pair Earlier A ∈ᴮ G) :
    Γ ≤ blockCandidate color R J E S Earlier ∅ A :=
  (le_inf (H.trans ((iInf_le _ Earlier).trans (iInf_le _ A)))
    (le_inf Hsmall Hpair)).trans bv_imp_elim

/-- The actual selected value is a candidate on every small input.
Support of the same selector supplies the whole-object containment. -/
theorem selected_tail_candidate_of_small
    {color : Bool} {R J I D E S G Earlier A : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Hproper : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D) (HI : Γ ≤ injects_into I omegaOne)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (Hlarge : Γ ≤ injects_into omegaTwo S)
    (HG : Γ ≤ is_function (bv_powerset (blockObjects color R)) (bv_powerset omegaTwo) G)
    (Hlaw : Γ ≤ tailSelectorLaw color R J E S G)
    (Hsmall : Γ ≤ injects_into Earlier omegaOne)
    (Hpair : Γ ≤ pair Earlier A ∈ᴮ G) :
    Γ ≤ blockCandidate color R J E S Earlier ∅ A := by
  have HEarlier := mem_powerset_iff.mp (mem_domain_of_is_function Hpair HG)
  obtain ⟨A', HA'⟩ := exists_candidate_of_large_active_future HCH Hproper Habsorb
    Hclosure Hdiag HD HDpos Hdense HI HE HElaw HEarlier Hsmall Hno HnoOpp
    HS Hlarge subset_self activeCompatible_empty
  exact selected_candidate
    (P := fun Earlier A => blockCandidate color R J E S Earlier ∅ A)
    HG Hlaw Hpair (le_iSup_of_le A'
    (le_inf (ErdosBlockSelector.blockCandidate_mem_powerset HA') HA'))

theorem tail_selector_small_candidates
    {color : Bool} {R J I D E S G : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Hproper : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D) (HI : Γ ≤ injects_into I omegaOne)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (Hlarge : Γ ≤ injects_into omegaTwo S)
    (HG : Γ ≤ is_function (bv_powerset (blockObjects color R)) (bv_powerset omegaTwo) G)
    (Hlaw : Γ ≤ tailSelectorLaw color R J E S G) :
    Γ ≤ smallTailCandidates color R J E S G := by
  apply le_iInf
  intro Earlier
  apply le_iInf
  intro A
  rw [← deduction]
  exact selected_tail_candidate_of_small (inf_le_left.trans HCH)
    (inf_le_left.trans Hproper) (inf_le_left.trans Habsorb) (inf_le_left.trans Hclosure)
    (inf_le_left.trans Hdiag) (inf_le_left.trans HD) (inf_le_left.trans HDpos)
    (inf_le_left.trans Hdense) (inf_le_left.trans HI) (inf_le_left.trans HE)
    (inf_le_left.trans HElaw) (inf_le_left.trans Hno) (inf_le_left.trans HnoOpp)
    (inf_le_left.trans HS) (inf_le_left.trans Hlarge) (inf_le_left.trans HG)
    (inf_le_left.trans Hlaw) (inf_le_right.trans inf_le_left)
    (inf_le_right.trans inf_le_right)

end bSet.ErdosCountableTailSelector
