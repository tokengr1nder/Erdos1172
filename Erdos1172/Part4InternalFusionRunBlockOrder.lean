/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionGlobalRowLaw

@[expose] public section

/-!
# The actual successful whole blocks are strictly separated

Every earlier whole block belongs to the exact strict-prefix input used
to select a later block. Its candidate law therefore puts every old point
strictly below every later point. This is derived from the actual run and
its proved success, not supplied as a final masked-family ordering law.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRunBlockOrder

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBlockSelector ErdosCountableChoicePoolStep
open ErdosFusionGlobalRowLaw ErdosFusionRun ErdosFusionEntrySpace ErdosFusionHistories
open ErdosFusionRunSuccess ErdosFusionPrefixCoherence ErdosFusionRunLocalStep
open ErdosBlockCandidate ErdosTaggedPrefix

/-- The exact full block graph, with no re-enumeration or shrinking of
either of its whole values. -/
theorem fusion_full_blocks_before
    {color : Bool} {R J E S F top Run ν μ b c x y : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hsuccess : Γ ≤ successfulRun Run)
    (Hνμ : Γ ≤ ν ∈ᴮ μ)
    (Hνb : Γ ≤ pair ν b ∈ᴮ fullBlocks Run)
    (Hμc : Γ ≤ pair μ c ∈ᴮ fullBlocks Run)
    (Hx : Γ ≤ x ∈ᴮ b) (Hy : Γ ≤ y ∈ᴮ c) : Γ ≤ x ∈ᴮ y := by
  have Hμ : Γ ≤ μ ∈ᴮ omegaOne := mem_domain_of_is_function Hμc (fullBlocks_is_function HRun Hlaw)
  have Hμsub := subset_of_mem_Ord Hμ omegaOne_Ord
  have Hprefix : Γ ≤ pair ν b ∈ᴮ
      blockHistory (taggedPrefix μ omegaOne entrySpace Run) :=
    (blockHistory_pair_coherent HRun Hlaw Hμsub subset_self Hνμ).mp Hνb
  have Hearlier : Γ ≤ b ∈ᴮ earlierHistory color R μ
      (blockHistory (taggedPrefix μ omegaOne entrySpace Run)) :=
    earlierHistory_mem_of_pair
      (blockHistory_is_function Hμsub (fusion_prefix_is_function HRun Hlaw Hμsub))
      Hprefix (fullBlocks_blockObject HE HElaw HF HFlaw HRun Hlaw Hsuccess Hνb)
  obtain ⟨Z, U, Hentry⟩ := blockHistory_witness Hμc
  have Hstored := ((mem_taggedPrefix_pair_iff HRun (fusion_run_tagging HRun Hlaw)).mp Hentry).2
  have Hcases := fusion_run_stored_block_candidate_or_empty HE HElaw HF HFlaw HRun Hlaw Hstored
  apply (le_inf le_rfl Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact objectsBefore_apply (blockCandidate_before inf_le_right)
      (inf_le_left.trans Hearlier) (inf_le_left.trans Hx) (inf_le_left.trans Hy)
  · exact (bot_of_mem_empty (mem_congr bv_refl inf_le_right (inf_le_left.trans Hy))).trans bot_le

def fullBlockOrder (Run : bSet 𝔹) : 𝔹 :=
  ⨅ ν, ⨅ μ, ⨅ b, ⨅ c, ⨅ x, ⨅ y, _root_.imp
    ((ν ∈ᴮ μ ⊓ (pair ν b ∈ᴮ fullBlocks Run ⊓ pair μ c ∈ᴮ fullBlocks Run)) ⊓
      (x ∈ᴮ b ⊓ y ∈ᴮ c)) (x ∈ᴮ y)

theorem fusion_full_blockOrder
    {color : Bool} {R J E S F top Run : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hsuccess : Γ ≤ successfulRun Run) : Γ ≤ fullBlockOrder Run := by
  apply le_iInf
  intro ν
  apply le_iInf
  intro μ
  apply le_iInf
  intro b
  apply le_iInf
  intro c
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  exact fusion_full_blocks_before (inf_le_left.trans HE) (inf_le_left.trans HElaw)
    (inf_le_left.trans HF) (inf_le_left.trans HFlaw) (inf_le_left.trans HRun)
    (inf_le_left.trans Hlaw) (inf_le_left.trans Hsuccess)
    (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_left)))
    (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_right)))
    (inf_le_right.trans (inf_le_right.trans inf_le_left))
    (inf_le_right.trans (inf_le_right.trans inf_le_right))

/-- The whole-object family passed to the countable-tail construction. -/
def fullBlockFamily (Run : bSet 𝔹) : bSet 𝔹 :=
  image omegaOne (bv_powerset omegaTwo) (fullBlocks Run)

theorem fullBlockFamily_small
    {color : Bool} {R E F top Run : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ injects_into (fullBlockFamily Run) omegaOne :=
  ErdosCountableImage.image_injects_into_ordinal
    (is_func'_of_is_function (fullBlocks_is_function HRun Hlaw))
    injects_into_refl omegaOne_Ord

theorem fullBlockFamily_subset
    {color : Bool} {R J E S F top Run : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hsuccess : Γ ≤ successfulRun Run) :
    Γ ≤ fullBlockFamily Run ⊆ᴮ blockObjects color R := by
  rw [subset_unfold']
  apply le_iInf
  intro b
  rw [← deduction]
  obtain ⟨ν, Hν⟩ := exists_convert (mem_image_iff.mp
    (show Γ ⊓ b ∈ᴮ fullBlockFamily Run ≤ b ∈ᴮ fullBlockFamily Run from inf_le_right)).2
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact fullBlocks_blockObject (inf_le_left.trans HE) (inf_le_left.trans HElaw)
    (inf_le_left.trans HF) (inf_le_left.trans HFlaw) (inf_le_left.trans HRun)
    (inf_le_left.trans Hlaw) (inf_le_left.trans Hsuccess) (Hν.trans inf_le_right)

end bSet.ErdosFusionRunBlockOrder
