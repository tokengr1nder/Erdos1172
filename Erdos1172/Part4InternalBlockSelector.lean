/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockCandidate
public import Erdos1172.Part4InternalBoundedFallbackChoice
public import Erdos1172.Part4InternalCountableChoicePoolStep

@[expose] public section

/-!
# A fixed actual block selector with exact failure

The input is just a pair of whole countable history sets: earlier block
objects and active physical points. The original set and enumeration
family are fixed parameters. Neither a terminal, recursion stage, rank
cut, nor a varying future is an input to this selector.

Bounded choice constructs one actual total graph, even where no candidate
exists. Empty is selected exactly on the no-candidate Boolean condition,
because every genuine candidate is a nonempty whole block object. This
does not assert that any candidate exists.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockSelector

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBlockCandidate
open ErdosBoundedFallbackChoice ErdosCountableChoicePoolStep

def selectorCandidate (color : Bool) (R J E S q A : bSet 𝔹) : 𝔹 :=
  ⨆ Earlier, ⨆ Active,
    q =ᴮ pair Earlier Active ⊓ blockCandidate color R J E S Earlier Active A

theorem selectorCandidate_ext_input (color : Bool) (R J E S A : bSet 𝔹) :
    B_ext (fun q => selectorCandidate color R J E S q A) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_inf B_ext_bv_eq_left B_ext_const))

theorem selectorCandidate_ext_output (color : Bool) (R J E S q : bSet 𝔹) :
    B_ext (selectorCandidate color R J E S q) :=
  B_ext_iSup (h := fun Earlier => B_ext_iSup (h := fun Active =>
    B_ext_inf B_ext_const (blockCandidate_ext_object color R J E S Earlier Active)))

/-- Pair decoding is extensional and Boolean; no external choice of a
history decomposition is used. -/
theorem selectorCandidate_pair_iff
    {color : Bool} {R J E S Earlier Active A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ selectorCandidate color R J E S (pair Earlier Active) A ↔
      Γ ≤ blockCandidate color R J E S Earlier Active A := by
  constructor
  · intro H
    apply H.trans
    apply iSup_le
    intro Earlier'
    apply iSup_le
    intro Active'
    exact bv_rw' (ϕ := fun T => blockCandidate color R J E S T Active A)
      (eq_of_eq_pair_left' inf_le_left)
      (h_congr := blockCandidate_ext_earlier color R J E S Active A)
      (H_new := bv_rw' (ϕ := fun U => blockCandidate color R J E S Earlier' U A)
        (eq_of_eq_pair_right' inf_le_left)
        (h_congr := blockCandidate_ext_active color R J E S Earlier' A)
        (H_new := inf_le_right))
  · intro H
    exact le_iSup_of_le Earlier (le_iSup_of_le Active (le_inf bv_refl H))

theorem selectorCandidate_pair_eq (color : Bool)
    (R J E S Earlier Active A : bSet 𝔹) :
    selectorCandidate color R J E S (pair Earlier Active) A =
      blockCandidate color R J E S Earlier Active A :=
  le_antisymm (selectorCandidate_pair_iff.mp le_rfl)
    (selectorCandidate_pair_iff.mpr le_rfl)

theorem blockCandidate_mem_powerset
    {color : Bool} {R J E S Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ blockCandidate color R J E S Earlier Active A) :
    Γ ≤ A ∈ᴮ bv_powerset omegaTwo :=
  mem_of_mem_subset blockObjects_subset (blockCandidate_object H)

/-- The powerset bound removes no candidate: the bounded existence value
is exactly the existence of the full whole-object candidate predicate. -/
theorem candidateValue_pair_eq (color : Bool)
    (R J E S Earlier Active : bSet 𝔹) :
    candidateValue (bv_powerset omegaTwo) (selectorCandidate color R J E S)
      (pair Earlier Active) = ⨆ A, blockCandidate color R J E S Earlier Active A := by
  unfold candidateValue
  apply le_antisymm
  · apply iSup_le
    intro A
    rw [selectorCandidate_pair_eq]
    exact le_iSup_of_le A inf_le_right
  · apply iSup_le
    intro A
    exact le_iSup_of_le A (le_inf (blockCandidate_mem_powerset le_rfl)
      (selectorCandidate_pair_iff.mpr le_rfl))

def blockSelectorLaw (color : Bool) (R J E S F : bSet 𝔹) : 𝔹 :=
  fallbackFamilyLaw (choicePoolDomain (blockObjects color R) omegaTwo)
    (bv_powerset omegaTwo) (selectorCandidate color R J E S) (∅ : bSet 𝔹) F

/-- The fixed selector is constructed without any CH, ideal, successful
history, or candidate-existence premise. Internally empty histories are
included in its actual domain. -/
theorem exists_block_selector (color : Bool) (R J E S : bSet 𝔹) {Γ : 𝔹} :
    ∃ F : bSet 𝔹,
      Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
        (bv_powerset omegaTwo) F ⊓ blockSelectorLaw color R J E S F :=
  exists_fallback_selector (fun A => selectorCandidate_ext_input color R J E S A)
    (fun q => selectorCandidate_ext_output color R J E S q)
    (mem_powerset_iff.mpr empty_subset)

/-- A selected output satisfies every candidate clause whenever a
candidate exists for this exact pair of histories. -/
theorem selected_blockCandidate
    {color : Bool} {R J E S F Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hpair : Γ ≤ pair (pair Earlier Active) A ∈ᴮ F)
    (Hex : Γ ≤ ⨆ B, blockCandidate color R J E S Earlier Active B) :
    Γ ≤ blockCandidate color R J E S Earlier Active A := by
  apply selectorCandidate_pair_iff.mp
  apply selected_candidate HF Hlaw Hpair
  rw [candidateValue_pair_eq]
  exact Hex

/-- This is an equivalence of local Boolean assertions, not just the
one-way statement that absence causes a fallback. -/
theorem selected_empty_iff_no_candidate
    {color : Bool} {R J E S F Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hpair : Γ ≤ pair (pair Earlier Active) A ∈ᴮ F) :
    Γ ≤ A =ᴮ (∅ : bSet 𝔹) ↔
      Γ ≤ (⨆ B, blockCandidate color R J E S Earlier Active B)ᶜ := by
  constructor
  · intro Hempty
    rw [← imp_bot, ← deduction]
    have Hcandidate := selected_blockCandidate (inf_le_left.trans HF)
      (inf_le_left.trans Hlaw) (inf_le_left.trans Hpair) inf_le_right
    exact bv_absurd _ (inf_le_left.trans Hempty) (blockCandidate_nonempty Hcandidate)
  · intro Hno
    apply selected_failure HF Hlaw Hpair
    rw [candidateValue_pair_eq]
    exact Hno

/-- Nonempty selected output is genuine success, retaining the full
candidate predicate rather than only its homogeneous-set component. -/
theorem selected_candidate_of_nonempty
    {color : Bool} {R J E S F Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hpair : Γ ≤ pair (pair Earlier Active) A ∈ᴮ F)
    (Hnonempty : Γ ≤ (A =ᴮ (∅ : bSet 𝔹))ᶜ) :
    Γ ≤ blockCandidate color R J E S Earlier Active A := by
  apply selected_blockCandidate HF Hlaw Hpair
  rw [← compl_compl (⨆ B, blockCandidate color R J E S Earlier Active B),
    ← imp_bot, ← deduction]
  have Hempty := (selected_empty_iff_no_candidate (inf_le_left.trans HF)
    (inf_le_left.trans Hlaw) (inf_le_left.trans Hpair)).mpr inf_le_right
  exact bv_absurd _ Hempty (inf_le_left.trans Hnonempty)

/-- The two alternatives remain inside the Boolean algebra. -/
theorem selected_candidate_or_empty
    {color : Bool} {R J E S F Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hpair : Γ ≤ pair (pair Earlier Active) A ∈ᴮ F) :
    Γ ≤ blockCandidate color R J E S Earlier Active A ⊔ A =ᴮ (∅ : bSet 𝔹) := by
  have H := selected_fallbackData HF Hlaw Hpair
  unfold fallbackData at H
  apply H.trans
  apply sup_le
  · exact (selectorCandidate_pair_iff.mp inf_le_right).trans le_sup_left
  · exact inf_le_right.trans le_sup_right

end bSet.ErdosBlockSelector
