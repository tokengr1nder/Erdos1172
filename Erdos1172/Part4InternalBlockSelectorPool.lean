/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockSelector

@[expose] public section

/-!
# One small closure step of the actual block selector

Every selected value is either a whole omega-one block or empty, so its
smallness is proved from the selector law rather than assumed. Restricting
the same selector to a small local history domain bounds both its object
image and its point union.

The next successful-object pool filters out failure: empty is never
asserted to be a block object. The raw point union may retain empty among
its indexed values, where it contributes no points. This is one local
closure step, not a closed hull or a completed fusion construction.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockSelectorPool

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBlockCandidate ErdosBlockSelector
open ErdosCountableChoicePoolStep ErdosCountableSubsetCodes ErdosSmallFamilyUnion
open ErdosRelationGraph

theorem blockObject_injects_omegaOne {color : Bool} {R A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ∈ᴮ blockObjects color R) : Γ ≤ injects_into A omegaOne := by
  obtain ⟨f, Hf⟩ := exists_block_enumeration HA
  exact bv_rw'' (ϕ := fun X => injects_into X omegaOne)
    (Hf.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    (ErdosLargeTwoBlock.injective_image_small (Hf.trans inf_le_left))
    B_ext_injects_into_left

/-- No external case distinction selects success or failure: both
Boolean branches give the same internal cardinal bound. -/
theorem selected_value_injects_omegaOne
    {color : Bool} {R J E S F Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hpair : Γ ≤ pair (pair Earlier Active) A ∈ᴮ F) :
    Γ ≤ injects_into A omegaOne := by
  have Hcases := selected_candidate_or_empty HF Hlaw Hpair
  apply (le_inf le_rfl Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact blockObject_injects_omegaOne (blockCandidate_object inf_le_right)
  · exact bv_rw' (ϕ := fun X => injects_into X omegaOne) inf_le_right
      (h_congr := B_ext_injects_into_left)
      (H_new := injects_into_of_subset empty_subset)

/-- Local totality requires genuine block and vertex pools. In particular
one cannot pass an unfiltered pool containing the empty failure object. -/
theorem selector_local_is_func'
    {color : Bool} {R F B P : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HBsub : Γ ≤ B ⊆ᴮ blockObjects color R) (HPsub : Γ ≤ P ⊆ᴮ omegaTwo) :
    Γ ≤ is_func' (choicePoolDomain B P) (bv_powerset omegaTwo) F :=
  is_func'_subset_of_is_func' (is_func'_of_is_function HF) (choicePoolDomain_subset HBsub HPsub)

/-- This is a guarded value law only. It does not assert totality on an
arbitrary local domain; that separate fact needs both pool inclusions. -/
theorem selector_local_smallValues
    {color : Bool} {R J E S F B P : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F) :
    Γ ≤ smallValues (choicePoolDomain B P) F := by
  apply le_iInf
  intro q
  apply le_iInf
  intro A
  rw [← deduction]
  let Δ := Γ ⊓ (q ∈ᴮ choicePoolDomain B P ⊓ pair q A ∈ᴮ F)
  obtain ⟨T, _, U, _, Hq⟩ := mem_prod_iff₂.mp
    (show Δ ≤ q ∈ᴮ prod (countableSubsets B) (countableSubsets P) from
      inf_le_right.trans inf_le_left)
  have Hpair : Δ ≤ pair (pair T U) A ∈ᴮ F :=
    mem_congr (pair_congr Hq bv_refl) bv_refl (inf_le_right.trans inf_le_right)
  exact selected_value_injects_omegaOne (inf_le_left.trans HF) (inf_le_left.trans Hlaw) Hpair

/-- The actual selector discharges the former pointwise-smallness premise. -/
theorem choice_pool_step_small
    {color : Bool} {R J E S F B P : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HBsmall : Γ ≤ injects_into B omegaOne)
    (HPsmall : Γ ≤ injects_into P omegaOne)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HBsub : Γ ≤ B ⊆ᴮ blockObjects color R) (HPsub : Γ ≤ P ⊆ᴮ omegaTwo) :
    Γ ≤ injects_into (selectedObjects omegaTwo B P F) omegaOne ⊓
      injects_into (selectedPoints omegaTwo B P F) omegaOne :=
  ErdosCountableChoicePoolStep.choice_pool_step_small HCH HBsmall HPsmall
    (selector_local_is_func' HF HBsub HPsub) (selector_local_smallValues HF Hlaw)

/-- Keep whole successful block objects, excluding the empty fallback. -/
def successfulObjects (color : Bool) (R B P F : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun A => A ∈ᴮ blockObjects color R) (selectedObjects omegaTwo B P F)

theorem mem_successfulObjects_iff
    {color : Bool} {R B P F A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ A ∈ᴮ successfulObjects color R B P F ↔
      Γ ≤ A ∈ᴮ selectedObjects omegaTwo B P F ∧ Γ ≤ A ∈ᴮ blockObjects color R :=
  mem_comprehend_and B_ext_mem_left

theorem successfulObjects_subset_selected
    {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ successfulObjects color R B P F ⊆ᴮ selectedObjects omegaTwo B P F :=
  comprehend_subset (ϕ := fun A => A ∈ᴮ blockObjects color R)
    (selectedObjects omegaTwo B P F)

theorem successfulObjects_subset_blocks
    {color : Bool} {R B P F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ successfulObjects color R B P F ⊆ᴮ blockObjects color R := by
  rw [subset_unfold']
  apply le_iInf
  intro A
  rw [← deduction]
  exact (mem_successfulObjects_iff.mp
    (show Γ ⊓ A ∈ᴮ successfulObjects color R B P F ≤
      A ∈ᴮ successfulObjects color R B P F from inf_le_right)).2

theorem successfulObjects_injects_omegaOne
    {color : Bool} {R F B P : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HBsmall : Γ ≤ injects_into B omegaOne)
    (HPsmall : Γ ≤ injects_into P omegaOne)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HBsub : Γ ≤ B ⊆ᴮ blockObjects color R) (HPsub : Γ ≤ P ⊆ᴮ omegaTwo) :
    Γ ≤ injects_into (successfulObjects color R B P F) omegaOne :=
  injects_into_trans (injects_into_of_subset successfulObjects_subset_selected)
    (selectedObjects_injects_omegaOne HCH HBsmall HPsmall (selector_local_is_func' HF HBsub HPsub))

/-- A nonempty local selected output belongs to the filtered object pool.
The proof uses the full candidate law, not just powerset support. -/
theorem nonempty_selected_value_mem_successful
    {color : Bool} {R J E S F B P Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HBsub : Γ ≤ B ⊆ᴮ blockObjects color R) (HPsub : Γ ≤ P ⊆ᴮ omegaTwo)
    (HEarlier : Γ ≤ Earlier ∈ᴮ countableSubsets B)
    (HActive : Γ ≤ Active ∈ᴮ countableSubsets P)
    (Hpair : Γ ≤ pair (pair Earlier Active) A ∈ᴮ F)
    (Hnonempty : Γ ≤ (A =ᴮ (∅ : bSet 𝔹))ᶜ) :
    Γ ≤ A ∈ᴮ successfulObjects color R B P F :=
  mem_successfulObjects_iff.mpr
    ⟨mem_selectedObjects_of_value (selector_local_is_func' HF HBsub HPsub)
      HEarlier HActive Hpair,
      blockCandidate_object (selected_candidate_of_nonempty HF Hlaw Hpair Hnonempty)⟩

/-- Both usable next pools are small: successful whole objects and the
point union of all raw outputs. This is only one closure step. -/
theorem successful_pool_step_small
    {color : Bool} {R J E S F B P : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HBsmall : Γ ≤ injects_into B omegaOne)
    (HPsmall : Γ ≤ injects_into P omegaOne)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HBsub : Γ ≤ B ⊆ᴮ blockObjects color R) (HPsub : Γ ≤ P ⊆ᴮ omegaTwo) :
    Γ ≤ injects_into (successfulObjects color R B P F) omegaOne ⊓
      injects_into (selectedPoints omegaTwo B P F) omegaOne :=
  le_inf (successfulObjects_injects_omegaOne HCH HBsmall HPsmall HF HBsub HPsub)
    ((choice_pool_step_small HCH HBsmall HPsmall HF Hlaw HBsub HPsub).trans inf_le_right)

end bSet.ErdosBlockSelectorPool
