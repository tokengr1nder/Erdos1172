/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockPoolFinalCut

@[expose] public section

/-!
# An actual small closed whole-block selector hull

The same fixed selector is closed on arbitrary internally countable
subsets of the whole-object and physical-point pools. Empty failures are
allowed as values but are not inserted into the block-object pool.
The point pool is an actual countably bounded ordinal below omega-two,
and contains every point of every whole object in the object pool.

The fixed canonical enumeration and selector can both be constructed
before the hull. Internal CH and countable boundedness of omega-one
suffice; the latter also follows from the displayed proper countably
closed ideal hypotheses. No supplied hull, successful fusion, normal
dense ideal model, or consistency conclusion is assumed or proved.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosClosedSelectorHull

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBlockSelector ErdosCountableChoicePoolStep
open ErdosCountableSubsetCodes ErdosOmegaOneIdealBounded
open ErdosBlockPoolFinalClosure ErdosBlockPoolFinalCut ErdosBlockPoolRecursion
open ErdosBoundedImageRecursion ErdosIdeal

def selectorClosed (F B P : bSet 𝔹) : 𝔹 :=
  ⨅ Earlier, ⨅ Active, ⨅ A, _root_.imp
    ((Earlier ∈ᴮ countableSubsets B ⊓ Active ∈ᴮ countableSubsets P) ⊓
      pair (pair Earlier Active) A ∈ᴮ F)
    (A ⊆ᴮ P ⊓ ((A =ᴮ (∅ : bSet 𝔹)) ⊔ A ∈ᴮ B))

def closedHullData (color : Bool) (R F B P : bSet 𝔹) : 𝔹 :=
  (B ⊆ᴮ blockObjects color R) ⊓ (injects_into B omegaOne ⊓
    (P ∈ᴮ omegaTwo ⊓ (countablyBounded P ⊓
      (bv_union B ⊆ᴮ P ⊓ selectorClosed F B P))))

theorem selectorClosed_apply {F B P Earlier Active A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ selectorClosed F B P)
    (HEarlier : Γ ≤ Earlier ∈ᴮ countableSubsets B)
    (HActive : Γ ≤ Active ∈ᴮ countableSubsets P)
    (Hpair : Γ ≤ pair (pair Earlier Active) A ∈ᴮ F) :
    Γ ≤ A ⊆ᴮ P ⊓ ((A =ᴮ (∅ : bSet 𝔹)) ⊔ A ∈ᴮ B) :=
  (le_inf (H.trans ((iInf_le _ Earlier).trans
    ((iInf_le _ Active).trans (iInf_le _ A))))
    (le_inf (le_inf HEarlier HActive) Hpair)).trans bv_imp_elim

theorem closedHullData_point_small {color : Bool} {R F B P : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ closedHullData color R F B P) : Γ ≤ injects_into P omegaOne :=
  omegaTwo_member_injects (H.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))

theorem final_pools_selectorClosed
    {color : Bool} {R J E S F Run : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ countablyBounded omegaOne)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R) (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ selectorClosed F (finalObjects color R Run) (finalPoints color R Run) := by
  apply le_iInf
  intro Earlier
  apply le_iInf
  intro Active
  apply le_iInf
  intro A
  rw [← deduction]
  have Hresult := selected_output_in_final_pools (inf_le_left.trans HB)
    (inf_le_left.trans HRun) (inf_le_left.trans Hrec) (inf_le_left.trans HF)
    (inf_le_left.trans Hlaw)
    (show Γ ⊓ ((Earlier ∈ᴮ countableSubsets (finalObjects color R Run) ⊓
      Active ∈ᴮ countableSubsets (finalPoints color R Run)) ⊓
      pair (pair Earlier Active) A ∈ᴮ F) ≤
      Earlier ∈ᴮ countableSubsets (finalObjects color R Run) from
        inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans inf_le_right)
  simpa only [_root_.imp, compl_compl] using Hresult

theorem closedHullData_of_pool_recursion
    {color : Bool} {R J E S F Run : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ countablyBounded omegaOne)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R) (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ closedHullData color R F (finalObjects color R Run) (finalPoints color R Run) :=
  le_inf finalObjects_subset
    (le_inf ((final_pools_small HCH HF Hlaw HRun Hrec).trans inf_le_left)
      (le_inf (finalPoints_mem_omegaTwo HCH HF Hlaw HRun Hrec)
        (le_inf (finalPoints_countablyBounded HB HCH HF Hlaw HRun Hrec)
          (le_inf (finalObjects_points_subset Hrec)
            (final_pools_selectorClosed HB HF Hlaw HRun Hrec)))))

/-- The hull is constructed for this exact previously fixed selector. -/
theorem exists_closed_pool_for_selector
    {color : Bool} {R J E S F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ countablyBounded omegaOne)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F) :
    ∃ B P : bSet 𝔹, Γ ≤ closedHullData color R F B P := by
  obtain ⟨Run, HRun⟩ := exists_pool_recursion color R F (Γ := Γ)
  exact ⟨finalObjects color R Run, finalPoints color R Run,
    closedHullData_of_pool_recursion HCH HB HF Hlaw
      (HRun.trans inf_le_left) (HRun.trans inf_le_right)⟩

end bSet.ErdosClosedSelectorHull
