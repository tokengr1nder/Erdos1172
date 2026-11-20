/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockPoolRecursion
public import Erdos1172.Part4InternalImageRecursionInvariant

@[expose] public section

/-!
# Smallness of the actual selector-pool recursion

Internal least-bad-stage induction proves that every actual stage has
two omega-one-small components. Prefix images are internally countable,
not externally enumerated. The full omega-one-indexed image is small
enough to prove both final aggregate pools small as well. The run and
these bounds are constructed; final history capture is not assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockPoolSmallInvariant

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBlockSelector ErdosCountableChoicePoolStep
open ErdosPoolAggregation ErdosBlockPoolUpdate ErdosBlockPoolRecursion
open ErdosImageRecursionInvariant ErdosBoundedImageRecursion ErdosCountableImage

def smallState (q : bSet 𝔹) : 𝔹 :=
  ⨅ B, ⨅ P, _root_.imp (q =ᴮ pair B P)
    (injects_into B omegaOne ⊓ injects_into P omegaOne)

theorem smallState_ext : B_ext (smallState : bSet 𝔹 → 𝔹) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_bv_eq_left) (h₂ := B_ext_const)))

theorem smallState_apply {B P : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ smallState (pair B P)) :
    Γ ≤ injects_into B omegaOne ⊓ injects_into P omegaOne :=
  (le_inf (H.trans ((iInf_le _ B).trans (iInf_le _ P))) bv_refl).trans bv_imp_elim

theorem smallState_of_pair {B P : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ injects_into B omegaOne) (HP : Γ ≤ injects_into P omegaOne) :
    Γ ≤ smallState (pair B P) := by
  apply le_iInf
  intro A
  apply le_iInf
  intro C
  rw [← deduction]
  exact le_inf
    (bv_rw'' (ϕ := fun X => injects_into X omegaOne) (eq_of_eq_pair_left' inf_le_right)
      (inf_le_left.trans HB) B_ext_injects_into_left)
    (bv_rw'' (ϕ := fun X => injects_into X omegaOne) (eq_of_eq_pair_right' inf_le_right)
      (inf_le_left.trans HP) B_ext_injects_into_left)

theorem aggregates_small {color : Bool} {R T : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HT : Γ ≤ T ⊆ᴮ stateSpace color R)
    (HTsmall : Γ ≤ injects_into T omegaOne) (Hgood : Γ ≤ allGood smallState T) :
    Γ ≤ injects_into (priorObjects color R T) omegaOne ⊓
      injects_into (priorPoints color R T) omegaOne := by
  refine le_inf (aggregateLeft_injects_omegaOne HCH HT HTsmall ?_)
    (aggregateRight_injects_omegaOne HCH HT HTsmall ?_)
  · apply le_iInf
    intro B
    apply le_iInf
    intro P
    rw [← deduction]
    exact (smallState_apply (allGood_apply (inf_le_left.trans Hgood) inf_le_right)).trans
      inf_le_left
  · apply le_iInf
    intro B
    apply le_iInf
    intro P
    rw [← deduction]
    exact (smallState_apply (allGood_apply (inf_le_left.trans Hgood) inf_le_right)).trans
      inf_le_right

theorem prefix_image_small {color : Bool} {R Run i : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) :
    Γ ≤ injects_into (image i (stateSpace color R) Run) omegaOne :=
  injects_into_trans
    (restricted_image_countable (is_func'_of_is_function HF)
      (subset_of_mem_Ord Hi omegaOne_Ord) (omegaOne_member_injects Hi))
    (injects_into_of_subset (subset_of_mem_Ord omega_mem_omegaOne omegaOne_Ord))

theorem poolUpdate_smallState {color : Bool} {R J E S F T : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HT : Γ ≤ T ⊆ᴮ stateSpace color R) (HTsmall : Γ ≤ injects_into T omegaOne)
    (Hgood : Γ ≤ allGood smallState T) : Γ ≤ smallState (poolUpdate color R F T) := by
  have Hagg := aggregates_small HCH HT HTsmall Hgood
  have Hnext := update_small HCH (Hagg.trans inf_le_left) (Hagg.trans inf_le_right)
    HF Hlaw aggregateLeft_subset aggregateRight_subset
  exact smallState_of_pair (Hnext.trans inf_le_left)
    (Hnext.trans (inf_le_right.trans inf_le_right))

theorem pool_small_invariant_step {color : Bool} {R J E S F Run : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run) :
    Γ ≤ imageRecInvariantStep omegaOne (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run smallState := by
  apply le_iInf
  intro i
  rw [← deduction]
  exact poolUpdate_smallState (inf_le_left.trans HCH) (inf_le_left.trans HF)
    (inf_le_left.trans Hlaw) image_subset
    (prefix_image_small (inf_le_left.trans HRun) (inf_le_right.trans inf_le_left))
    (inf_le_right.trans inf_le_right)

theorem pool_run_allSmall {color : Bool} {R J E S F Run : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ allGood smallState (image omegaOne (stateSpace color R) Run) :=
  image_allGood_of_imageRecLaw omegaOne_Ord HRun Hrec smallState_ext
    (pool_small_invariant_step HCH HF Hlaw HRun)

theorem pool_final_aggregates_small {color : Bool} {R J E S F Run : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (Hlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hrec : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ injects_into (priorObjects color R (image omegaOne (stateSpace color R) Run)) omegaOne ⊓
      injects_into (priorPoints color R (image omegaOne (stateSpace color R) Run)) omegaOne :=
  aggregates_small HCH image_subset
    (image_injects_into_ordinal (is_func'_of_is_function HRun) injects_into_refl omegaOne_Ord)
    (pool_run_allSmall HCH HF Hlaw HRun Hrec)

end bSet.ErdosBlockPoolSmallInvariant
