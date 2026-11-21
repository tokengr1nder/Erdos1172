/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionEntrySpace
public import Erdos1172.Part4InternalFusionChoiceCongruence
public import Erdos1172.Part4InternalTaggedPrefix
public import Erdos1172.Part4InternalBoundedImageRecursionTotal

@[expose] public section

/-!
# Constructing the actual total ordered whole-block fusion run

The next entry computes all least-or-zero row coordinates, then stores
the full active point history, then evaluates the same fixed selector
on the earlier whole objects and that active history. Stage tags retain
the entire ordered prefix graph, including failed block stages.

The operators are bounded and congruent on arbitrary inputs; no reachable
state invariant, successful block choice, or run is supplied as a premise.
This constructs the total run, not its nonstopping or target conclusion.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosBoundedFunctionValue ErdosFusionEntrySpace
open ErdosFusionHistories ErdosFusionHistoryCongruence ErdosFusionActiveHistory
open ErdosFusionRowChoice ErdosFusionChoiceCongruence ErdosSmallFamilyUnion
open ErdosBoundedImageRecursion ErdosTaggedPrefix

def nextIndices (color : Bool) (R E top ξ T : bSet 𝔹) : bSet 𝔹 :=
  currentChoices color R E top ξ (blockHistory T) (coordinateHistory T)

def nextActive (color : Bool) (R E top ξ T : bSet 𝔹) : bSet 𝔹 :=
  activeHistory color R E ξ (blockHistory T) (nextIndices color R E top ξ T) (activeFamily T)

def nextBlock (color : Bool) (R E F top ξ T : bSet 𝔹) : bSet 𝔹 :=
  graphValue (bv_powerset omegaTwo) F
    (pair (earlierHistory color R ξ (blockHistory T)) (nextActive color R E top ξ T))

def nextEntry (color : Bool) (R E F top ξ T : bSet 𝔹) : bSet 𝔹 :=
  entry (nextBlock color R E F top ξ T) (nextIndices color R E top ξ T)
    (nextActive color R E top ξ T)

theorem nextIndices_is_function
    {color : Bool} {R E top ξ T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_function omegaOne omegaOne (nextIndices color R E top ξ T) :=
  currentChoices_is_function

theorem nextActive_subset {color : Bool} {R E top ξ T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ nextActive color R E top ξ T ⊆ᴮ omegaTwo := activeHistory_subset

/-- The bounded evaluator always returns a subset of omega-two, even
outside the selector's valid history domain. No selector law is used. -/
theorem nextBlock_subset {color : Bool} {R E F top ξ T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ nextBlock color R E F top ξ T ⊆ᴮ omegaTwo := indexed_union_subset

theorem nextEntry_mem {color : Bool} {R E F top ξ T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ nextEntry color R E F top ξ T ∈ᴮ entrySpace :=
  mem_entrySpace_iff.mpr ⟨nextBlock_subset,
    nextIndices_is_function.trans inf_le_right, nextActive_subset⟩

theorem nextIndices_congr
    {color : Bool} {R E top ξ η T Q : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ =ᴮ η) (HT : Γ ≤ T =ᴮ Q) :
    Γ ≤ nextIndices color R E top ξ T =ᴮ nextIndices color R E top η Q :=
  currentChoices_congr bv_refl Hξ (blockHistory_congr HT) (coordinateHistory_congr HT)

theorem nextActive_congr
    {color : Bool} {R E top ξ η T Q : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ =ᴮ η) (HT : Γ ≤ T =ᴮ Q) :
    Γ ≤ nextActive color R E top ξ T =ᴮ nextActive color R E top η Q :=
  activeHistory_currentChoices_congr bv_refl Hξ (blockHistory_congr HT)
    (coordinateHistory_congr HT) (activeFamily_congr HT)

theorem nextBlock_congr
    {color : Bool} {R E F top ξ η T Q : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ =ᴮ η) (HT : Γ ≤ T =ᴮ Q) :
    Γ ≤ nextBlock color R E F top ξ T =ᴮ nextBlock color R E F top η Q :=
  graphValue_congr_input _ _ (pair_congr
    (bv_trans (earlierHistory_congr_stage color R (blockHistory T) Hξ)
      (earlierHistory_congr_blocks color R η (blockHistory_congr HT)))
    (nextActive_congr Hξ HT))

theorem nextEntry_congr
    {color : Bool} {R E F top ξ η T Q : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ =ᴮ η) (HT : Γ ≤ T =ᴮ Q) :
    Γ ≤ nextEntry color R E F top ξ T =ᴮ nextEntry color R E F top η Q :=
  pair_congr (nextBlock_congr Hξ HT) (pair_congr (nextIndices_congr Hξ HT) (nextActive_congr Hξ HT))

def runSpace : bSet 𝔹 := prod omegaOne entrySpace

def runLaw (color : Bool) (R E F top Run : bSet 𝔹) : 𝔹 :=
  imageRecLaw runSpace (fun ξ T => pair ξ (nextEntry color R E F top ξ T)) Run

/-- An actual total stage-tagged omega-one run exists without assuming
its success, a legal input history, or any induction invariant. -/
theorem exists_total_fusion_run (color : Bool) (R E F top : bSet 𝔹) {Γ : 𝔹} :
    ∃ Run : bSet 𝔹, Γ ≤ is_function omegaOne runSpace Run ⊓ runLaw color R E F top Run := by
  apply exists_bounded_image_recursion omegaOne_Ord
  · intro T ξ η Δ H
    exact pair_congr H (nextEntry_congr H bv_refl)
  · intro ξ T Q Δ H
    exact pair_congr bv_refl (nextEntry_congr bv_refl H)
  · apply le_iInf
    intro ξ
    apply le_iInf
    intro T
    rw [← deduction]
    exact mem_prod (inf_le_right.trans inf_le_left) nextEntry_mem

theorem fusion_run_tagging
    {color : Bool} {R E F top Run : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) : Γ ≤ taggingLaw entrySpace Run :=
  taggingLaw_of_imageRecLaw HRun Hlaw

theorem fusion_prefix_is_function
    {color : Bool} {R E F top Run ξ : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) :
    Γ ≤ is_function ξ entrySpace (taggedPrefix ξ omegaOne entrySpace Run) :=
  taggedPrefix_is_function HRun (fusion_run_tagging HRun Hlaw) Hξ

theorem fusion_run_entry_eq
    {color : Bool} {R E F top Run ξ A Z U : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hpair : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run) :
    Γ ≤ entry A Z U =ᴮ nextEntry color R E F top ξ (taggedPrefix ξ omegaOne entrySpace Run) :=
  eq_of_eq_pair_right' (imageRecLaw_apply Hlaw Hpair)

/-- Every actual stored row graph is total, before any later invariant
about countability, legality, or nonfailure is proved. -/
theorem fusion_run_indices_function
    {color : Bool} {R E F top Run ξ A Z U : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hpair : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run) :
    Γ ≤ is_function omegaOne omegaOne Z :=
  bv_rw' (ϕ := is_function omegaOne omegaOne)
    (eq_of_eq_pair_left' (eq_of_eq_pair_right' (fusion_run_entry_eq Hlaw Hpair)))
    (h_congr := B_ext_is_function_right) (H_new := nextIndices_is_function)

theorem fusion_prefix_rowFunctions
    {color : Bool} {R E F top Run ξ : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ rowFunctions (taggedPrefix ξ omegaOne entrySpace Run) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro A
  apply le_iInf
  intro Z
  apply le_iInf
  intro U
  rw [← deduction]
  have Hpair := (mem_taggedPrefix_pair_iff (inf_le_left.trans HRun)
    (inf_le_left.trans (fusion_run_tagging HRun Hlaw))).mp
    (show Γ ⊓ pair i (entry A Z U) ∈ᴮ taggedPrefix ξ omegaOne entrySpace Run ≤
      pair i (entry A Z U) ∈ᴮ taggedPrefix ξ omegaOne entrySpace Run from inf_le_right)
  exact fusion_run_indices_function (inf_le_left.trans Hlaw) Hpair.2

theorem fusion_prefix_coordinates_function
    {color : Bool} {R E F top Run ξ : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) :
    Γ ≤ is_function (prod ξ omegaOne) omegaOne
      (coordinateHistory (taggedPrefix ξ omegaOne entrySpace Run)) :=
  coordinateHistory_is_function Hξ (fusion_prefix_is_function HRun Hlaw Hξ)
    (fusion_prefix_rowFunctions HRun Hlaw)

end bSet.ErdosFusionRun
