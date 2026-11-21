/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountableTailSelector
public import Erdos1172.Part4InternalBoundedImageRecursionTotal
public import Erdos1172.Part4InternalImageRecursionInvariant
public import Erdos1172.Part4InternalBoundedFunctionValue
public import Erdos1172.Part4InternalSmallPoolOperations

@[expose] public section

/-!
# An actual countable tail of whole blocks

The update is globally bounded and congruent, including on malformed
past sets. Internal ordinal invariant induction proves that the actual
run has only block-object values, so its filter is then exactly its full
strict-prefix image. The final theorem constructs both the large-input
selector and the entire omega-run, deriving every candidate and every
nonempty output rather than assuming success of the recursion.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableTailRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis ErdosCanonicalBlocks
open ErdosBlockCandidate ErdosCountableTailSelector ErdosRelationGraph
open ErdosBoundedImageRecursion ErdosImageRecursionInvariant ErdosBoundedFunctionValue
open ErdosSmallPoolOperations ErdosSmallFamilyUnion ErdosCountableImage

def filteredPast (color : Bool) (R T : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun A => A ∈ᴮ blockObjects color R) T

def tailEarlier (color : Bool) (R B T : bSet 𝔹) : bSet 𝔹 :=
  binary_union B (filteredPast color R T)

def tailStep (color : Bool) (R B G T : bSet 𝔹) : bSet 𝔹 :=
  graphValue (bv_powerset omegaTwo) G (tailEarlier color R B T)

def tailRunLaw (color : Bool) (R B G Tail : bSet 𝔹) : 𝔹 :=
  imageRecLaw (bv_powerset omegaTwo) (fun _ T => tailStep color R B G T) Tail

def tailCandidatesLaw (color : Bool) (R J E S B Tail : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ A, _root_.imp (pair i A ∈ᴮ Tail)
    (blockCandidate color R J E S
      (binary_union B (image i (bv_powerset omegaTwo) Tail)) ∅ A ⊓ (A =ᴮ ∅)ᶜ)

theorem mem_filteredPast_iff {color : Bool} {R T A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ A ∈ᴮ filteredPast color R T ↔ Γ ≤ A ∈ᴮ T ∧ Γ ≤ A ∈ᴮ blockObjects color R :=
  mem_comprehend_and B_ext_mem_left

theorem filteredPast_subset {color : Bool} {R T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ filteredPast color R T ⊆ᴮ T :=
  comprehend_subset (ϕ := fun A => A ∈ᴮ blockObjects color R) T

theorem filteredPast_subset_objects {color : Bool} {R T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ filteredPast color R T ⊆ᴮ blockObjects color R := by
  rw [subset_unfold']
  apply le_iInf
  intro A
  rw [← deduction]
  exact (mem_filteredPast_iff.mp
    (show Γ ⊓ A ∈ᴮ filteredPast color R T ≤ A ∈ᴮ filteredPast color R T from
      inf_le_right)).2

theorem filteredPast_congr (color : Bool) (R : bSet 𝔹) : B_congr (filteredPast color R) := by
  intro T U Γ H
  exact B_congr_comprehend (ϕ := fun A => A ∈ᴮ blockObjects color R)
    (H_congr := B_ext_mem_left) H

theorem filteredPast_eq_of_subset {color : Bool} {R T : bSet 𝔹} {Γ : 𝔹}
    (HT : Γ ≤ T ⊆ᴮ blockObjects color R) :
    Γ ≤ filteredPast color R T =ᴮ T := by
  apply mem_ext
  · apply le_iInf
    intro A
    rw [← deduction]
    exact (mem_filteredPast_iff.mp
      (show Γ ⊓ A ∈ᴮ filteredPast color R T ≤ A ∈ᴮ filteredPast color R T from
        inf_le_right)).1
  · apply le_iInf
    intro A
    rw [← deduction]
    exact mem_filteredPast_iff.mpr
      ⟨inf_le_right, mem_of_mem_subset (inf_le_left.trans HT) inf_le_right⟩

theorem tailEarlier_subset_objects {color : Bool} {R B T : bSet 𝔹} {Γ : 𝔹}
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) :
    Γ ≤ tailEarlier color R B T ⊆ᴮ blockObjects color R :=
  binary_union_subset HB filteredPast_subset_objects

theorem tailEarlier_congr (color : Bool) (R B : bSet 𝔹) : B_congr (tailEarlier color R B) := by
  intro T U Γ H
  exact binary_union_congr bv_refl (filteredPast_congr color R H)

theorem tailStep_congr (color : Bool) (R B G : bSet 𝔹) : B_congr (tailStep color R B G) := by
  intro T U Γ H
  exact graphValue_congr_input _ _ (tailEarlier_congr color R B H)

/-- This support is unconditional, also for inputs outside the selector
domain. No success or smallness assumption enters the recursion engine. -/
theorem tailStep_mem_powerset {color : Bool} {R B G T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ tailStep color R B G T ∈ᴮ bv_powerset omegaTwo :=
  mem_powerset_iff.mpr indexed_union_subset

theorem exists_tail_recursion (color : Bool) (R B G : bSet 𝔹) {Γ : 𝔹} :
    ∃ Tail : bSet 𝔹, Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail ⊓
      tailRunLaw color R B G Tail := by
  apply exists_bounded_image_recursion Ord_omega
  · intro T i j Δ H
    exact bv_refl
  · intro i
    exact tailStep_congr color R B G
  · apply le_iInf
    intro i
    apply le_iInf
    intro T
    rw [← deduction]
    exact tailStep_mem_powerset

theorem tailEarlier_small {color : Bool} {R B Tail i : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ injects_into B omegaOne)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Hi : Γ ≤ i ∈ᴮ bSet.omega) :
    Γ ≤ injects_into (tailEarlier color R B (image i (bv_powerset omegaTwo) Tail))
      omegaOne := by
  have Hisub : Γ ≤ i ⊆ᴮ bSet.omega := subset_of_mem_Ord Hi Ord_omega
  have Hcount : Γ ≤ injects_into (image i (bv_powerset omegaTwo) Tail) bSet.omega :=
    restricted_image_countable (is_func'_of_is_function HTail) Hisub (injects_into_of_subset Hisub)
  have Hfiltered : Γ ≤ injects_into
      (filteredPast color R (image i (bv_powerset omegaTwo) Tail)) omegaOne :=
    injects_into_trans (injects_into_of_subset filteredPast_subset)
      (injects_into_trans Hcount
        (injects_into_of_subset (subset_of_mem_Ord omega_mem_omegaOne omegaOne_Ord)))
  exact binary_union_injects_omegaOne HCH HB Hfiltered

theorem tailStep_candidate {color : Bool} {R J E S B G Tail i : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (HBsmall : Γ ≤ injects_into B omegaOne)
    (HG : Γ ≤ is_function (bv_powerset (blockObjects color R)) (bv_powerset omegaTwo) G)
    (Hchoice : Γ ≤ smallTailCandidates color R J E S G)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Hi : Γ ≤ i ∈ᴮ bSet.omega) :
    Γ ≤ blockCandidate color R J E S
      (tailEarlier color R B (image i (bv_powerset omegaTwo) Tail)) ∅
      (tailStep color R B G (image i (bv_powerset omegaTwo) Tail)) :=
  smallTailCandidates_apply Hchoice (tailEarlier_small HCH HBsmall HTail Hi)
    (graphValue_pair_mem HG (mem_powerset_iff.mpr (tailEarlier_subset_objects HB)))

/-- The invariant is established at actual internal ordinal stages.
Its step needs no inductive success premise: filtering supplies support,
and countable prefix-image size supplies the selector's small input. -/
theorem tailRun_object_step {color : Bool} {R J E S B G Tail : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (HBsmall : Γ ≤ injects_into B omegaOne)
    (HG : Γ ≤ is_function (bv_powerset (blockObjects color R)) (bv_powerset omegaTwo) G)
    (Hchoice : Γ ≤ smallTailCandidates color R J E S G)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail) :
    Γ ≤ imageRecInvariantStep bSet.omega (bv_powerset omegaTwo)
      (fun _ T => tailStep color R B G T) Tail (fun A => A ∈ᴮ blockObjects color R) := by
  apply le_iInf
  intro i
  rw [← deduction]
  exact blockCandidate_object (tailStep_candidate (inf_le_left.trans HCH)
    (inf_le_left.trans HB) (inf_le_left.trans HBsmall) (inf_le_left.trans HG)
    (inf_le_left.trans Hchoice) (inf_le_left.trans HTail) (inf_le_right.trans inf_le_left))

theorem tailRun_values_objects {color : Bool} {R J E S B G Tail : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (HBsmall : Γ ≤ injects_into B omegaOne)
    (HG : Γ ≤ is_function (bv_powerset (blockObjects color R)) (bv_powerset omegaTwo) G)
    (Hchoice : Γ ≤ smallTailCandidates color R J E S G)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Hlaw : Γ ≤ tailRunLaw color R B G Tail) :
    Γ ≤ ⨅ i, ⨅ A, _root_.imp (pair i A ∈ᴮ Tail) (A ∈ᴮ blockObjects color R) :=
  values_good_of_imageRecLaw Ord_omega HTail Hlaw B_ext_mem_left
    (tailRun_object_step HCH HB HBsmall HG Hchoice HTail)

theorem tailRun_prefix_subset_objects
    {color : Bool} {R J E S B G Tail i : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (HBsmall : Γ ≤ injects_into B omegaOne)
    (HG : Γ ≤ is_function (bv_powerset (blockObjects color R)) (bv_powerset omegaTwo) G)
    (Hchoice : Γ ≤ smallTailCandidates color R J E S G)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Hlaw : Γ ≤ tailRunLaw color R B G Tail) :
    Γ ≤ image i (bv_powerset omegaTwo) Tail ⊆ᴮ blockObjects color R := by
  have Hvalues := tailRun_values_objects HCH HB HBsmall HG Hchoice HTail Hlaw
  rw [subset_unfold']
  apply le_iInf
  intro A
  rw [← deduction]
  obtain ⟨j, Hj⟩ := exists_convert ((mem_image_iff.mp
    (show Γ ⊓ A ∈ᴮ image i (bv_powerset omegaTwo) Tail ≤
      A ∈ᴮ image i (bv_powerset omegaTwo) Tail from inf_le_right)).2)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact (le_inf (inf_le_left.trans (Hvalues.trans
    ((iInf_le _ j).trans (iInf_le _ A)))) (Hj.trans inf_le_right)).trans bv_imp_elim

/-- The candidate uses the complete actual earlier image, not the
filtered approximation used to make the update globally bounded. -/
theorem tailRun_candidate_of_pair
    {color : Bool} {R J E S B G Tail i A : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (HBsmall : Γ ≤ injects_into B omegaOne)
    (HG : Γ ≤ is_function (bv_powerset (blockObjects color R)) (bv_powerset omegaTwo) G)
    (Hchoice : Γ ≤ smallTailCandidates color R J E S G)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Hlaw : Γ ≤ tailRunLaw color R B G Tail) (Hpair : Γ ≤ pair i A ∈ᴮ Tail) :
    Γ ≤ blockCandidate color R J E S
      (binary_union B (image i (bv_powerset omegaTwo) Tail)) ∅ A := by
  have Hstep := tailStep_candidate HCH HB HBsmall HG Hchoice HTail
    (mem_domain_of_is_function Hpair HTail)
  have Hvalue : Γ ≤ A =ᴮ tailStep color R B G (image i (bv_powerset omegaTwo) Tail) :=
    imageRecLaw_apply Hlaw Hpair
  have Hcandidate : Γ ≤ blockCandidate color R J E S
      (tailEarlier color R B (image i (bv_powerset omegaTwo) Tail)) ∅ A :=
    bv_rw' (ϕ := blockCandidate color R J E S
      (tailEarlier color R B (image i (bv_powerset omegaTwo) Tail)) ∅) Hvalue
      (h_congr := blockCandidate_ext_object _ _ _ _ _ _ _) (H_new := Hstep)
  have Hearlier : Γ ≤ tailEarlier color R B (image i (bv_powerset omegaTwo) Tail) =ᴮ
      binary_union B (image i (bv_powerset omegaTwo) Tail) :=
    binary_union_congr bv_refl (filteredPast_eq_of_subset
      (tailRun_prefix_subset_objects HCH HB HBsmall HG Hchoice HTail Hlaw))
  exact bv_rw'' (ϕ := fun Earlier => blockCandidate color R J E S Earlier ∅ A)
    Hearlier Hcandidate (blockCandidate_ext_earlier color R J E S ∅ A)

theorem tailRun_candidates {color : Bool} {R J E S B G Tail : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (HBsmall : Γ ≤ injects_into B omegaOne)
    (HG : Γ ≤ is_function (bv_powerset (blockObjects color R)) (bv_powerset omegaTwo) G)
    (Hchoice : Γ ≤ smallTailCandidates color R J E S G)
    (HTail : Γ ≤ is_function bSet.omega (bv_powerset omegaTwo) Tail)
    (Hlaw : Γ ≤ tailRunLaw color R B G Tail) :
    Γ ≤ tailCandidatesLaw color R J E S B Tail := by
  apply le_iInf
  intro i
  apply le_iInf
  intro A
  rw [← deduction]
  have Hcandidate : Γ ⊓ pair i A ∈ᴮ Tail ≤ blockCandidate color R J E S
      (binary_union B (image i (bv_powerset omegaTwo) Tail)) ∅ A :=
    tailRun_candidate_of_pair (inf_le_left.trans HCH)
    (inf_le_left.trans HB) (inf_le_left.trans HBsmall) (inf_le_left.trans HG)
    (inf_le_left.trans Hchoice) (inf_le_left.trans HTail) (inf_le_left.trans Hlaw)
    inf_le_right
  exact le_inf Hcandidate (blockCandidate_nonempty Hcandidate)

/-- Both the selector and the entire tail are constructed here. The
conclusion contains the exact recursion equation and actual successful
candidate at every stored pair; no successful run is a hypothesis. -/
theorem exists_countable_tail
    {color : Bool} {R J I D E S B : bSet 𝔹} {Γ : 𝔹}
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
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R) (HBsmall : Γ ≤ injects_into B omegaOne)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (Hlarge : Γ ≤ injects_into omegaTwo S) :
    ∃ G Tail : bSet 𝔹, Γ ≤
      is_function (bv_powerset (blockObjects color R)) (bv_powerset omegaTwo) G ⊓
      (tailSelectorLaw color R J E S G ⊓
      (is_function bSet.omega (bv_powerset omegaTwo) Tail ⊓
      (tailRunLaw color R B G Tail ⊓ tailCandidatesLaw color R J E S B Tail))) := by
  obtain ⟨G, HG⟩ := exists_tail_selector color R J E S Γ
  have Hchoice := tail_selector_small_candidates HCH Hproper Habsorb Hclosure Hdiag
    HD HDpos Hdense HI HE HElaw Hno HnoOpp HS Hlarge (HG.trans inf_le_left)
    (HG.trans inf_le_right)
  obtain ⟨Tail, HTail⟩ := exists_tail_recursion color R B G (Γ := Γ)
  exact ⟨G, Tail, le_inf (HG.trans inf_le_left) (le_inf (HG.trans inf_le_right)
    (le_inf (HTail.trans inf_le_left) (le_inf (HTail.trans inf_le_right)
      (tailRun_candidates HCH HB HBsmall (HG.trans inf_le_left) Hchoice
        (HTail.trans inf_le_left) (HTail.trans inf_le_right)))))⟩

end bSet.ErdosCountableTailRun
