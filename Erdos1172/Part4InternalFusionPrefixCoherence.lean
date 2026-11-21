/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRunLocalStep
public import Erdos1172.Part4InternalFusionSeedBridge

@[expose] public section

/-!
# Exact coherence of the actual ordered fusion prefixes

All prefix names are the actual tagged images of the same run. Their
decoded blocks, active sets, and coordinates agree on a smaller domain;
no independently chosen restriction graphs or coherence premise occurs.
The generic comparison assumes inclusion of the smaller index set, not
mere membership in an arbitrary nontransitive larger index set.

At an actual ordinal stage, this identifies every stored candidate's
strict earlier history with the corresponding image of the later block
graph. Thus the existing actual stored candidate-or-empty law supplies
the structural `storedBlockCandidates` premise for the row seed bridge.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionPrefixCoherence

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
variable {color : Bool} {R E F top Run : bSet 𝔹} {Γ : 𝔹}

open ErdosOmegaTwo ErdosTaggedPrefix ErdosFusionEntrySpace ErdosFusionRun
open ErdosFusionHistories ErdosFusionActiveHistory ErdosFusionRunLocalStep
open ErdosCanonicalBlocks ErdosCountableChoicePoolStep ErdosBlockSelector
open ErdosBlockCandidate ErdosFusionSeedBridge

theorem taggedPrefix_pair_coherent {j ξ i q : bSet 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hjξ : Γ ≤ j ⊆ᴮ ξ) (Hi : Γ ≤ i ∈ᴮ j) :
    (Γ ≤ pair i q ∈ᴮ taggedPrefix ξ omegaOne entrySpace Run) ↔
      Γ ≤ pair i q ∈ᴮ taggedPrefix j omegaOne entrySpace Run := by
  have Htag := fusion_run_tagging HRun Hlaw
  constructor
  · intro Hpair
    exact (mem_taggedPrefix_pair_iff HRun Htag).mpr
      ⟨Hi, ((mem_taggedPrefix_pair_iff HRun Htag).mp Hpair).2⟩
  · intro Hpair
    exact (mem_taggedPrefix_pair_iff HRun Htag).mpr
      ⟨mem_of_mem_subset Hjξ Hi, ((mem_taggedPrefix_pair_iff HRun Htag).mp Hpair).2⟩

theorem blockHistory_pair_coherent {j ξ i A : bSet 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hjξ : Γ ≤ j ⊆ᴮ ξ) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (Hi : Γ ≤ i ∈ᴮ j) :
    (Γ ≤ pair i A ∈ᴮ blockHistory (taggedPrefix ξ omegaOne entrySpace Run)) ↔
      Γ ≤ pair i A ∈ᴮ blockHistory (taggedPrefix j omegaOne entrySpace Run) := by
  have Hj : Γ ≤ j ⊆ᴮ omegaOne := subset_trans' Hjξ Hξ
  constructor
  · intro Hpair
    obtain ⟨Z, U, Hentry⟩ := blockHistory_witness Hpair
    exact blockHistory_pair Hj (fusion_prefix_is_function HRun Hlaw Hj)
      ((taggedPrefix_pair_coherent HRun Hlaw Hjξ Hi).mp Hentry)
  · intro Hpair
    obtain ⟨Z, U, Hentry⟩ := blockHistory_witness Hpair
    exact blockHistory_pair Hξ (fusion_prefix_is_function HRun Hlaw Hξ)
      ((taggedPrefix_pair_coherent HRun Hlaw Hjξ Hi).mpr Hentry)

theorem coordinateHistory_pair_coherent {j ξ i ν v : bSet 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hjξ : Γ ≤ j ⊆ᴮ ξ) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (Hi : Γ ≤ i ∈ᴮ j) :
    (Γ ≤ pair (pair i ν) v ∈ᴮ coordinateHistory (taggedPrefix ξ omegaOne entrySpace Run)) ↔
      Γ ≤ pair (pair i ν) v ∈ᴮ coordinateHistory (taggedPrefix j omegaOne entrySpace Run) := by
  have Hj : Γ ≤ j ⊆ᴮ omegaOne := subset_trans' Hjξ Hξ
  constructor
  · intro Hpair
    obtain ⟨A, Z, U, Hentry, Hv⟩ := coordinateHistory_witness Hpair
    have HZ : Γ ≤ is_function omegaOne omegaOne Z :=
      rowFunctions_apply (fusion_prefix_rowFunctions HRun Hlaw) Hentry
    exact coordinateHistory_pair Hj (fusion_prefix_is_function HRun Hlaw Hj)
      ((taggedPrefix_pair_coherent HRun Hlaw Hjξ Hi).mp Hentry) HZ Hv
  · intro Hpair
    obtain ⟨A, Z, U, Hentry, Hv⟩ := coordinateHistory_witness Hpair
    have HZ : Γ ≤ is_function omegaOne omegaOne Z :=
      rowFunctions_apply (fusion_prefix_rowFunctions HRun Hlaw) Hentry
    exact coordinateHistory_pair Hξ (fusion_prefix_is_function HRun Hlaw Hξ)
      ((taggedPrefix_pair_coherent HRun Hlaw Hjξ Hi).mpr Hentry) HZ Hv

private theorem image_eq_of_guarded_pair_iff {D C f g : bSet 𝔹}
    (Hpair : ∀ (i x : bSet 𝔹) (Δ : 𝔹), Δ ≤ Γ → Δ ≤ i ∈ᴮ D →
      ((Δ ≤ pair i x ∈ᴮ f) ↔ Δ ≤ pair i x ∈ᴮ g)) :
    Γ ≤ image D C f =ᴮ image D C g := by
  apply mem_ext
  · apply le_iInf
    intro x
    rw [← deduction]
    let Δ := Γ ⊓ x ∈ᴮ image D C f
    have Hx := mem_image_iff.mp (show Δ ≤ x ∈ᴮ image D C f from inf_le_right)
    obtain ⟨i, Hi⟩ := exists_convert Hx.2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_image ((Hpair i x Δ inf_le_left (Hi.trans inf_le_left)).mp
      (Hi.trans inf_le_right)) (Hi.trans inf_le_left) Hx.1
  · apply le_iInf
    intro x
    rw [← deduction]
    let Δ := Γ ⊓ x ∈ᴮ image D C g
    have Hx := mem_image_iff.mp (show Δ ≤ x ∈ᴮ image D C g from inf_le_right)
    obtain ⟨i, Hi⟩ := exists_convert Hx.2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_image ((Hpair i x Δ inf_le_left (Hi.trans inf_le_left)).mpr
      (Hi.trans inf_le_right)) (Hi.trans inf_le_left) Hx.1

theorem blockHistory_image_coherent {j ξ : bSet 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hjξ : Γ ≤ j ⊆ᴮ ξ) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) :
    Γ ≤ image j (bv_powerset omegaTwo) (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
      =ᴮ image j (bv_powerset omegaTwo) (blockHistory (taggedPrefix j omegaOne entrySpace Run)) :=
  image_eq_of_guarded_pair_iff (fun _ _ _ HΔ Hi =>
    blockHistory_pair_coherent (HΔ.trans HRun) (HΔ.trans Hlaw) (HΔ.trans Hjξ) (HΔ.trans Hξ) Hi)

/-- The exact whole-object history computed from a longer decoded graph
agrees with the history originally used at the smaller stage. -/
theorem earlierHistory_prefix_coherent {j ξ : bSet 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hjξ : Γ ≤ j ⊆ᴮ ξ) (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) :
    Γ ≤ earlierHistory color R j (blockHistory (taggedPrefix ξ omegaOne entrySpace Run)) =ᴮ
      earlierHistory color R j (blockHistory (taggedPrefix j omegaOne entrySpace Run)) :=
  B_congr_comprehend (ϕ := fun A => A ∈ᴮ blockObjects color R) (H_congr := B_ext_mem_left)
    (blockHistory_image_coherent HRun Hlaw Hjξ Hξ)

/-- At real run stages, transitivity of the ordinal xi supplies the
smaller-prefix inclusion. Membership alone in a general set would not. -/
theorem earlierHistory_prefix_coherent_of_mem {j ξ : bSet 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hjξ : Γ ≤ j ∈ᴮ ξ) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) :
    Γ ≤ earlierHistory color R j (blockHistory (taggedPrefix ξ omegaOne entrySpace Run)) =ᴮ
      earlierHistory color R j (blockHistory (taggedPrefix j omegaOne entrySpace Run)) :=
  earlierHistory_prefix_coherent HRun Hlaw
    (subset_of_mem_Ord Hjξ (Ord_of_mem_Ord Hξ omegaOne_Ord))
    (subset_of_mem_Ord Hξ omegaOne_Ord)

/-- Every stored candidate in the later actual prefix has the exact
earlier history used by its own recursion equation. No coherent-history
or candidate-law premise is assumed for this conclusion. -/
theorem fusion_prefix_storedBlockCandidates {J S ξ : bSet 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) :
    Γ ≤ storedBlockCandidates color R J E S ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run)) := by
  apply le_iInf
  intro j
  apply le_iInf
  intro c
  rw [← deduction]
  let Δ := Γ ⊓ (j ∈ᴮ ξ ⊓ pair j c ∈ᴮ blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hj : Δ ≤ j ∈ᴮ ξ := inf_le_right.trans inf_le_left
  obtain ⟨Z, U, Hentry⟩ := blockHistory_witness
    (show Δ ≤ pair j c ∈ᴮ blockHistory (taggedPrefix ξ omegaOne entrySpace Run) from
      inf_le_right.trans inf_le_right)
  have Hactual := ((mem_taggedPrefix_pair_iff (HΔ.trans HRun)
    (HΔ.trans (fusion_run_tagging HRun Hlaw))).mp Hentry).2
  have Hstored := fusion_run_stored_block_candidate_or_empty
    (HΔ.trans HE) (HΔ.trans HElaw) (HΔ.trans HF) (HΔ.trans HFlaw)
    (HΔ.trans HRun) (HΔ.trans Hlaw) Hactual
  have Hearlier := earlierHistory_prefix_coherent_of_mem
    (HΔ.trans HRun) (HΔ.trans Hlaw) Hj (HΔ.trans Hξ)
  have Htransport : Δ ≤ blockCandidate color R J E S
      (earlierHistory color R j (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))) U c ⊔
      c =ᴮ (∅ : bSet 𝔹) :=
    bv_rw' (ϕ := fun Earlier => blockCandidate color R J E S Earlier U c ⊔
      c =ᴮ (∅ : bSet 𝔹)) Hearlier
      (h_congr := B_ext_sup (h₁ := blockCandidate_ext_earlier color R J E S U c)
        (h₂ := B_ext_const)) (H_new := Hstored)
  have Hinto : blockCandidate color R J E S
      (earlierHistory color R j (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))) U c ≤
      ⨆ Active, blockCandidate color R J E S
        (earlierHistory color R j (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))) Active c :=
    le_iSup_of_le U le_rfl
  exact Htransport.trans (sup_le (Hinto.trans le_sup_right) le_sup_left)

end bSet.ErdosFusionPrefixCoherence
