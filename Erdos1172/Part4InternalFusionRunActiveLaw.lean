/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionPrefixCoherence
public import Erdos1172.Part4InternalFusionMaskedTailCross

@[expose] public section

/-!
# Inclusive activity of the actual fusion coordinates

Every stored active set is contained in every later stored active set.
The current physical points belong to the active set stored at that
very stage, before its block is selected. The actual candidate-or-empty
law therefore gives opposite-color edges into the entire same-stage or
later block. Empty target blocks are handled by vacuity.

The final law is for the actual full decoded block and coordinate
graphs, not supplied mask compatibility. No successful-run, ideal,
pool, terminal adjacency, or cardinal assumption is needed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRunActiveLaw

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosBoundedFunctionValue
open ErdosFusionEntrySpace ErdosFusionRun ErdosFusionHistories ErdosFusionActiveHistory
open ErdosTaggedPrefix ErdosFusionPrefixCoherence ErdosFusionRunLocalStep
open ErdosFusionRowCandidates ErdosFusionMaskedTail ErdosPartition ErdosBlockCandidate
open ErdosBlockSelector ErdosCountableChoicePoolStep

/-- An actual member of the bounded evaluator's value forces its input
into the actual function domain. This handles an unguarded source row
without assuming that an empty/failure source block was successful. -/
theorem graphValue_input_mem_of_mem {D V F a x : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function D V F) (Hx : Γ ≤ x ∈ᴮ graphValue V F a) :
    Γ ≤ a ∈ᴮ D := by
  obtain ⟨y, Hy⟩ := exists_convert (mem_bv_union_iff.mp Hx)
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  obtain ⟨b, Hb⟩ := exists_convert (mem_image_iff.mp (Hy.trans inf_le_left)).2
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact mem_congr (eq_mem_singleton (Hb.trans inf_le_left)) bv_refl
    (mem_domain_of_is_function (Hb.trans inf_le_right) HF)

theorem fusion_run_active_subset
    {color : Bool} {R E F top Run i j A Z U C W V : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hi : Γ ≤ pair i (pair i (entry A Z U)) ∈ᴮ Run)
    (Hj : Γ ≤ pair j (pair j (entry C W V)) ∈ᴮ Run)
    (Hij : Γ ≤ i ∈ᴮ j) : Γ ≤ U ⊆ᴮ V := by
  let T := taggedPrefix j omegaOne entrySpace Run
  have Hjcut : Γ ≤ j ⊆ᴮ omegaOne :=
    subset_of_mem_Ord (mem_domain_of_is_function Hj HRun) omegaOne_Ord
  have HT : Γ ≤ is_function j entrySpace T := fusion_prefix_is_function HRun Hlaw Hjcut
  have Hentry : Γ ≤ pair i (entry A Z U) ∈ᴮ T :=
    (mem_taggedPrefix_pair_iff HRun (fusion_run_tagging HRun Hlaw)).mpr ⟨Hij, Hi⟩
  have Hactive : Γ ≤ pair i U ∈ᴮ activeFamily T := activeFamily_pair Hjcut HT Hentry
  have Himage : Γ ≤ U ∈ᴮ image j (bv_powerset omegaTwo) (activeFamily T) :=
    mem_image Hactive Hij (mem_codomain_of_is_function Hactive (activeFamily_is_function Hjcut HT))
  have Hsub : Γ ≤ U ⊆ᴮ previousActive j (activeFamily T) := by
    rw [subset_unfold']
    apply le_iInf
    intro x
    rw [← deduction]
    exact mem_bv_union_iff.mpr (le_iSup_of_le U
      (le_inf (inf_le_left.trans Himage) inf_le_right))
  have HV : Γ ≤ V =ᴮ nextActive color R E top j T :=
    eq_of_eq_pair_right' (eq_of_eq_pair_right' (fusion_run_entry_eq Hlaw Hj))
  exact subset_trans' Hsub (subset_trans'
    (previousActive_subset_activeHistory (color := color) (R := R) (E := E)
      (ξ := j) (Blocks := blockHistory T) (Z := nextIndices color R E top j T)
      (Acts := activeFamily T)) (subset_of_eq (bv_symm HV)))

/-- Equality and strict extension are Boolean alternatives; no external
choice between them or shrinking of the condition occurs. -/
theorem fusion_run_active_subset_of_le
    {color : Bool} {R E F top Run i j A Z U C W V : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hi : Γ ≤ pair i (pair i (entry A Z U)) ∈ᴮ Run)
    (Hj : Γ ≤ pair j (pair j (entry C W V)) ∈ᴮ Run)
    (Hij : Γ ≤ i =ᴮ j ⊔ i ∈ᴮ j) : Γ ≤ U ⊆ᴮ V := by
  apply (le_inf (le_refl Γ) Hij).trans
  rw [inf_sup_left]
  apply sup_le
  · exact subset_of_eq (eq_of_eq_pair_right' (eq_of_eq_pair_right' (eq_of_eq_pair_right'
      (eq_of_is_function_of_eq (inf_le_left.trans HRun) inf_le_right
        (inf_le_left.trans Hi) (inf_le_left.trans Hj)))))
  · exact fusion_run_active_subset (inf_le_left.trans HRun) (inf_le_left.trans Hlaw)
      (inf_le_left.trans Hi) (inf_le_left.trans Hj) inf_le_right

/-- A point of the original canonical row at the actual stored
coordinate lies in the active set stored at that same stage. -/
theorem fusion_run_selected_point_mem_active
    {color : Bool} {R E F top Run ξ A Z U ν b v x : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run)
    (Hνξ : Γ ≤ ν ∈ᴮ ξ)
    (Hνb : Γ ≤ pair ν b ∈ᴮ blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
    (Hνv : Γ ≤ pair ν v ∈ᴮ Z)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b) : Γ ≤ x ∈ᴮ U := by
  let T := taggedPrefix ξ omegaOne entrySpace Run
  let Blocks := blockHistory T
  let Indices := nextIndices color R E top ξ T
  have Hξcut : Γ ≤ ξ ⊆ᴮ omegaOne :=
    subset_of_mem_Ord (mem_domain_of_is_function Hentry HRun) omegaOne_Ord
  have HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks :=
    blockHistory_is_function Hξcut (fusion_prefix_is_function HRun Hlaw Hξcut)
  have Hb : Γ ≤ b ∈ᴮ blockObjects color R := graphValue_input_mem_of_mem HE Hvx
  have Hbeq : Γ ≤ blockValue Blocks ν =ᴮ b := graphValue_eq_of_pair HBlocks Hνb
  have Hactive : Γ ≤ ν ∈ᴮ successfulRows color R ξ Blocks :=
    mem_successfulRows_iff.mpr ⟨Hνξ, mem_congr (bv_symm Hbeq) bv_refl Hb⟩
  have Hentryeq := fusion_run_entry_eq Hlaw Hentry
  have HZ : Γ ≤ Z =ᴮ Indices := eq_of_eq_pair_left' (eq_of_eq_pair_right' Hentryeq)
  have HU : Γ ≤ U =ᴮ nextActive color R E top ξ T :=
    eq_of_eq_pair_right' (eq_of_eq_pair_right' Hentryeq)
  have Hpoint : Γ ≤ currentPoint E Blocks Indices ν =ᴮ x :=
    currentPoint_eq_of_pairs HE HElaw HBlocks nextIndices_is_function Hνb
      (canonicalRow_pair HE Hb) (mem_congr bv_refl HZ Hνv) Hvx
  have Hcurrent : Γ ≤ x ∈ᴮ currentPoints color R E ξ Blocks Indices :=
    mem_congr Hpoint bv_refl
      (currentPoint_mem_currentPoints HE HElaw nextIndices_is_function Hξcut Hactive)
  have Hnext : Γ ≤ x ∈ᴮ nextActive color R E top ξ T :=
    mem_of_mem_subset currentPoints_subset_activeHistory Hcurrent
  exact mem_congr bv_refl (bv_symm HU) Hnext

theorem fusion_run_selected_point_mem_later_active
    {color : Bool} {R E F top Run ξ μ A Z U C W V ν b v x : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hξentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run)
    (Hμentry : Γ ≤ pair μ (pair μ (entry C W V)) ∈ᴮ Run)
    (Hξμ : Γ ≤ ξ =ᴮ μ ⊔ ξ ∈ᴮ μ)
    (Hνξ : Γ ≤ ν ∈ᴮ ξ)
    (Hνb : Γ ≤ pair ν b ∈ᴮ blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
    (Hνv : Γ ≤ pair ν v ∈ᴮ Z)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b) : Γ ≤ x ∈ᴮ V :=
  mem_of_mem_subset (fusion_run_active_subset_of_le HRun Hlaw Hξentry Hμentry Hξμ)
    (fusion_run_selected_point_mem_active HE HElaw HRun Hlaw Hξentry Hνξ Hνb Hνv Hvx)

/-- The candidate branch supplies its active compatibility; the empty
branch has no target point. This uses neither success nor nonemptiness. -/
theorem fusion_run_active_cross_block
    {color : Bool} {R J E S F top Run μ C W V x y : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hentry : Γ ≤ pair μ (pair μ (entry C W V)) ∈ᴮ Run)
    (Hx : Γ ≤ x ∈ᴮ V) (Hy : Γ ≤ y ∈ᴮ C) : Γ ≤ graphColor (!color) R x y := by
  have Hcases := fusion_run_stored_block_candidate_or_empty HE HElaw HF HFlaw HRun Hlaw Hentry
  apply (le_inf (le_refl Γ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact activeCompatible_apply (blockCandidate_active inf_le_right)
      (inf_le_left.trans Hx) (inf_le_left.trans Hy)
  · exact (bot_of_mem_empty (mem_congr bv_refl inf_le_right (inf_le_left.trans Hy))).trans bot_le

theorem fusion_run_selected_point_cross_later_block
    {color : Bool} {R J E S F top Run ξ μ A Z U C W V ν b v x y : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hξentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run)
    (Hμentry : Γ ≤ pair μ (pair μ (entry C W V)) ∈ᴮ Run)
    (Hξμ : Γ ≤ ξ =ᴮ μ ⊔ ξ ∈ᴮ μ)
    (Hνξ : Γ ≤ ν ∈ᴮ ξ)
    (Hνb : Γ ≤ pair ν b ∈ᴮ blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
    (Hνv : Γ ≤ pair ν v ∈ᴮ Z)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b) (Hy : Γ ≤ y ∈ᴮ C) :
    Γ ≤ graphColor (!color) R x y :=
  fusion_run_active_cross_block HE HElaw HF HFlaw HRun Hlaw Hμentry
    (fusion_run_selected_point_mem_later_active HE HElaw HRun Hlaw Hξentry Hμentry
      Hξμ Hνξ Hνb Hνv Hvx) Hy

/-- The abstract inclusive law is now proved for the actual full decoded
histories. Its equality branch includes the current selected block. -/
theorem fusion_run_inclusiveActiveLaw
    {color : Bool} {R J E S F top Run : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ inclusiveActiveLaw (!color) R E
      (blockHistory (taggedPrefix omegaOne omegaOne entrySpace Run))
      (coordinateHistory (taggedPrefix omegaOne omegaOne entrySpace Run)) := by
  apply le_iInf
  intro ν
  apply le_iInf
  intro ξ
  apply le_iInf
  intro μ
  apply le_iInf
  intro b
  apply le_iInf
  intro c
  apply le_iInf
  intro v
  rw [← deduction]
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let T := taggedPrefix omegaOne omegaOne entrySpace Run
  let Δ := (Γ ⊓ ((ν ∈ᴮ ξ ⊓ ξ ∈ᴮ omegaOne) ⊓
    ((ξ =ᴮ μ ⊔ ξ ∈ᴮ μ) ⊓ (pair ν b ∈ᴮ blockHistory T ⊓
      (pair μ c ∈ᴮ blockHistory T ⊓ pair (pair ξ ν) v ∈ᴮ coordinateHistory T))))) ⊓
    (pair v x ∈ᴮ canonicalRow E b ⊓ y ∈ᴮ c)
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Hνξ : Δ ≤ ν ∈ᴮ ξ := inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have Hξ : Δ ≤ ξ ∈ᴮ omegaOne :=
    inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have Hξμ : Δ ≤ ξ =ᴮ μ ⊔ ξ ∈ᴮ μ :=
    inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have Hνb : Δ ≤ pair ν b ∈ᴮ blockHistory T :=
    inf_le_left.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
  have Hμc : Δ ≤ pair μ c ∈ᴮ blockHistory T :=
    inf_le_left.trans (inf_le_right.trans (inf_le_right.trans
      (inf_le_right.trans (inf_le_right.trans inf_le_left))))
  have Hcoord : Δ ≤ pair (pair ξ ν) v ∈ᴮ coordinateHistory T :=
    inf_le_left.trans (inf_le_right.trans (inf_le_right.trans
      (inf_le_right.trans (inf_le_right.trans inf_le_right))))
  obtain ⟨A, Z, U, Hξentry, Hνv⟩ := coordinateHistory_witness Hcoord
  obtain ⟨W, V, Hμentry⟩ := blockHistory_witness Hμc
  have Htag : Δ ≤ taggingLaw entrySpace Run := HΔ.trans (fusion_run_tagging HRun Hlaw)
  have Hrawξ := ((mem_taggedPrefix_pair_iff (HΔ.trans HRun) Htag).mp Hξentry).2
  have Hrawμ := ((mem_taggedPrefix_pair_iff (HΔ.trans HRun) Htag).mp Hμentry).2
  have Hνprefix : Δ ≤ pair ν b ∈ᴮ blockHistory (taggedPrefix ξ omegaOne entrySpace Run) :=
    (blockHistory_pair_coherent (HΔ.trans HRun) (HΔ.trans Hlaw)
      (subset_of_mem_Ord Hξ omegaOne_Ord) subset_self Hνξ).mp Hνb
  exact fusion_run_selected_point_cross_later_block (HΔ.trans HE) (HΔ.trans HElaw)
    (HΔ.trans HF) (HΔ.trans HFlaw) (HΔ.trans HRun) (HΔ.trans Hlaw)
    Hrawξ Hrawμ Hξμ Hνξ Hνprefix Hνv
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)

end bSet.ErdosFusionRunActiveLaw
