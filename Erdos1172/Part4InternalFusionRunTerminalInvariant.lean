/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRunRowLegality
public import Erdos1172.Part4InternalImageRecursionInvariant

@[expose] public section

/-!
# Terminal adjacency of the entire actual active history

The invariant includes all earlier active sets and every physical point
selected at the current stage, whether the current block succeeds or
fails. Internal ordinal induction constructs the invariant on the actual
tagged run. Neither the invariant nor a successful block is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRunTerminalInvariant

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosCanonicalBlocks ErdosPartition
open ErdosFusionEntrySpace ErdosFusionRun ErdosFusionActiveHistory
open ErdosTaggedPrefix ErdosImageRecursionInvariant ErdosFusionRunRowLegality
open ErdosClosedSelectorHull ErdosClosedPoolFuture ErdosBlockSelector ErdosCountableChoicePoolStep

def terminalAdjacent (color : Bool) (R top U : bSet 𝔹) : 𝔹 :=
  ⨅ x, _root_.imp (x ∈ᴮ U) (graphColor (!color) R x top)

theorem terminalAdjacent_ext (color : Bool) (R top : bSet 𝔹) :
    B_ext (terminalAdjacent color R top) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))

theorem terminalAdjacent_apply {color : Bool} {R top U x : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ terminalAdjacent color R top U) (Hx : Γ ≤ x ∈ᴮ U) :
    Γ ≤ graphColor (!color) R x top :=
  (le_inf (H.trans (iInf_le _ x)) Hx).trans bv_imp_elim

theorem terminalAdjacent_binary_union {color : Bool} {R top U V : bSet 𝔹} {Γ : 𝔹}
    (HU : Γ ≤ terminalAdjacent color R top U)
    (HV : Γ ≤ terminalAdjacent color R top V) :
    Γ ≤ terminalAdjacent color R top (binary_union U V) := by
  apply le_iInf
  intro x
  rw [← deduction, mem_binary_union, inf_sup_left]
  exact sup_le (terminalAdjacent_apply (inf_le_left.trans HU) inf_le_right)
    (terminalAdjacent_apply (inf_le_left.trans HV) inf_le_right)

def terminalActiveState (color : Bool) (R top q : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ A, ⨅ Z, ⨅ U, _root_.imp (q =ᴮ pair i (entry A Z U))
    (terminalAdjacent color R top U)

theorem terminalActiveState_ext (color : Bool) (R top : bSet 𝔹) :
    B_ext (terminalActiveState color R top) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_bv_eq_left) (h₂ := B_ext_const)))))

theorem terminalActiveState_apply {color : Bool} {R top i A Z U : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ terminalActiveState color R top (pair i (entry A Z U))) :
    Γ ≤ terminalAdjacent color R top U :=
  (le_inf (H.trans ((iInf_le _ i).trans ((iInf_le _ A).trans
    ((iInf_le _ Z).trans (iInf_le _ U))))) bv_refl).trans bv_imp_elim

theorem terminalActiveState_of_entry {color : Bool} {R top i A Z U : bSet 𝔹} {Γ : 𝔹}
    (HU : Γ ≤ terminalAdjacent color R top U) :
    Γ ≤ terminalActiveState color R top (pair i (entry A Z U)) := by
  apply le_iInf
  intro j
  apply le_iInf
  intro B
  apply le_iInf
  intro W
  apply le_iInf
  intro V
  rw [← deduction]
  exact bv_rw'' (ϕ := terminalAdjacent color R top)
    (eq_of_eq_pair_right' (eq_of_eq_pair_right' (eq_of_eq_pair_right' inf_le_right)))
    (inf_le_left.trans HU) (terminalAdjacent_ext color R top)

/-- Membership in the actual union is decoded through the actual image
and then the actual stored entry, all at the same Boolean condition. -/
theorem previousActive_terminal_of_allGood
    {color : Bool} {R top ξ T : bSet 𝔹} {Γ : 𝔹}
    (Hgood : Γ ≤ allGood (terminalActiveState color R top) T) :
    Γ ≤ terminalAdjacent color R top (previousActive ξ (activeFamily T)) := by
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ previousActive ξ (activeFamily T)
  obtain ⟨U, HU⟩ := exists_convert (mem_bv_union_iff.mp
    (show Δ ≤ x ∈ᴮ bv_union (image ξ (bv_powerset omegaTwo) (activeFamily T)) from
      inf_le_right)) (B_ext_inf B_ext_mem_left B_ext_mem_right)
  obtain ⟨i, Hi⟩ := exists_convert (mem_image_iff.mp (HU.trans inf_le_left)).2
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  obtain ⟨A, Z, Hentry⟩ := activeFamily_witness (Hi.trans inf_le_right)
  exact terminalAdjacent_apply
    (terminalActiveState_apply (allGood_apply (inf_le_left.trans Hgood) Hentry))
    (HU.trans inf_le_right)

/-- The new current points satisfy terminal adjacency by row legality.
Only previous active entries are supplied by the induction hypothesis. -/
theorem fusion_terminal_invariant_step
    {color : Bool} {R J E S F B P Y top Run : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (Hseeds : Γ ≤ poolSeedLaw color R J E B Y) (Htop : Γ ≤ top ∈ᴮ Y)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ imageRecInvariantStep omegaOne runSpace
      (fun i T => pair i (nextEntry color R E F top i T)) Run
      (terminalActiveState color R top) := by
  apply le_iInf
  intro i
  rw [← deduction]
  let Δ := Γ ⊓ (i ∈ᴮ omegaOne ⊓
    allGood (terminalActiveState color R top) (image i runSpace Run))
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hi : Δ ≤ i ∈ᴮ omegaOne := inf_le_right.trans inf_le_left
  have Hgood : Δ ≤ allGood (terminalActiveState color R top)
      (taggedPrefix i omegaOne entrySpace Run) := inf_le_right.trans inf_le_right
  have Hcurrent : Δ ≤ terminalAdjacent color R top
      (ErdosFusionHistories.currentPoints color R E i
        (blockHistory (taggedPrefix i omegaOne entrySpace Run))
        (nextIndices color R E top i (taggedPrefix i omegaOne entrySpace Run))) :=
    fusion_run_currentPoints_terminal (HΔ.trans HJ) (HΔ.trans Habsorb) (HΔ.trans Hclosure)
      (HΔ.trans HE) (HΔ.trans HElaw) (HΔ.trans HF) (HΔ.trans HFlaw)
      (HΔ.trans Hhull) (HΔ.trans Hseeds) (HΔ.trans Htop) (HΔ.trans HRun) (HΔ.trans Hlaw) Hi
  exact terminalActiveState_of_entry
    (terminalAdjacent_binary_union (previousActive_terminal_of_allGood Hgood) Hcurrent)

/-- Every stored active set, including at a failed current block stage,
has the required edge to the terminal. This invariant is proved, not assumed. -/
theorem fusion_run_active_terminal
    {color : Bool} {R J E S F B P Y top Run ξ A Z U : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (Hseeds : Γ ≤ poolSeedLaw color R J E B Y) (Htop : Γ ≤ top ∈ᴮ Y)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run) :
    Γ ≤ terminalAdjacent color R top U :=
  terminalActiveState_apply
    (good_of_imageRecLaw_pair omegaOne_Ord HRun Hlaw (terminalActiveState_ext color R top)
      (fusion_terminal_invariant_step HJ Habsorb Hclosure HE HElaw HF HFlaw Hhull Hseeds Htop
        HRun Hlaw) Hentry)

theorem fusion_run_active_terminal_apply
    {color : Bool} {R J E S F B P Y top Run ξ A Z U x : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (Hhull : Γ ≤ closedHullData color R F B P)
    (Hseeds : Γ ≤ poolSeedLaw color R J E B Y) (Htop : Γ ≤ top ∈ᴮ Y)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run) (Hx : Γ ≤ x ∈ᴮ U) :
    Γ ≤ graphColor (!color) R x top :=
  terminalAdjacent_apply
    (fusion_run_active_terminal HJ Habsorb Hclosure HE HElaw HF HFlaw Hhull Hseeds Htop
      HRun Hlaw Hentry) Hx

end bSet.ErdosFusionRunTerminalInvariant
