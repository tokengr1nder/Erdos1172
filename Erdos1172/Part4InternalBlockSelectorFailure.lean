/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalLargeHistoryFiber
public import Erdos1172.Part4InternalBlockCandidateExistence
public import Erdos1172.Part4InternalBlockSelector

@[expose] public section

/-!
# A large family of valid failed selector inputs is impossible

The two internally countable sets actually read by the fixed selector
are frozen on a full-sized terminal fiber. The first set retains whole
block objects; the second retains all current active physical points,
including those chosen at a failed stage. The frozen fiber itself then
witnesses a candidate for those exact inputs, contradicting their empty
output in the original selector graph.

No stationary domain, stopping-stage bound, common ordered history,
externally coherent choice, or successful run is assumed. Normality is
explicit in the final candidate-existence step. The run invariants needed
to produce the pointwise failed inputs are not asserted here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockSelectorFailure

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis
open ErdosCanonicalBlocks ErdosBlockCandidate ErdosBlockCandidateExistence
open ErdosBlockSelector ErdosCountableChoicePoolStep ErdosCountableSubsetCodes
open ErdosLargeHistoryFiber ErdosSmallCodomainPigeonhole

def activeTerminalEdges (color : Bool) (R Active top : bSet 𝔹) : 𝔹 :=
  ⨅ x, _root_.imp (x ∈ᴮ Active) (graphColor (!color) R x top)

theorem activeTerminalEdges_ext_active (color : Bool) (R top : bSet 𝔹) :
    B_ext (fun Active => activeTerminalEdges color R Active top) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))

theorem activeTerminalEdges_ext_terminal (color : Bool) (R Active : bSet 𝔹) :
    B_ext (activeTerminalEdges color R Active) :=
  B_ext_iInf (h := fun x =>
    B_ext_imp (h₁ := B_ext_const) (h₂ := graphColor_ext_right (!color) R x))

theorem activeTerminalEdges_apply {color : Bool} {R Active top x : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ activeTerminalEdges color R Active top) (Hx : Γ ≤ x ∈ᴮ Active) :
    Γ ≤ graphColor (!color) R x top :=
  (le_inf (H.trans (iInf_le _ x)) Hx).trans bv_imp_elim

/-- The label is exactly the pair of selector inputs; no stage, terminal,
cut, or modified future is included in that selector input. -/
def failedLabel (color : Bool) (R F top q : bSet 𝔹) : 𝔹 :=
  ⨆ Earlier, ⨆ Active, q =ᴮ pair Earlier Active ⊓
    (pair q (∅ : bSet 𝔹) ∈ᴮ F ⊓ activeTerminalEdges color R Active top)

theorem failedLabel_ext_terminal (color : Bool) (R F q : bSet 𝔹) :
    B_ext (fun top => failedLabel color R F top q) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun Active =>
    B_ext_inf B_ext_const
      (B_ext_inf B_ext_const (activeTerminalEdges_ext_terminal color R Active))))

theorem failedLabel_ext_label (color : Bool) (R F top : bSet 𝔹) :
    B_ext (failedLabel color R F top) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_inf B_ext_bv_eq_left (B_ext_inf B_ext_pair_mem_left B_ext_const)))

/-- Exact pair decoding is Boolean-extensional, including mixed names. -/
theorem failedLabel_pair_iff
    {color : Bool} {R F top Earlier Active : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ failedLabel color R F top (pair Earlier Active) ↔
      Γ ≤ pair (pair Earlier Active) (∅ : bSet 𝔹) ∈ᴮ F ⊓
        activeTerminalEdges color R Active top := by
  constructor
  · intro H
    apply H.trans
    apply iSup_le
    intro Earlier'
    apply iSup_le
    intro Active'
    exact le_inf (inf_le_right.trans inf_le_left)
      (bv_rw' (ϕ := fun U => activeTerminalEdges color R U top)
        (eq_of_eq_pair_right' inf_le_left)
        (h_congr := activeTerminalEdges_ext_active color R top)
        (H_new := inf_le_right.trans inf_le_right))
  · intro H
    exact le_iSup_of_le Earlier (le_iSup_of_le Active (le_inf bv_refl H))

/-- This is pointwise existence of failed actual inputs, not a supplied
coherent history family. Current active points are part of each input. -/
def allTerminalFailures (color : Bool) (R F B P Y : bSet 𝔹) : 𝔹 :=
  ⨅ top, _root_.imp (top ∈ᴮ Y)
    (⨆ Earlier, ⨆ Active, pair Earlier Active ∈ᴮ choicePoolDomain B P ⊓
      (pair (pair Earlier Active) (∅ : bSet 𝔹) ∈ᴮ F ⊓
        activeTerminalEdges color R Active top))

/-- Both whole histories become fixed on an actual omega-two-large
terminal subfamily. Neither the terminal family nor the pools need be
stationary or ordinal, and no least failure stage is used. -/
theorem exists_large_failed_history
    {color : Bool} {R F B P Y : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HY : Γ ≤ injects_into omegaTwo Y)
    (HB : Γ ≤ injects_into B omegaOne) (HP : Γ ≤ injects_into P omegaOne)
    (Hfail : Γ ≤ allTerminalFailures color R F B P Y) :
    ∃ Earlier Active T : bSet 𝔹,
      (Γ ≤ Earlier ∈ᴮ countableSubsets B) ∧
      (Γ ≤ Active ∈ᴮ countableSubsets P) ∧
      (Γ ≤ T ⊆ᴮ Y) ∧ (Γ ≤ injects_into omegaTwo T) ∧
      (Γ ≤ pair (pair Earlier Active) (∅ : bSet 𝔹) ∈ᴮ F) ∧
      Γ ≤ activeCompatible color R Active T := by
  have Hex : Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ Y)
      (⨆ q, q ∈ᴮ choicePoolDomain B P ⊓ failedLabel color R F top q) := by
    apply le_iInf
    intro top
    rw [← deduction]
    have Hfailed := (le_inf (inf_le_left.trans (Hfail.trans (iInf_le _ top)))
      (show Γ ⊓ top ∈ᴮ Y ≤ top ∈ᴮ Y from inf_le_right)).trans bv_imp_elim
    apply Hfailed.trans
    apply iSup_le
    intro Earlier
    apply iSup_le
    intro Active
    exact le_iSup_of_le (pair Earlier Active) (le_inf inf_le_left
      (failedLabel_pair_iff.mpr inf_le_right))
  obtain ⟨q, T, Hq, HTY, HTlarge, Hfixed⟩ := exists_large_constant_label
    HCH HY (choicePoolDomain_injects_omegaOne HCH HB HP)
    (failedLabel_ext_terminal color R F) (failedLabel_ext_label color R F) Hex
  obtain ⟨Earlier, HEarlier, Active, HActive, Hqeq⟩ := mem_prod_iff₂.mp Hq
  have HfixedPair : Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ T)
      (pair (pair Earlier Active) (∅ : bSet 𝔹) ∈ᴮ F ⊓
        activeTerminalEdges color R Active top) := by
    apply le_iInf
    intro top
    rw [← deduction]
    have Hlocal : Γ ⊓ top ∈ᴮ T ≤ failedLabel color R F top q :=
      (le_inf (inf_le_left.trans (Hfixed.trans (iInf_le _ top))) inf_le_right).trans bv_imp_elim
    exact failedLabel_pair_iff.mp
      (bv_rw'' (ϕ := failedLabel color R F top) (inf_le_left.trans Hqeq)
        Hlocal (failedLabel_ext_label color R F top))
  obtain ⟨top, Htop⟩ := exists_mem_of_injects_into HTlarge omegaOne_mem_omegaTwo
  have Hempty := ((le_inf (HfixedPair.trans (iInf_le _ top)) Htop).trans bv_imp_elim).trans
    inf_le_left
  refine ⟨Earlier, Active, T, HEarlier, HActive, HTY, HTlarge, Hempty, ?_⟩
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  have Hterminal : Γ ⊓ (x ∈ᴮ Active ⊓ y ∈ᴮ T) ≤
      activeTerminalEdges color R Active y :=
    ((le_inf (inf_le_left.trans (HfixedPair.trans (iInf_le _ y)))
      (inf_le_right.trans inf_le_right)).trans bv_imp_elim).trans inf_le_right
  exact activeTerminalEdges_apply Hterminal (inf_le_right.trans inf_le_left)

/-- A fixed selector cannot output empty for a large family of valid
countable histories whose active points all see their own terminal.
The terminal fiber witnesses a candidate in the original future `S`.
The normality hypothesis is explicit and is used by candidate existence. -/
theorem all_terminal_failures_false
    {color : Bool} {R J I D E S F B P Y : bSet 𝔹} {Γ : 𝔹}
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
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (HBsmall : Γ ≤ injects_into B omegaOne) (HPsmall : Γ ≤ injects_into P omegaOne)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HY : Γ ≤ Y ⊆ᴮ S)
    (HYlarge : Γ ≤ injects_into omegaTwo Y)
    (Hfail : Γ ≤ allTerminalFailures color R F B P Y) : Γ ≤ ⊥ := by
  obtain ⟨Earlier, Active, T, HEarlier, _, HTY, HTlarge, Hempty, Hactive⟩ :=
    exists_large_failed_history HCH HYlarge HBsmall HPsmall Hfail
  have HEarlierSub := (mem_countableSubsets_iff.mp HEarlier).1
  obtain ⟨A, HA⟩ := exists_candidate_of_large_active_future
    HCH Hproper Habsorb Hclosure Hdiag HD HDpos Hdense HI HE HElaw
    (subset_trans' HEarlierSub HB)
    (injects_into_trans (injects_into_of_subset HEarlierSub) HBsmall)
    Hno HnoOpp (subset_trans' HTY (subset_trans' HY HS)) HTlarge
    (subset_trans' HTY HY) Hactive
  have Hnone : Γ ≤ (⨆ A, blockCandidate color R J E S Earlier Active A)ᶜ :=
    (selected_empty_iff_no_candidate HF HFlaw Hempty).mp bv_refl
  exact bv_absurd _ (le_iSup_of_le A HA) Hnone

end bSet.ErdosBlockSelectorFailure
