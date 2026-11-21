/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRunFailure

@[expose] public section

/-!
# An actual full fusion run with no empty block

Success is the complement of the internal existence of an empty stored
entry. On the complementary condition to the existence of a successful
terminal and run, the unconditional recursion constructs a full run at
each terminal. Its empty entry supplies the exact failed selector input.
The already established all-terminal failure contradiction then applies.

Boolean joins are not converted into external choices of a case or a
failure stage. Fullness is used only with proved extensional predicates
to obtain an actual terminal and actual full run at the original condition.
This is a nonstopping fusion run, not yet the final partition relation or
an ideal/model construction.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRunSuccess

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosDenseBasis ErdosPartition ErdosCanonicalBlocks
open ErdosBlockCandidate ErdosBlockSelector ErdosCountableChoicePoolStep
open ErdosClosedSelectorHull ErdosClosedPoolFuture ErdosBoundedFunctionValue
open ErdosBoundedImageRecursion ErdosFusionEntrySpace ErdosFusionHistories
open ErdosFusionRun ErdosFusionChoiceCongruence ErdosFusionRunLocalStep
open ErdosFusionRunFailure ErdosBlockSelectorFailure ErdosTaggedPrefix

def emptyEntry (Run : bSet 𝔹) : 𝔹 :=
  ⨆ ξ, ⨆ Z, ⨆ U, pair ξ (pair ξ (entry (∅ : bSet 𝔹) Z U)) ∈ᴮ Run

def successfulRun (Run : bSet 𝔹) : 𝔹 := (emptyEntry Run)ᶜ

def successfulRunData (color : Bool) (R E F top Run : bSet 𝔹) : 𝔹 :=
  is_function omegaOne runSpace Run ⊓
    (runLaw color R E F top Run ⊓ successfulRun Run)

def hasSuccessfulRun (color : Bool) (R E F Y : bSet 𝔹) : 𝔹 :=
  ⨆ top, top ∈ᴮ Y ⊓ ⨆ Run, successfulRunData color R E F top Run

theorem emptyEntry_ext : B_ext (emptyEntry (𝔹 := 𝔹)) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_iSup (h := fun _ => B_ext_mem_right)))

theorem successfulRun_ext : B_ext (successfulRun (𝔹 := 𝔹)) := B_ext_neg (h := emptyEntry_ext)

theorem nextEntry_congr_top (color : Bool) (R E F ξ T : bSet 𝔹) :
    B_congr (fun top => nextEntry color R E F top ξ T) := by
  intro a b Γ H
  have HZ : Γ ≤ nextIndices color R E a ξ T =ᴮ nextIndices color R E b ξ T :=
    currentChoices_congr H bv_refl bv_refl bv_refl
  have HU : Γ ≤ nextActive color R E a ξ T =ᴮ nextActive color R E b ξ T :=
    activeHistory_currentChoices_congr H bv_refl bv_refl bv_refl bv_refl
  have HA : Γ ≤ nextBlock color R E F a ξ T =ᴮ nextBlock color R E F b ξ T :=
    graphValue_congr_input _ _ (pair_congr bv_refl HU)
  exact pair_congr HA (pair_congr HZ HU)

theorem fusionRunLaw_ext_top (color : Bool) (R E F Run : bSet 𝔹) :
    B_ext (fun top => runLaw color R E F top Run) :=
  B_ext_iInf (h := fun i => B_ext_iInf (h := fun y =>
    B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_term (ϕ := fun z => y =ᴮ z)
        (t := fun top => pair i (nextEntry color R E F top i (image i runSpace Run)))
        B_ext_bv_eq_right (by
          intro a b Γ H
          exact pair_congr bv_refl (nextEntry_congr_top color R E F i _ H)))))

theorem fusionRunLaw_ext_graph (color : Bool) (R E F top : bSet 𝔹) :
    B_ext (runLaw color R E F top) :=
  imageRecLaw_ext_graph runSpace (fun i T => pair i (nextEntry color R E F top i T))
    (fun _ _ _ _ H => pair_congr bv_refl (nextEntry_congr bv_refl H))

theorem successfulRunData_ext_top (color : Bool) (R E F Run : bSet 𝔹) :
    B_ext (fun top => successfulRunData color R E F top Run) :=
  B_ext_inf B_ext_const (B_ext_inf (fusionRunLaw_ext_top color R E F Run) B_ext_const)

theorem successfulRunData_ext_graph (color : Bool) (R E F top : bSet 𝔹) :
    B_ext (successfulRunData color R E F top) :=
  B_ext_inf B_ext_is_function_right
    (B_ext_inf (fusionRunLaw_ext_graph color R E F top) successfulRun_ext)

/-- The complement definition covers every arbitrary stored name, not
only entries syntactically containing the empty set. -/
theorem successfulRun_nonempty
    {Run ξ A Z U : bSet 𝔹} {Γ : 𝔹}
    (Hsuccess : Γ ≤ successfulRun Run)
    (Hentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run) :
    Γ ≤ (A =ᴮ (∅ : bSet 𝔹))ᶜ := by
  rw [← imp_bot, ← deduction]
  have HA : Γ ⊓ A =ᴮ (∅ : bSet 𝔹) ≤ entry A Z U =ᴮ entry (∅ : bSet 𝔹) Z U :=
    pair_congr inf_le_right bv_refl
  have Hempty : Γ ⊓ A =ᴮ (∅ : bSet 𝔹) ≤ emptyEntry Run :=
    le_iSup_of_le ξ (le_iSup_of_le Z (le_iSup_of_le U
      (mem_congr (pair_congr bv_refl (pair_congr bv_refl HA)) bv_refl (inf_le_left.trans Hentry))))
  exact bv_absurd _ Hempty (inf_le_left.trans Hsuccess)

/-- Success upgrades the actual candidate-or-empty law to genuine whole
block membership for every stored entry of the full run. -/
theorem successfulRun_blockObject
    {color : Bool} {R J E S F top Run ξ A Z U : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hsuccess : Γ ≤ successfulRun Run)
    (Hentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run) :
    Γ ≤ A ∈ᴮ blockObjects color R := by
  have Hcases := fusion_run_stored_block_candidate_or_empty HE HElaw HF HFlaw HRun Hlaw Hentry
  apply (le_inf le_rfl Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact blockCandidate_object inf_le_right
  · exact (bv_absurd _ inf_le_right
      (inf_le_left.trans (successfulRun_nonempty Hsuccess Hentry))).trans bot_le

/-- An internal empty-entry join gives a failed terminal label directly
by distribution. No externally selected first failure is required. -/
theorem failed_input_of_emptyEntry
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
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hempty : Γ ≤ emptyEntry Run) :
    Γ ≤ ⨆ Earlier, ⨆ Active,
      pair Earlier Active ∈ᴮ choicePoolDomain B P ⊓
        (pair (pair Earlier Active) (∅ : bSet 𝔹) ∈ᴮ F ⊓
          activeTerminalEdges color R Active top) := by
  apply (le_inf le_rfl Hempty).trans
  unfold emptyEntry
  rw [inf_iSup_eq]
  apply iSup_le
  intro ξ
  rw [inf_iSup_eq]
  apply iSup_le
  intro Z
  rw [inf_iSup_eq]
  apply iSup_le
  intro U
  exact le_iSup_of_le _ (le_iSup_of_le U (fusion_run_failed_input
    (inf_le_left.trans HJ) (inf_le_left.trans Habsorb) (inf_le_left.trans Hclosure)
    (inf_le_left.trans HE) (inf_le_left.trans HElaw) (inf_le_left.trans HF)
    (inf_le_left.trans HFlaw) (inf_le_left.trans Hhull) (inf_le_left.trans Hseeds)
    (inf_le_left.trans Htop) (inf_le_left.trans HRun) (inf_le_left.trans Hlaw)
    inf_le_right bv_refl))

/-- Neither a successful run nor a family of failed runs is a premise.
The prepared fixed selector and closed pool are used exactly as given. -/
theorem successful_fusion_run_value
    {color : Bool} {R J I D E S F B P Y : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HJ : Γ ≤ properIdeal omegaOne J)
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
    (Hhull : Γ ≤ closedHullData color R F B P)
    (Hseeds : Γ ≤ poolSeedLaw color R J E B Y)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HY : Γ ≤ Y ⊆ᴮ S)
    (HYlarge : Γ ≤ injects_into omegaTwo Y) :
    Γ ≤ hasSuccessfulRun color R E F Y := by
  rw [← compl_compl (hasSuccessfulRun color R E F Y), ← imp_bot, ← deduction]
  let Δ := Γ ⊓ (hasSuccessfulRun color R E F Y)ᶜ
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hfail : Δ ≤ allTerminalFailures color R F B P Y := by
    apply le_iInf
    intro top
    rw [← deduction]
    let Ξ := Δ ⊓ top ∈ᴮ Y
    have HΞ : Ξ ≤ Γ := inf_le_left.trans HΔ
    have Htop : Ξ ≤ top ∈ᴮ Y := inf_le_right
    have HnoSuccess : Ξ ≤ (hasSuccessfulRun color R E F Y)ᶜ := inf_le_left.trans inf_le_right
    obtain ⟨Run, HRunData⟩ := exists_total_fusion_run color R E F top (Γ := Ξ)
    have HRun := HRunData.trans inf_le_left
    have Hlaw := HRunData.trans inf_le_right
    have Hempty : Ξ ≤ emptyEntry Run := by
      rw [← compl_compl (emptyEntry Run), ← imp_bot, ← deduction]
      have Hgood : Ξ ⊓ (emptyEntry Run)ᶜ ≤ hasSuccessfulRun color R E F Y :=
        le_iSup_of_le top (le_inf (inf_le_left.trans Htop)
          (le_iSup_of_le Run (le_inf (inf_le_left.trans HRun)
            (le_inf (inf_le_left.trans Hlaw) inf_le_right))))
      exact bv_absurd _ Hgood (inf_le_left.trans HnoSuccess)
    exact failed_input_of_emptyEntry (HΞ.trans HJ) (HΞ.trans Habsorb)
      (HΞ.trans Hclosure) (HΞ.trans HE) (HΞ.trans HElaw) (HΞ.trans HF)
      (HΞ.trans HFlaw) (HΞ.trans Hhull) (HΞ.trans Hseeds) Htop HRun Hlaw Hempty
  exact all_terminal_failures_false (HΔ.trans HCH) (HΔ.trans HJ)
    (HΔ.trans Habsorb) (HΔ.trans Hclosure) (HΔ.trans Hdiag) (HΔ.trans HD)
    (HΔ.trans HDpos) (HΔ.trans Hdense) (HΔ.trans HI) (HΔ.trans HE)
    (HΔ.trans HElaw) (HΔ.trans HF) (HΔ.trans HFlaw)
    (HΔ.trans (Hhull.trans inf_le_left))
    (HΔ.trans (Hhull.trans (inf_le_right.trans inf_le_left)))
    (HΔ.trans (closedHullData_point_small Hhull))
    (HΔ.trans Hno) (HΔ.trans HnoOpp) (HΔ.trans HS) (HΔ.trans HY)
    (HΔ.trans HYlarge) Hfail

theorem exists_successful_fusion_run_of_value
    {color : Bool} {R E F Y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ hasSuccessfulRun color R E F Y) :
    ∃ top Run : bSet 𝔹, Γ ≤ top ∈ᴮ Y ⊓
      (is_function omegaOne runSpace Run ⊓ (runLaw color R E F top Run ⊓ successfulRun Run)) := by
  obtain ⟨top, Htop⟩ := exists_convert H
    (B_ext_inf B_ext_mem_left
      (B_ext_iSup (h := fun Run => successfulRunData_ext_top color R E F Run)))
  obtain ⟨Run, HRun⟩ := exists_convert (Htop.trans inf_le_right)
    (successfulRunData_ext_graph color R E F top)
  exact ⟨top, Run, le_inf (Htop.trans inf_le_left) HRun⟩

/-- The final same-condition witnesses are an actual terminal and a
supported total omega-one run whose every stored block is nonempty. -/
theorem exists_successful_fusion_run
    {color : Bool} {R J I D E S F B P Y : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HJ : Γ ≤ properIdeal omegaOne J)
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
    (Hhull : Γ ≤ closedHullData color R F B P)
    (Hseeds : Γ ≤ poolSeedLaw color R J E B Y)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HY : Γ ≤ Y ⊆ᴮ S)
    (HYlarge : Γ ≤ injects_into omegaTwo Y) :
    ∃ top Run : bSet 𝔹, Γ ≤ top ∈ᴮ Y ⊓
      (is_function omegaOne runSpace Run ⊓ (runLaw color R E F top Run ⊓ successfulRun Run)) :=
  exists_successful_fusion_run_of_value
    (successful_fusion_run_value HCH HJ Habsorb Hclosure Hdiag HD HDpos Hdense HI
      HE HElaw HF HFlaw Hhull Hseeds Hno HnoOpp HS HY HYlarge)

end bSet.ErdosFusionRunSuccess
