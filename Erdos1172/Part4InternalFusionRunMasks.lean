/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionBirthSections
public import Erdos1172.Part4InternalFusionGlobalRowLaw

@[expose] public section

/-!
# Co-large active masks of an actual successful fusion

The complete decoded history inherits every original stored candidate
law by strict-prefix coherence. Thus its activated whole-block sections
are co-large. Completing the family by omega-one before birth preserves
the exact candidate sets. Actual full-run leastness, followed by the
active-inverse closure argument, makes each literal active mask co-large.

Neither section co-largeness nor mask positivity is an input. The fixed
enumeration, selector, original seed terminal, and ideal are unchanged.
Success remains explicit; constructing a successful run is separate.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRunMasks

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosCanonicalBlocks ErdosBlockCandidate
open ErdosBlockSelector ErdosCountableChoicePoolStep ErdosClosedSelectorHull
open ErdosClosedPoolFuture ErdosFusionHistories ErdosFusionRowCandidates
open ErdosFusionSeedBridge ErdosFusionEntrySpace ErdosFusionRun ErdosTaggedPrefix
open ErdosFusionPrefixCoherence ErdosFusionRunLocalStep ErdosFusionRunPoolInvariant
open ErdosFusionRunSuccess ErdosFusionGlobalRowLaw ErdosFusionBirthSections
open ErdosBirthGreedyRange ErdosFusionMaskedTail ErdosColargeIntersection
open ErdosOrdinalLeast ErdosSimultaneousTraces

variable {color : Bool} {R J E S F B P Y top Run : bSet 𝔹} {Γ : 𝔹}
variable (HJ : Γ ≤ properIdeal omegaOne J)
  (Habsorb : Γ ≤ countableAbsorption omegaOne J)
  (Hclosure : Γ ≤ countableClosure J)
  (Hnormal : Γ ≤ diagonalClosure omegaOne J)
  (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
  (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
  (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
    (bv_powerset omegaTwo) F)
  (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
  (Hhull : Γ ≤ closedHullData color R F B P)
  (Hseeds : Γ ≤ poolSeedLaw color R J E B Y) (Htop : Γ ≤ top ∈ᴮ Y)
  (HRun : Γ ≤ is_function omegaOne runSpace Run)
  (Hlaw : Γ ≤ runLaw color R E F top Run)
  (Hsuccess : Γ ≤ successfulRun Run)

include HE HElaw HF HFlaw HRun Hlaw in
/-- The full omega-one endpoint uses subset coherence; it never asks
for the false assertion that omega-one is a member of itself. -/
theorem fusion_full_storedBlockCandidates :
    Γ ≤ storedBlockCandidates color R J E S omegaOne (fullBlocks Run) := by
  apply le_iInf
  intro j
  apply le_iInf
  intro c
  rw [← deduction]
  let Δ := Γ ⊓ (j ∈ᴮ omegaOne ⊓ pair j c ∈ᴮ fullBlocks Run)
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hj : Δ ≤ j ∈ᴮ omegaOne := inf_le_right.trans inf_le_left
  obtain ⟨Z, U, Hentry⟩ := blockHistory_witness
    (show Δ ≤ pair j c ∈ᴮ fullBlocks Run from inf_le_right.trans inf_le_right)
  have Hactual := ((mem_taggedPrefix_pair_iff (HΔ.trans HRun)
    (HΔ.trans (fusion_run_tagging HRun Hlaw))).mp Hentry).2
  have Hstored := fusion_run_stored_block_candidate_or_empty
    (HΔ.trans HE) (HΔ.trans HElaw) (HΔ.trans HF) (HΔ.trans HFlaw)
    (HΔ.trans HRun) (HΔ.trans Hlaw) Hactual
  have Hearlier := earlierHistory_prefix_coherent
    (HΔ.trans HRun) (HΔ.trans Hlaw) (subset_of_mem_Ord Hj omegaOne_Ord) subset_self
  have Htransport : Δ ≤ blockCandidate color R J E S
      (earlierHistory color R j (fullBlocks Run)) U c ⊔ c =ᴮ (∅ : bSet 𝔹) :=
    bv_rw' (ϕ := fun Earlier => blockCandidate color R J E S Earlier U c ⊔
      c =ᴮ (∅ : bSet 𝔹)) Hearlier
      (h_congr := B_ext_sup (h₁ := blockCandidate_ext_earlier color R J E S U c)
        (h₂ := B_ext_const)) (H_new := Hstored)
  have Hinto : blockCandidate color R J E S (earlierHistory color R j (fullBlocks Run)) U c ≤
      ⨆ Active, blockCandidate color R J E S (earlierHistory color R j (fullBlocks Run)) Active c :=
    le_iSup_of_le U le_rfl
  exact Htransport.trans (sup_le (Hinto.trans le_sup_right) le_sup_left)

include HE HElaw HF HFlaw Hhull HRun Hlaw Hsuccess in
theorem fusion_full_block_mem_pool {ν b : bSet 𝔹}
    (Hν : Γ ≤ ν ∈ᴮ omegaOne) (Hνb : Γ ≤ pair ν b ∈ᴮ fullBlocks Run) :
    Γ ≤ b ∈ᴮ B := by
  have Hb := fullBlocks_blockObject HE HElaw HF HFlaw HRun Hlaw Hsuccess Hνb
  have Hvalues := fusion_prefix_poolValues (ξ := omegaOne) HE HElaw HF Hhull HRun Hlaw
  have Hcases : Γ ≤ b =ᴮ (∅ : bSet 𝔹) ⊔ b ∈ᴮ B :=
    (le_inf (Hvalues.trans ((iInf_le _ ν).trans (iInf_le _ b))) (le_inf Hν Hνb)).trans
      bv_imp_elim
  apply (le_inf le_rfl Hcases).trans
  rw [inf_sup_left]
  exact sup_le
    ((bv_absurd _ inf_le_right (inf_le_left.trans (blockObject_nonempty Hb))).trans bot_le)
    inf_le_right

include HJ HE HElaw HF HFlaw HRun Hlaw Hsuccess in
theorem fusion_full_birthSection_values {ν b : bSet 𝔹}
    (Hνb : Γ ≤ pair ν b ∈ᴮ fullBlocks Run) :
    Γ ≤ ⨅ j, ⨅ A, _root_.imp
      (j ∈ᴮ omegaOne ⊓ pair j A ∈ᴮ birthSectionFamily (!color) R E b (fullBlocks Run) ν)
      (colarge omegaOne J A) :=
  birthSectionFamily_colarge_values (HJ.trans inf_le_left)
    (fusionSections_colarge_of_stored_candidates (HJ.trans inf_le_left) HE
      (fullBlocks_is_function HRun Hlaw) Hνb
      (fullBlocks_blockObject HE HElaw HF HFlaw HRun Hlaw Hsuccess Hνb)
      (fusion_full_storedBlockCandidates HE HElaw HF HFlaw HRun Hlaw))

/-- The literal full-family candidates equal the exact candidates of
the stored minimum. No discarded inactive coordinate is required to
satisfy an increasingness or leastness law. -/
theorem birthGreedyLaw_of_fullLeastLaw {ν b : bSet 𝔹}
    (HX : Γ ≤ is_func' (prod omegaOne omegaOne) omegaOne (fullCoordinates Run))
    (Hleast : Γ ≤ fullCoordinateLeastLaw color R E top Run)
    (Hν : Γ ≤ ν ∈ᴮ omegaOne) (Hνb : Γ ≤ pair ν b ∈ᴮ fullBlocks Run) :
    Γ ≤ birthGreedyLaw ν (fusionSeed (!color) R E b top)
      (birthSectionFamily (!color) R E b (fullBlocks Run) ν)
      (rowHistory omegaOne (fullCoordinates Run) ν) := by
  apply le_iInf
  intro ξ
  apply le_iInf
  intro v
  rw [← deduction]
  let Δ := Γ ⊓ ((ν ∈ᴮ ξ ⊓ ξ ∈ᴮ omegaOne) ⊓
    pair ξ v ∈ᴮ rowHistory omegaOne (fullCoordinates Run) ν)
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hξ : Δ ≤ ξ ∈ᴮ omegaOne := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have Hνξ : Δ ≤ ν ∈ᴮ ξ := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have Hcoord : Δ ≤ pair (pair ξ ν) v ∈ᴮ fullCoordinates Run :=
    rowHistory_apply (show Δ ≤ pair ξ v ∈ᴮ rowHistory omegaOne (fullCoordinates Run) ν from
      inf_le_right.trans inf_le_right)
  have Hmin : Δ ≤ leastIn (fusionRowCandidates (!color) R E b top ξ ν
      (fullBlocks Run) (fullCoordinates Run)) v :=
    (le_inf (HΔ.trans (Hleast.trans ((iInf_le _ ν).trans
      ((iInf_le _ ξ).trans ((iInf_le _ b).trans (iInf_le _ v))))))
      (le_inf (le_inf Hνξ Hξ) (le_inf (HΔ.trans Hνb) Hcoord))).trans bv_imp_elim
  exact bv_rw' (ϕ := fun C => leastIn C v)
    (birth_rowCandidates_eq_fusion (HΔ.trans HX)
      (subset_of_mem_Ord Hξ omegaOne_Ord) (HΔ.trans Hν))
    (h_congr := leastIn_ext_set v) (H_new := Hmin)

include HJ Habsorb Hclosure Hnormal HE HElaw HF HFlaw Hhull Hseeds Htop HRun Hlaw Hsuccess in
/-- Actual mask co-largeness for every internal birth index. The seed,
all whole-block sections, and leastness are derived from the same run. -/
theorem fusion_activeMask_colarge {ν : bSet 𝔹} (Hν : Γ ≤ ν ∈ᴮ omegaOne) :
    Γ ≤ colarge omegaOne J (activeMask (fullCoordinates Run) ν) := by
  have HBlocks := fullBlocks_is_function HRun Hlaw
  have Hex : Γ ≤ ⨆ b, b ∈ᴮ bv_powerset omegaTwo ⊓ pair ν b ∈ᴮ fullBlocks Run :=
    (le_inf ((is_total_of_is_function HBlocks).trans (iInf_le _ ν)) Hν).trans bv_imp_elim
  obtain ⟨b, Hb⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hνb := Hb.trans inf_le_right
  have Hseed : Γ ≤ colarge omegaOne J (fusionSeed (!color) R E b top) :=
    fusionSeed_colarge_of_poolSeedLaw (HJ.trans inf_le_left) HE (Hhull.trans inf_le_left)
      Hseeds (fusion_full_block_mem_pool HE HElaw HF HFlaw Hhull HRun Hlaw Hsuccess Hν Hνb) Htop
  have Hvalues := fusion_full_birthSection_values HJ HE HElaw HF HFlaw HRun Hlaw Hsuccess Hνb
  have HX := is_func'_of_is_function (fullCoordinates_is_function HRun Hlaw)
  apply activeMask_colarge_of_birthGreedyLaw (HJ.trans inf_le_left) Habsorb Hclosure Hnormal Hν
    Hseed (is_func'_of_is_function birthSectionFamily_is_function) ?_ HX
    (birthGreedyLaw_of_fullLeastLaw HX
      (fusion_full_coordinateLeastLaw HJ Habsorb Hclosure HE HElaw HF HFlaw Hhull
        Hseeds Htop HRun Hlaw Hsuccess) Hν Hνb)
  apply le_iInf
  intro j
  apply le_iInf
  intro A
  rw [← deduction]
  exact ((le_inf (inf_le_left.trans (Hvalues.trans
    ((iInf_le _ j).trans (iInf_le _ A)))) inf_le_right).trans bv_imp_elim).trans inf_le_right

include HJ Habsorb Hclosure Hnormal HE HElaw HF HFlaw Hhull Hseeds Htop HRun Hlaw Hsuccess in
theorem fusion_activeMasks_colarge :
    Γ ≤ ⨅ ν, _root_.imp (ν ∈ᴮ omegaOne)
      (colarge omegaOne J (activeMask (fullCoordinates Run) ν)) := by
  apply le_iInf
  intro ν
  rw [← deduction]
  exact fusion_activeMask_colarge (inf_le_left.trans HJ) (inf_le_left.trans Habsorb)
    (inf_le_left.trans Hclosure) (inf_le_left.trans Hnormal)
    (inf_le_left.trans HE) (inf_le_left.trans HElaw) (inf_le_left.trans HF)
    (inf_le_left.trans HFlaw) (inf_le_left.trans Hhull) (inf_le_left.trans Hseeds)
    (inf_le_left.trans Htop) (inf_le_left.trans HRun) (inf_le_left.trans Hlaw)
    (inf_le_left.trans Hsuccess) inf_le_right

end bSet.ErdosFusionRunMasks
