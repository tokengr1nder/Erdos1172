/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRunSuccess
public import Erdos1172.Part4InternalFusionCandidateRestriction
public import Erdos1172.Part4InternalFusionMaskedTailCross

@[expose] public section

/-!
# Exact leastness on the full decoded fusion history

The full block and coordinate graphs are decoded from the actual tagged
omega-one prefix, not from the stage-tagged run graph as though it had a
smaller domain. Their strict-prefix pairs agree with the actual stage
prefix. Guarded candidate restriction therefore transfers leastness to
the full graphs without identifying unequal prefix and full graphs.

The same whole object and the same fixed canonical enumeration are kept.
Only rows strictly after their birth are active. Co-largeness of the
active range and the final countable tail remain separate obligations.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionGlobalRowLaw

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosCanonicalBlocks ErdosBlockSelector
open ErdosCountableChoicePoolStep ErdosClosedSelectorHull ErdosClosedPoolFuture
open ErdosBoundedFunctionValue ErdosFusionHistories ErdosFusionEntrySpace
open ErdosFusionRowCandidates ErdosFusionRowChoice
open ErdosFusionRun ErdosFusionRunSuccess ErdosFusionRunRowLegality
open ErdosFusionPrefixCoherence ErdosFusionCandidateRestriction ErdosFusionMaskedTail
open ErdosTaggedPrefix ErdosOrdinalLeast

def fullBlocks (Run : bSet 𝔹) : bSet 𝔹 :=
  blockHistory (taggedPrefix omegaOne omegaOne entrySpace Run)

def fullCoordinates (Run : bSet 𝔹) : bSet 𝔹 :=
  coordinateHistory (taggedPrefix omegaOne omegaOne entrySpace Run)

def fullCoordinateLeastLaw (color : Bool) (R E top Run : bSet 𝔹) : 𝔹 :=
  ⨅ ν, ⨅ ξ, ⨅ b, ⨅ v, _root_.imp
    ((ν ∈ᴮ ξ ⊓ ξ ∈ᴮ omegaOne) ⊓
      (pair ν b ∈ᴮ fullBlocks Run ⊓ pair (pair ξ ν) v ∈ᴮ fullCoordinates Run))
    (leastIn (fusionRowCandidates (!color) R E b top ξ ν
      (fullBlocks Run) (fullCoordinates Run)) v)

theorem fullBlocks_is_function
    {color : Bool} {R E F top Run : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ is_function omegaOne (bv_powerset omegaTwo) (fullBlocks Run) :=
  blockHistory_is_function subset_self (fusion_prefix_is_function HRun Hlaw subset_self)

theorem fullCoordinates_is_function
    {color : Bool} {R E F top Run : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ is_function (prod omegaOne omegaOne) omegaOne (fullCoordinates Run) :=
  fusion_prefix_coordinates_function HRun Hlaw subset_self

/-- Candidate equality uses only actual strict-prefix coherence. It
does not need success, an ideal, or an equality of whole history graphs. -/
theorem fusion_full_candidates_eq_prefix
    {color edgeColor : Bool} {R E F top Run b ξ ν : bSet 𝔹} {Γ : 𝔹}
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hξ : Γ ≤ ξ ⊆ᴮ omegaOne) (Hν : Γ ≤ ν ∈ᴮ omegaOne) :
    Γ ≤ fusionRowCandidates edgeColor R E b top ξ ν
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
      (coordinateHistory (taggedPrefix ξ omegaOne entrySpace Run)) =ᴮ
      fusionRowCandidates edgeColor R E b top ξ ν
        (fullBlocks Run) (fullCoordinates Run) := by
  apply fusionRowCandidates_eq_of_history_coherence
    (is_func'_of_is_function (fusion_prefix_coordinates_function HRun Hlaw Hξ))
    (is_func'_subset_of_is_func'
      (is_func'_of_is_function (fullCoordinates_is_function HRun Hlaw))
      (ErdosPartialInjection.prod_domain_mono Hξ)) Hν
  · intro j A Δ HΔ Hj
    exact (blockHistory_pair_coherent (HΔ.trans HRun) (HΔ.trans Hlaw)
      (HΔ.trans Hξ) subset_self Hj).symm
  · intro j v Δ HΔ Hj
    exact (coordinateHistory_pair_coherent (HΔ.trans HRun) (HΔ.trans Hlaw)
      (HΔ.trans Hξ) subset_self Hj).symm

theorem fullBlocks_blockObject
    {color : Bool} {R J E S F top Run ν b : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HF : Γ ≤ is_function (choicePoolDomain (blockObjects color R) omegaTwo)
      (bv_powerset omegaTwo) F)
    (HFlaw : Γ ≤ blockSelectorLaw color R J E S F)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hsuccess : Γ ≤ successfulRun Run)
    (Hpair : Γ ≤ pair ν b ∈ᴮ fullBlocks Run) :
    Γ ≤ b ∈ᴮ blockObjects color R := by
  obtain ⟨Z, U, Hentry⟩ := blockHistory_witness Hpair
  exact successfulRun_blockObject HE HElaw HF HFlaw HRun Hlaw Hsuccess
    ((mem_taggedPrefix_pair_iff HRun (fusion_run_tagging HRun Hlaw)).mp Hentry).2

/-- Every genuinely active value of the full decoded coordinate graph
is the least legal value for the full graphs and the same stored object. -/
theorem fusion_full_row_least
    {color : Bool} {R J E S F B P Y top Run ξ ν b v : bSet 𝔹} {Γ : 𝔹}
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
    (Hsuccess : Γ ≤ successfulRun Run)
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (Hνξ : Γ ≤ ν ∈ᴮ ξ)
    (Hνb : Γ ≤ pair ν b ∈ᴮ fullBlocks Run)
    (Hcoord : Γ ≤ pair (pair ξ ν) v ∈ᴮ fullCoordinates Run) :
    Γ ≤ leastIn (fusionRowCandidates (!color) R E b top ξ ν
      (fullBlocks Run) (fullCoordinates Run)) v := by
  let T := taggedPrefix ξ omegaOne entrySpace Run
  have Hξsub := subset_of_mem_Ord Hξ omegaOne_Ord
  have Hν := mem_of_mem_Ord Hνξ Hξ omegaOne_Ord
  have Hpref : Γ ≤ pair ν b ∈ᴮ blockHistory T :=
    (blockHistory_pair_coherent HRun Hlaw Hξsub subset_self Hνξ).mp Hνb
  have Hbeq : Γ ≤ blockValue (blockHistory T) ν =ᴮ b :=
    graphValue_eq_of_pair
      (blockHistory_is_function Hξsub (fusion_prefix_is_function HRun Hlaw Hξsub)) Hpref
  have Hb := fullBlocks_blockObject HE HElaw HF HFlaw HRun Hlaw Hsuccess Hνb
  have Hactive : Γ ≤ ν ∈ᴮ successfulRows color R ξ (blockHistory T) :=
    mem_successfulRows_iff.mpr ⟨Hνξ, mem_congr (bv_symm Hbeq) bv_refl Hb⟩
  obtain ⟨A, Z, U, Hentry, Hνv⟩ := coordinateHistory_witness Hcoord
  have Hstored := ((mem_taggedPrefix_pair_iff HRun
    (fusion_run_tagging HRun Hlaw)).mp Hentry).2
  have Hleast : Γ ≤ leastIn
      (fusionRowCandidates (!color) R E (blockValue (blockHistory T) ν)
        top ξ ν (blockHistory T) (coordinateHistory T)) v :=
    fusion_run_row_least HJ Habsorb Hclosure HE HElaw HF HFlaw Hhull Hseeds Htop
      HRun Hlaw Hstored Hactive Hνv
  have Hobject : Γ ≤
      fusionRowCandidates (!color) R E (blockValue (blockHistory T) ν)
        top ξ ν (blockHistory T) (coordinateHistory T) =ᴮ
      fusionRowCandidates (!color) R E b top ξ ν (blockHistory T) (coordinateHistory T) :=
    fusionRowCandidates_congr_object (!color) R E top ξ ν _ _ Hbeq
  have Hhistory : Γ ≤
      fusionRowCandidates (!color) R E b top ξ ν (blockHistory T) (coordinateHistory T) =ᴮ
      fusionRowCandidates (!color) R E b top ξ ν (fullBlocks Run) (fullCoordinates Run) :=
    fusion_full_candidates_eq_prefix HRun Hlaw Hξsub Hν
  exact bv_rw'' (ϕ := fun C => leastIn C v) (bv_trans Hobject Hhistory) Hleast
    (leastIn_ext_set v)

theorem fusion_full_coordinateLeastLaw
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
    (Hsuccess : Γ ≤ successfulRun Run) :
    Γ ≤ fullCoordinateLeastLaw color R E top Run := by
  apply le_iInf
  intro ν
  apply le_iInf
  intro ξ
  apply le_iInf
  intro b
  apply le_iInf
  intro v
  rw [← deduction]
  exact fusion_full_row_least (inf_le_left.trans HJ) (inf_le_left.trans Habsorb)
    (inf_le_left.trans Hclosure) (inf_le_left.trans HE) (inf_le_left.trans HElaw)
    (inf_le_left.trans HF) (inf_le_left.trans HFlaw) (inf_le_left.trans Hhull)
    (inf_le_left.trans Hseeds) (inf_le_left.trans Htop) (inf_le_left.trans HRun)
    (inf_le_left.trans Hlaw) (inf_le_left.trans Hsuccess)
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_right.trans inf_le_left))
    (inf_le_right.trans (inf_le_right.trans inf_le_right))

theorem coordinateCandidateLaw_of_fullLeastLaw
    {color : Bool} {R E top Run : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ fullCoordinateLeastLaw color R E top Run) :
    Γ ≤ coordinateCandidateLaw (!color) R E top (fullBlocks Run) (fullCoordinates Run) := by
  apply le_iInf
  intro ν
  apply le_iInf
  intro ξ
  apply le_iInf
  intro b
  apply le_iInf
  intro v
  rw [← deduction]
  exact leastIn_mem ((le_inf (inf_le_left.trans (H.trans
    ((iInf_le _ ν).trans ((iInf_le _ ξ).trans ((iInf_le _ b).trans (iInf_le _ v))))))
    inf_le_right).trans bv_imp_elim)

theorem fusion_full_coordinateCandidateLaw
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
    (Hsuccess : Γ ≤ successfulRun Run) :
    Γ ≤ coordinateCandidateLaw (!color) R E top (fullBlocks Run) (fullCoordinates Run) :=
  coordinateCandidateLaw_of_fullLeastLaw
    (fusion_full_coordinateLeastLaw HJ Habsorb Hclosure HE HElaw HF HFlaw Hhull
      Hseeds Htop HRun Hlaw Hsuccess)

end bSet.ErdosFusionGlobalRowLaw
