/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionSeedBridge
public import Erdos1172.Part4InternalFusionRunLocalStep
public import Erdos1172.Part4InternalFusionRunPoolInvariant
public import Erdos1172.Part4InternalFusionPrefixCoherence

@[expose] public section

/-!
# Legality of the actual fusion row coordinates

The terminal seed is inherited from the same closed whole-object pool.
Every activated section is inherited from the actual earlier candidate
law, with empty intermediate blocks imposing the full section. Thus the
actual least-or-zero coordinate is a least legal coordinate on every
successful earlier row. No candidate nonemptiness is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRunRowLegality

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosCanonicalBlocks ErdosBoundedFunctionValue
open ErdosFusionHistories ErdosFusionRowCandidates ErdosFusionRowChoice
open ErdosFusionSeedBridge ErdosFusionRunLocalStep ErdosClosedPoolFuture
open ErdosOrdinalLeast ErdosPartition
open ErdosFusionRun ErdosFusionEntrySpace ErdosTaggedPrefix
open ErdosClosedSelectorHull ErdosBlockSelector ErdosCountableChoicePoolStep
open ErdosFusionRunPoolInvariant ErdosFusionPrefixCoherence

theorem successfulRow_mem_pool
    {color : Bool} {R ξ Blocks B ν : bSet 𝔹} {Γ : 𝔹}
    (HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks)
    (Hobjects : Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ ξ ⊓ pair i A ∈ᴮ Blocks)
      (A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B))
    (Hactive : Γ ≤ ν ∈ᴮ successfulRows color R ξ Blocks) :
    Γ ≤ blockValue Blocks ν ∈ᴮ B := by
  have Hparts := mem_successfulRows_iff.mp Hactive
  exact mem_of_mem_subset (earlierHistory_subset_pool_of_values Hobjects)
    (earlierHistory_mem_of_pair HBlocks (graphValue_pair_mem HBlocks Hparts.1) Hparts.2)

/-- Structural seed and stored whole-block laws prove leastness of the
actual choice value, including mixed empty intermediate stages. -/
theorem currentChoices_least_of_stored_candidates
    {color : Bool} {R J E S B Y top ξ Blocks X ν v : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (Hseeds : Γ ≤ poolSeedLaw color R J E B Y) (Htop : Γ ≤ top ∈ᴮ Y)
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne)
    (HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks)
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X)
    (Hobjects : Γ ≤ ⨅ i, ⨅ A, _root_.imp (i ∈ᴮ ξ ⊓ pair i A ∈ᴮ Blocks)
      (A =ᴮ (∅ : bSet 𝔹) ⊔ A ∈ᴮ B))
    (Hstored : Γ ≤ storedBlockCandidates color R J E S ξ Blocks)
    (Hactive : Γ ≤ ν ∈ᴮ successfulRows color R ξ Blocks)
    (Hchoice : Γ ≤ pair ν v ∈ᴮ currentChoices color R E top ξ Blocks X) :
    Γ ≤ leastIn (rowCandidatesAt color R E top ξ Blocks X ν) v := by
  have Hparts := mem_successfulRows_iff.mp Hactive
  obtain ⟨w, Hw⟩ := exists_least_fusionRowCandidate_of_stored_candidates
    HJ Habsorb Hclosure Hξ HX HE HB Hseeds
    (successfulRow_mem_pool HBlocks Hobjects Hactive) Htop HBlocks
    (graphValue_pair_mem HBlocks Hparts.1) Hstored
  exact currentChoices_least_of_witness Hchoice Hactive (Hw.trans inf_le_right)

/-- Every consequence concerns the same selected coordinate and the
same canonical row. Strict coordinate growth also retains failed stages. -/
theorem row_properties_of_least
    {color : Bool} {R E top ξ Blocks X ν v : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X)
    (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (Hb : Γ ≤ blockValue Blocks ν ∈ᴮ blockObjects color R)
    (Hleast : Γ ≤ leastIn (rowCandidatesAt color R E top ξ Blocks X ν) v) :
    Γ ≤ (⨅ x, _root_.imp (pair v x ∈ᴮ canonicalRow E (blockValue Blocks ν))
      (graphColor (!color) R x top)) ⊓
      ((⨅ j, ⨅ c, ⨅ x, ⨅ y, _root_.imp
        ((j ∈ᴮ ξ ⊓ ν ∈ᴮ j) ⊓
          (pair j c ∈ᴮ Blocks ⊓ (pair v x ∈ᴮ canonicalRow E (blockValue Blocks ν) ⊓ y ∈ᴮ c)))
        (graphColor (!color) R x y)) ⊓
       (⨅ j, ⨅ w, _root_.imp ((j ∈ᴮ ξ ⊓ ν ∈ᴮ j) ⊓ pair (pair j ν) w ∈ᴮ X)
         (w ∈ᴮ v))) := by
  have Hv : Γ ≤ v ∈ᴮ fusionRowCandidates (!color) R E (blockValue Blocks ν)
      top ξ ν Blocks X := leastIn_mem Hleast
  have Hr : Γ ≤ is_function omegaOne omegaTwo (canonicalRow E (blockValue Blocks ν)) :=
    (canonicalRow_data HE HElaw Hb).trans (inf_le_left.trans inf_le_left)
  apply le_inf
  · apply le_iInf
    intro x
    rw [← deduction]
    exact fusionCandidate_seed_edge (inf_le_left.trans HX) (inf_le_left.trans Hν)
      (inf_le_left.trans (Hr.trans (inf_le_left.trans inf_le_left)))
      (inf_le_left.trans Hv) inf_le_right
  · apply le_inf
    · apply le_iInf
      intro j
      apply le_iInf
      intro c
      apply le_iInf
      intro x
      apply le_iInf
      intro y
      rw [← deduction]
      exact fusionCandidate_cross_previous_block (inf_le_left.trans HX)
        (inf_le_left.trans Hν) (inf_le_left.trans Hv)
        (inf_le_right.trans (inf_le_left.trans inf_le_left))
        (inf_le_right.trans (inf_le_left.trans inf_le_right))
        (inf_le_right.trans (inf_le_right.trans inf_le_left))
        (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
        (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    · apply le_iInf
      intro j
      apply le_iInf
      intro w
      rw [← deduction]
      exact fusionCandidate_above_previous (inf_le_left.trans HX)
        (inf_le_left.trans Hν) (inf_le_left.trans Hv)
        (inf_le_right.trans (inf_le_left.trans inf_le_left))
        (inf_le_right.trans (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right)

/-- No structural prefix law is supplied here: pool preservation and
stored candidate coherence are consequences of the actual run. -/
theorem fusion_run_next_row_least
    {color : Bool} {R J E S F B P Y top Run ξ ν v : bSet 𝔹} {Γ : 𝔹}
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
    (Hlaw : Γ ≤ runLaw color R E F top Run) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne)
    (Hactive : Γ ≤ ν ∈ᴮ successfulRows color R ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run)))
    (Hchoice : Γ ≤ pair ν v ∈ᴮ
      nextIndices color R E top ξ (taggedPrefix ξ omegaOne entrySpace Run)) :
    Γ ≤ leastIn (rowCandidatesAt color R E top ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
      (coordinateHistory (taggedPrefix ξ omegaOne entrySpace Run)) ν) v :=
  currentChoices_least_of_stored_candidates HJ Habsorb Hclosure HE
    (Hhull.trans inf_le_left) Hseeds Htop Hξ
    (blockHistory_is_function (subset_of_mem_Ord Hξ omegaOne_Ord)
      (fusion_prefix_is_function HRun Hlaw (subset_of_mem_Ord Hξ omegaOne_Ord)))
    (is_func'_of_is_function
      (fusion_prefix_coordinates_function HRun Hlaw (subset_of_mem_Ord Hξ omegaOne_Ord)))
    (fusion_prefix_poolValues HE HElaw HF Hhull HRun Hlaw)
    (fusion_prefix_storedBlockCandidates HE HElaw HF HFlaw HRun Hlaw Hξ) Hactive Hchoice

/-- Leastness holds for the value of the actual stored coordinate graph,
not for a newly selected legal coordinate graph. -/
theorem fusion_run_row_least
    {color : Bool} {R J E S F B P Y top Run ξ A Z U ν v : bSet 𝔹} {Γ : 𝔹}
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
    (Hentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run)
    (Hactive : Γ ≤ ν ∈ᴮ successfulRows color R ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run)))
    (Hνv : Γ ≤ pair ν v ∈ᴮ Z) :
    Γ ≤ leastIn (rowCandidatesAt color R E top ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
      (coordinateHistory (taggedPrefix ξ omegaOne entrySpace Run)) ν) v := by
  have HZ : Γ ≤ Z =ᴮ nextIndices color R E top ξ (taggedPrefix ξ omegaOne entrySpace Run) :=
    eq_of_eq_pair_left' (eq_of_eq_pair_right' (fusion_run_entry_eq Hlaw Hentry))
  exact fusion_run_next_row_least HJ Habsorb Hclosure HE HElaw HF HFlaw Hhull Hseeds Htop
    HRun Hlaw (mem_domain_of_is_function Hentry HRun) Hactive
    (mem_congr bv_refl HZ Hνv)

/-- Seed adjacency, all activated whole-block cross edges, and strict
growth follow for the actual stored value under the same hypotheses. -/
theorem fusion_run_row_properties
    {color : Bool} {R J E S F B P Y top Run ξ A Z U ν v : bSet 𝔹} {Γ : 𝔹}
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
    (Hentry : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run)
    (Hactive : Γ ≤ ν ∈ᴮ successfulRows color R ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run)))
    (Hνv : Γ ≤ pair ν v ∈ᴮ Z) :
    let T := taggedPrefix ξ omegaOne entrySpace Run
    let Blocks := blockHistory T
    let X := coordinateHistory T
    Γ ≤ (⨅ x, _root_.imp (pair v x ∈ᴮ canonicalRow E (blockValue Blocks ν))
      (graphColor (!color) R x top)) ⊓
      ((⨅ j, ⨅ c, ⨅ x, ⨅ y, _root_.imp
        ((j ∈ᴮ ξ ⊓ ν ∈ᴮ j) ⊓
          (pair j c ∈ᴮ Blocks ⊓ (pair v x ∈ᴮ canonicalRow E (blockValue Blocks ν) ⊓ y ∈ᴮ c)))
        (graphColor (!color) R x y)) ⊓
       (⨅ j, ⨅ w, _root_.imp ((j ∈ᴮ ξ ⊓ ν ∈ᴮ j) ⊓ pair (pair j ν) w ∈ᴮ X)
         (w ∈ᴮ v))) := by
  have Hξ := mem_domain_of_is_function Hentry HRun
  have Hparts := mem_successfulRows_iff.mp Hactive
  exact row_properties_of_least HE HElaw
    (is_func'_of_is_function
      (fusion_prefix_coordinates_function HRun Hlaw (subset_of_mem_Ord Hξ omegaOne_Ord)))
    (mem_of_mem_Ord Hparts.1 Hξ omegaOne_Ord) Hparts.2
    (fusion_run_row_least HJ Habsorb Hclosure HE HElaw HF HFlaw Hhull Hseeds Htop
      HRun Hlaw Hentry Hactive Hνv)

/-- The computed physical point on each successful old row has the
opposite-color edge to the same terminal, before choosing the next block. -/
theorem fusion_run_currentPoint_terminal
    {color : Bool} {R J E S F B P Y top Run ξ ν : bSet 𝔹} {Γ : 𝔹}
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
    (Hlaw : Γ ≤ runLaw color R E F top Run) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne)
    (Hactive : Γ ≤ ν ∈ᴮ successfulRows color R ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))) :
    Γ ≤ graphColor (!color) R
      (currentPoint E (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
        (nextIndices color R E top ξ (taggedPrefix ξ omegaOne entrySpace Run)) ν) top := by
  let T := taggedPrefix ξ omegaOne entrySpace Run
  let Blocks := blockHistory T
  let Z := nextIndices color R E top ξ T
  have Hparts := mem_successfulRows_iff.mp Hactive
  have Hν : Γ ≤ ν ∈ᴮ omegaOne := mem_of_mem_Ord Hparts.1 Hξ omegaOne_Ord
  have Hchoice : Γ ≤ pair ν (graphValue omegaOne Z ν) ∈ᴮ Z :=
    graphValue_pair_mem nextIndices_is_function Hν
  have Hleast := fusion_run_next_row_least HJ Habsorb Hclosure HE HElaw HF HFlaw Hhull
    Hseeds Htop HRun Hlaw Hξ Hactive Hchoice
  have Hr : Γ ≤ is_function omegaOne omegaTwo (canonicalRow E (blockValue Blocks ν)) :=
    (canonicalRow_data HE HElaw Hparts.2).trans (inf_le_left.trans inf_le_left)
  have Hpoint := currentPoint_spec HE HElaw (show Γ ≤ is_function omegaOne omegaOne Z from
    nextIndices_is_function) Hν Hparts.2
  exact fusionCandidate_seed_edge
    (is_func'_of_is_function
      (fusion_prefix_coordinates_function HRun Hlaw (subset_of_mem_Ord Hξ omegaOne_Ord))) Hν
    (Hr.trans (inf_le_left.trans inf_le_left)) (leastIn_mem Hleast)
    (Hpoint.trans (inf_le_right.trans inf_le_left))

theorem fusion_run_currentPoints_terminal
    {color : Bool} {R J E S F B P Y top Run ξ : bSet 𝔹} {Γ : 𝔹}
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
    (Hlaw : Γ ≤ runLaw color R E F top Run) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) :
    Γ ≤ ⨅ x, _root_.imp
      (x ∈ᴮ ErdosFusionHistories.currentPoints color R E ξ
        (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
        (nextIndices color R E top ξ (taggedPrefix ξ omegaOne entrySpace Run)))
      (graphColor (!color) R x top) := by
  apply le_iInf
  intro x
  rw [← deduction]
  obtain ⟨ν, Hν, Hx⟩ := ErdosFusionActiveHistory.currentPoints_witness
    (show Γ ⊓ x ∈ᴮ ErdosFusionHistories.currentPoints color R E ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
      (nextIndices color R E top ξ (taggedPrefix ξ omegaOne entrySpace Run)) ≤
      x ∈ᴮ ErdosFusionHistories.currentPoints color R E ξ
      (blockHistory (taggedPrefix ξ omegaOne entrySpace Run))
      (nextIndices color R E top ξ (taggedPrefix ξ omegaOne entrySpace Run)) from inf_le_right)
  exact bv_rw' (ϕ := fun z => graphColor (!color) R z top) Hx
    (h_congr := graphColor_ext_left (!color) R top)
    (H_new := fusion_run_currentPoint_terminal (inf_le_left.trans HJ)
      (inf_le_left.trans Habsorb) (inf_le_left.trans Hclosure)
      (inf_le_left.trans HE) (inf_le_left.trans HElaw) (inf_le_left.trans HF)
      (inf_le_left.trans HFlaw) (inf_le_left.trans Hhull) (inf_le_left.trans Hseeds)
      (inf_le_left.trans Htop) (inf_le_left.trans HRun) (inf_le_left.trans Hlaw)
      (inf_le_left.trans Hξ) Hν)

end bSet.ErdosFusionRunRowLegality
