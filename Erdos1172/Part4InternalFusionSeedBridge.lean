/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRowCandidates
public import Erdos1172.Part4InternalFusionHistories
public import Erdos1172.Part4InternalClosedPoolFuture
public import Erdos1172.Part4InternalSeedBlock

@[expose] public section

/-!
# Structural seed and section laws for the second fusion

The same fixed enumeration identifies each canonical row. The constructed
pool future supplies its terminal seed. An actual intermediate block
candidate supplies a co-large cross-row subset, which lies in the exact
whole-block section. An empty intermediate block has the full section.
Boolean mixtures of these alternatives are handled inside the algebra.

Thus least row choice follows from real stored candidate-or-failure laws,
not from an assumed nonempty candidate or successful intermediate run.
The full block graph may have later support: strict-prefix membership is
proved from its actual pairs and is never confused with graph restriction.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionSeedBridge

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosCanonicalBlocks ErdosBlockCandidate
open ErdosFusionRowCandidates ErdosFusionHistories ErdosForwardSections
open ErdosClosedPoolFuture ErdosColargeIntersection ErdosGreedyPartial ErdosOrdinalLeast
open ErdosRelationGraph

theorem forwardSection_subset_fusionSeed
    {edgeColor : Bool} {R E b top : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ forwardSection edgeColor R (canonicalRow E b) top ⊆ᴮ
      fusionSeed edgeColor R E b top := by
  rw [subset_unfold']
  apply le_iInf
  intro v
  rw [← deduction]
  have Hv := mem_forwardSection_iff.mp
    (show Γ ⊓ v ∈ᴮ forwardSection edgeColor R (canonicalRow E b) top ≤
      v ∈ᴮ forwardSection edgeColor R (canonicalRow E b) top from inf_le_right)
  apply mem_fusionSeed_iff.mpr
  refine ⟨Hv.1, Hv.2.trans ?_⟩
  apply iSup_le
  intro x
  exact le_iSup_of_le x (le_inf inf_le_left (inf_le_right.trans inf_le_right))

/-- The plain seed used by the row minimum contains the constructed
forward seed of this very same selected enumeration. -/
theorem fusionSeed_colarge_of_poolSeedLaw
    {color : Bool} {R J E B Y b top : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (Hseeds : Γ ≤ poolSeedLaw color R J E B Y)
    (Hb : Γ ≤ b ∈ᴮ B) (Htop : Γ ≤ top ∈ᴮ Y) :
    Γ ≤ colarge omegaOne J (fusionSeed (!color) R E b top) :=
  colarge_of_subset HJ
    (poolSeedLaw_apply Hseeds Hb (canonicalRow_pair HE (mem_of_mem_subset HB Hb)) Htop)
    forwardSection_subset_fusionSeed fusionSeed_subset

/-- A co-large cross-row witness constrains every value at the same
intermediate index, by functionality of the actual block history. -/
theorem rowCross_subset_fusionSection
    {color : Bool} {R E b Blocks j c C : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func Blocks) (Hjc : Γ ≤ pair j c ∈ᴮ Blocks)
    (HC : Γ ≤ C ⊆ᴮ omegaOne)
    (Hcross : Γ ≤ rowCross color R (canonicalRow E b) C c) :
    Γ ≤ C ⊆ᴮ fusionSection (!color) R E b Blocks j := by
  rw [subset_unfold']
  apply le_iInf
  intro v
  rw [← deduction]
  apply mem_fusionSection_iff.mpr
  refine ⟨mem_of_mem_subset (inf_le_left.trans HC) inf_le_right, ?_⟩
  apply le_iInf
  intro c'
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := (Γ ⊓ v ∈ᴮ C) ⊓
    ((pair j c' ∈ᴮ Blocks ⊓ pair v x ∈ᴮ canonicalRow E b) ⊓ y ∈ᴮ c')
  have Hc : Δ ≤ c' =ᴮ c :=
    eq_of_is_func_of_eq (inf_le_left.trans (inf_le_left.trans Hfunc)) bv_refl
      (inf_le_right.trans (inf_le_left.trans inf_le_left))
      (inf_le_left.trans (inf_le_left.trans Hjc))
  exact rowCross_apply (inf_le_left.trans (inf_le_left.trans Hcross))
    (show Δ ≤ v ∈ᴮ C from inf_le_left.trans inf_le_right)
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (mem_congr bv_refl Hc (inf_le_right.trans inf_le_right))

theorem fusionSection_colarge_of_oldRowsCompatible
    {color : Bool} {R J E b Blocks j c Earlier : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (Hb : Γ ≤ b ∈ᴮ blockObjects color R)
    (Hfunc : Γ ≤ is_func Blocks) (Hjc : Γ ≤ pair j c ∈ᴮ Blocks)
    (Hbefore : Γ ≤ b ∈ᴮ Earlier)
    (Hcompat : Γ ≤ oldRowsCompatible color R J E Earlier c) :
    Γ ≤ colarge omegaOne J (fusionSection (!color) R E b Blocks j) := by
  obtain ⟨C, HC, Hcross⟩ := oldRowsCompatible_witness Hcompat Hbefore (canonicalRow_pair HE Hb)
  exact colarge_of_subset HJ HC
    (rowCross_subset_fusionSection Hfunc Hjc (HC.trans inf_le_left) Hcross)
    fusionSection_subset

theorem fusionSection_colarge_of_blockCandidate
    {color : Bool} {R J E S b Blocks j c Earlier Active : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (Hb : Γ ≤ b ∈ᴮ blockObjects color R)
    (Hfunc : Γ ≤ is_func Blocks) (Hjc : Γ ≤ pair j c ∈ᴮ Blocks)
    (Hbefore : Γ ≤ b ∈ᴮ Earlier)
    (Hcandidate : Γ ≤ blockCandidate color R J E S Earlier Active c) :
    Γ ≤ colarge omegaOne J (fusionSection (!color) R E b Blocks j) :=
  fusionSection_colarge_of_oldRowsCompatible HJ HE Hb Hfunc Hjc Hbefore
    (blockCandidate_oldRows Hcandidate)

/-- Empty is the failure value, so its whole-block section is the full
base. Even properness is unnecessary for this co-largeness assertion. -/
theorem fusionSection_colarge_of_empty
    {edgeColor : Bool} {R J E b Blocks j : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J) (Hfunc : Γ ≤ is_func Blocks)
    (Hempty : Γ ≤ pair j (∅ : bSet 𝔹) ∈ᴮ Blocks) :
    Γ ≤ colarge omegaOne J (fusionSection edgeColor R E b Blocks j) :=
  bv_rw' (ϕ := colarge omegaOne J) (fusionSection_eq_omegaOne_of_empty Hfunc Hempty)
    (h_congr := colarge_ext_common omegaOne J)
    (H_new := ErdosSeedBlock.colarge_self_of_isIdeal HJ)

/-- The two alternatives are Boolean values, not an externally chosen
case. The same condition is retained in the result. -/
theorem fusionSection_colarge_of_candidate_or_empty
    {color : Bool} {R J E S b Blocks j c Earlier : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (Hb : Γ ≤ b ∈ᴮ blockObjects color R)
    (Hfunc : Γ ≤ is_func Blocks) (Hjc : Γ ≤ pair j c ∈ᴮ Blocks)
    (Hbefore : Γ ≤ b ∈ᴮ Earlier)
    (Hcases : Γ ≤ (c =ᴮ (∅ : bSet 𝔹)) ⊔
      (⨆ Active, blockCandidate color R J E S Earlier Active c)) :
    Γ ≤ colarge omegaOne J (fusionSection (!color) R E b Blocks j) := by
  apply (le_inf le_rfl Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact fusionSection_colarge_of_empty (inf_le_left.trans HJ) (inf_le_left.trans Hfunc)
      (mem_congr (pair_congr bv_refl inf_le_right) bv_refl (inf_le_left.trans Hjc))
  · rw [inf_iSup_eq]
    apply iSup_le
    intro Active
    exact fusionSection_colarge_of_blockCandidate (inf_le_left.trans HJ)
      (inf_le_left.trans HE) (inf_le_left.trans Hb) (inf_le_left.trans Hfunc)
      (inf_le_left.trans Hjc) (inf_le_left.trans Hbefore) inf_le_right

/-- The stored law records actual whole-block candidates or actual empty
failures. It does not assume the co-largeness of any derived section. -/
def storedBlockCandidates (color : Bool) (R J E S ξ Blocks : bSet 𝔹) : 𝔹 :=
  ⨅ j, ⨅ c, _root_.imp (j ∈ᴮ ξ ⊓ pair j c ∈ᴮ Blocks)
    ((c =ᴮ (∅ : bSet 𝔹)) ⊔
      (⨆ Active, blockCandidate color R J E S (earlierHistory color R j Blocks) Active c))

theorem storedBlockCandidates_apply
    {color : Bool} {R J E S ξ Blocks j c : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ storedBlockCandidates color R J E S ξ Blocks)
    (Hj : Γ ≤ j ∈ᴮ ξ) (Hjc : Γ ≤ pair j c ∈ᴮ Blocks) :
    Γ ≤ (c =ᴮ (∅ : bSet 𝔹)) ⊔
      (⨆ Active, blockCandidate color R J E S (earlierHistory color R j Blocks) Active c) :=
  (le_inf (H.trans ((iInf_le _ j).trans (iInf_le _ c))) (le_inf Hj Hjc)).trans bv_imp_elim

/-- A full graph is reused on the smaller image domain without claiming
that its graph support is restricted to that domain. -/
theorem earlierHistory_mem_of_pair_at_prefix
    {color : Bool} {R ξ Blocks ν j b : bSet 𝔹} {Γ : 𝔹}
    (HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks)
    (Hνb : Γ ≤ pair ν b ∈ᴮ Blocks) (Hνj : Γ ≤ ν ∈ᴮ j)
    (Hb : Γ ≤ b ∈ᴮ blockObjects color R) :
    Γ ≤ b ∈ᴮ earlierHistory color R j Blocks :=
  (mem_comprehend_and B_ext_mem_left).mpr
    ⟨mem_image Hνb Hνj (mem_codomain_of_is_function Hνb HBlocks), Hb⟩

/-- Every activated section is co-large from the actual earlier stored
candidate law, including when the intermediate output is partly empty. -/
theorem fusionSections_colarge_of_stored_candidates
    {color : Bool} {R J E S ξ Blocks ν b : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks)
    (Hνb : Γ ≤ pair ν b ∈ᴮ Blocks) (Hb : Γ ≤ b ∈ᴮ blockObjects color R)
    (Hstored : Γ ≤ storedBlockCandidates color R J E S ξ Blocks) :
    Γ ≤ ⨅ j, _root_.imp (j ∈ᴮ ξ ⊓ ν ∈ᴮ j)
      (colarge omegaOne J (fusionSection (!color) R E b Blocks j)) := by
  apply le_iInf
  intro j
  rw [← deduction]
  let Δ := Γ ⊓ (j ∈ᴮ ξ ⊓ ν ∈ᴮ j)
  have Hj : Δ ≤ j ∈ᴮ ξ := inf_le_right.trans inf_le_left
  have Hex : Δ ≤ ⨆ c, c ∈ᴮ bv_powerset omegaTwo ⊓ pair j c ∈ᴮ Blocks :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function HBlocks).trans (iInf_le _ j))) Hj).trans
      bv_imp_elim
  obtain ⟨c, Hc⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hbefore : Δ ≤ b ∈ᴮ earlierHistory color R j Blocks :=
    earlierHistory_mem_of_pair_at_prefix (inf_le_left.trans HBlocks)
      (inf_le_left.trans Hνb) (inf_le_right.trans inf_le_right) (inf_le_left.trans Hb)
  exact fusionSection_colarge_of_candidate_or_empty (inf_le_left.trans HJ)
    (inf_le_left.trans HE) (inf_le_left.trans Hb)
    (inf_le_left.trans (HBlocks.trans (inf_le_left.trans inf_le_left)))
    (Hc.trans inf_le_right) Hbefore
    (storedBlockCandidates_apply (inf_le_left.trans Hstored) Hj (Hc.trans inf_le_right))

/-- Both structural co-largeness premises of least row choice are now
derived from the pool future and the stored whole-block candidate law. -/
theorem exists_least_fusionRowCandidate_of_stored_candidates
    {color : Bool} {R J E S B Y b top ξ ν Blocks X : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne)
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X)
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HB : Γ ≤ B ⊆ᴮ blockObjects color R)
    (Hseeds : Γ ≤ poolSeedLaw color R J E B Y)
    (Hb : Γ ≤ b ∈ᴮ B) (Htop : Γ ≤ top ∈ᴮ Y)
    (HBlocks : Γ ≤ is_function ξ (bv_powerset omegaTwo) Blocks)
    (Hνb : Γ ≤ pair ν b ∈ᴮ Blocks)
    (Hstored : Γ ≤ storedBlockCandidates color R J E S ξ Blocks) :
    ∃ v : bSet 𝔹,
      Γ ≤ colarge omegaOne J (fusionRowCandidates (!color) R E b top ξ ν Blocks X) ⊓
        leastIn (fusionRowCandidates (!color) R E b top ξ ν Blocks X) v :=
  exists_least_fusionRowCandidate HJ Habsorb Hclosure Hξ
    (mem_of_mem_Ord (mem_domain_of_is_function Hνb HBlocks) Hξ omegaOne_Ord) HX
    (fusionSeed_colarge_of_poolSeedLaw (HJ.trans inf_le_left) HE HB Hseeds Hb Htop)
    (fusionSections_colarge_of_stored_candidates (HJ.trans inf_le_left) HE HBlocks
      Hνb (mem_of_mem_subset HB Hb) Hstored)

end bSet.ErdosFusionSeedBridge
