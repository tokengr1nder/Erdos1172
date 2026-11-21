/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRowCandidates

@[expose] public section

/-!
# Exact candidate sets depend only on their guarded prefix

The block and coordinate graphs may differ outside the current prefix.
Agreement on guarded pairs suffices for equality of the entire legal
candidate set, not only for transport of a chosen candidate. This permits
leastness to pass between an actual run prefix and its full decoded graph
without asserting a false equality of those graphs or smaller support.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionCandidateRestriction

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosFusionRowCandidates ErdosRowCandidates ErdosSimultaneousTraces

theorem fusionRowCandidates_mem_of_history_transfer
    {edgeColor : Bool} {R E b top ξ ν Blocks Blocks' X X' v : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X)
    (HX' : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X')
    (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (HBlocks : ∀ j A Δ, Δ ≤ Γ → Δ ≤ j ∈ᴮ ξ → Δ ≤ pair j A ∈ᴮ Blocks' → Δ ≤ pair j A ∈ᴮ Blocks)
    (Hcoords : ∀ j w Δ, Δ ≤ Γ → Δ ≤ j ∈ᴮ ξ →
      Δ ≤ pair (pair j ν) w ∈ᴮ X' → Δ ≤ pair (pair j ν) w ∈ᴮ X)
    (Hv : Γ ≤ v ∈ᴮ fusionRowCandidates edgeColor R E b top ξ ν Blocks X) :
    Γ ≤ v ∈ᴮ fusionRowCandidates edgeColor R E b top ξ ν Blocks' X' := by
  have Hlegal := (mem_fusionRowCandidates_iff HX Hν).mp Hv
  apply (mem_fusionRowCandidates_iff HX' Hν).mpr
  refine le_inf (Hlegal.trans inf_le_left)
    (le_inf (Hlegal.trans (inf_le_right.trans inf_le_left)) (le_inf ?_ ?_))
  · apply le_iInf
    intro j
    apply le_iInf
    intro A
    rw [← deduction]
    let Δ := Γ ⊓ (j ∈ᴮ activatedStages ξ ν ⊓
      pair j A ∈ᴮ fusionSectionFamily edgeColor R E b Blocks' ξ)
    have Hj := mem_activatedStages_iff.mp
      (show Δ ≤ j ∈ᴮ activatedStages ξ ν from inf_le_right.trans inf_le_left)
    have Heq := (mem_fusionSectionFamily_iff.mp
      (show Δ ≤ pair j A ∈ᴮ fusionSectionFamily edgeColor R E b Blocks' ξ from
        inf_le_right.trans inf_le_right)).2.2
    have Hsection : Δ ≤ v ∈ᴮ fusionSection edgeColor R E b Blocks' j := by
      apply mem_fusionSection_iff.mpr
      refine ⟨inf_le_left.trans (Hlegal.trans inf_le_left), ?_⟩
      apply le_iInf
      intro c
      apply le_iInf
      intro x
      apply le_iInf
      intro y
      rw [← deduction]
      let Ξ := Δ ⊓ ((pair j c ∈ᴮ Blocks' ⊓ pair v x ∈ᴮ canonicalRow E b) ⊓ y ∈ᴮ c)
      have HΞ : Ξ ≤ Γ := inf_le_left.trans inf_le_left
      exact fusionCandidate_cross_previous_block (HΞ.trans HX) (HΞ.trans Hν)
        (HΞ.trans Hv) (inf_le_left.trans Hj.1) (inf_le_left.trans Hj.2)
        (HBlocks j c Ξ HΞ (inf_le_left.trans Hj.1)
          (inf_le_right.trans (inf_le_left.trans inf_le_left)))
        (inf_le_right.trans (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right)
    exact mem_congr bv_refl (bv_symm Heq) Hsection
  · apply le_iInf
    intro j
    apply le_iInf
    intro w
    rw [← deduction]
    let Δ := Γ ⊓ (j ∈ᴮ activatedStages ξ ν ⊓ pair j w ∈ᴮ rowHistory ξ X' ν)
    have HΔ : Δ ≤ Γ := inf_le_left
    have Hj := mem_activatedStages_iff.mp
      (show Δ ≤ j ∈ᴮ activatedStages ξ ν from inf_le_right.trans inf_le_left)
    have Hpair : Δ ≤ pair (pair j ν) w ∈ᴮ X' :=
      (rowHistory_pair_iff (HΔ.trans HX') (HΔ.trans Hν) Hj.1).mp
        (show Δ ≤ pair j w ∈ᴮ rowHistory ξ X' ν from inf_le_right.trans inf_le_right)
    exact fusionCandidate_above_previous (HΔ.trans HX) (HΔ.trans Hν)
      (HΔ.trans Hv) Hj.1 Hj.2 (Hcoords j w Δ HΔ Hj.1 Hpair)

/-- Guarded pair coherence identifies the exact sets, so it preserves
leastness as well as legality. Neither graph is claimed equal globally. -/
theorem fusionRowCandidates_eq_of_history_coherence
    {edgeColor : Bool} {R E b top ξ ν Blocks Blocks' X X' : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X)
    (HX' : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X')
    (Hν : Γ ≤ ν ∈ᴮ omegaOne)
    (HBlocks : ∀ j A Δ, Δ ≤ Γ → Δ ≤ j ∈ᴮ ξ → ((Δ ≤ pair j A ∈ᴮ Blocks) ↔ Δ ≤ pair j A ∈ᴮ Blocks'))
    (Hcoords : ∀ j v Δ, Δ ≤ Γ → Δ ≤ j ∈ᴮ ξ →
      ((Δ ≤ pair (pair j ν) v ∈ᴮ X) ↔ Δ ≤ pair (pair j ν) v ∈ᴮ X')) :
    Γ ≤ fusionRowCandidates edgeColor R E b top ξ ν Blocks X =ᴮ
      fusionRowCandidates edgeColor R E b top ξ ν Blocks' X' := by
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    exact fusionRowCandidates_mem_of_history_transfer
      (inf_le_left.trans HX) (inf_le_left.trans HX') (inf_le_left.trans Hν)
      (fun j A Δ HΔ Hj Hpair => (HBlocks j A Δ (HΔ.trans inf_le_left) Hj).mpr Hpair)
      (fun j w Δ HΔ Hj Hpair => (Hcoords j w Δ (HΔ.trans inf_le_left) Hj).mpr Hpair)
      inf_le_right
  · apply le_iInf
    intro v
    rw [← deduction]
    exact fusionRowCandidates_mem_of_history_transfer
      (inf_le_left.trans HX') (inf_le_left.trans HX) (inf_le_left.trans Hν)
      (fun j A Δ HΔ Hj Hpair => (HBlocks j A Δ (HΔ.trans inf_le_left) Hj).mp Hpair)
      (fun j w Δ HΔ Hj Hpair => (Hcoords j w Δ (HΔ.trans inf_le_left) Hj).mp Hpair)
      inf_le_right

end bSet.ErdosFusionCandidateRestriction
