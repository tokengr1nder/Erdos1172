/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRowCandidateCongruence

@[expose] public section

/-!
# The actual total least-or-zero current-coordinate graph

Successful old rows use their exact activated candidate set. Other rows
have an empty masked set and choose zero. On an empty candidate set the
same zero fallback is used, without claiming it legal. The supported
omega-one-to-omega-one graph exists for arbitrary (even malformed) input
histories. Ideals enter only when proving least-choice legality later.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRowChoice

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosRelationGraph ErdosOrdinalLeast
open ErdosOrdinalFallback ErdosFusionHistories ErdosFusionHistoryCongruence
open ErdosFusionRowCandidates ErdosIdeal ErdosColargeIntersection

def rowCandidatesAt (color : Bool) (R E top ξ Blocks X ν : bSet 𝔹) : bSet 𝔹 :=
  fusionRowCandidates (!color) R E (blockValue Blocks ν) top ξ ν Blocks X

theorem rowCandidatesAt_congr_row (color : Bool) (R E top ξ Blocks X : bSet 𝔹) :
    B_congr (rowCandidatesAt color R E top ξ Blocks X) := by
  intro ν μ Γ H
  exact bv_trans
    (fusionRowCandidates_congr_object (!color) R E top ξ ν Blocks X (blockValue_congr Blocks H))
    (fusionRowCandidates_congr_row (!color) R E (blockValue Blocks μ) top ξ Blocks X H)

def maskedCandidates (color : Bool) (R E top ξ Blocks X ν : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun v => ν ∈ᴮ successfulRows color R ξ Blocks ⊓
    v ∈ᴮ rowCandidatesAt color R E top ξ Blocks X ν) omegaOne

theorem mem_maskedCandidates_iff
    {color : Bool} {R E top ξ Blocks X ν v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ v ∈ᴮ maskedCandidates color R E top ξ Blocks X ν ↔
      Γ ≤ v ∈ᴮ omegaOne ∧
        Γ ≤ ν ∈ᴮ successfulRows color R ξ Blocks ⊓
          v ∈ᴮ rowCandidatesAt color R E top ξ Blocks X ν :=
  mem_comprehend_and (B_ext_inf B_ext_const B_ext_mem_left)

theorem maskedCandidates_subset
    {color : Bool} {R E top ξ Blocks X ν : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ maskedCandidates color R E top ξ Blocks X ν ⊆ᴮ omegaOne :=
  comprehend_subset (ϕ := fun v => ν ∈ᴮ successfulRows color R ξ Blocks ⊓
    v ∈ᴮ rowCandidatesAt color R E top ξ Blocks X ν) omegaOne

theorem maskedCandidates_congr_row (color : Bool) (R E top ξ Blocks X : bSet 𝔹) :
    B_congr (maskedCandidates color R E top ξ Blocks X) :=
  comprehend_parameter_congr omegaOne
    (fun ν v => ν ∈ᴮ successfulRows color R ξ Blocks ⊓
      v ∈ᴮ rowCandidatesAt color R E top ξ Blocks X ν)
    (fun _ => B_ext_inf B_ext_const B_ext_mem_left)
    (fun _ => B_ext_inf B_ext_mem_left
      (B_ext_term _ _ B_ext_mem_right (rowCandidatesAt_congr_row color R E top ξ Blocks X)))

theorem maskedCandidates_eq_of_active
    {color : Bool} {R E top ξ Blocks X ν : bSet 𝔹} {Γ : 𝔹}
    (Hactive : Γ ≤ ν ∈ᴮ successfulRows color R ξ Blocks) :
    Γ ≤ maskedCandidates color R E top ξ Blocks X ν =ᴮ
      rowCandidatesAt color R E top ξ Blocks X ν := by
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    exact ((mem_maskedCandidates_iff.mp
      (show Γ ⊓ v ∈ᴮ maskedCandidates color R E top ξ Blocks X ν ≤
        v ∈ᴮ maskedCandidates color R E top ξ Blocks X ν from inf_le_right)).2).trans
          inf_le_right
  · apply le_iInf
    intro v
    rw [← deduction]
    exact mem_maskedCandidates_iff.mpr
      ⟨mem_of_mem_subset fusionRowCandidates_subset inf_le_right,
        le_inf (inf_le_left.trans Hactive) inf_le_right⟩

def currentChoices (color : Bool) (R E top ξ Blocks X : bSet 𝔹) : bSet 𝔹 :=
  relationGraph omegaOne omegaOne
    (fun ν v => leastOrTop (maskedCandidates color R E top ξ Blocks X ν) 0 v)

theorem mem_currentChoices_iff
    {color : Bool} {R E top ξ Blocks X ν v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair ν v ∈ᴮ currentChoices color R E top ξ Blocks X ↔
      Γ ≤ ν ∈ᴮ omegaOne ∧ Γ ≤ v ∈ᴮ omegaOne ∧
        Γ ≤ leastOrTop (maskedCandidates color R E top ξ Blocks X ν) 0 v :=
  mem_relationGraph_iff
    (fun v => B_ext_term _ _ (leastOrTop_ext_set 0 v)
      (maskedCandidates_congr_row color R E top ξ Blocks X))
    (fun ν => leastOrTop_ext_value (maskedCandidates color R E top ξ Blocks X ν) 0)

/-- Totality and support hold without any validity, ideal, nonempty
candidate, or successful block premise. -/
theorem currentChoices_is_function
    {color : Bool} {R E top ξ Blocks X : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_function omegaOne omegaOne (currentChoices color R E top ξ Blocks X) := by
  apply relationGraph_is_function
    (fun v => B_ext_term _ _ (leastOrTop_ext_set 0 v)
      (maskedCandidates_congr_row color R E top ξ Blocks X))
    (fun ν => leastOrTop_ext_value (maskedCandidates color R E top ξ Blocks X ν) 0)
  · apply le_iInf
    intro ν
    rw [← deduction]
    obtain ⟨v, Hv⟩ := exists_bounded_leastOrTop omegaOne_Ord
      (maskedCandidates_subset (color := color) (R := R) (E := E) (top := top)
        (ξ := ξ) (Blocks := Blocks) (X := X) (ν := ν) (Γ := Γ ⊓ ν ∈ᴮ omegaOne))
      ErdosLargeDifference.zero_mem_omegaOne
    exact le_iSup_of_le v Hv
  · intro ν μ v w Δ _ _ _ _ _ Hv Hw Hνμ
    exact leastOrTop_unique_of_eq (maskedCandidates_congr_row color R E top ξ Blocks X Hνμ) Hv Hw

theorem currentChoices_least_of_witness
    {color : Bool} {R E top ξ Blocks X ν v w : bSet 𝔹} {Γ : 𝔹}
    (Hpair : Γ ≤ pair ν v ∈ᴮ currentChoices color R E top ξ Blocks X)
    (Hactive : Γ ≤ ν ∈ᴮ successfulRows color R ξ Blocks)
    (Hleast : Γ ≤ leastIn (rowCandidatesAt color R E top ξ Blocks X ν) w) :
    Γ ≤ leastIn (rowCandidatesAt color R E top ξ Blocks X ν) v := by
  have Hchoice : Γ ≤ leastOrTop (rowCandidatesAt color R E top ξ Blocks X ν) 0 v :=
    bv_rw'' (maskedCandidates_eq_of_active Hactive)
      (mem_currentChoices_iff.mp Hpair).2.2 (leastOrTop_ext_set 0 v)
  have Heq : Γ ≤ v =ᴮ w := leastOrTop_unique Hchoice (leastOrTop_of_least Hleast)
  exact bv_rw' Heq (h_congr := leastIn_ext_value _) (H_new := Hleast)

end bSet.ErdosFusionRowChoice
