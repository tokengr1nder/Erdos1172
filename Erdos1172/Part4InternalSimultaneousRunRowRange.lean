/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousRunLaws
public import Erdos1172.Part4InternalSimultaneousTraces
public import Erdos1172.Part4InternalGreedyRange

@[expose] public section

/-!
Every decoded row of a full simultaneous run obeys the exact full greedy
law. Its stage candidates are compared with the guarded prefixes of the
full trace graphs; the local and full graphs are not asserted equal.
Normality therefore makes the actual row range co-large, whether or not
the vertex sequence reaches its endpoint sentinel. No homogeneous block
or common set for all vertex sections is asserted here.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosRowCandidates ErdosOrdinalLeast
open ErdosGreedyPartial ErdosColargeIntersection ErdosSimultaneousEntry
open ErdosSimultaneousHistory ErdosSimultaneousCandidates ErdosSimultaneousTraces

/-- Only the guarded earlier coordinates of the full trace graphs are
read at stage i. Full trace support must not be confused with stage support. -/
theorem mem_simultaneousCandidates_iff_full_rowCandidates
    {i S Y X top σ seed v : bSet 𝔹} {Γ : 𝔹}
    (Hi : Γ ≤ i ⊆ᴮ omegaOne)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (HY : Γ ≤ is_func' omegaOne omegaTwo Y)
    (HX : Γ ≤ is_func' (prod omegaOne omegaOne) omegaOne X)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hseed : Γ ≤ pair (pair σ top) seed ∈ᴮ S) :
    (Γ ≤ v ∈ᴮ simultaneousCandidates i S Y X top σ) ↔
      Γ ≤ v ∈ᴮ rowCandidates i seed (sectionTrace omegaOne S Y σ)
        (rowHistory omegaOne X σ) := by
  have Hhistory : Γ ≤ is_func' i omegaOne (rowHistory omegaOne X σ) :=
    is_func'_subset_of_is_func'
      ((rowHistory_is_function HX Hσ).trans inf_le_left) Hi
  rw [mem_rowCandidates_iff Hhistory]
  constructor
  · intro Hv
    refine le_inf (mem_simultaneousCandidates_iff.mp Hv).1
      (le_inf (simultaneousCandidate_mem_seed Hv Hseed) (le_inf ?_ ?_))
    · apply le_iInf
      intro j
      apply le_iInf
      intro A
      rw [← deduction]
      let Δ := Γ ⊓ (j ∈ᴮ i ⊓ pair j A ∈ᴮ sectionTrace omegaOne S Y σ)
      obtain ⟨y, Hjy, HyA⟩ := sectionTrace_witness
        (show Δ ≤ pair j A ∈ᴮ sectionTrace omegaOne S Y σ from
          inf_le_right.trans inf_le_right)
      exact simultaneousCandidate_mem_previous_section (inf_le_left.trans Hv)
        (inf_le_right.trans inf_le_left) Hjy HyA
    · apply le_iInf
      intro j
      apply le_iInf
      intro w
      rw [← deduction]
      exact simultaneousCandidate_above_previous (inf_le_left.trans Hv)
        (inf_le_right.trans inf_le_left)
        (rowHistory_apply (inf_le_right.trans inf_le_right))
  · intro Hv
    have Hvω : Γ ≤ v ∈ᴮ omegaOne := Hv.trans inf_le_left
    have Hvseed : Γ ≤ v ∈ᴮ seed := Hv.trans (inf_le_right.trans inf_le_left)
    have Hvsections : Γ ≤ ⨅ j, ⨅ A, _root_.imp
        (j ∈ᴮ i ⊓ pair j A ∈ᴮ sectionTrace omegaOne S Y σ) (v ∈ᴮ A) :=
      Hv.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    have Hvprevious : Γ ≤ ⨅ j, ⨅ w, _root_.imp
        (j ∈ᴮ i ⊓ pair j w ∈ᴮ rowHistory omegaOne X σ) (w ∈ᴮ v) :=
      Hv.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
    apply mem_simultaneousCandidates_iff.mpr
    refine ⟨Hvω, le_inf ?_ (le_inf ?_ ?_)⟩
    · apply le_iInf
      intro A
      rw [← deduction]
      have HseedA : Γ ⊓ pair (pair σ top) A ∈ᴮ S ≤ seed =ᴮ A :=
        eq_of_is_func_of_eq (inf_le_left.trans (HS.trans inf_le_left)) bv_refl
          (inf_le_left.trans Hseed) inf_le_right
      exact mem_congr bv_refl HseedA (inf_le_left.trans Hvseed)
    · apply le_iInf
      intro j
      apply le_iInf
      intro y
      apply le_iInf
      intro A
      rw [← deduction]
      let Δ := Γ ⊓ (j ∈ᴮ i ⊓ (pair j y ∈ᴮ Y ⊓ pair (pair σ y) A ∈ᴮ S))
      have Hjω : Δ ≤ j ∈ᴮ omegaOne :=
        mem_of_mem_subset (inf_le_left.trans Hi) (inf_le_right.trans inf_le_left)
      have HjA : Δ ≤ pair j A ∈ᴮ sectionTrace omegaOne S Y σ :=
        (sectionTrace_pair_iff (inf_le_left.trans HY) (inf_le_left.trans HS)
          (inf_le_left.trans Hσ) Hjω
          (inf_le_right.trans (inf_le_right.trans inf_le_left))).mpr
          (inf_le_right.trans (inf_le_right.trans inf_le_right))
      exact (le_inf (inf_le_left.trans
        (Hvsections.trans ((iInf_le _ j).trans (iInf_le _ A))))
        (le_inf (inf_le_right.trans inf_le_left) HjA)).trans bv_imp_elim
    · apply le_iInf
      intro j
      apply le_iInf
      intro w
      rw [← deduction]
      let Δ := Γ ⊓ (j ∈ᴮ i ⊓ pair (pair j σ) w ∈ᴮ X)
      have Hjω : Δ ≤ j ∈ᴮ omegaOne :=
        mem_of_mem_subset (inf_le_left.trans Hi) (inf_le_right.trans inf_le_left)
      have Hjw : Δ ≤ pair j w ∈ᴮ rowHistory omegaOne X σ :=
        (rowHistory_pair_iff (inf_le_left.trans HX) (inf_le_left.trans Hσ) Hjω).mpr
          (inf_le_right.trans inf_le_right)
      exact (le_inf (inf_le_left.trans
        (Hvprevious.trans ((iInf_le _ j).trans (iInf_le _ w))))
        (le_inf (inf_le_right.trans inf_le_left) Hjw)).trans bv_imp_elim

theorem simultaneousCandidates_eq_full_rowCandidates
    {i S Y X top σ seed : bSet 𝔹} {Γ : 𝔹}
    (Hi : Γ ≤ i ⊆ᴮ omegaOne)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (HY : Γ ≤ is_func' omegaOne omegaTwo Y)
    (HX : Γ ≤ is_func' (prod omegaOne omegaOne) omegaOne X)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hseed : Γ ≤ pair (pair σ top) seed ∈ᴮ S) :
    Γ ≤ simultaneousCandidates i S Y X top σ =ᴮ
      rowCandidates i seed (sectionTrace omegaOne S Y σ) (rowHistory omegaOne X σ) := by
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    exact (mem_simultaneousCandidates_iff_full_rowCandidates
      (inf_le_left.trans Hi) (inf_le_left.trans HS) (inf_le_left.trans HY)
      (inf_le_left.trans HX) (inf_le_left.trans Hσ) (inf_le_left.trans Hseed)).mp inf_le_right
  · apply le_iInf
    intro v
    rw [← deduction]
    exact (mem_simultaneousCandidates_iff_full_rowCandidates
      (inf_le_left.trans Hi) (inf_le_left.trans HS) (inf_le_left.trans HY)
      (inf_le_left.trans HX) (inf_le_left.trans Hσ) (inf_le_left.trans Hseed)).mpr inf_le_right

/-- The actual full row graph, not an assumed enumeration of its range. -/
theorem run_row_is_function {color : Bool} {R S top P σ : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P) (Hσ : Γ ≤ σ ∈ᴮ omegaOne) :
    Γ ≤ is_function omegaOne omegaOne (rowHistory omegaOne (coordinateHistory P) σ) :=
  rowHistory_is_function
    (is_func'_of_is_function (coordinateHistory_is_function_of_run HP Hlaw)) Hσ

theorem run_row_greedyLaw {color : Bool} {R S top P σ seed : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hseed : Γ ≤ pair (pair σ top) seed ∈ᴮ S) :
    Γ ≤ greedyLaw seed (sectionTrace omegaOne S (vertexHistory P) σ)
      (rowHistory omegaOne (coordinateHistory P) σ) := by
  have HY : Γ ≤ is_func' omegaOne omegaTwo (vertexHistory P) :=
    is_func'_of_is_function (vertexHistory_is_function_of_run HP)
  have HX : Γ ≤ is_func' (prod omegaOne omegaOne) omegaOne (coordinateHistory P) :=
    is_func'_of_is_function (coordinateHistory_is_function_of_run HP Hlaw)
  apply le_iInf
  intro i
  apply le_iInf
  intro v
  rw [← deduction]
  let Δ := Γ ⊓ pair i v ∈ᴮ rowHistory omegaOne (coordinateHistory P) σ
  have Hparts := mem_rowHistory_iff.mp
    (show Δ ≤ pair i v ∈ᴮ rowHistory omegaOne (coordinateHistory P) σ from inf_le_right)
  have Hleast : Δ ≤ leastIn
      (simultaneousCandidates i S (vertexHistory P) (coordinateHistory P) top σ) v :=
    coordinate_least_of_run (inf_le_left.trans Hlaw) Hparts.2.2
  have Heq := simultaneousCandidates_eq_full_rowCandidates
    (subset_of_mem_Ord Hparts.1 omegaOne_Ord) (inf_le_left.trans HS)
    (inf_le_left.trans HY) (inf_le_left.trans HX) (inf_le_left.trans Hσ)
    (inf_le_left.trans Hseed)
  exact bv_rw'' (ϕ := fun C => leastIn C v) Heq Hleast (leastIn_ext_set v)

theorem run_row_increasing {color : Bool} {R S top P σ seed : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hseed : Γ ≤ pair (pair σ top) seed ∈ᴮ S) :
    Γ ≤ increasingOn omegaOne (rowHistory omegaOne (coordinateHistory P) σ) :=
  increasingOn_of_greedyLaw (is_func'_of_is_function (run_row_is_function HP Hlaw Hσ))
    (run_row_greedyLaw HP Hlaw HS Hσ Hseed)

theorem run_row_is_injective {color : Bool} {R S top P σ seed : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hseed : Γ ≤ pair (pair σ top) seed ∈ᴮ S) :
    Γ ≤ is_injective_function omegaOne omegaOne (rowHistory omegaOne (coordinateHistory P) σ) :=
  is_injective_function_of_greedyLaw (run_row_is_function HP Hlaw Hσ)
    (run_row_greedyLaw HP Hlaw HS Hσ Hseed)

theorem run_row_range_colarge {color : Bool} {J R S top P σ seed : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hnormal : Γ ≤ diagonalClosure omegaOne J)
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hseed : Γ ≤ pair (pair σ top) seed ∈ᴮ S)
    (HseedColarge : Γ ≤ colarge omegaOne J seed)
    (Hvalues : Γ ≤ ⨅ y, ⨅ A, _root_.imp
      (y ∈ᴮ omegaTwo ⊓ pair (pair σ y) A ∈ᴮ S) (colarge omegaOne J A)) :
    Γ ≤ colarge omegaOne J
      (image omegaOne omegaOne (rowHistory omegaOne (coordinateHistory P) σ)) := by
  have HY : Γ ≤ is_func' omegaOne omegaTwo (vertexHistory P) :=
    is_func'_of_is_function (vertexHistory_is_function_of_run HP)
  have HF : Γ ≤ is_func' omegaOne (bv_powerset omegaOne)
      (sectionTrace omegaOne S (vertexHistory P) σ) :=
    is_func'_of_is_function (sectionTrace_is_function HY HS Hσ)
  have HtraceValues := sectionTrace_row_colarge_values HY Hvalues
  have Hsmall : Γ ≤ ⨅ i, ⨅ A, _root_.imp
      (i ∈ᴮ omegaOne ⊓ pair i A ∈ᴮ sectionTrace omegaOne S (vertexHistory P) σ)
      (difference omegaOne A ∈ᴮ J) := by
    apply le_iInf
    intro i
    apply le_iInf
    intro A
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans
      (HtraceValues.trans ((iInf_le _ i).trans (iInf_le _ A)))) inf_le_right).trans
      bv_imp_elim).trans inf_le_right
  exact greedy_range_colarge HJ Habsorb Hclosure Hnormal HseedColarge HF Hsmall
    (is_func'_of_is_function (run_row_is_function HP Hlaw Hσ))
    (run_row_greedyLaw HP Hlaw HS Hσ Hseed)

/-- All properties concern the very same explicit decoded row graph.
Normality is supplied for this row's ideal, not inferred from rowIdealData. -/
theorem run_row_increasing_injective_colarge
    {color : Bool} {J R S top P σ seed : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hnormal : Γ ≤ diagonalClosure omegaOne J)
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hseed : Γ ≤ pair (pair σ top) seed ∈ᴮ S)
    (HseedColarge : Γ ≤ colarge omegaOne J seed)
    (Hvalues : Γ ≤ ⨅ y, ⨅ A, _root_.imp
      (y ∈ᴮ omegaTwo ⊓ pair (pair σ y) A ∈ᴮ S) (colarge omegaOne J A)) :
    Γ ≤ is_injective_function omegaOne omegaOne
        (rowHistory omegaOne (coordinateHistory P) σ) ⊓
      (increasingOn omegaOne (rowHistory omegaOne (coordinateHistory P) σ) ⊓
        colarge omegaOne J
          (image omegaOne omegaOne (rowHistory omegaOne (coordinateHistory P) σ))) :=
  le_inf (run_row_is_injective HP Hlaw HS Hσ Hseed)
    (le_inf (run_row_increasing HP Hlaw HS Hσ Hseed)
      (run_row_range_colarge HJ Habsorb Hclosure Hnormal HP Hlaw HS Hσ Hseed
        HseedColarge Hvalues))

end bSet.ErdosSimultaneousRun
