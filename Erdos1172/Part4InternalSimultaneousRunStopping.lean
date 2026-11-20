/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousRunTotal

@[expose] public section

/-!
# Stopping and local successful-stage laws

An earlier occurrence of the endpoint makes every later future-candidate
set empty. The exact fallback rule therefore makes stopping persistent.
At a non-sentinel stage the actual decoded vertex obeys all order, color,
and active-coordinate constraints. No globally successful run, ideal,
cardinal hypothesis, or global truth condition is assumed here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartition ErdosOrdinalLeast ErdosOrdinalFallback
open ErdosSimultaneousHistory ErdosSimultaneousEntry ErdosSimultaneousVertex

/-- At a locally non-sentinel entry, the chosen vertex lies in the exact
future-candidate set computed from that entry's whole current row graph. -/
theorem nonstop_entry_mem_future
    {color : Bool} {R S top P i y Z : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hentry : Γ ≤ pair i (pair y Z) ∈ᴮ P) (Hne : Γ ≤ (y =ᴮ top)ᶜ) :
    Γ ≤ y ∈ᴮ futureCandidates color i R S (vertexHistory P) (coordinateHistory P) Z top :=
  leastIn_mem (next_vertex_ne_top_least
    ((runLaw_apply Hlaw Hentry).trans (inf_le_right.trans inf_le_right)) Hne)

theorem nonstop_stage_below_top
    {color : Bool} {R S top P i y : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hcurrent : Γ ≤ pair i y ∈ᴮ vertexHistory P) (Hne : Γ ≤ (y =ᴮ top)ᶜ) :
    Γ ≤ y ∈ᴮ top := by
  obtain ⟨Z, Hentry⟩ := vertexHistory_witness Hcurrent
  exact (mem_futureCandidates_iff.mp (nonstop_entry_mem_future Hlaw Hentry Hne)).1

/-- Only the current vertex needs to be non-sentinel; all earlier existing
vertices are automatically strictly below it and joined by the chosen color. -/
theorem nonstop_stage_above_previous
    {color : Bool} {R S top P i j y v : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hcurrent : Γ ≤ pair i y ∈ᴮ vertexHistory P) (Hne : Γ ≤ (y =ᴮ top)ᶜ)
    (Hji : Γ ≤ j ∈ᴮ i) (Hprevious : Γ ≤ pair j v ∈ᴮ vertexHistory P) :
    Γ ≤ v ∈ᴮ y ⊓ graphColor color R v y := by
  obtain ⟨Z, Hentry⟩ := vertexHistory_witness Hcurrent
  exact futureCandidate_above_previous (nonstop_entry_mem_future Hlaw Hentry Hne)
    Hji Hprevious

theorem nonstop_stage_color_top
    {color : Bool} {R S top P i y : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hcurrent : Γ ≤ pair i y ∈ᴮ vertexHistory P) (Hne : Γ ≤ (y =ᴮ top)ᶜ) :
    Γ ≤ graphColor color R y top := by
  obtain ⟨Z, Hentry⟩ := vertexHistory_witness Hcurrent
  exact futureCandidate_color_top (nonstop_entry_mem_future Hlaw Hentry Hne)

theorem nonstop_stage_old_active_section
    {color : Bool} {R S top P i j y σ w A : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hcurrent : Γ ≤ pair i y ∈ᴮ vertexHistory P) (Hne : Γ ≤ (y =ᴮ top)ᶜ)
    (Hji : Γ ≤ j ∈ᴮ i) (Hσj : Γ ≤ σ ∈ᴮ j)
    (Hcoord : Γ ≤ pair (pair j σ) w ∈ᴮ coordinateHistory P)
    (Hsection : Γ ≤ pair (pair σ y) A ∈ᴮ S) : Γ ≤ w ∈ᴮ A := by
  obtain ⟨Z, Hentry⟩ := vertexHistory_witness Hcurrent
  exact futureCandidate_old_active_section (nonstop_entry_mem_future Hlaw Hentry Hne)
    Hji Hσj Hcoord Hsection

/-- Exact entry uniqueness identifies the current row component even
without a separate global functionality hypothesis on the history. -/
theorem runLaw_coordinate_value_of_entry
    {color : Bool} {R S top P i y Z σ w : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hentry : Γ ≤ pair i (pair y Z) ∈ᴮ P)
    (Hcoord : Γ ≤ pair (pair i σ) w ∈ᴮ coordinateHistory P) :
    Γ ≤ pair σ w ∈ᴮ Z := by
  obtain ⟨z, W, Hother, Hw⟩ := coordinateHistory_witness Hcoord
  have HZW : Γ ≤ Z =ᴮ W := (entryValid_unique
    (runLaw_apply Hlaw Hentry) (runLaw_apply Hlaw Hother)).trans inf_le_right
  exact mem_congr bv_refl (bv_symm HZW) Hw

/-- The current active coordinate is read from the actual rectangular
decoder, not from an independently supplied current row function. -/
theorem nonstop_stage_current_active_section
    {color : Bool} {R S top P i y σ w A : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hcurrent : Γ ≤ pair i y ∈ᴮ vertexHistory P) (Hne : Γ ≤ (y =ᴮ top)ᶜ)
    (Hσi : Γ ≤ σ ∈ᴮ i)
    (Hcoord : Γ ≤ pair (pair i σ) w ∈ᴮ coordinateHistory P)
    (Hsection : Γ ≤ pair (pair σ y) A ∈ᴮ S) : Γ ≤ w ∈ᴮ A := by
  obtain ⟨Z, Hentry⟩ := vertexHistory_witness Hcurrent
  exact futureCandidate_current_active_section (nonstop_entry_mem_future Hlaw Hentry Hne)
    Hσi (runLaw_coordinate_value_of_entry Hlaw Hentry Hcoord) Hsection

end bSet.ErdosSimultaneousRun
