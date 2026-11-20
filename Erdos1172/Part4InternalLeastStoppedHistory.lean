/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountablyBoundedSup
public import Erdos1172.Part4InternalSimultaneousRunLaws
public import Erdos1172.Part4InternalSimultaneousRunStopping

@[expose] public section

/-!
# The least stopping stage and its strict prior-history bound

An actual occurrence of the endpoint in a full run supplies a least
stopping stage. All earlier vertices are non-sentinel and lie below the
endpoint. Their actual internal image is countable; countable boundedness
of the endpoint consequently supplies a strict cutoff at the original
Boolean condition. Stopping remains an explicit premise. This module
does not assume a supplied first stop or freeze a stationary history.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosOrdinalLeast ErdosRelationGraph
open ErdosSimultaneousEntry ErdosSimultaneousHistory ErdosCountableImage
open ErdosOmegaOneIdealBounded ErdosCountablyBoundedSup

def stoppingIndices (P top : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun i => pair i top ∈ᴮ vertexHistory P) omegaOne

theorem mem_stoppingIndices_iff {P top i : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ i ∈ᴮ stoppingIndices P top ↔
      Γ ≤ i ∈ᴮ omegaOne ∧ Γ ≤ pair i top ∈ᴮ vertexHistory P :=
  mem_comprehend_and B_ext_pair_mem_left

theorem stoppingIndices_subset {P top : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ stoppingIndices P top ⊆ᴮ omegaOne :=
  comprehend_subset (ϕ := fun i => pair i top ∈ᴮ vertexHistory P) omegaOne

/-- An arbitrary internal stopping witness, possibly mixed, gives one
actual least stopping index at the same Boolean condition. -/
theorem exists_least_stoppingIndex {P top : bSet 𝔹} {Γ : 𝔹}
    (Hfail : Γ ≤ rangeMem omegaOne (vertexHistory P) top) :
    ∃ ρ : bSet 𝔹, Γ ≤ leastIn (stoppingIndices P top) ρ := by
  obtain ⟨i, Hi⟩ := exists_convert Hfail
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hstop : Γ ≤ i ∈ᴮ stoppingIndices P top :=
    mem_stoppingIndices_iff.mpr ⟨Hi.trans inf_le_left, Hi.trans inf_le_right⟩
  exact exists_least_of_nonempty omegaOne_Ord stoppingIndices_subset
    (nonempty_of_exists_mem (stoppingIndices P top) (le_iSup_of_le i Hstop))

theorem least_stop_mem_omegaOne {P top ρ : bSet 𝔹} {Γ : 𝔹}
    (Hleast : Γ ≤ leastIn (stoppingIndices P top) ρ) : Γ ≤ ρ ∈ᴮ omegaOne :=
  (mem_stoppingIndices_iff.mp (leastIn_mem Hleast)).1

theorem least_stop_pair {P top ρ : bSet 𝔹} {Γ : 𝔹}
    (Hleast : Γ ≤ leastIn (stoppingIndices P top) ρ) :
    Γ ≤ pair ρ top ∈ᴮ vertexHistory P :=
  (mem_stoppingIndices_iff.mp (leastIn_mem Hleast)).2

theorem not_stopping_before_least {P top ρ i : bSet 𝔹} {Γ : 𝔹}
    (Hleast : Γ ≤ leastIn (stoppingIndices P top) ρ) (Hiρ : Γ ≤ i ∈ᴮ ρ) :
    Γ ≤ (pair i top ∈ᴮ vertexHistory P)ᶜ := by
  have Hi : Γ ≤ i ∈ᴮ omegaOne :=
    mem_of_mem_Ord Hiρ (least_stop_mem_omegaOne Hleast) omegaOne_Ord
  rw [← imp_bot, ← deduction]
  let Δ := Γ ⊓ pair i top ∈ᴮ vertexHistory P
  have Hstop : Δ ≤ i ∈ᴮ stoppingIndices P top :=
    mem_stoppingIndices_iff.mpr ⟨inf_le_left.trans Hi, inf_le_right⟩
  have Hcases : Δ ≤ ρ =ᴮ i ⊔ ρ ∈ᴮ i :=
    leastIn_apply (inf_le_left.trans Hleast) Hstop
  apply (le_inf (le_refl Δ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact bot_of_mem_self' (mem_congr bv_refl inf_le_right
      (inf_le_left.trans (inf_le_left.trans Hiρ)))
  · exact bot_of_mem_mem' i ρ (inf_le_left.trans (inf_le_left.trans Hiρ)) inf_le_right

theorem prior_vertex_ne_top {P top ρ i y : bSet 𝔹} {Γ : 𝔹}
    (Hleast : Γ ≤ leastIn (stoppingIndices P top) ρ) (Hiρ : Γ ≤ i ∈ᴮ ρ)
    (Hiy : Γ ≤ pair i y ∈ᴮ vertexHistory P) : Γ ≤ (y =ᴮ top)ᶜ := by
  have Hnot := not_stopping_before_least Hleast Hiρ
  rw [← imp_bot, ← deduction]
  have Hstop : Γ ⊓ y =ᴮ top ≤ pair i top ∈ᴮ vertexHistory P :=
    bv_rw'' (ϕ := fun z => pair i z ∈ᴮ vertexHistory P) inf_le_right
      (inf_le_left.trans Hiy) B_ext_pair_mem_right
  exact bv_absurd _ Hstop (inf_le_left.trans Hnot)

theorem prior_vertex_below_top_color
    {color : Bool} {R S top P ρ i y : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hleast : Γ ≤ leastIn (stoppingIndices P top) ρ) (Hiρ : Γ ≤ i ∈ᴮ ρ)
    (Hiy : Γ ≤ pair i y ∈ᴮ vertexHistory P) :
    Γ ≤ y ∈ᴮ top ⊓ graphColor color R y top := by
  have Hne := prior_vertex_ne_top Hleast Hiρ Hiy
  exact le_inf (nonstop_stage_below_top Hlaw Hiy Hne)
    (nonstop_stage_color_top Hlaw Hiy Hne)

/-- Only the strict prior vertex range is used; the sentinel at the
stopping stage is excluded by the domain itself. -/
def priorVertices (ρ P : bSet 𝔹) : bSet 𝔹 :=
  image ρ omegaTwo (vertexHistory P)

theorem priorVertices_countable {P ρ : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P) (Hρ : Γ ≤ ρ ∈ᴮ omegaOne) :
    Γ ≤ injects_into (priorVertices ρ P) bSet.omega :=
  image_countable
    (is_func'_subset_of_is_func'
      (is_func'_of_is_function (vertexHistory_is_function_of_run HP))
      (subset_of_mem_Ord Hρ omegaOne_Ord))
    (omegaOne_member_injects Hρ)

theorem priorVertices_subset_top
    {color : Bool} {R S top P ρ : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hleast : Γ ≤ leastIn (stoppingIndices P top) ρ) :
    Γ ≤ priorVertices ρ P ⊆ᴮ top := by
  rw [subset_unfold']
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ y ∈ᴮ priorVertices ρ P
  have Hrange : Δ ≤ ⨆ i, i ∈ᴮ ρ ⊓ pair i y ∈ᴮ vertexHistory P :=
    (mem_image_iff.mp (show Δ ≤ y ∈ᴮ priorVertices ρ P from inf_le_right)).2
  obtain ⟨i, Hi⟩ := exists_convert Hrange
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact (prior_vertex_below_top_color (inf_le_left.trans Hlaw)
    (inf_le_left.trans Hleast) (Hi.trans inf_le_left) (Hi.trans inf_le_right)).trans
    inf_le_left

/-- Countable boundedness also handles the zero stopping stage, whose
prior history is empty, and still supplies a strict internal cutoff. -/
theorem exists_prior_history_bound
    {color : Bool} {R S top P ρ : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hleast : Γ ≤ leastIn (stoppingIndices P top) ρ)
    (Hbounded : Γ ≤ countablyBounded top) :
    ∃ b : bSet 𝔹, Γ ≤ b ∈ᴮ top ⊓ priorVertices ρ P ⊆ᴮ b :=
  exists_bound_of_countablyBounded Hbounded (priorVertices_subset_top Hlaw Hleast)
    (priorVertices_countable HP (least_stop_mem_omegaOne Hleast))

/-- Construct both the first stop and a strict bound of its actual prior
history. The stopping and endpoint-boundedness hypotheses are explicit. -/
theorem exists_least_stopped_history_cutoff
    {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hfail : Γ ≤ rangeMem omegaOne (vertexHistory P) top)
    (Hbounded : Γ ≤ countablyBounded top) :
    ∃ ρ b : bSet 𝔹, Γ ≤ leastIn (stoppingIndices P top) ρ ⊓
      (injects_into (priorVertices ρ P) bSet.omega ⊓
        (priorVertices ρ P ⊆ᴮ top ⊓ (b ∈ᴮ top ⊓ priorVertices ρ P ⊆ᴮ b))) := by
  obtain ⟨ρ, Hleast⟩ := exists_least_stoppingIndex Hfail
  obtain ⟨b, Hb⟩ := exists_prior_history_bound HP Hlaw Hleast Hbounded
  exact ⟨ρ, b, le_inf Hleast
    (le_inf (priorVertices_countable HP (least_stop_mem_omegaOne Hleast))
      (le_inf (priorVertices_subset_top Hlaw Hleast) Hb))⟩

end bSet.ErdosSimultaneousRun
