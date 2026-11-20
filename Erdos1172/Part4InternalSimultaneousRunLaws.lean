/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousRunTotal

@[expose] public section

/-!
# Decoded function and choice laws of an actual simultaneous run

The fixed history decoders become supported total functions when the
stored run has full domain. Every decoded row value is the actual least
candidate at its stage, and every decoded vertex comes from one stored
complete entry satisfying the least-or-sentinel law. All earlier stages
constrain every row; no active-triangle restriction is added to row choice.
These are laws of the constructed run, not assumptions of successful
vertex choices or of a homogeneous block.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosOrdinalLeast ErdosOrdinalFallback
open ErdosSimultaneousEntry ErdosSimultaneousHistory ErdosSimultaneousRowChoice
open ErdosSimultaneousCandidates ErdosSimultaneousVertex

/-- The fixed vertex decoder has exactly the required full support. -/
theorem vertexHistory_is_function_of_run {P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P) :
    Γ ≤ is_function omegaOne omegaTwo (vertexHistory P) :=
  le_inf (vertexHistory_is_func' subset_self (is_func'_of_is_function HP))
    vertexHistory_subset

/-- The stored entry law supplies the row functionality not contained in
the entry-space bound alone. Every stage supplies all omega-one rows. -/
theorem coordinateHistory_is_function_of_run
    {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P) :
    Γ ≤ is_function (prod omegaOne omegaOne) omegaOne (coordinateHistory P) :=
  le_inf (coordinateHistory_is_func'_prefix subset_self (is_func'_of_is_function HP)
    (runLaw_rowFunctions Hlaw)) coordinateHistory_subset

/-- A decoded coordinate comes from an actual stored row graph and is the
least member of its exact simultaneous candidate set at the same condition. -/
theorem coordinate_least_of_run
    {color : Bool} {R S top P i σ v : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hcoord : Γ ≤ pair (pair i σ) v ∈ᴮ coordinateHistory P) :
    Γ ≤ leastIn (simultaneousCandidates i S (vertexHistory P)
      (coordinateHistory P) top σ) v := by
  obtain ⟨y, Z, Hentry, Hrow⟩ := coordinateHistory_witness Hcoord
  have Hvalid := runLaw_apply Hlaw Hentry
  exact simultaneousRowLaw_apply (Hvalid.trans (inf_le_right.trans inf_le_left))
    (coordinateHistory_pair_iff.mp Hcoord).2.1 Hrow

theorem coordinate_mem_seed_of_run
    {color : Bool} {R S top P i σ v A : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hcoord : Γ ≤ pair (pair i σ) v ∈ᴮ coordinateHistory P)
    (HA : Γ ≤ pair (pair σ top) A ∈ᴮ S) : Γ ≤ v ∈ᴮ A :=
  simultaneousCandidate_mem_seed (leastIn_mem (coordinate_least_of_run Hlaw Hcoord)) HA

/-- All previous stages constrain the row, including stages before this
row became active in the separate next-vertex triangle. -/
theorem coordinate_mem_previous_section_of_run
    {color : Bool} {R S top P i σ v j y A : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hcoord : Γ ≤ pair (pair i σ) v ∈ᴮ coordinateHistory P)
    (Hji : Γ ≤ j ∈ᴮ i) (Hvertex : Γ ≤ pair j y ∈ᴮ vertexHistory P)
    (HA : Γ ≤ pair (pair σ y) A ∈ᴮ S) : Γ ≤ v ∈ᴮ A :=
  simultaneousCandidate_mem_previous_section
    (leastIn_mem (coordinate_least_of_run Hlaw Hcoord)) Hji Hvertex HA

theorem coordinate_above_previous_of_run
    {color : Bool} {R S top P i σ v j w : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hcoord : Γ ≤ pair (pair i σ) v ∈ᴮ coordinateHistory P)
    (Hji : Γ ≤ j ∈ᴮ i) (Hprevious : Γ ≤ pair (pair j σ) w ∈ᴮ coordinateHistory P) :
    Γ ≤ w ∈ᴮ v :=
  simultaneousCandidate_above_previous
    (leastIn_mem (coordinate_least_of_run Hlaw Hcoord)) Hji Hprevious

/-- Extract the actual row graph stored with a decoded vertex, retaining
both the original stored pair and its complete entry law. -/
theorem exists_run_entry
    {color : Bool} {R S top P i y : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hiy : Γ ≤ pair i y ∈ᴮ vertexHistory P) :
    ∃ Z : bSet 𝔹, Γ ≤ pair i (pair y Z) ∈ᴮ P ⊓
      entryValid color i R S (vertexHistory P) (coordinateHistory P) top y Z := by
  obtain ⟨Z, HZ⟩ := vertexHistory_witness Hiy
  exact ⟨Z, le_inf HZ (runLaw_apply Hlaw HZ)⟩

/-- The vertex fallback law refers to the very row graph stored with that
vertex, not an independently chosen graph or external row enumeration. -/
theorem exists_vertex_choice_of_run
    {color : Bool} {R S top P i y : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ runLaw color R S top P)
    (Hiy : Γ ≤ pair i y ∈ᴮ vertexHistory P) :
    ∃ Z : bSet 𝔹, Γ ≤ pair i (pair y Z) ∈ᴮ P ⊓
      leastOrTop (futureCandidates color i R S (vertexHistory P)
        (coordinateHistory P) Z top) top y := by
  obtain ⟨Z, HZ⟩ := exists_run_entry Hlaw Hiy
  exact ⟨Z, le_inf (HZ.trans inf_le_left)
    (HZ.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))⟩

/-- Construct a full run together with the full supported function laws
of both fixed decoders. Fallback vertices are allowed throughout. -/
theorem exists_simultaneous_run_with_decoders
    {color : Bool} {R S top : bSet 𝔹} {Γ : 𝔹}
    (Htop : Γ ≤ top ∈ᴮ omegaTwo)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J)) :
    ∃ P : bSet 𝔹, Γ ≤ is_function omegaOne entrySpace P ⊓
      (runLaw color R S top P ⊓
        (is_function omegaOne omegaTwo (vertexHistory P) ⊓
          is_function (prod omegaOne omegaOne) omegaOne (coordinateHistory P))) := by
  obtain ⟨P, HP⟩ := exists_simultaneous_run (color := color) (R := R) Htop HS Hrows
  have Hfunction := HP.trans inf_le_left
  have Hlaw := HP.trans inf_le_right
  exact ⟨P, le_inf Hfunction (le_inf Hlaw
    (le_inf (vertexHistory_is_function_of_run Hfunction)
      (coordinateHistory_is_function_of_run Hfunction Hlaw)))⟩

end bSet.ErdosSimultaneousRun
