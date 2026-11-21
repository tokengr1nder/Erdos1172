/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockPoolUpdate
public import Erdos1172.Part4InternalPoolAggregation
public import Erdos1172.Part4InternalBoundedImageRecursionTotal

@[expose] public section

/-!
# The actual transfinite recursion for the fixed selector's pool update

Every prior-state set is aggregated using fixed coordinate projections.
The concrete bounded, congruent update then yields an actual run on the
entire omega-one domain. No pre-existing chain or stagewise success is
assumed. Cardinal invariants and final selector closure are separate.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockPoolRecursion

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosPoolAggregation ErdosBlockPoolUpdate
open ErdosBoundedImageRecursion

def stateSpace (color : Bool) (R : bSet 𝔹) : bSet 𝔹 :=
  poolSpace (blockObjects color R) omegaTwo

def priorObjects (color : Bool) (R T : bSet 𝔹) : bSet 𝔹 :=
  aggregateLeft (blockObjects color R) omegaTwo T

def priorPoints (color : Bool) (R T : bSet 𝔹) : bSet 𝔹 :=
  aggregateRight (blockObjects color R) omegaTwo T

def poolUpdate (color : Bool) (R F T : bSet 𝔹) : bSet 𝔹 :=
  pair (nextObjects color R (priorObjects color R T) (priorPoints color R T) F)
    (nextPoints (priorObjects color R T) (priorPoints color R T) F)

theorem poolUpdate_congr (color : Bool) (R F : bSet 𝔹) : B_congr (poolUpdate color R F) := by
  intro T U Γ H
  exact pair_congr
    (nextObjects_congr (aggregateLeft_congr _ _ H) (aggregateRight_congr _ _ H))
    (nextPoints_congr (aggregateLeft_congr _ _ H) (aggregateRight_congr _ _ H))

/-- Global support holds even for malformed or large past inputs. -/
theorem poolUpdate_mem_stateSpace {color : Bool} {R F T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ poolUpdate color R F T ∈ᴮ stateSpace color R :=
  mem_poolSpace_iff.mpr ⟨nextObjects_subset aggregateLeft_subset, nextPoints_subset⟩

theorem exists_pool_recursion (color : Bool) (R F : bSet 𝔹) {Γ : 𝔹} :
    ∃ Run : bSet 𝔹, Γ ≤ is_function omegaOne (stateSpace color R) Run ⊓
      imageRecLaw (stateSpace color R) (fun _ T => poolUpdate color R F T) Run := by
  apply exists_bounded_image_recursion omegaOne_Ord
  · intro T i j Δ H
    exact bv_refl
  · intro i
    exact poolUpdate_congr color R F
  · apply le_iInf
    intro i
    apply le_iInf
    intro T
    rw [← deduction]
    exact poolUpdate_mem_stateSpace

theorem pool_recursion_entry {color : Bool} {R F Run i B P : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ imageRecLaw (stateSpace color R) (fun _ T => poolUpdate color R F T) Run)
    (Hpair : Γ ≤ pair i (pair B P) ∈ᴮ Run) :
    Γ ≤ B =ᴮ nextObjects color R
        (priorObjects color R (image i (stateSpace color R) Run))
        (priorPoints color R (image i (stateSpace color R) Run)) F ⊓
      P =ᴮ nextPoints (priorObjects color R (image i (stateSpace color R) Run))
        (priorPoints color R (image i (stateSpace color R) Run)) F := by
  have H := imageRecLaw_apply Hlaw Hpair
  exact le_inf (eq_of_eq_pair_left' H) (eq_of_eq_pair_right' H)

end bSet.ErdosBlockPoolRecursion
