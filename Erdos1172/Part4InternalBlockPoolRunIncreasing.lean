/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBlockPoolRecursion
public import Erdos1172.Part4InternalCountableChainCapture
public import Erdos1172.Part4InternalIncreasingComposition

@[expose] public section

/-!
# Increasing coordinate families of the actual pool recursion

Each earlier state belongs to the actual strict-prefix image. Its two
components lie in the corresponding aggregates, and the concrete update
retains both aggregates. Thus the actual pool run is increasing without
any cardinal, success, or selector-law premise.

The coordinate families are actual compositions of that same run with
the fixed projections. Their membership witnesses recover the original
paired state, and both satisfy the increasing-family law used by countable
chain capture. No independently selected coordinate history is introduced.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBlockPoolRunIncreasing

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosPoolAggregation ErdosBlockPoolUpdate
open ErdosBlockPoolRecursion ErdosBoundedImageRecursion ErdosCountableChainCapture
open ErdosIncreasingComposition

theorem pool_recursion_increasing
    {color : Bool} {R F Run j i B P C Q : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hlaw : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run)
    (Hji : Γ ≤ j ∈ᴮ i)
    (Hj : Γ ≤ pair j (pair B P) ∈ᴮ Run)
    (Hi : Γ ≤ pair i (pair C Q) ∈ᴮ Run) :
    Γ ≤ B ⊆ᴮ C ⊓ P ⊆ᴮ Q := by
  have Hpast : Γ ≤ pair B P ∈ᴮ image i (stateSpace color R) Run :=
    mem_image Hj Hji (mem_codomain_of_is_function Hj HF)
  have HB : Γ ≤ B ⊆ᴮ priorObjects color R (image i (stateSpace color R) Run) :=
    left_subset_aggregate image_subset Hpast
  have HP : Γ ≤ P ⊆ᴮ priorPoints color R (image i (stateSpace color R) Run) :=
    right_subset_aggregate image_subset Hpast
  have Hentry := pool_recursion_entry Hlaw Hi
  have HBnext : Γ ≤ B ⊆ᴮ nextObjects color R
      (priorObjects color R (image i (stateSpace color R) Run))
      (priorPoints color R (image i (stateSpace color R) Run)) F :=
    subset_trans' HB oldObjects_subset_nextObjects
  have HPnext : Γ ≤ P ⊆ᴮ nextPoints
      (priorObjects color R (image i (stateSpace color R) Run))
      (priorPoints color R (image i (stateSpace color R) Run)) F :=
    subset_trans' HP (oldPoints_subset_nextPoints aggregateLeft_subset aggregateRight_subset)
  exact le_inf
    (bv_rw' (ϕ := fun X => B ⊆ᴮ X) (Hentry.trans inf_le_left)
      (h_congr := B_ext_subset_right) (H_new := HBnext))
    (bv_rw' (ϕ := fun X => P ⊆ᴮ X) (Hentry.trans inf_le_right)
      (h_congr := B_ext_subset_right) (H_new := HPnext))

def objectFamily {color : Bool} {R Run : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run) : bSet 𝔹 :=
  function_comp HF (leftProjection_is_function (K := blockObjects color R) (L := omegaTwo))

def pointFamily {color : Bool} {R Run : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run) : bSet 𝔹 :=
  function_comp HF (rightProjection_is_function (K := blockObjects color R) (L := omegaTwo))

theorem objectFamily_is_function {color : Bool} {R Run : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run) :
    Γ ≤ is_function omegaOne (bv_powerset (blockObjects color R)) (objectFamily HF) :=
  function_comp_is_function

theorem pointFamily_is_function {color : Bool} {R Run : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run) :
    Γ ≤ is_function omegaOne (bv_powerset omegaTwo) (pointFamily HF) :=
  function_comp_is_function

/-- Membership in the actual coordinate composition recovers an actual
paired entry of the original run, even under a different local condition. -/
theorem objectFamily_witness {color : Bool} {R Run i B : bSet 𝔹} {Γ Δ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hpair : Δ ≤ pair i B ∈ᴮ objectFamily HF) :
    ∃ P : bSet 𝔹, Δ ≤ pair i (pair B P) ∈ᴮ Run := by
  obtain ⟨s, Hs⟩ := comp_pair_witness (is_func'_of_is_function HF)
    (is_func'_of_is_function (leftProjection_is_function
      (K := blockObjects color R) (L := omegaTwo))) Hpair
  obtain ⟨P, Heq, _, _⟩ := leftProjection_witness
    (Hs.trans (inf_le_right.trans inf_le_right))
  exact ⟨P, mem_congr (pair_congr bv_refl Heq) bv_refl
    (Hs.trans (inf_le_right.trans inf_le_left))⟩

theorem pointFamily_witness {color : Bool} {R Run i P : bSet 𝔹} {Γ Δ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hpair : Δ ≤ pair i P ∈ᴮ pointFamily HF) :
    ∃ B : bSet 𝔹, Δ ≤ pair i (pair B P) ∈ᴮ Run := by
  obtain ⟨s, Hs⟩ := comp_pair_witness (is_func'_of_is_function HF)
    (is_func'_of_is_function (rightProjection_is_function
      (K := blockObjects color R) (L := omegaTwo))) Hpair
  obtain ⟨B, Heq, _, _⟩ := rightProjection_witness
    (Hs.trans (inf_le_right.trans inf_le_right))
  exact ⟨B, mem_congr (pair_congr bv_refl Heq) bv_refl
    (Hs.trans (inf_le_right.trans inf_le_left))⟩

theorem objectFamily_pair {color : Bool} {R Run i B P : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hpair : Γ ≤ pair i (pair B P) ∈ᴮ Run) : Γ ≤ pair i B ∈ᴮ objectFamily HF := by
  have Hvalue := mem_codomain_of_is_function Hpair HF
  have Hbounds := mem_poolSpace_iff.mp Hvalue
  exact (mem_is_func'_comp_iff (is_func'_of_is_function HF)
    (is_func'_of_is_function (leftProjection_is_function
      (K := blockObjects color R) (L := omegaTwo)))).mpr
    ⟨mem_domain_of_is_function Hpair HF, mem_powerset_iff.mpr Hbounds.1,
      le_iSup_of_le (pair B P) (le_inf Hvalue
        (le_inf Hpair (leftProjection_pair Hbounds.1 Hbounds.2)))⟩

theorem pointFamily_pair {color : Bool} {R Run i B P : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hpair : Γ ≤ pair i (pair B P) ∈ᴮ Run) : Γ ≤ pair i P ∈ᴮ pointFamily HF := by
  have Hvalue := mem_codomain_of_is_function Hpair HF
  have Hbounds := mem_poolSpace_iff.mp Hvalue
  exact (mem_is_func'_comp_iff (is_func'_of_is_function HF)
    (is_func'_of_is_function (rightProjection_is_function
      (K := blockObjects color R) (L := omegaTwo)))).mpr
    ⟨mem_domain_of_is_function Hpair HF, mem_powerset_iff.mpr Hbounds.2,
      le_iSup_of_le (pair B P) (le_inf Hvalue
        (le_inf Hpair (rightProjection_pair Hbounds.1 Hbounds.2)))⟩

theorem objectFamily_increasing {color : Bool} {R F Run : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hlaw : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ increasingFamily (objectFamily HF) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro A
  apply le_iInf
  intro B
  rw [← deduction]
  let Δ := Γ ⊓ ((i ∈ᴮ omegaOne ⊓ j ∈ᴮ omegaOne) ⊓
    (i ∈ᴮ j ⊓ (pair i A ∈ᴮ objectFamily HF ⊓ pair j B ∈ᴮ objectFamily HF)))
  have Hi : Δ ≤ pair i A ∈ᴮ objectFamily HF :=
    inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have Hj : Δ ≤ pair j B ∈ᴮ objectFamily HF :=
    inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  obtain ⟨P, HP⟩ := objectFamily_witness HF Hi
  obtain ⟨Q, HQ⟩ := objectFamily_witness HF Hj
  exact (pool_recursion_increasing (inf_le_left.trans HF) (inf_le_left.trans Hlaw)
    (show Δ ≤ i ∈ᴮ j from inf_le_right.trans (inf_le_right.trans inf_le_left))
    HP HQ).trans inf_le_left

theorem pointFamily_increasing {color : Bool} {R F Run : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function omegaOne (stateSpace color R) Run)
    (Hlaw : Γ ≤ imageRecLaw (stateSpace color R)
      (fun _ T => poolUpdate color R F T) Run) :
    Γ ≤ increasingFamily (pointFamily HF) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro P
  apply le_iInf
  intro Q
  rw [← deduction]
  let Δ := Γ ⊓ ((i ∈ᴮ omegaOne ⊓ j ∈ᴮ omegaOne) ⊓
    (i ∈ᴮ j ⊓ (pair i P ∈ᴮ pointFamily HF ⊓ pair j Q ∈ᴮ pointFamily HF)))
  have Hi : Δ ≤ pair i P ∈ᴮ pointFamily HF :=
    inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have Hj : Δ ≤ pair j Q ∈ᴮ pointFamily HF :=
    inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  obtain ⟨A, HA⟩ := pointFamily_witness HF Hi
  obtain ⟨B, HB⟩ := pointFamily_witness HF Hj
  exact (pool_recursion_increasing (inf_le_left.trans HF) (inf_le_left.trans Hlaw)
    (show Δ ≤ i ∈ᴮ j from inf_le_right.trans (inf_le_right.trans inf_le_left))
    HA HB).trans inf_le_right

end bSet.ErdosBlockPoolRunIncreasing
