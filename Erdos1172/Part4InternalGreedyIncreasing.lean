/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalGreedyTotal
public import Erdos1172.Part4InternalPartitionOrder

@[expose] public section

/-!
Order and constraint consequences of the constructed greedy law. A weak
total-functional graph on omega-one suffices: restriction to each internal
prefix turns least-candidate membership into the exact admissibility law.
Increasingness, seed containment and all earlier section constraints are
derived, not supplied as additional properties of a successful run.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosGreedyPartial

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosRowCandidates ErdosOrdinalLeast

/-- At every arbitrary internal stage, the least-choice law implies the
full admissibility law using totality only on that stage's strict prefix. -/
theorem rowAdmissible_of_greedyLaw {seed F f i x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f) (Hlaw : Γ ≤ greedyLaw seed F f)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hpair : Γ ≤ pair i x ∈ᴮ f) :
    Γ ≤ rowAdmissible i seed F f x :=
  (mem_rowCandidates_iff
    (is_func'_subset_of_is_func' Hf (subset_of_mem_Ord Hi omegaOne_Ord))).mp
    (leastIn_mem (greedyLaw_apply Hlaw Hpair))

theorem value_mem_seed_of_greedyLaw {seed F f i x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f) (Hlaw : Γ ≤ greedyLaw seed F f)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hpair : Γ ≤ pair i x ∈ᴮ f) :
    Γ ≤ x ∈ᴮ seed :=
  (rowAdmissible_of_greedyLaw Hf Hlaw Hi Hpair).trans (inf_le_right.trans inf_le_left)

/-- Every value satisfies each earlier indexed section, with arbitrary
internal stage, index, section, and value names. -/
theorem value_mem_previous_section_of_greedyLaw
    {seed F f i x j A : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f) (Hlaw : Γ ≤ greedyLaw seed F f)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hpair : Γ ≤ pair i x ∈ᴮ f)
    (Hji : Γ ≤ j ∈ᴮ i) (Hsection : Γ ≤ pair j A ∈ᴮ F) :
    Γ ≤ x ∈ᴮ A := by
  have Hprevious : Γ ≤ ⨅ j, ⨅ A,
      _root_.imp (j ∈ᴮ i ⊓ pair j A ∈ᴮ F) (x ∈ᴮ A) :=
    (rowAdmissible_of_greedyLaw Hf Hlaw Hi Hpair).trans
      (inf_le_right.trans (inf_le_right.trans inf_le_left))
  exact (le_inf (Hprevious.trans ((iInf_le _ j).trans (iInf_le _ A)))
    (le_inf Hji Hsection)).trans bv_imp_elim

theorem value_above_previous_of_greedyLaw
    {seed F f i x j y : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f) (Hlaw : Γ ≤ greedyLaw seed F f)
    (Hi : Γ ≤ i ∈ᴮ omegaOne) (Hpair : Γ ≤ pair i x ∈ᴮ f)
    (Hji : Γ ≤ j ∈ᴮ i) (HpreviousPair : Γ ≤ pair j y ∈ᴮ f) :
    Γ ≤ y ∈ᴮ x := by
  have Hprevious : Γ ≤ ⨅ j, ⨅ y,
      _root_.imp (j ∈ᴮ i ⊓ pair j y ∈ᴮ f) (y ∈ᴮ x) :=
    (rowAdmissible_of_greedyLaw Hf Hlaw Hi Hpair).trans
      (inf_le_right.trans (inf_le_right.trans inf_le_right))
  exact (le_inf (Hprevious.trans ((iInf_le _ j).trans (iInf_le _ y)))
    (le_inf Hji HpreviousPair)).trans bv_imp_elim

/-- Strict increasingness of the full graph follows from the exact
least-candidate rule; no increasingness hypothesis is added. -/
theorem increasingOn_of_greedyLaw {seed F f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f) (Hlaw : Γ ≤ greedyLaw seed F f) :
    Γ ≤ increasingOn omegaOne f := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  exact value_above_previous_of_greedyLaw (inf_le_left.trans Hf) (inf_le_left.trans Hlaw)
    (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
    (inf_le_right.trans (inf_le_right.trans inf_le_right))
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans (inf_le_right.trans inf_le_left))

theorem rangeMem_mem_seed_of_greedyLaw {seed F f x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f) (Hlaw : Γ ≤ greedyLaw seed F f)
    (Hx : Γ ≤ rangeMem omegaOne f x) : Γ ≤ x ∈ᴮ seed := by
  obtain ⟨i, Hi⟩ := exists_convert Hx
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact value_mem_seed_of_greedyLaw Hf Hlaw (Hi.trans inf_le_left) (Hi.trans inf_le_right)

theorem image_subset_seed_of_greedyLaw {seed F f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f) (Hlaw : Γ ≤ greedyLaw seed F f) :
    Γ ≤ image omegaOne omegaOne f ⊆ᴮ seed := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  exact rangeMem_mem_seed_of_greedyLaw (inf_le_left.trans Hf) (inf_le_left.trans Hlaw)
    ((mem_image_iff.mp inf_le_right).2)

/-- If the graph is actually supported on the stated product, the derived
increasingness proves injectivity of that same graph, without restriction. -/
theorem is_injective_function_of_greedyLaw {seed F f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function omegaOne omegaOne f) (Hlaw : Γ ≤ greedyLaw seed F f) :
    Γ ≤ is_injective_function omegaOne omegaOne f := by
  have Hinc := increasingOn_of_greedyLaw (is_func'_of_is_function Hf) Hlaw
  refine le_inf Hf ?_
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (pair i x ∈ᴮ f ⊓ pair j y ∈ᴮ f ⊓ x =ᴮ y)
  have Hix : Δ ≤ pair i x ∈ᴮ f := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have Hjy : Δ ≤ pair j y ∈ᴮ f := inf_le_right.trans (inf_le_left.trans inf_le_right)
  exact increasingOn_injective_on omegaOne_Ord (inf_le_left.trans Hinc)
    (mem_domain_of_is_function Hix (inf_le_left.trans Hf))
    (mem_domain_of_is_function Hjy (inf_le_left.trans Hf)) Hix Hjy
    (inf_le_right.trans inf_le_right)

end bSet.ErdosGreedyPartial
