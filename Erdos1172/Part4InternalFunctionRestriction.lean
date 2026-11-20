/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartitionOrder

@[expose] public section

/-!
Domain restriction of arbitrary internal function graphs. Restricting the
total-functional relation and then intersecting with the supported product
produces an actual function graph. Injectivity, increasingness, and used
range inclusion are preserved at the same Boolean condition.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFunctionRestriction

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPartition

theorem is_func'_restrict_domain {U K S f : bSet 𝔹} {Γ : 𝔹}
    (HU : Γ ≤ U ⊆ᴮ K) (Hf : Γ ≤ is_function K S f) :
    Γ ≤ is_func' U S f :=
  is_func'_subset_of_is_func' (is_func'_of_is_function Hf) HU

/-- Injectivity is hereditary under graph inclusion, without assumptions
about the domain or codomain of the smaller relation. -/
theorem is_inj_of_subset {f g : bSet 𝔹} {Γ : 𝔹}
    (Hgf : Γ ≤ g ⊆ᴮ f) (Hinj : Γ ≤ is_inj f) : Γ ≤ is_inj g := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  exact eq_of_is_inj_of_eq (inf_le_left.trans Hinj)
    (inf_le_right.trans inf_le_right)
    (mem_of_mem_subset (inf_le_left.trans Hgf)
      (inf_le_right.trans (inf_le_left.trans inf_le_left)))
    (mem_of_mem_subset (inf_le_left.trans Hgf)
      (inf_le_right.trans (inf_le_left.trans inf_le_right)))

/-- Restricting both the guarded domain and the graph preserves strict
increasingness. No ordinal assumption is needed for this inheritance. -/
theorem increasingOn_of_subsets {U K f g : bSet 𝔹} {Γ : 𝔹}
    (HU : Γ ≤ U ⊆ᴮ K) (Hgf : Γ ≤ g ⊆ᴮ f)
    (Hinc : Γ ≤ increasingOn K f) : Γ ≤ increasingOn U g := by
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (((i ∈ᴮ U ⊓ j ∈ᴮ U) ⊓ i ∈ᴮ j) ⊓
    (pair i x ∈ᴮ g ⊓ pair j y ∈ᴮ g))
  have Hi : Δ ≤ i ∈ᴮ K :=
    mem_of_mem_subset (inf_le_left.trans HU)
      (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
  have Hj : Δ ≤ j ∈ᴮ K :=
    mem_of_mem_subset (inf_le_left.trans HU)
      (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  exact increasingOn_apply (inf_le_left.trans Hinc) Hi Hj
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (mem_of_mem_subset (inf_le_left.trans Hgf)
      (inf_le_right.trans (inf_le_right.trans inf_le_left)))
    (mem_of_mem_subset (inf_le_left.trans Hgf)
      (inf_le_right.trans (inf_le_right.trans inf_le_right)))

/-- Every value used by a restricted graph is used by the original graph.
This is an internal guarded-range statement, not an external range claim. -/
theorem rangeMem_of_subsets {U K f g x : bSet 𝔹} {Γ : 𝔹}
    (HU : Γ ≤ U ⊆ᴮ K) (Hgf : Γ ≤ g ⊆ᴮ f)
    (Hx : Γ ≤ rangeMem U g x) : Γ ≤ rangeMem K f x := by
  obtain ⟨i, Hi⟩ := exists_convert Hx
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact le_iSup_of_le i (le_inf
    (mem_of_mem_subset HU (Hi.trans inf_le_left))
    (mem_of_mem_subset Hgf (Hi.trans inf_le_right)))

theorem exists_restricted_function {U K S f : bSet 𝔹} {Γ : 𝔹}
    (HU : Γ ≤ U ⊆ᴮ K) (Hf : Γ ≤ is_function K S f) :
    ∃ g : bSet 𝔹, Γ ≤ is_function U S g ⊓ g ⊆ᴮ f := by
  have Hweak : Γ ≤ is_func' U S f := is_func'_restrict_domain HU Hf
  exact ⟨function_of_func' Hweak,
    le_inf (ErdosPartition.function_of_func'_is_function Hweak)
      (function_of_func'_subset (H_is_func' := Hweak))⟩

/-- The restricted graph is an actual increasing injection on the entire
new internal domain. Empty domains require no special assumption. -/
theorem exists_restricted_increasing_injection {U K S f : bSet 𝔹} {Γ : 𝔹}
    (HU : Γ ≤ U ⊆ᴮ K) (Hinj : Γ ≤ is_injective_function K S f)
    (Hinc : Γ ≤ increasingOn K f) :
    ∃ g : bSet 𝔹, Γ ≤ is_injective_function U S g ⊓
      (increasingOn U g ⊓ g ⊆ᴮ f) := by
  have Hweak : Γ ≤ is_func' U S f :=
    is_func'_restrict_domain HU (Hinj.trans inf_le_left)
  let g := function_of_func' Hweak
  have Hgf : Γ ≤ g ⊆ᴮ f := function_of_func'_subset (H_is_func' := Hweak)
  have Hfunction : Γ ≤ is_function U S g :=
    ErdosPartition.function_of_func'_is_function Hweak
  exact ⟨g, le_inf
    (le_inf Hfunction (is_inj_of_subset Hgf (Hinj.trans inf_le_right)))
    (le_inf (increasingOn_of_subsets HU Hgf Hinc) Hgf)⟩

end bSet.ErdosFunctionRestriction
