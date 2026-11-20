/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartialInjection

@[expose] public section

/-!
# Ordinal-domain functions as initial-segment partial graphs

An actual injective internal function on an ordinal domain below the bound
is a partial graph of the required kind. Its domain computed from the graph
is exactly the given domain. All sets and graphs are arbitrary names.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPartialInjection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem prod_domain_mono {A κ S : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ κ) : Γ ≤ prod A S ⊆ᴮ prod κ S := by
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction]
  obtain ⟨x, Hx, y, Hy, Hz⟩ := mem_prod_iff₂.mp
    (show Γ ⊓ (z ∈ᴮ prod A S) ≤ z ∈ᴮ prod A S from inf_le_right)
  exact mem_prod_iff₂.mpr
    ⟨x, mem_of_mem_subset (inf_le_left.trans HA) Hx, y, Hy, Hz⟩

theorem prefixClosed_of_ordinal_function {A S f : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ Ord A) (Hf : Γ ≤ is_function A S f) :
    Γ ≤ prefixClosed S f := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro z
  rw [← deduction]
  let Δ := Γ ⊓ ((pair x y ∈ᴮ f) ⊓ z ∈ᴮ x)
  have Hfunction : Δ ≤ is_function A S f := inf_le_left.trans Hf
  have Hx : Δ ≤ x ∈ᴮ A :=
    mem_domain_of_is_function (inf_le_right.trans inf_le_left) Hfunction
  have Hz : Δ ≤ z ∈ᴮ A :=
    mem_of_mem_Ord (inf_le_right.trans inf_le_right) Hx (inf_le_left.trans HA)
  exact (le_inf ((is_total_of_is_function Hfunction).trans (iInf_le _ z)) Hz).trans
    bv_imp_elim

theorem partialGraph_of_ordinal_function {A κ S f : bSet 𝔹} {Γ : 𝔹}
    (HAOrd : Γ ≤ Ord A) (HAsub : Γ ≤ A ⊆ᴮ κ)
    (Hinj : Γ ≤ is_injective_function A S f) :
    Γ ≤ partialGraph κ S f := by
  have Hf : Γ ≤ is_function A S f := Hinj.trans inf_le_left
  exact le_inf
    (subset_trans' (subset_prod_of_is_function Hf) (prod_domain_mono HAsub))
    (le_inf (Hf.trans (inf_le_left.trans inf_le_left))
      (le_inf (Hinj.trans inf_le_right) (prefixClosed_of_ordinal_function HAOrd Hf)))

/-- Computing a supported total function's graph domain recovers exactly
its original domain; no ordinal hypothesis is needed for this equality. -/
theorem graphDomain_eq_of_function {A κ S f : bSet 𝔹} {Γ : 𝔹}
    (HAsub : Γ ≤ A ⊆ᴮ κ) (Hf : Γ ≤ is_function A S f) :
    Γ ≤ graphDomain κ S f =ᴮ A := by
  apply subset_ext
  · rw [subset_unfold']
    apply le_iInf
    intro x
    rw [← deduction]
    have Hmem : Γ ⊓ (x ∈ᴮ graphDomain κ S f) ≤
        (x ∈ᴮ κ) ⊓ ⨆ y, (y ∈ᴮ S) ⊓ pair x y ∈ᴮ f := by
      rw [← mem_graphDomain]
      exact inf_le_right
    obtain ⟨y, Hy⟩ := exists_convert (Hmem.trans inf_le_right)
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    exact mem_domain_of_is_function (Hy.trans inf_le_right) (inf_le_left.trans Hf)
  · rw [subset_unfold']
    apply le_iInf
    intro x
    rw [← deduction, mem_graphDomain]
    refine le_inf (mem_of_mem_subset (inf_le_left.trans HAsub) inf_le_right) ?_
    exact (le_inf
      (inf_le_left.trans ((is_total_of_is_function Hf).trans (iInf_le _ x)))
      inf_le_right).trans bv_imp_elim

end bSet.ErdosPartialInjection
