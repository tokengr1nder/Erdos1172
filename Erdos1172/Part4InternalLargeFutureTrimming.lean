/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaTwoBounded

@[expose] public section

/-!
An actual large future simultaneously lies strictly beyond every member
of a small row-value set and avoids an independently small exception set.
The bound and the retained set are constructed, including for empty rows.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosLargeFutureTrimming

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal

theorem exists_large_future_avoiding_small_sets
    {A E S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HA : Γ ≤ A ⊆ᴮ omegaTwo)
    (HAsmall : Γ ≤ injects_into A omegaOne)
    (HEsmall : Γ ≤ injects_into E omegaOne)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HSlarge : Γ ≤ injects_into omegaTwo S) :
    ∃ a L : bSet 𝔹, Γ ≤ a ∈ᴮ omegaTwo ⊓ (A ⊆ᴮ a ⊓
      (L ⊆ᴮ S ⊓ (injects_into omegaTwo L ⊓
        (⨅ y, _root_.imp (y ∈ᴮ L) (a ∈ᴮ y ⊓ (y ∈ᴮ E)ᶜ))))) := by
  obtain ⟨a, Ha⟩ := ErdosOmegaTwoBounded.exists_strict_upper_bound HCH HA HAsmall
  let L := difference (difference S E) (succ a)
  have HLS : Γ ≤ L ⊆ᴮ S := subset_trans' difference_subset difference_subset
  have HLlarge : Γ ≤ injects_into omegaTwo L :=
    ErdosLargeDifference.omegaTwo_injects_difference_succ HCH
      (ErdosLargeDifference.omegaTwo_injects_difference HCH HSlarge HEsmall)
      (Ha.trans inf_le_left)
  refine ⟨a, L, le_inf (Ha.trans inf_le_left)
    (le_inf (Ha.trans inf_le_right) (le_inf HLS (le_inf HLlarge ?_)))⟩
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ y ∈ᴮ L
  have Hy : Δ ≤ y ∈ᴮ L := inf_le_right
  have Hdata : Δ ≤ (y ∈ᴮ S ⊓ (y ∈ᴮ E)ᶜ) ⊓ (y ∈ᴮ succ a)ᶜ := by
    simpa only [L, mem_difference] using Hy
  have Hytwo : Δ ≤ y ∈ᴮ omegaTwo :=
    mem_of_mem_subset (inf_le_left.trans HS) (Hdata.trans (inf_le_left.trans inf_le_left))
  exact le_inf
    (ErdosOmegaReservoir.above_of_not_mem_succ
      (inf_le_left.trans (Ha.trans inf_le_left)) Hytwo (Hdata.trans inf_le_right))
    (Hdata.trans (inf_le_left.trans inf_le_right))

end bSet.ErdosLargeFutureTrimming
