/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartitionSemantics

@[expose] public section

/-!
# Noncollapse of the internal ordered blocks

An increasing relation on an ordinal domain cannot identify two different
domain elements. Separated guarded ranges cannot overlap. Restricting a
total functional relation to its domain/codomain product consequently gives
a genuine injective internal function. All statements concern arbitrary
Boolean-valued names under the stated Boolean condition.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPartition

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem increasingOn_apply {A f i j x y : bSet 𝔹} {Γ : 𝔹}
    (Hinc : Γ ≤ increasingOn A f)
    (Hi : Γ ≤ i ∈ᴮ A) (Hj : Γ ≤ j ∈ᴮ A) (Hij : Γ ≤ i ∈ᴮ j)
    (Hix : Γ ≤ pair i x ∈ᴮ f) (Hjy : Γ ≤ pair j y ∈ᴮ f) :
    Γ ≤ x ∈ᴮ y := by
  have Hspec := Hinc.trans ((iInf_le _ i).trans
    ((iInf_le _ j).trans ((iInf_le _ x).trans (iInf_le _ y))))
  exact (le_inf Hspec (le_inf (le_inf (le_inf Hi Hj) Hij) (le_inf Hix Hjy))).trans
    bv_imp_elim

/-- Increasingness on an ordinal domain reflects equality of graph values.
No totality or single-valuedness assumption is needed for this implication. -/
theorem increasingOn_injective_on {A f i j x y : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ Ord A) (Hinc : Γ ≤ increasingOn A f)
    (Hi : Γ ≤ i ∈ᴮ A) (Hj : Γ ≤ j ∈ᴮ A)
    (Hix : Γ ≤ pair i x ∈ᴮ f) (Hjy : Γ ≤ pair j y ∈ᴮ f)
    (Hxy : Γ ≤ x =ᴮ y) : Γ ≤ i =ᴮ j := by
  apply Ord.eq_of_not_mem (Ord_of_mem_Ord Hi HA) (Ord_of_mem_Ord Hj HA)
  · rw [← imp_bot, ← deduction]
    have Hmem : Γ ⊓ i ∈ᴮ j ≤ x ∈ᴮ y :=
      increasingOn_apply (inf_le_left.trans Hinc)
        (inf_le_left.trans Hi) (inf_le_left.trans Hj) inf_le_right
        (inf_le_left.trans Hix) (inf_le_left.trans Hjy)
    exact bot_of_mem_self' (mem_congr (inf_le_left.trans Hxy) bv_refl Hmem)
  · rw [← imp_bot, ← deduction]
    have Hmem : Γ ⊓ j ∈ᴮ i ≤ y ∈ᴮ x :=
      increasingOn_apply (inf_le_left.trans Hinc)
        (inf_le_left.trans Hj) (inf_le_left.trans Hi) inf_le_right
        (inf_le_left.trans Hjy) (inf_le_left.trans Hix)
    exact bot_of_mem_self' (mem_congr (inf_le_left.trans (bv_symm Hxy)) bv_refl Hmem)

/-- The standard product restriction turns a total functional relation into
an exact internal function graph, without changing its used domain. -/
theorem function_of_func'_is_function {A κ f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' A κ f) :
    Γ ≤ is_function A κ (function_of_func' Hf) := by
  refine le_inf (le_inf ?_ ?_) ?_
  · exact is_func_subset_of_is_func (Hf.trans inf_le_left)
      (function_of_func'_subset (H_is_func' := Hf))
  · apply le_iInf
    intro i
    rw [← deduction]
    have Htotal : Γ ⊓ i ∈ᴮ A ≤ ⨆ x, x ∈ᴮ κ ⊓ pair i x ∈ᴮ f :=
      (le_inf (inf_le_left.trans ((Hf.trans inf_le_right).trans (iInf_le _ i)))
        inf_le_right).trans bv_imp_elim
    obtain ⟨x, Hx⟩ := exists_convert Htotal
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    apply le_iSup_of_le x
    refine le_inf (Hx.trans inf_le_left) ?_
    change Γ ⊓ i ∈ᴮ A ≤ pair i x ∈ᴮ (f ∩ᴮ prod A κ)
    exact mem_binary_inter_iff.mpr
      ⟨Hx.trans inf_le_right, mem_prod_iff.mpr ⟨inf_le_right, Hx.trans inf_le_left⟩⟩
  · exact binary_inter_subset_right

end bSet.ErdosPartition
