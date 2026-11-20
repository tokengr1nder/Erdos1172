/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The subset representation proof is extracted from the proof of
`bSet.bv_powerset_spec` in Flypitch4/Bvm.lean.
-/
module

public import Flypitch4.BvmExtras

@[expose] public section

/-!
# Representation of arbitrary internal subsets and relations

Every Boolean-valued subset name is equal, under the same Boolean condition,
to the name whose coefficients are its membership values on the ambient
name's members. The relation specialization applies to arbitrary internal
relation names. It does not turn Boolean-valued adjacency into a ground-model
graph and does not assert a partition or forcing theorem.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Canonical membership-indicator representation of an arbitrary internal
subset, valid under the Boolean condition witnessing the subset relation. -/
lemma eq_membership_indicator_of_subset {x v : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ x ⊆ᴮ v) :
    Γ ≤ x =ᴮ set_of_indicator (u := v) (fun i => v.func i ∈ᴮ x) := by
  apply mem_ext
  · apply le_iInf
    intro z
    rw [← deduction]
    rw [mem_unfold (v := set_of_indicator (u := v) (fun i => v.func i ∈ᴮ x))]
    have hmem_v : Γ ⊓ z ∈ᴮ x ≤ z ∈ᴮ v := by
      have hspec : Γ ≤ z ∈ᴮ x ⟹ z ∈ᴮ v :=
        le_trans H (by rw [subset_unfold']; exact iInf_le _ z)
      exact le_trans (le_inf (le_trans inf_le_left hspec) inf_le_right) bv_imp_elim
    calc
      Γ ⊓ z ∈ᴮ x ≤ (Γ ⊓ z ∈ᴮ x) ⊓ (z ∈ᴮ v) := le_inf le_rfl hmem_v
      _ = (Γ ⊓ z ∈ᴮ x) ⊓ ⨆ i, v.bval i ⊓ z =ᴮ v.func i := by
        rw [← mem_unfold]
      _ = ⨆ i, (Γ ⊓ z ∈ᴮ x) ⊓ (v.bval i ⊓ z =ᴮ v.func i) := by
        rw [inf_iSup_eq]
      _ ≤ ⨆ i, (v.func i ∈ᴮ x) ⊓ z =ᴮ v.func i := by
        apply iSup_le
        intro i
        apply le_iSup_of_le i
        apply le_inf
        · have h : (Γ ⊓ z ∈ᴮ x) ⊓ (v.bval i ⊓ z =ᴮ v.func i) ≤
              z ∈ᴮ x ⊓ z =ᴮ v.func i :=
            le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
          exact le_trans h (by rw [inf_comm]; exact subst_congr_mem_left)
        · exact inf_le_right.trans inf_le_right
  · apply le_iInf
    intro z
    rw [← deduction]
    rw [mem_unfold (v := set_of_indicator (u := v) (fun i => v.func i ∈ᴮ x))]
    rw [inf_iSup_eq]
    apply iSup_le
    intro i
    calc
      Γ ⊓ (v.func i ∈ᴮ x ⊓ z =ᴮ v.func i) ≤
          v.func i ∈ᴮ x ⊓ z =ᴮ v.func i := inf_le_right
      _ ≤ v.func i =ᴮ z ⊓ v.func i ∈ᴮ x :=
        le_inf (inf_le_right.trans (le_of_eq bv_eq_symm)) inf_le_left
      _ ≤ z ∈ᴮ x := subst_congr_mem_left

end bSet
