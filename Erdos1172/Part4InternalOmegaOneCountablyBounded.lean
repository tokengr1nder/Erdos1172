/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountableFamilyUnion
public import Erdos1172.Part4InternalCountableSuccessor
public import Erdos1172.Part4InternalOmegaOneIdealBounded

@[expose] public section

/-!
# Ideal-free countable boundedness of the internal omega-one

The actual union of an internally countable family of countable ordinals
is countable. Its set successor is still a countable ordinal, hence belongs
to the Hartogs ordinal of omega and bounds the original family. The proof
covers empty families and arbitrary Boolean-mixed names at the original
condition; it does not require CH or an ideal.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOmegaOneCountablyBounded

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosInitialSegments ErdosCountableFamilyUnion

/-- Every internally countable ordinal belongs to the actual omega-one. -/
theorem countable_ordinal_mem_omegaOne {a : bSet 𝔹} {Γ : 𝔹}
    (Hord : Γ ≤ Ord a) (Hcount : Γ ≤ injects_into a bSet.omega) :
    Γ ≤ a ∈ᴮ omegaOne :=
  (ErdosHartogs.mem_hartogs_iff (κ := bSet.omega) one_injects_omega Hord).mpr
    (injection_into_of_injects_into Hcount)

/-- Members of a subset of omega-one form an actual countable-valued family. -/
theorem union_countable_of_subset {A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ omegaOne) (Hcount : Γ ≤ injects_into A bSet.omega) :
    Γ ≤ injects_into (bv_union A) bSet.omega := by
  apply union_countable Hcount
  apply le_iInf
  intro a
  rw [← deduction]
  exact omegaOne_member_injects (mem_of_mem_subset (inf_le_left.trans HA) inf_le_right)

theorem union_Ord_of_subset {A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ omegaOne) : Γ ≤ Ord (bv_union A) := by
  apply union_Ord_of_ordinal_subsets omegaOne_Ord
  apply le_iInf
  intro a
  rw [← deduction]
  have Ha : Γ ⊓ a ∈ᴮ A ≤ a ∈ᴮ omegaOne := mem_of_mem_subset (inf_le_left.trans HA) inf_le_right
  exact le_inf (Ord_of_mem_Ord Ha omegaOne_Ord) (subset_of_mem_Ord Ha omegaOne_Ord)

/-- Taking a successor gives a strict bound, even if the family has a maximum
or is empty. No internally supplied upper bound is assumed. -/
theorem succ_union_mem_omegaOne {A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ omegaOne) (Hcount : Γ ≤ injects_into A bSet.omega) :
    Γ ≤ succ (bv_union A) ∈ᴮ omegaOne :=
  countable_ordinal_mem_omegaOne (Ord_succ (union_Ord_of_subset HA))
    (ErdosCountableSuccessor.succ_countable (union_countable_of_subset HA Hcount))

theorem subset_succ_union {A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ omegaOne) : Γ ≤ A ⊆ᴮ succ (bv_union A) := by
  rw [subset_unfold']
  apply le_iInf
  intro a
  rw [← deduction]
  have Ha : Γ ⊓ a ∈ᴮ A ≤ a ∈ᴮ omegaOne := mem_of_mem_subset (inf_le_left.trans HA) inf_le_right
  have Hsub : Γ ⊓ a ∈ᴮ A ≤ a ⊆ᴮ bv_union A :=
    (le_inf (le_top.trans ((bv_union_spec'' A).trans (iInf_le _ a)))
      (show Γ ⊓ a ∈ᴮ A ≤ a ∈ᴮ A from inf_le_right)).trans bv_imp_elim
  have Hcases := (Ord.le_iff_lt_or_eq (Ord_of_mem_Ord Ha omegaOne_Ord)
    (inf_le_left.trans (union_Ord_of_subset HA))).mp Hsub
  change Γ ⊓ a ∈ᴮ A ≤ a ∈ᴮ bSet.insert1 (bv_union A) (bv_union A)
  have Hinsert : a ∈ᴮ bSet.insert1 (bv_union A) (bv_union A) =
      (a =ᴮ bv_union A) ⊔ a ∈ᴮ bv_union A := mem_insert1
  exact (Hcases.trans_eq (sup_comm _ _)).trans_eq Hinsert.symm

/-- An actual bound exists at the same Boolean condition. -/
theorem exists_bound_of_countable {A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ omegaOne) (Hcount : Γ ≤ injects_into A bSet.omega) :
    ∃ b : bSet 𝔹, Γ ≤ b ∈ᴮ omegaOne ⊓ A ⊆ᴮ b :=
  ⟨succ (bv_union A), le_inf (succ_union_mem_omegaOne HA Hcount) (subset_succ_union HA)⟩

end bSet.ErdosOmegaOneCountablyBounded
