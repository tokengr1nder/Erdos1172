/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountablePast
public import Erdos1172.Part4InternalInitialSegments
public import Erdos1172.Part4InternalOmegaTwoBounded

@[expose] public section

/-!
# The actual ordinal closure of a small point pool

The existing set `past T = T ∪ ⋃T` is transitive whenever T consists of
ordinals. It contains T and stays below every ordinal bound of T. Under
internal CH a supplied omega-one-small subset of omega-two has such a
bound strictly inside omega-two; its actual past is therefore itself a
member of omega-two and omega-one-small.

Empty T is included. No nonempty-pool, supplied bound, external index, or
completed pool-hierarchy hypothesis is used.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOrdinalPointHull

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosCountablePast ErdosInitialSegments
open ErdosOmegaTwoBounded

theorem subset_past {T : bSet 𝔹} {Γ : 𝔹} : Γ ≤ T ⊆ᴮ past T := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, past, mem_binary_union]
  exact inf_le_right.trans le_sup_left

theorem union_subset_past {T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ bv_union T ⊆ᴮ past T := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, past, mem_binary_union]
  exact inf_le_right.trans le_sup_right

theorem past_subset_of_ordinal_bound {κ T : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HT : Γ ≤ T ⊆ᴮ κ) : Γ ≤ past T ⊆ᴮ κ := by
  have HU : Γ ≤ bv_union T ⊆ᴮ κ := by
    apply union_subset_of_members_subset
    apply le_iInf
    intro a
    rw [← deduction]
    exact subset_of_mem_Ord (mem_of_mem_subset (inf_le_left.trans HT) inf_le_right)
      (inf_le_left.trans Hκ)
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, past, mem_binary_union, inf_sup_left]
  exact sup_le (mem_of_mem_subset (inf_le_left.trans HT) inf_le_right)
    (mem_of_mem_subset (inf_le_left.trans HU) inf_le_right)

theorem past_transitive_of_ordinal_subset {κ T : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HT : Γ ≤ T ⊆ᴮ κ) : Γ ≤ is_transitive (past T) := by
  have HU : Γ ≤ is_transitive (bv_union T) := by
    apply union_transitive_of_ordinal_members
    apply le_iInf
    intro a
    rw [← deduction]
    exact Ord_of_mem_Ord (mem_of_mem_subset (inf_le_left.trans HT) inf_le_right)
      (inf_le_left.trans Hκ)
  apply le_iInf
  intro x
  rw [← deduction, past, mem_binary_union, inf_sup_left]
  apply sup_le
  · exact subset_trans' (loss_subset_union inf_le_right) union_subset_past
  · exact subset_trans' (subset_of_mem_transitive (inf_le_left.trans HU) inf_le_right)
      union_subset_past

theorem past_Ord_of_subset {κ T : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HT : Γ ≤ T ⊆ᴮ κ) : Γ ≤ Ord (past T) :=
  Ord_of_transitive_subset Hκ (past_subset_of_ordinal_bound Hκ HT)
    (past_transitive_of_ordinal_subset Hκ HT)

/-- The ordinal bound is constructed, including when T is empty. -/
theorem past_mem_omegaTwo {T : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HT : Γ ≤ T ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into T omegaOne) : Γ ≤ past T ∈ᴮ omegaTwo := by
  obtain ⟨b, Hb⟩ := exists_strict_upper_bound HCH HT Hsmall
  have Hbω : Γ ≤ b ∈ᴮ omegaTwo := Hb.trans inf_le_left
  have HTb : Γ ≤ T ⊆ᴮ b := Hb.trans inf_le_right
  have HbOrd : Γ ≤ Ord b := Ord_of_mem_Ord Hbω omegaTwo_Ord
  have Hpast : Γ ≤ Ord (past T) := past_Ord_of_subset HbOrd HTb
  have Hsub : Γ ≤ past T ⊆ᴮ b := past_subset_of_ordinal_bound HbOrd HTb
  have Hcases := eq_or_mem_of_ordinal_subset Hpast HbOrd Hsub
  apply (le_inf le_rfl Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact mem_congr (bv_symm inf_le_right) bv_refl (inf_le_left.trans Hbω)
  · exact mem_of_mem_Ord inf_le_right (inf_le_left.trans Hbω) omegaTwo_Ord

theorem past_injects_omegaOne {T : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HT : Γ ≤ T ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into T omegaOne) : Γ ≤ injects_into (past T) omegaOne :=
  omegaTwo_member_injects (past_mem_omegaTwo HCH HT Hsmall)

end bSet.ErdosOrdinalPointHull
