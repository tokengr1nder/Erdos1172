/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalNonstationaryIdeal
public import Erdos1172.Part4InternalBinaryClubs

@[expose] public section

/-!
The explicitly defined club-avoiding family is a proper internal ideal
under CH. Its union witness is the actual intersection of the two
constructed avoiding clubs. No ideal existence package is assumed.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosNonstationary

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosClubs

theorem union_subset_complement_inter {κ A B C D : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ difference κ C) (HB : Γ ≤ B ⊆ᴮ difference κ D) :
    Γ ≤ binary_union A B ⊆ᴮ difference κ (C ∩ᴮ D) := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, mem_binary_union, inf_sup_left]
  apply sup_le
  · have Hx := mem_of_mem_subset (inf_le_left.trans HA)
      (show Γ ⊓ x ∈ᴮ A ≤ x ∈ᴮ A from inf_le_right)
    rw [mem_difference] at Hx ⊢
    refine le_inf (Hx.trans inf_le_left) ?_
    rw [← imp_bot, ← deduction]
    exact bv_absurd _ (mem_binary_inter_iff.mp inf_le_right).1
      (inf_le_left.trans (Hx.trans inf_le_right))
  · have Hx := mem_of_mem_subset (inf_le_left.trans HB)
      (show Γ ⊓ x ∈ᴮ B ≤ x ∈ᴮ B from inf_le_right)
    rw [mem_difference] at Hx ⊢
    refine le_inf (Hx.trans inf_le_left) ?_
    rw [← imp_bot, ← deduction]
    exact bv_absurd _ (mem_binary_inter_iff.mp inf_le_right).2
      (inf_le_left.trans (Hx.trans inf_le_right))

theorem union_mem_nonstationaryIdeal {A B : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HA : Γ ≤ A ∈ᴮ nonstationaryIdeal)
    (HB : Γ ≤ B ∈ᴮ nonstationaryIdeal) :
    Γ ≤ binary_union A B ∈ᴮ nonstationaryIdeal := by
  obtain ⟨C, HC⟩ := exists_avoiding_club HA
  obtain ⟨D, HD⟩ := exists_avoiding_club HB
  exact mem_nonstationaryIdeal_of_club
    (club_binary_inter HCH (HC.trans inf_le_left) (HD.trans inf_le_left))
    (union_subset_complement_inter (HC.trans inf_le_right) (HD.trans inf_le_right))

theorem nonstationaryIdeal_unionClosed {Γ : 𝔹} (HCH : Γ ≤ (CH : 𝔹)) :
    Γ ≤ unionClosed (nonstationaryIdeal : bSet 𝔹) := by
  apply le_iInf
  intro A
  apply le_iInf
  intro B
  rw [← deduction]
  exact union_mem_nonstationaryIdeal (inf_le_left.trans HCH)
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)

theorem nonstationaryIdeal_isIdeal {Γ : 𝔹} (HCH : Γ ≤ (CH : 𝔹)) :
    Γ ≤ isIdeal omegaTwo nonstationaryIdeal :=
  le_inf nonstationaryIdeal_subset (le_inf (empty_mem_nonstationaryIdeal HCH)
    (le_inf nonstationaryIdeal_downward (nonstationaryIdeal_unionClosed HCH)))

theorem nonstationaryIdeal_proper {Γ : 𝔹} (HCH : Γ ≤ (CH : 𝔹)) :
    Γ ≤ properIdeal omegaTwo nonstationaryIdeal :=
  le_inf (nonstationaryIdeal_isIdeal HCH) omegaTwo_not_mem_nonstationaryIdeal

end bSet.ErdosNonstationary
