/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalClubIntersectionStep

@[expose] public section

/-!
Actual upper tails of internal omega-two are clubs under CH. Consequently
every internally omega-one-small subset of omega-two misses a constructed
club. These are the later nonstationary-ideal absorption witnesses; no
nonstationary ideal, stationarity, or pressing-down principle is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosClubs

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosOmegaTwoBounded ErdosRelationGraph ErdosIdeal

def upperTail (b : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun x => b ∈ᴮ x) omegaTwo

theorem mem_upperTail_iff {b x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ∈ᴮ upperTail b ↔ Γ ≤ x ∈ᴮ omegaTwo ∧ Γ ≤ b ∈ᴮ x :=
  mem_comprehend_and B_ext_mem_right

theorem upperTail_subset {b : bSet 𝔹} {Γ : 𝔹} : Γ ≤ upperTail b ⊆ᴮ omegaTwo :=
  comprehend_subset (ϕ := fun x => b ∈ᴮ x) omegaTwo

theorem unboundedIn_upperTail {b : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (Hb : Γ ≤ b ∈ᴮ omegaTwo) :
    Γ ≤ unboundedIn omegaTwo (upperTail b) := by
  apply le_iInf
  intro a
  rw [← deduction]
  obtain ⟨y, Hy⟩ := exists_above_two (inf_le_left.trans HCH)
    (show Γ ⊓ a ∈ᴮ omegaTwo ≤ a ∈ᴮ omegaTwo from inf_le_right) (inf_le_left.trans Hb)
  exact le_iSup_of_le y (le_inf
    (le_inf (mem_upperTail_iff.mpr ⟨Hy.trans inf_le_left,
      Hy.trans (inf_le_right.trans inf_le_right)⟩) (Hy.trans inf_le_left))
    (Hy.trans (inf_le_right.trans inf_le_left)))

/-- Closure of an upper tail needs no bound on its cut value. -/
theorem closedIn_upperTail (b : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ closedIn omegaTwo (upperTail b) := by
  apply le_iInf
  intro a
  rw [← deduction]
  let Δ := Γ ⊓ ((a ∈ᴮ omegaTwo ⊓ (a =ᴮ (∅ : bSet 𝔹))ᶜ) ⊓
    unboundedIn a (upperTail b))
  have Ha : Δ ≤ a ∈ᴮ omegaTwo := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have Hne : Δ ≤ (a =ᴮ (∅ : bSet 𝔹))ᶜ :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  obtain ⟨t, Ht⟩ := exists_convert (nonempty_iff_exists_mem.mp Hne) B_ext_mem_left
  obtain ⟨z, Hz⟩ := exists_unbounded_above
    (show Δ ≤ unboundedIn a (upperTail b) from inf_le_right.trans inf_le_right) Ht
  have Hbz : Δ ≤ b ∈ᴮ z :=
    (mem_upperTail_iff.mp (Hz.trans (inf_le_left.trans inf_le_left))).2
  exact mem_upperTail_iff.mpr ⟨Ha,
    mem_of_mem_Ord Hbz (Hz.trans (inf_le_left.trans inf_le_right))
      (Ord_of_mem_Ord Ha omegaTwo_Ord)⟩

theorem club_upperTail {b : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (Hb : Γ ≤ b ∈ᴮ omegaTwo) :
    Γ ≤ club omegaTwo (upperTail b) :=
  le_inf upperTail_subset (le_inf (unboundedIn_upperTail HCH Hb) (closedIn_upperTail b))

theorem exists_mem_club {C : bSet 𝔹} {Γ : 𝔹}
    (HC : Γ ≤ club omegaTwo C) : ∃ x : bSet 𝔹, Γ ≤ x ∈ᴮ C := by
  obtain ⟨x, Hx⟩ := exists_club_above HC omegaOne_mem_omegaTwo
  exact ⟨x, Hx.trans (inf_le_left.trans inf_le_left)⟩

theorem subset_complement_upperTail_of_bound {A b : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ omegaTwo) (Hbound : Γ ≤ A ⊆ᴮ b) :
    Γ ≤ A ⊆ᴮ difference omegaTwo (upperTail b) := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, mem_difference]
  refine le_inf (mem_of_mem_subset (inf_le_left.trans HA) inf_le_right) ?_
  rw [← imp_bot, ← deduction]
  have Hxb : (Γ ⊓ x ∈ᴮ A) ⊓ x ∈ᴮ upperTail b ≤ x ∈ᴮ b :=
    mem_of_mem_subset (inf_le_left.trans (inf_le_left.trans Hbound))
      (inf_le_left.trans inf_le_right)
  exact bot_of_mem_mem' x b Hxb (mem_upperTail_iff.mp inf_le_right).2

/-- The small set and the avoiding club are both arbitrary internal
names. No externally countable presentation is used. -/
theorem exists_club_avoiding_small {A : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HA : Γ ≤ A ⊆ᴮ omegaTwo)
    (Hsmall : Γ ≤ injects_into A omegaOne) :
    ∃ C : bSet 𝔹, Γ ≤ club omegaTwo C ⊓ A ⊆ᴮ difference omegaTwo C := by
  obtain ⟨b, Hb⟩ := exists_strict_upper_bound HCH HA Hsmall
  exact ⟨upperTail b, le_inf (club_upperTail HCH (Hb.trans inf_le_left))
    (subset_complement_upperTail_of_bound HA (Hb.trans inf_le_right))⟩

end bSet.ErdosClubs
