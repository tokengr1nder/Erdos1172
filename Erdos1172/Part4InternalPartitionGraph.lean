/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartitionSemantics

@[expose] public section

/-!
# Symmetric graph colors of arbitrary internal relation names

The increasing orientation used by the partition semantics determines a
symmetric, loop-free Boolean-valued graph color. On distinct members of an
internal ordinal, the two colors cover every pair. All vertices and relations
are arbitrary names; no graph on host-language vertices is substituted.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPartition

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- `true` means membership in `R`; `false` means its Boolean complement. -/
def graphColor (color : Bool) (R x y : bSet 𝔹) : 𝔹 :=
  ((x ∈ᴮ y) ⊓ (if color then pair x y ∈ᴮ R else (pair x y ∈ᴮ R)ᶜ)) ⊔
  ((y ∈ᴮ x) ⊓ (if color then pair y x ∈ᴮ R else (pair y x ∈ᴮ R)ᶜ))

theorem graphColor_symm (color : Bool) (R x y : bSet 𝔹) :
    graphColor color R x y = graphColor color R y x := by
  unfold graphColor
  exact sup_comm _ _

theorem graphColor_self (color : Bool) (R x : bSet 𝔹) :
    graphColor color R x x = ⊥ := by
  have Hmem : x ∈ᴮ x = ⊥ := bot_unique (bot_of_mem_self' le_rfl)
  simp only [graphColor, Hmem, bot_inf_eq, sup_self]

theorem membership_two_cycle_eq_bot (x y : bSet 𝔹) :
    (x ∈ᴮ y) ⊓ (y ∈ᴮ x) = ⊥ :=
  bot_unique (bot_of_mem_mem' x y inf_le_left inf_le_right)

theorem graphColor_sup (R x y : bSet 𝔹) :
    graphColor false R x y ⊔ graphColor true R x y =
      (x ∈ᴮ y) ⊔ (y ∈ᴮ x) := by
  change ((x ∈ᴮ y ⊓ (pair x y ∈ᴮ R)ᶜ) ⊔
    (y ∈ᴮ x ⊓ (pair y x ∈ᴮ R)ᶜ)) ⊔
    ((x ∈ᴮ y ⊓ pair x y ∈ᴮ R) ⊔ (y ∈ᴮ x ⊓ pair y x ∈ᴮ R)) = _
  calc
    _ = ((x ∈ᴮ y ⊓ (pair x y ∈ᴮ R)ᶜ) ⊔ (x ∈ᴮ y ⊓ pair x y ∈ᴮ R)) ⊔
      ((y ∈ᴮ x ⊓ (pair y x ∈ᴮ R)ᶜ) ⊔ (y ∈ᴮ x ⊓ pair y x ∈ᴮ R)) := by
        ac_rfl
    _ = (x ∈ᴮ y) ⊔ (y ∈ᴮ x) := by
      simp only [← inf_sup_left, compl_sup_eq_top, inf_top_eq]

/-- The two graph colors never overlap, even for nonordinal names. -/
theorem graphColor_inf (R x y : bSet 𝔹) :
    graphColor false R x y ⊓ graphColor true R x y = ⊥ := by
  apply bot_unique
  change ((x ∈ᴮ y ⊓ (pair x y ∈ᴮ R)ᶜ) ⊔
    (y ∈ᴮ x ⊓ (pair y x ∈ᴮ R)ᶜ)) ⊓
    ((x ∈ᴮ y ⊓ pair x y ∈ᴮ R) ⊔ (y ∈ᴮ x ⊓ pair y x ∈ᴮ R)) ≤ ⊥
  rw [inf_sup_right]
  apply sup_le
  · rw [inf_sup_left]
    apply sup_le
    · exact (le_inf (inf_le_right.trans inf_le_right)
        (inf_le_left.trans inf_le_right)).trans inf_compl_eq_bot.le
    · exact (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left)).trans (membership_two_cycle_eq_bot x y).le
  · rw [inf_sup_left]
    apply sup_le
    · exact (le_inf (inf_le_right.trans inf_le_left)
        (inf_le_left.trans inf_le_left)).trans (membership_two_cycle_eq_bot x y).le
    · exact (le_inf (inf_le_right.trans inf_le_right)
        (inf_le_left.trans inf_le_right)).trans inf_compl_eq_bot.le

/-- On a forced increasing pair, symmetrization preserves the chosen color. -/
theorem graphColor_eq_oriented (color : Bool) (R : bSet 𝔹)
    {x y : bSet 𝔹} {Γ : 𝔹} (Hxy : Γ ≤ x ∈ᴮ y) :
    Γ ⊓ graphColor color R x y =
      Γ ⊓ (if color then pair x y ∈ᴮ R else (pair x y ∈ᴮ R)ᶜ) := by
  have Hyx : Γ ⊓ (y ∈ᴮ x) = ⊥ :=
    bot_unique (bot_of_mem_mem' x y (inf_le_left.trans Hxy) inf_le_right)
  unfold graphColor
  rw [inf_sup_left, ← inf_assoc, inf_eq_left.mpr Hxy,
    ← inf_assoc, Hyx, bot_inf_eq, sup_bot_eq]

theorem le_graphColor_iff_oriented (color : Bool) (R : bSet 𝔹)
    {x y : bSet 𝔹} {Γ : 𝔹} (Hxy : Γ ≤ x ∈ᴮ y) :
    Γ ≤ graphColor color R x y ↔
      Γ ≤ (if color then pair x y ∈ᴮ R else (pair x y ∈ᴮ R)ᶜ) := by
  rw [← inf_eq_left, graphColor_eq_oriented color R Hxy, inf_eq_left]

end bSet.ErdosPartition
