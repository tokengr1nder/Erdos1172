/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4GroundIndexNameBound
public import Erdos1172.Part4LevyOrdinalSegments

@[expose] public section

/-!
# Checked ordinals and their ground cardinal representatives

The mutual internal injections are constructed from the exact external
cardinalities of the indexing types. No checked bijection is assumed, and
the zero ordinal is included. For the actual below-κ collapse, an ordinal
whose ground cardinality is below κ is consequently internally countable.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace bSet.ErdosCheckedOrdinalCardinality

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem checked_ordinal_injects_cardinal (η : Ordinal.{u}) :
    (⊤ : 𝔹) ≤ injects_into (check (PSet.ordinalMk η))
      (check (PSet.ordinalMk η.card.ord)) := by
  apply ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le
  simpa only [check_type', PSet.ordinalMk_card] using
    (le_rfl : η.card ≤ η.card)

theorem checked_cardinal_injects_ordinal (η : Ordinal.{u}) :
    (⊤ : 𝔹) ≤ injects_into (check (PSet.ordinalMk η.card.ord))
      (check (PSet.ordinalMk η)) := by
  have Hbound :
      Cardinal.mk (check (PSet.ordinalMk η.card.ord) : bSet 𝔹).type ≤
        Cardinal.mk (PSet.ordinalMk η).Type := by
    simpa only [check_type', PSet.ordinalMk_card, Cardinal.card_ord] using
      (le_rfl : η.card ≤ η.card)
  obtain ⟨e⟩ := (Cardinal.le_def
    (check (PSet.ordinalMk η.card.ord) : bSet 𝔹).type
    (PSet.ordinalMk η).Type).mp Hbound
  exact ErdosGroundIndexNameBound.injects_checked_ordinal_of_index_embedding
    η (check (PSet.ordinalMk η.card.ord)) e

theorem checked_ordinal_cardinal_mutual_injections (η : Ordinal.{u}) :
    (⊤ : 𝔹) ≤
      injects_into (check (PSet.ordinalMk η)) (check (PSet.ordinalMk η.card.ord)) ⊓
      injects_into (check (PSet.ordinalMk η.card.ord)) (check (PSet.ordinalMk η)) :=
  le_inf (checked_ordinal_injects_cardinal η) (checked_cardinal_injects_ordinal η)

end bSet.ErdosCheckedOrdinalCardinality

namespace Erdos1172LevyCollapse

open bSet Erdos1172PosetCompletion

/-- This countability direction needs no regularity of κ and includes
ordinals with empty indexing type. -/
theorem below_checked_ordinal_countable_of_cardinal_lt (κ : Cardinal.{u})
    (η : Ordinal.{u}) (Hcard : η.card < κ) :
    (⊤ : Completion (BelowCondition κ)) ≤
      injects_into (check (PSet.ordinalMk η)) omega := by
  have Hmember : (⊤ : Completion (BelowCondition κ)) ≤
      check (PSet.ordinalMk η.card.ord) ∈ᴮ check (PSet.ordinalMk κ.ord) :=
    check_mem (PSet.mk_mem_mk_of_lt (Cardinal.ord_lt_ord.mpr Hcard))
  exact injects_into_trans
    (ErdosCheckedOrdinalCardinality.checked_ordinal_injects_cardinal η)
    (below_checked_member_countable κ Hmember)

end Erdos1172LevyCollapse
