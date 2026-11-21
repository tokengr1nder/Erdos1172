/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCollapseConditions
public import Erdos1172.Part4PosetProjectionCompletion
public import Erdos1172.Part4CollapseMatrix

@[expose] public section

/-!
# Coordinate embeddings into the finite-support collapse completion

Evaluation at a coordinate is an actual forcing projection: replace that
coordinate by any requested strengthening and leave all other coordinates
unchanged. Evaluation is also surjective. Its inverse-image map therefore
embeds the factor's Boolean completion completely into the product's
completion. The factor's collapse matrix is transported along this concrete
embedding, with arbitrary row and column joins preserved.

This supplies coordinate collapse values only. No chain condition,
preservation of the upper cardinal, or anonymous-collapse theorem is assumed
or asserted.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace Erdos1172LevyCollapse

open Erdos1172PosetCompletion Erdos1172PosetProjection
open scoped Erdos1172LevyCollapse

variable {I : Type u} {A : I → Type v}

/-- Evaluate the finitely supported condition at one fixed coordinate. -/
def evaluationOrderHom (i : I) :
    ProductCondition A →o Erdos1172Collapse.Condition (A i) where
  toFun p := p i
  monotone' := fun _ _ h => h i

/-- Updating one coordinate gives the exact strengthening lift, without
changing the other coordinates or assuming an external support bound. -/
theorem evaluation_exactLifts (i : I) :
    ExactLifts (evaluationOrderHom (A := A) i) := by
  classical
  intro p q hq
  change q ≤ p i at hq
  refine ⟨p.update i q, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [DFinsupp.coe_update, Function.update_self] using hq
    · simpa only [DFinsupp.coe_update, Function.update_of_ne hji] using
        (le_rfl : p j ≤ p j)
  · change (p.update i q) i = q
    simp only [DFinsupp.coe_update, Function.update_self]

/-- The concrete coordinate complete homomorphism, obtained from the exact
lifting proof rather than supplied as a hypothesis. -/
def coordinateCompletionHom (i : I) :
    CompleteLatticeHom (Erdos1172Collapse.Algebra (A i))
      (Completion (ProductCondition A)) :=
  completionHom (evaluationOrderHom i) (evaluation_exactLifts i)

/-- Collapse matrix for one coordinate, now in the actual product algebra. -/
def coordinateEntry (i : I) (n : ℕ) (a : A i) :
    Completion (ProductCondition A) :=
  coordinateCompletionHom i (Erdos1172Collapse.entry n a)

theorem coordinateEntry_inf_eq_bot {i : I} {n : ℕ} {a b : A i}
    (hab : a ≠ b) : coordinateEntry i n a ⊓ coordinateEntry i n b = ⊥ := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  change p i ∈ ((Erdos1172Collapse.entry n a ⊓
    Erdos1172Collapse.entry n b).val) ↔ False
  rw [Erdos1172Collapse.entry_inf_eq_bot hab]
  rfl

theorem coordinateEntry_row_iSup_eq_top (i : I) [Nonempty (A i)] (n : ℕ) :
    (⨆ a : A i, coordinateEntry i n a) = ⊤ := by
  unfold coordinateEntry
  rw [← map_iSup, Erdos1172Collapse.row_iSup_eq_top, map_top]

theorem coordinateEntry_column_iSup_eq_top (i : I) (a : A i) :
    (⨆ n : ℕ, coordinateEntry i n a) = ⊤ := by
  unfold coordinateEntry
  rw [← map_iSup, Erdos1172Collapse.column_iSup_eq_top, map_top]

end Erdos1172LevyCollapse
