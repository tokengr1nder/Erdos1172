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

@[simp] theorem evaluationOrderHom_apply (i : I) (p : ProductCondition A) :
    evaluationOrderHom i p = p i := rfl

@[simp] theorem evaluationOrderHom_top (i : I) :
    evaluationOrderHom (A := A) i ⊤ = ⊤ := rfl

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

/-- Every factor condition is the value of a condition supported on that
single coordinate; the alphabet may be empty. -/
theorem evaluation_surjective (i : I) :
    Function.Surjective (evaluationOrderHom (A := A) i) := by
  classical
  intro q
  refine ⟨(⊤ : ProductCondition A).update i q, ?_⟩
  change ((⊤ : ProductCondition A).update i q) i = q
  simp only [DFinsupp.coe_update, Function.update_self]

/-- The concrete coordinate complete homomorphism, obtained from the exact
lifting proof rather than supplied as a hypothesis. -/
def coordinateCompletionHom (i : I) :
    CompleteLatticeHom (Erdos1172Collapse.Algebra (A i))
      (Completion (ProductCondition A)) :=
  completionHom (evaluationOrderHom i) (evaluation_exactLifts i)

theorem coordinateCompletionHom_injective (i : I) :
    Function.Injective (coordinateCompletionHom (A := A) i) :=
  completionHom_injective (evaluationOrderHom i) (evaluation_exactLifts i)
    (evaluation_surjective i)

theorem coordinateCompletionHom_compl (i : I)
    (b : Erdos1172Collapse.Algebra (A i)) :
    coordinateCompletionHom i bᶜ = (coordinateCompletionHom i b)ᶜ :=
  map_compl' (coordinateCompletionHom i) b

/-- The pullback is exactly tested by the corresponding coordinate. -/
theorem condition_le_coordinateCompletionHom_iff (i : I)
    (p : ProductCondition A) (b : Erdos1172Collapse.Algebra (A i)) :
    condition p ≤ coordinateCompletionHom i b ↔ condition (p i) ≤ b :=
  condition_le_completionHom_iff (evaluationOrderHom i)
    (evaluation_exactLifts i) p b

/-- Collapse matrix for one coordinate, now in the actual product algebra. -/
def coordinateEntry (i : I) (n : ℕ) (a : A i) :
    Completion (ProductCondition A) :=
  coordinateCompletionHom i (Erdos1172Collapse.entry n a)

theorem condition_le_coordinateEntry {i : I} {p : ProductCondition A}
    {n : ℕ} {a : A i} (hp : (p i).entries[n]? = some a) :
    condition p ≤ coordinateEntry i n a :=
  (condition_le_coordinateCompletionHom_iff i p _).mpr
    (Erdos1172Collapse.condition_le_entry hp)

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

theorem coordinateEntry_ne_bot (i : I) (n : ℕ) (a : A i) :
    coordinateEntry i n a ≠ ⊥ := by
  intro h
  apply Erdos1172Collapse.entry_ne_bot n a
  apply coordinateCompletionHom_injective i
  change coordinateEntry i n a = coordinateCompletionHom i (⊥ : Erdos1172Collapse.Algebra (A i))
  rw [map_bot]
  exact h

end Erdos1172LevyCollapse
