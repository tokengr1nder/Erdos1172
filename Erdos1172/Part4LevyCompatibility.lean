/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCollapseConditions

@[expose] public section

/-!
# Concrete compatibility in the finite-support collapse product

Compatible coordinate sequences have a common strengthening whose support
is finite: choose the stronger sequence at each coordinate using `zipWith`.
This gives coordinatewise compatibility, the disjoint-support case, and an
erase-and-restore construction for induction on support size.

The final factor-cardinality bound concerns individual factors only. No
chain condition or cardinal-preservation theorem is assumed or asserted.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace Erdos1172LevyCollapse

open scoped Erdos1172LevyCollapse

variable {I : Type u} {A : I → Type v}

def Compatible (p q : ProductCondition A) : Prop :=
  ∃ r : ProductCondition A, r ≤ p ∧ r ≤ q

theorem compatible_refl (p : ProductCondition A) : Compatible p p :=
  ⟨p, le_rfl, le_rfl⟩

/-- Choose the stronger coordinate when comparable. This is finitely
supported even without a compatibility hypothesis. -/
def amalgamate (p q : ProductCondition A) : ProductCondition A := by
  classical
  exact DFinsupp.zipWith (fun _ x y => if x ≤ y then x else y)
    (fun _ => if_pos le_rfl) p q

theorem amalgamate_apply_of_le {p q : ProductCondition A} {i : I}
    (h : p i ≤ q i) : amalgamate p q i = p i := by
  classical
  simp only [amalgamate, DFinsupp.zipWith_apply, if_pos h]

theorem amalgamate_apply_of_not_le {p q : ProductCondition A} {i : I}
    (h : ¬ p i ≤ q i) : amalgamate p q i = q i := by
  classical
  simp only [amalgamate, DFinsupp.zipWith_apply, if_neg h]

theorem amalgamate_le_of_comparable {p q : ProductCondition A}
    (h : ∀ i, p i ≤ q i ∨ q i ≤ p i) :
    amalgamate p q ≤ p ∧ amalgamate p q ≤ q := by
  constructor
  · intro i
    by_cases hpq : p i ≤ q i
    · rw [amalgamate_apply_of_le hpq]
    · rw [amalgamate_apply_of_not_le hpq]
      exact (h i).resolve_left hpq
  · intro i
    by_cases hpq : p i ≤ q i
    · rw [amalgamate_apply_of_le hpq]
      exact hpq
    · rw [amalgamate_apply_of_not_le hpq]

theorem compatible_iff_coordinates {p q : ProductCondition A} :
    Compatible p q ↔ ∀ i, Erdos1172Collapse.Compatible (p i) (q i) := by
  constructor
  · rintro ⟨r, hrp, hrq⟩ i
    exact ⟨r i, hrp i, hrq i⟩
  · intro h
    have hcomp : ∀ i, p i ≤ q i ∨ q i ≤ p i :=
      fun i => Erdos1172Collapse.compatible_iff_comparable.mp (h i)
    exact ⟨amalgamate p q, amalgamate_le_of_comparable hcomp⟩

/-- At coordinates where only one condition is nonempty, that condition
already supplies the required common strengthening. -/
theorem compatible_of_disjoint_supports {p q : ProductCondition A}
    (h : Disjoint {i | p i ≠ ⊤} {i | q i ≠ ⊤}) : Compatible p q := by
  apply compatible_iff_coordinates.mpr
  intro i
  by_cases hp : p i = ⊤
  · refine ⟨q i, ?_, le_rfl⟩
    rw [hp]
    exact le_top
  · have hq : q i = ⊤ := by
      by_contra hne
      exact Set.disjoint_left.mp h hp hne
    refine ⟨p i, le_rfl, ?_⟩
    rw [hq]
    exact le_top

/-- A common strengthening after erasure can be updated by any common
strengthening of the removed coordinate. -/
theorem compatible_of_erase_of_coordinate {p q : ProductCondition A} (i : I)
    [DecidableEq I]
    (hi : Erdos1172Collapse.Compatible (p i) (q i))
    (h : Compatible (p.erase i) (q.erase i)) : Compatible p q := by
  classical
  obtain ⟨a, hap, haq⟩ := hi
  obtain ⟨r, hrp, hrq⟩ := h
  refine ⟨r.update i a, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [DFinsupp.coe_update, Function.update_self] using hap
    · simpa only [DFinsupp.coe_update, Function.update_of_ne hji,
        DFinsupp.erase_ne hji] using hrp j
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [DFinsupp.coe_update, Function.update_self] using haq
    · simpa only [DFinsupp.coe_update, Function.update_of_ne hji,
        DFinsupp.erase_ne hji] using hrq j

/-- The common-coordinate-value form needed for finite-support induction. -/
theorem compatible_of_erase_eq {p q : ProductCondition A} (i : I)
    [DecidableEq I]
    (hi : p i = q i) (h : Compatible (p.erase i) (q.erase i)) : Compatible p q :=
  compatible_of_erase_of_coordinate i ⟨p i, le_rfl, hi.le⟩ h

/-- For an uncountable upper cardinal, every individual below-κ factor
has strictly fewer than κ possible finite conditions. -/
theorem belowFactor_cardinal_lt (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 < κ)
    (i : κ.ord.ToType) :
    Cardinal.mk (Erdos1172Collapse.Condition (Set.Iio i)) < κ :=
  Erdos1172Collapse.cardinal_le.trans_lt
    (max_lt_iff.mpr ⟨hκ, belowAlphabet_cardinal_lt κ i⟩)

end Erdos1172LevyCollapse
