/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CollapseConditions
public import Mathlib.Data.DFinsupp.Order

@[expose] public section

/-!
# Finite-support dependent collapse conditions and their projections

Each coordinate is a finite sequence, ordered by reverse prefix. Only finitely
many coordinates are nonempty. For `BelowCondition κ`, a coordinate indexed
below κ has as alphabet its own strict initial segment; there is no coordinate
whose alphabet is κ itself.

Restriction to any coordinate set has an actual strengthening-lifting
operation: splice the prescribed restricted extension into the old condition.
No chain condition, countable closure, cardinal preservation, Boolean
completion embedding, or forcing-equivalence theorem is asserted here.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace Erdos1172LevyCollapse

/-- Zero records an unused coordinate, hence is the weakest factor condition. -/
scoped instance factorZero (α : Type v) : Zero (Erdos1172Collapse.Condition α) :=
  ⟨⊤⟩

/-- A finite-support dependent product of the concrete finite collapses. -/
abbrev ProductCondition {I : Type u} (A : I → Type v) :=
  Π₀ i, Erdos1172Collapse.Condition (A i)

/-- The below-κ specialization uses only alphabets strictly below κ. -/
abbrev BelowCondition (κ : Cardinal.{u}) :=
  ProductCondition (fun i : κ.ord.ToType => Set.Iio i)

/-- Every coordinate alphabet is genuinely smaller than the collapse bound. -/
theorem belowAlphabet_cardinal_lt (κ : Cardinal.{u}) (i : κ.ord.ToType) :
    Cardinal.mk (Set.Iio i) < κ := by
  simpa using Cardinal.mk_Iio_lt i (by simp)

variable {I : Type u} {A : I → Type v}

@[simp] theorem factor_zero_eq_top {α : Type v} :
    (0 : Erdos1172Collapse.Condition α) = ⊤ := rfl

instance productOrderTop : OrderTop (ProductCondition A) where
  top := 0
  le_top _ _ := le_top

@[simp] theorem top_apply (i : I) : (⊤ : ProductCondition A) i = ⊤ := rfl

theorem le_iff_prefixes {p q : ProductCondition A} :
    p ≤ q ↔ ∀ i, (q i).entries <+: (p i).entries := Iff.rfl

def SupportedOn (s : Set I) (p : ProductCondition A) : Prop :=
  ∀ i, i ∉ s → p i = ⊤

/-- Discard all coordinates outside a set, leaving their values empty. -/
def restrict (s : Set I) (p : ProductCondition A) : ProductCondition A := by
  classical
  exact p.filter (· ∈ s)

@[simp] theorem restrict_apply_of_mem {s : Set I} {i : I}
    (hi : i ∈ s) (p : ProductCondition A) : restrict s p i = p i := by
  classical
  exact DFinsupp.filter_apply_pos p hi

@[simp] theorem restrict_apply_of_not_mem {s : Set I} {i : I}
    (hi : i ∉ s) (p : ProductCondition A) : restrict s p i = ⊤ := by
  classical
  exact DFinsupp.filter_apply_neg p hi

theorem restrict_supported (s : Set I) (p : ProductCondition A) :
    SupportedOn s (restrict s p) :=
  fun _ hi => restrict_apply_of_not_mem hi p

theorem restrict_eq_self_iff {s : Set I} {p : ProductCondition A} :
    restrict s p = p ↔ SupportedOn s p := by
  constructor
  · intro h i hi
    exact (congrArg (fun q : ProductCondition A => q i) h.symm).trans
      (restrict_apply_of_not_mem hi p)
  · intro h
    apply DFinsupp.ext
    intro i
    by_cases hi : i ∈ s
    · exact restrict_apply_of_mem hi p
    · exact (restrict_apply_of_not_mem hi p).trans (h i hi).symm

@[simp] theorem restrict_idempotent (s : Set I) (p : ProductCondition A) :
    restrict s (restrict s p) = restrict s p :=
  restrict_eq_self_iff.mpr (restrict_supported s p)

@[simp] theorem restrict_top (s : Set I) : restrict s (⊤ : ProductCondition A) = ⊤ :=
  restrict_eq_self_iff.mpr (fun _ _ => rfl)

@[simp] theorem restrict_univ (p : ProductCondition A) : restrict Set.univ p = p :=
  restrict_eq_self_iff.mpr (fun _ hi => (hi (Set.mem_univ _)).elim)

@[simp] theorem restrict_empty (p : ProductCondition A) : restrict ∅ p = ⊤ := by
  apply DFinsupp.ext
  intro i
  exact restrict_apply_of_not_mem (Set.notMem_empty i) p

/-- Use the first condition on the selected coordinates and the second outside. -/
def splice (s : Set I) (q p : ProductCondition A) : ProductCondition A := by
  classical
  exact q.piecewise p s

@[simp] theorem splice_apply_of_mem {s : Set I} {i : I}
    (hi : i ∈ s) (q p : ProductCondition A) : splice s q p i = q i := by
  classical
  simp only [splice, DFinsupp.piecewise_apply, if_pos hi]

@[simp] theorem splice_apply_of_not_mem {s : Set I} {i : I}
    (hi : i ∉ s) (q p : ProductCondition A) : splice s q p i = p i := by
  classical
  simp only [splice, DFinsupp.piecewise_apply, if_neg hi]

end Erdos1172LevyCollapse
