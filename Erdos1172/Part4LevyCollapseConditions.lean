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

instance productOrderTop : OrderTop (ProductCondition A) where
  top := 0
  le_top _ _ := le_top

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

end Erdos1172LevyCollapse
