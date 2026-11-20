/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerAtomic
public import Erdos1172.Part4InternalSmallPoolOperations

@[expose] public section

/-! # Set operations on hereditary Boolean ultrapowers -/

set_option autoImplicit false
noncomputable section
open Filter bSet bSet.ErdosIdeal
open scoped Flypitch
universe u

namespace Erdos1172BooleanUltrapower

variable {I B : Type u} [NontrivialCompleteBooleanAlgebra B] (U : Ultrafilter I)
variable [CountableInterFilter (U : Filter I)]

/-- Membership tests on represented elements suffice for an inclusion out
of a hereditary name, even when the target name is arbitrary. -/
theorem hereditary_subset_test (X : I → bSet B) (Z : bSet (Algebra U B))
    (h : ∀ W : I → bSet B, value U (fun i => W i ∈ᴮ X i) ≤ hereditary U W ∈ᴮ Z) :
    (⊤ : Algebra U B) ≤ hereditary U X ⊆ᴮ Z := by
  rw [show hereditary U X = _ from liftName_eq U _ X, subset_unfold]
  apply le_iInf
  intro a
  rw [← deduction]
  apply inf_le_right.trans ((value_le_value_iff U).2 ?_ |>.trans (h (child U X a)))
  filter_upwards [a.large] with i hi
  simpa only [weight, selected, child, dif_pos hi] using
    (mem_mk' (X i) (a.pick ⟨i, hi⟩))

private theorem mem_empty_value {A : Type u} [NontrivialCompleteBooleanAlgebra A]
    (z : bSet A) : (z ∈ᴮ (∅ : bSet A)) = ⊥ := bot_unique (bot_of_mem_empty le_rfl)

theorem hereditary_empty :
    (⊤ : Algebra U B) ≤ hereditary U (fun _ => (∅ : bSet B)) =ᴮ (∅ : bSet (Algebra U B)) := by
  apply subset_ext _ empty_subset
  apply hereditary_subset_test
  intro W
  simp only [mem_empty_value, value_bot, le_refl]

end Erdos1172BooleanUltrapower
