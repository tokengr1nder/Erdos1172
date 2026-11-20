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

theorem hereditary_binary_union_subset (X Y : I → bSet B) :
    (⊤ : Algebra U B) ≤ hereditary U (fun i => binary_union (X i) (Y i)) ⊆ᴮ
      binary_union (hereditary U X) (hereditary U Y) := by
  apply hereditary_subset_test
  intro W
  simp only [mem_binary_union, value_sup, value_name_mem, le_refl]

theorem hereditary_singleton_subset (X : I → bSet B) :
    (⊤ : Algebra U B) ≤ hereditary U (fun i => ({X i} : bSet B)) ⊆ᴮ
      ({hereditary U X} : bSet (Algebra U B)) := by
  apply hereditary_subset_test
  intro W
  simp only [mem_singleton_bSet, mem_empty_value, sup_bot_eq, value_name_eq, le_refl]

omit [CountableInterFilter (U : Filter I)] in
/-- An existential truth value over all source names is computed by allowing
an arbitrary source name at each index of the ultrafilter. -/
theorem value_exists_name (P : I → bSet B → B) :
    value U (fun i => ⨆ x, P i x) = ⨆ X : I → bSet B, value U (fun i => P i (X i)) := by
  classical
  apply le_antisymm
  · rw [value_iSup U (fun _ => bSet B) P]
    apply iSup_le
    intro s
    let X (i : I) : bSet B := if hi : i ∈ s.carrier then s.pick ⟨i, hi⟩ else ∅
    apply le_iSup_of_le X
    apply (value_le_value_iff U).mpr
    filter_upwards [s.large] with i hi
    simp only [selected, X, dif_pos hi, le_refl]
  · apply iSup_le
    intro X
    exact (value_le_value_iff U).mpr (Eventually.of_forall (fun i => le_iSup (P i) (X i)))

private theorem mem_union_value {A : Type u} [NontrivialCompleteBooleanAlgebra A]
    (x z : bSet A) : (z ∈ᴮ bv_union x) = ⨆ y, y ∈ᴮ x ⊓ z ∈ᴮ y :=
  le_antisymm ((bv_union_spec_split x z).mp le_rfl) ((bv_union_spec_split x z).mpr le_rfl)

theorem hereditary_union_subset (X : I → bSet B) :
    (⊤ : Algebra U B) ≤ hereditary U (fun i => bv_union (X i)) ⊆ᴮ bv_union (hereditary U X) := by
  apply hereditary_subset_test
  intro W
  simp only [mem_union_value]
  rw [value_exists_name U (fun i y => y ∈ᴮ X i ⊓ W i ∈ᴮ y)]
  apply iSup_le
  intro F
  rw [value_inf, value_name_mem, value_name_mem]
  exact le_iSup (fun y : bSet (Algebra U B) => y ∈ᴮ hereditary U X ⊓ hereditary U W ∈ᴮ y)
    (hereditary U F)

end Erdos1172BooleanUltrapower
