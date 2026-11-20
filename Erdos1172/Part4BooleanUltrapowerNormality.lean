/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerOperations
public import Erdos1172.Part4BooleanFactorPoset
public import Erdos1172.Part4InternalOmegaOneCountablyBounded
public import Erdos1172.Part4InternalIdealNormality

@[expose] public section

/-! # Preservation of inverse fibers and diagonal unions by hereditary ultrapowers -/

set_option autoImplicit false
noncomputable section
open Filter bSet bSet.ErdosIdeal
open scoped Flypitch
universe u

namespace Erdos1172BooleanUltrapower

variable {I B : Type u} [NontrivialCompleteBooleanAlgebra B] (U : Ultrafilter I)
variable [CountableInterFilter (U : Filter I)]

omit [CountableInterFilter (U : Filter I)] in
private theorem value_everywhere_top (f : I → B) (h : ∀ i, (⊤ : B) ≤ f i) :
    (⊤ : Algebra U B) ≤ value U f := by
  rw [← value_top U]
  exact (value_le_value_iff U).mpr (Eventually.of_forall h)

theorem hereditary_insert (X Y : I → bSet B) :
    (⊤ : Algebra U B) ≤ hereditary U (fun i => insert (X i) (Y i)) =ᴮ
      insert (hereditary U X) (hereditary U Y) := by
  let F := fun i => insert (X i) (Y i)
  apply subset_ext
  · apply hereditary_subset_test
    intro W
    simp only [mem_insert1, value_sup, value_name_eq, value_name_mem, le_refl]
  · have hx : (⊤ : Algebra U B) ≤ hereditary U X ∈ᴮ hereditary U F := by
      rw [← value_name_mem]
      apply value_everywhere_top
      intro i
      change (⊤ : B) ≤ X i ∈ᴮ insert (X i) (Y i)
      rw [mem_insert1, bv_eq_refl, top_sup_eq]
    have hy : (⊤ : Algebra U B) ≤ hereditary U Y ⊆ᴮ hereditary U F := by
      rw [← value_name_subset]
      apply value_everywhere_top
      intro i
      rw [subset_unfold']
      apply le_iInf
      intro y
      rw [← deduction, top_inf_eq, show F i = _ from rfl, mem_insert1]
      exact le_sup_right
    rw [subset_unfold']
    apply le_iInf
    intro z
    rw [← deduction, top_inf_eq, mem_insert1]
    exact sup_le (bv_rw' le_rfl (h_congr := B_ext_mem_left) (H_new := le_top.trans hx))
      (mem_of_mem_subset (le_top.trans hy) le_rfl)

private theorem lift_insert_congr (X Y : I → bSet B) {x y : bSet (Algebra U B)}
    (hx : (⊤ : Algebra U B) ≤ hereditary U X =ᴮ x)
    (hy : (⊤ : Algebra U B) ≤ hereditary U Y =ᴮ y) :
    (⊤ : Algebra U B) ≤ hereditary U (fun i => insert (X i) (Y i)) =ᴮ insert x y :=
  bv_trans (hereditary_insert U X Y) (bv_trans (B_congr_insert1_left hx) (B_congr_insert1_right hy))

theorem hereditary_pair (X Y : I → bSet B) :
    (⊤ : Algebra U B) ≤ hereditary U (fun i => pair (X i) (Y i)) =ᴮ
      pair (hereditary U X) (hereditary U Y) := by
  have single (W : I → bSet B) :
      (⊤ : Algebra U B) ≤ hereditary U (fun i => ({W i} : bSet B)) =ᴮ {hereditary U W} :=
    lift_insert_congr U W (fun _ => ∅) bv_refl (hereditary_empty U)
  exact lift_insert_congr U _ _ (single X)
    (lift_insert_congr U _ _ (lift_insert_congr U _ _ bv_refl (single Y)) (hereditary_empty U))

end Erdos1172BooleanUltrapower
