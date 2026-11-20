/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerOperations
public import Erdos1172.Part4BooleanSeedKernelClosure

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

private theorem value_pair_mem (X Y R : I → bSet B) :
    value U (fun i => pair (X i) (Y i) ∈ᴮ R i) =
      (pair (hereditary U X) (hereditary U Y) ∈ᴮ hereditary U R) := by
  rw [value_name_mem]
  exact (bv_rw (top_unique (hereditary_pair U X Y)) (fun z => z ∈ᴮ hereditary U R)
    (h_congr := B_ext_mem_left)).symm

theorem hereditary_diagonalUnion_subset (K R : I → bSet B) :
    (⊤ : Algebra U B) ≤ hereditary U (fun i => diagonalUnion (K i) (R i)) ⊆ᴮ
      diagonalUnion (hereditary U K) (hereditary U R) := by
  apply hereditary_subset_test
  intro W
  simp only [mem_diagonalUnion, value_inf, value_name_mem]
  apply inf_le_inf_left
  rw [value_exists_name U (fun i j => (j ∈ᴮ K i ⊓ j ∈ᴮ W i) ⊓ pair (W i) j ∈ᴮ R i)]
  apply iSup_le
  intro J
  simp only [value_inf]
  rw [value_pair_mem, value_name_mem, value_name_mem]
  apply le_iSup_of_le (hereditary U J)
  rfl

/-- The membership truth of an arbitrary target name splits over represented elements. -/
theorem hereditary_mem_cover (K : I → bSet B) (z : bSet (Algebra U B)) :
    z ∈ᴮ hereditary U K ≤ ⨆ W : I → bSet B,
      (z =ᴮ hereditary U W) ⊓ (hereditary U W ∈ᴮ hereditary U K) := by
  conv_lhs => rw [show hereditary U K = _ from liftName_eq U _ K, mem_unfold]
  apply iSup_le
  intro a
  apply le_iSup_of_le (child U K a)
  apply le_inf inf_le_right
  apply inf_le_left.trans
  rw [← value_name_mem]
  apply (value_le_value_iff U).2
  filter_upwards [a.large] with i hi
  simpa only [weight, selected, child, dif_pos hi] using (mem_mk' (K i) (a.pick ⟨i,hi⟩))

theorem hereditary_fiber_subset (K R J : I → bSet B) :
    (⊤ : Algebra U B) ≤ fiber (hereditary U K) (hereditary U R) (hereditary U J) ⊆ᴮ
      hereditary U (fun i => fiber (K i) (R i) (J i)) := by
  let F := fun i => fiber (K i) (R i) (J i)
  let G := fiber (hereditary U K) (hereditary U R) (hereditary U J)
  have hm (W : I → bSet B) : (hereditary U W ∈ᴮ hereditary U F) = (hereditary U W ∈ᴮ G) := by
    rw [← value_name_mem]
    simp only [F, G, mem_fiber, value_inf]
    exact congrArg₂ (· ⊓ ·) (value_name_mem U W K) (value_pair_mem U W J R)
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction, top_inf_eq]
  change z ∈ᴮ G ≤ z ∈ᴮ hereditary U F
  have hc : z ∈ᴮ G ≤ ⨆ W : I → bSet B,
      (z =ᴮ hereditary U W) ⊓ (hereditary U W ∈ᴮ hereditary U K) :=
    (mem_of_mem_subset (show (z ∈ᴮ G) ≤ G ⊆ᴮ hereditary U K from fiber_subset) le_rfl).trans
      (hereditary_mem_cover U K z)
  apply (le_inf le_rfl hc).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro W
  have he : z ∈ᴮ G ⊓ ((z =ᴮ hereditary U W) ⊓ hereditary U W ∈ᴮ hereditary U K) ≤
      z =ᴮ hereditary U W := inf_le_right.trans inf_le_left
  apply bv_rw' he (h_congr := B_ext_mem_left)
  rw [hm W]
  exact bv_rw'' he inf_le_left B_ext_mem_left

end Erdos1172BooleanUltrapower
