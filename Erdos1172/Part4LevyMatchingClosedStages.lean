/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingJointForcing

@[expose] public section

/-! # Stage density and countability for the Lévy collapse through a coordinate -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172PosetCompletion Erdos1172PositiveBoolean Erdos1172Collapse bSet
open scoped Flypitch Erdos1172LevyCollapse
namespace Erdos1172LevyCollapse.Matching

variable {θ : Cardinal.{u}}

/-- Finite conditions on all coordinates up to and including i. -/
abbrev ClosedCondition (i : θ.ord.ToType) := ProductCondition (fun j : Set.Iic i => Set.Iio j.val)

abbrev ClosedStage (i : θ.ord.ToType) := Completion (ClosedCondition i)

instance closedStageNontrivial (i : θ.ord.ToType) : NontrivialCompleteBooleanAlgebra (ClosedStage i) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

private theorem mk_Iio_toType_eq_card (i : θ.ord.ToType) :
    #(Set.Iio i) = i.toOrd.val.card := by
  let bOrd : Ordinal.{u} := i.toOrd.val
  have hbOrd : bOrd < θ.ord := Set.mem_Iio.mp i.toOrd.property
  rw [← Cardinal.mk_toType bOrd]
  apply le_antisymm
  · let f : Set.Iio i → bOrd.ToType := fun z =>
      Ordinal.ToType.mk ⟨z.val.toOrd.val,
        Set.mem_Iio.mpr (Subtype.mk_lt_mk.mp (Ordinal.ToType.mk.symm.lt_iff_lt.mpr z.property))⟩
    refine Cardinal.mk_le_of_injective (f := f) fun z₁ z₂ h => Subtype.ext ?_
    have hsub := Ordinal.ToType.mk.injective h
    have hval : z₁.val.toOrd.val = z₂.val.toOrd.val :=
      congrArg (Subtype.val : Set.Iio bOrd → Ordinal.{u}) hsub
    exact Ordinal.ToType.mk.symm.injective (Subtype.ext hval)
  · let g : bOrd.ToType → Set.Iio i := fun w =>
      let q : θ.ord.ToType := Ordinal.ToType.mk ⟨w.toOrd.val,
        Set.mem_Iio.mpr ((Set.mem_Iio.mp w.toOrd.property).trans hbOrd)⟩
      ⟨q, Ordinal.ToType.mk.symm.lt_iff_lt.mp (by
        change Ordinal.ToType.mk.symm q < Ordinal.ToType.mk.symm i
        rw [Ordinal.ToType.mk.symm_apply_apply]
        exact Subtype.mk_lt_mk.mpr (Set.mem_Iio.mp w.toOrd.property))⟩
    refine Cardinal.mk_le_of_injective (f := g) fun w₁ w₂ h => ?_
    have hq : (g w₁).val = (g w₂).val := congrArg Subtype.val h
    have hsub := Ordinal.ToType.mk.injective hq
    have hval : w₁.toOrd.val = w₂.toOrd.val :=
      congrArg (Subtype.val : Set.Iio θ.ord → Ordinal.{u}) hsub
    exact Ordinal.ToType.mk.symm.injective (Subtype.ext hval)

/-- Including the last coordinate gives density at most μ, even though this
stage collapses μ itself. -/
theorem closedCondition_cardinal_le (i : θ.ord.ToType) {μ : Cardinal.{u}}
    (inf : ℵ₀ ≤ μ) (hi : i.toOrd.val.card = μ) : #(ClosedCondition i) ≤ μ := by
  have pred : #(Set.Iio i) = μ := (mk_Iio_toType_eq_card i).trans hi
  have idx : #(Set.Iic i) = μ := by
    rw [← Set.Iio_insert,Cardinal.mk_insert Set.self_notMem_Iio,pred,Cardinal.add_one_eq inf]
  let T := Σ j : Set.Iic i, Condition (Set.Iio j.val)
  have point (j : Set.Iic i) : #(Condition (Set.Iio j.val)) ≤ μ :=
    cardinal_le.trans (max_le inf ((Cardinal.mk_le_mk_of_subset (Set.Iio_subset_Iio j.property)).trans_eq pred))
  have ht : #T ≤ μ := calc
    #T = Cardinal.sum fun j : Set.Iic i => #(Condition (Set.Iio j.val)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : Set.Iic i => μ) := Cardinal.sum_le_sum _ _ point
    _ = μ := by rw [Cardinal.sum_const',idx,Cardinal.mul_eq_self inf]
  calc
    #(ClosedCondition i) ≤ #(Finset T) := productCondition_cardinal_le_finite_graphs
    _ ≤ #(List T) := Cardinal.mk_le_of_surjective List.toFinset_surjective
    _ ≤ max ℵ₀ #T := Cardinal.mk_list_le_max T
    _ ≤ μ := max_le inf ht

theorem closedStage_countable (i : θ.ord.ToType) {μ : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hi : i.toOrd.val = μ.ord) :
    (⊤ : ClosedStage i) ≤ injects_into (check (PSet.ordinalMk μ.ord)) omega := by
  let t : Set.Iic i := ⟨i,Set.mem_Iic.mpr (le_refl i)⟩
  have hm : #(Set.Iio i) = μ := (mk_Iio_toType_eq_card i).trans (by rw [hi, Cardinal.card_ord])
  have : Nonempty ((segmentPSet i).Type) := Cardinal.mk_ne_zero_iff.mp
    (hm.trans_ne (Cardinal.aleph0_pos.trans_le hμ).ne')
  have surj : (⊤ : ClosedStage i) ≤ surjects_onto omega (check (segmentPSet i)) :=
    forces_coordinate_countable_surjection (fun j : Set.Iic i => segmentPSet j.val) t
  have h := bSet.ErdosCHHartogs.injects_into_of_larger_than_ordinal Ord_omega (larger_than_of_surjects_onto surj)
  rw [← hi]
  exact bv_rw'' (ϕ := fun z => injects_into z omega)
    (check_bv_eq (segmentPSet_equiv_ordinalMk i)) h B_ext_injects_into_left

/-- Both target-side hypotheses in the dependent stage amalgamation theorem
hold at the concrete terminal coordinate representing μ. -/
theorem closedStage_matching_data (i : θ.ord.ToType) {μ : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hi : i.toOrd.val = μ.ord) :
    (∃ d : μ.ord.ToType → Positive (ClosedStage i), ∀ a, ∃ k, d k ≤ a) ∧
    (⊤ : ClosedStage i) ≤ injects_into (check (PSet.ordinalMk μ.ord)) omega := by
  classical
  refine ⟨?_,closedStage_countable i hμ hi⟩
  have small : #(ClosedCondition i) ≤ #μ.ord.ToType := by
    rw [Cardinal.mk_ord_toType]
    exact closedCondition_cardinal_le _ hμ (by rw [hi,Cardinal.card_ord])
  obtain ⟨e⟩ := small
  refine ⟨fun k => ⟨condition (Function.invFun e k),condition_ne_bot _⟩,?_⟩
  intro a
  obtain ⟨p,hp⟩ := exists_condition_le a.property
  exact ⟨e p,by change condition (Function.invFun e (e p)) ≤ a.val; rw [Function.leftInverse_invFun e.injective]; exact hp⟩

end Erdos1172LevyCollapse.Matching
