/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4GroundFineSeed
public import Mathlib.Order.Filter.CardinalInter

@[expose] public section

/-!
# Computing the critical image from the order types of the fine fibers

For a fine normal measure on families of ordinals below θ, assume the
fibers have order type κ on a measure-one set. Their pointwise ranks then
enumerate the members of the diagonal image of κ, in exactly the order θ.
-/

set_option autoImplicit false
noncomputable section
open Filter
universe u

namespace Erdos1172GroundUltrapower

variable {I : Type u} (U : Ultrafilter I) (κ θ : Cardinal.{u})

def FiberOrderType (a : I → Set θ.ord.ToType) : Prop :=
  ∀ᶠ i in U, Nonempty (κ.ord.ToType ≃o a i)

def fiberValue (s : Set θ.ord.ToType) (ξ : θ.ord.ToType) : ZFSet.{u} := by
  classical
  exact if h : Nonempty (κ.ord.ToType ≃o s) ∧ ξ ∈ s then
    ((Classical.choice h.1).symm ⟨ξ, h.2⟩).toOrd.val.toZFSet else ∅

private theorem fiberValue_good (s : Set θ.ord.ToType) (h : Nonempty (κ.ord.ToType ≃o s))
    (x : s) : fiberValue κ θ s x.val = ((Classical.choice h).symm x).toOrd.val.toZFSet := by
  classical
  simp only [fiberValue, dif_pos (And.intro h x.property)]

private theorem fiberValue_range (s : Set θ.ord.ToType) (h : Nonempty (κ.ord.ToType ≃o s)) :
    ZFSet.range (fun x : s => fiberValue κ θ s x.val) = κ.ord.toZFSet := by
  ext z
  rw [ZFSet.mem_range, Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ((Classical.choice h).symm x).toOrd.property, (fiberValue_good κ θ s h x).symm⟩
  · rintro ⟨α, hα, rfl⟩
    let k := Ordinal.ToType.mk (⟨α, hα⟩ : Set.Iio κ.ord)
    refine ⟨(Classical.choice h) k, ?_⟩
    rw [fiberValue_good κ θ s h, OrderIso.symm_apply_apply]
    exact congrArg (fun t : Set.Iio κ.ord => t.val.toZFSet) (Ordinal.ToType.mk.symm_apply_apply _)

private theorem rank_index_lt {o : Ordinal.{u}} (x y : o.ToType) :
    x.toOrd.val < y.toOrd.val ↔ x < y := Ordinal.ToType.mk.symm.lt_iff_lt

def fineRankGerm (a : I → Set θ.ord.ToType) (ξ : θ.ord.ToType) : Ground U :=
  Germ.ofFun fun i => fiberValue κ θ (a i) ξ

theorem fineRankGerm_mem_iff (a : I → Set θ.ord.ToType) (hf : FineOn U a)
    (ht : FiberOrderType U κ θ a) (η ξ : θ.ord.ToType) :
    memRel U (fineRankGerm U κ θ a η) (fineRankGerm U κ θ a ξ) ↔ η < ξ := by
  change (∀ᶠ i in U, fiberValue κ θ (a i) η ∈ fiberValue κ θ (a i) ξ) ↔ η < ξ
  have he : ∀ᶠ i in U, (fiberValue κ θ (a i) η ∈ fiberValue κ θ (a i) ξ ↔ η < ξ) := by
    filter_upwards [ht, hf η, hf ξ] with i hi hη hξ
    rw [fiberValue_good κ θ (a i) hi ⟨η, hη⟩, fiberValue_good κ θ (a i) hi ⟨ξ, hξ⟩,
      Ordinal.toZFSet_mem_toZFSet_iff, rank_index_lt, OrderIso.lt_iff_lt]
    rfl
  constructor
  · intro h
    exact (he.and h).exists.elim fun _ hi => hi.1.mp hi.2
  · exact fun h => he.mono fun _ hi => hi.mpr h

variable [CountableInterFilter (U : Filter I)]

theorem diagonal_eq_fineRank_range (a : I → Set θ.ord.ToType) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) :
    diagonal U κ.ord.toZFSet = ZFSet.range (fun ξ => collapse U (fineRankGerm U κ θ a ξ)) := by
  let v := fun (ξ : θ.ord.ToType) i => fiberValue κ θ (a i) ξ
  have he : fineFamilyCode U a v = Germ.const κ.ord.toZFSet :=
    Germ.coe_eq.mpr (ht.mono fun i hi => fiberValue_range κ θ (a i) hi)
  exact (congrArg (collapse U) he.symm).trans (collapse_fineFamilyCode U a hf hn v)

private theorem fineRank_predecessor_mem_diagonal (a : I → Set θ.ord.ToType)
    (hf : FineOn U a) (ht : FiberOrderType U κ θ a) (ξ : θ.ord.ToType)
    {x : ZFSet.{u}} (hx : x ∈ collapse U (fineRankGerm U κ θ a ξ)) :
    x ∈ diagonal U κ.ord.toZFSet := by
  obtain ⟨z, hz, rfl⟩ := (mem_collapse_iff U _ _).mp hx
  apply (collapse_mem_collapse_iff U _ _).mpr
  induction z using Germ.inductionOn with
  | _ Z =>
    have hm : ∀ᶠ i in U, Z i ∈ fiberValue κ θ (a i) ξ := hz
    change ∀ᶠ i in U, Z i ∈ κ.ord.toZFSet
    filter_upwards [hm, hf ξ, ht] with i hi hξ hgood
    rw [fiberValue_good κ θ (a i) hgood ⟨ξ, hξ⟩] at hi
    exact Ordinal.toZFSet_monotone (((Classical.choice hgood).symm ⟨ξ, hξ⟩).toOrd.property.le) hi

theorem collapse_fineRankGerm (a : I → Set θ.ord.ToType) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (ξ : θ.ord.ToType) :
    collapse U (fineRankGerm U κ θ a ξ) = ξ.toOrd.val.toZFSet := by
  induction ξ using WellFoundedLT.induction with
  | ind ξ ih =>
    ext z
    constructor
    · intro hz
      have hz' := fineRank_predecessor_mem_diagonal U κ θ a hf ht ξ hz
      rw [diagonal_eq_fineRank_range U κ θ a hf hn ht, ZFSet.mem_range] at hz'
      obtain ⟨η, rfl⟩ := hz'
      have hη := (fineRankGerm_mem_iff U κ θ a hf ht η ξ).mp ((collapse_mem_collapse_iff U _ _).mp hz)
      rw [ih η hη]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr ((rank_index_lt η ξ).mpr hη)
    · intro hz
      obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      let η := Ordinal.ToType.mk (⟨β, hβ.trans ξ.toOrd.property⟩ : Set.Iio θ.ord)
      have he : η.toOrd.val = β := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
      have hη : η < ξ := (rank_index_lt η ξ).mp (he ▸ hβ)
      rw [← he, ← ih η hη]
      exact (collapse_mem_collapse_iff U _ _).mpr ((fineRankGerm_mem_iff U κ θ a hf ht η ξ).mpr hη)

/-- The ground elementary embedding sends the actual initial ordinal of
κ to the actual initial ordinal of θ. -/
theorem diagonal_cardinal_eq_of_fine_order_type (a : I → Set θ.ord.ToType)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    diagonal U κ.ord.toZFSet = θ.ord.toZFSet := by
  rw [diagonal_eq_fineRank_range U κ θ a hf hn ht]
  ext z
  rw [ZFSet.mem_range, Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ.toOrd.val, ξ.toOrd.property, (collapse_fineRankGerm U κ θ a hf hn ht ξ).symm⟩
  · rintro ⟨β, hβ, rfl⟩
    let ξ := Ordinal.ToType.mk (⟨β, hβ⟩ : Set.Iio θ.ord)
    exact ⟨ξ, (collapse_fineRankGerm U κ θ a hf hn ht ξ).trans
      (congrArg (fun t : Set.Iio θ.ord => t.val.toZFSet) (Ordinal.ToType.mk.symm_apply_apply _))⟩

section Critical

variable [CardinalInterFilter (U : Filter I) κ]

omit [CountableInterFilter (U : Filter I)] in
private theorem constant_below_small_ordinal {α : Ordinal.{u}} (hα : α < κ.ord)
    (z : Ground U) (hz : memRel U z (Germ.const α.toZFSet)) :
    ∃ ξ : α.ToType, z = Germ.const ξ.toOrd.val.toZFSet := by
  classical
  induction z using Germ.inductionOn with
  | _ Z =>
    have hm : ∀ᶠ i in U, Z i ∈ α.toZFSet := hz
    by_contra hn
    have hnξ (ξ : α.ToType) : ∀ᶠ i in U, Z i ≠ ξ.toOrd.val.toZFSet :=
      U.eventually_not.mpr (fun h => hn ⟨ξ, Germ.coe_eq.mpr h⟩)
    have hcard : Cardinal.mk α.ToType < κ := by
      rw [Cardinal.mk_toType]
      exact Cardinal.lt_ord.mp hα
    have hall := (eventually_cardinal_forall hcard).mpr hnξ
    obtain ⟨i, hi, hnone⟩ := (hm.and hall).exists
    obtain ⟨β, hβ, he⟩ := Ordinal.mem_toZFSet_iff.mp hi
    let ξ := Ordinal.ToType.mk (⟨β, hβ⟩ : Set.Iio α)
    apply hnone ξ
    exact he.symm.trans (congrArg (fun t : Set.Iio α => t.val.toZFSet)
      (Ordinal.ToType.mk.symm_apply_apply (⟨β, hβ⟩ : Set.Iio α))).symm

theorem diagonal_fix_of_cardinalInterFilter (α : Ordinal.{u}) :
    α < κ.ord → diagonal U α.toZFSet = α.toZFSet := by
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    intro hα
    ext x
    constructor
    · intro h
      obtain ⟨z, hz, rfl⟩ := (mem_collapse_iff U _ _).mp h
      obtain ⟨ξ, rfl⟩ := constant_below_small_ordinal U κ hα z hz
      change diagonal U ξ.toOrd.val.toZFSet ∈ α.toZFSet
      rw [ih ξ.toOrd.val ξ.toOrd.property (ξ.toOrd.property.trans hα)]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr ξ.toOrd.property
    · intro h
      obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp h
      rw [← ih β hβ (hβ.trans hα)]
      exact (collapse_mem_collapse_iff U _ _).mpr
        (Eventually.of_forall fun _ => Ordinal.toZFSet_mem_toZFSet_iff.mpr hβ)

/-- A κ-complete fine normal measure concentrated on order-type-κ fibers
gives the huge embedding data: an elementary map into the transitive
target, with critical point κ, image θ and closure under θ-sequences. -/
theorem groundEmbedding_fine_critical_image_closure (a : I → Set θ.ord.ToType)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) (hkθ : κ < θ) :
    (∀ α < κ.ord, (groundEmbedding U α.toZFSet).val = α.toZFSet) ∧
    κ.ord.toZFSet ∈ (groundEmbedding U κ.ord.toZFSet).val ∧
    (groundEmbedding U κ.ord.toZFSet).val = θ.ord.toZFSet ∧
    ∀ S F : ZFSet.{u}, ZFSet.IsFunc θ.ord.toZFSet S F →
      (∀ (ξ : θ.ord.ToType) y, ZFSet.pair ξ.toOrd.val.toZFSet y ∈ F → y ∈ targetClass U) →
      F ∈ targetClass U := by
  have hj : (groundEmbedding U κ.ord.toZFSet).val = θ.ord.toZFSet :=
    diagonal_cardinal_eq_of_fine_order_type U κ θ a hf hn ht
  refine ⟨diagonal_fix_of_cardinalInterFilter U κ, ?_, hj, fine_targetClass_closed_sequences U θ a hf hn⟩
  rw [hj]
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (Cardinal.ord_lt_ord.mpr hkθ)

end Critical
end Erdos1172GroundUltrapower
