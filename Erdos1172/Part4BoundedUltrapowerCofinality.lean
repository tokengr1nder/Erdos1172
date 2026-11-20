/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4GroundFineSeedOrderType
public import Erdos1172.Part4BoundedUltrapowerHull
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

@[expose] public section

/-! # Ranks and cofinality for bounded ultrapower representatives -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Ordinal
universe u

namespace Erdos1172GroundUltrapower

variable {I : Type u} (U : Ultrafilter I) (κ θ : Cardinal.{u})
variable (a : I → Set θ.ord.ToType)

private theorem type_bounded_prefix (S : Set θ.ord.ToType) (e : κ.ord.ToType ≃o S)
    (ξ : θ.ord.ToType) (hξ : ξ ∈ S) :
    typeLT ↥(S ∩ Set.Iio ξ) = (e.symm ⟨ξ,hξ⟩).toOrd.val := by
  let P := S ∩ Set.Iio ξ
  let p : S := ⟨ξ,hξ⟩
  let bOrd : Ordinal.{u} := (e.symm p).toOrd.val
  have hbOrd : bOrd < κ.ord := Set.mem_Iio.mp (e.symm p).toOrd.property
  let E1 : P ≃o Set.Iio (e.symm p) := {
    toFun := fun z => ⟨e.symm ⟨z.val, z.property.1⟩, e.symm.strictMono z.property.2⟩
    invFun := fun z => ⟨(e z.val).val, (e z.val).property, by
      change e z.val < p
      simpa only [OrderIso.apply_symm_apply] using e.strictMono z.property⟩
    left_inv := fun z => Subtype.ext (congrArg (fun y : S => y.val) (e.apply_symm_apply ⟨z.val,z.property.1⟩))
    right_inv := fun z => Subtype.ext (e.symm_apply_apply z.val)
    map_rel_iff' := fun {_ _} => e.symm.le_iff_le }
  let E2 : Set.Iio (e.symm p) ≃o Set.Iio bOrd := {
    toFun := fun z => ⟨z.val.toOrd.val, Set.mem_Iio.mpr (Subtype.mk_lt_mk.mp (Ordinal.ToType.mk.symm.lt_iff_lt.mpr z.property))⟩
    invFun := fun z =>
      let q : κ.ord.ToType := Ordinal.ToType.mk ⟨z.val, Set.mem_Iio.mpr ((Set.mem_Iio.mp z.property).trans hbOrd)⟩
      ⟨q, Ordinal.ToType.mk.symm.lt_iff_lt.mp (by
        change Ordinal.ToType.mk.symm q < Ordinal.ToType.mk.symm (e.symm p)
        rw [Ordinal.ToType.mk.symm_apply_apply]
        exact Subtype.mk_lt_mk.mpr (Set.mem_Iio.mp z.property))⟩
    left_inv := fun z => Subtype.ext (Ordinal.ToType.mk.apply_symm_apply z.val)
    right_inv := fun z => Subtype.ext (by
      change (Ordinal.ToType.mk.symm (Ordinal.ToType.mk ⟨z.val, _⟩)).val = z.val
      rw [Ordinal.ToType.mk.symm_apply_apply])
    map_rel_iff' := fun {_ _} => Subtype.mk_le_mk.trans Ordinal.ToType.mk.symm.le_iff_le }
  exact ((E1.trans E2).trans Ordinal.ToType.mk).toRelIsoLT.ordinalType_congr.trans (Ordinal.type_toType bOrd)

theorem fineRankGerm_eq_prefix (η : θ.ord.ToType) (hf : FineOn U a) (ht : FiberOrderType U κ θ a) :
    fineRankGerm U κ θ a η = Germ.ofFun (fun i =>
      (typeLT ↥(a i ∩ Set.Iio η)).toZFSet) := by
  classical
  apply Germ.coe_eq.mpr
  filter_upwards [ht, hf η] with i hi hη
  change (if h : Nonempty (κ.ord.ToType ≃o a i) ∧ η ∈ a i then
    ((Classical.choice h.1).symm ⟨η,h.2⟩).toOrd.val.toZFSet else ∅) = _
  rw [dif_pos ⟨hi,hη⟩, type_bounded_prefix κ θ (a i) (Classical.choice hi) η hη]

theorem fineRankGerm_boundedSupport (η : θ.ord.ToType) (hf : FineOn U a) (ht : FiberOrderType U κ θ a) :
    BoundedSupport U θ a (fineRankGerm U κ θ a η) :=
  ⟨η, fun S => (typeLT S).toZFSet, (fineRankGerm_eq_prefix U κ θ a η hf ht).symm⟩

variable [CountableInterFilter (U : Filter I)]

/-- If the hull represents all the smaller ordinals, collapsing its own
membership relation preserves the full ultrapower's value at this ordinal. -/
theorem boundedCollapse_ordinal_agrees (o : Ordinal.{u})
    (hcover : ∀ α < o, ∃ x : BoundedHull U θ a, collapse U x.val = α.toZFSet)
    (x : BoundedHull U θ a) (hx : collapse U x.val = o.toZFSet) :
    boundedCollapse U θ a x = o.toZFSet := by
  induction o using WellFoundedLT.induction generalizing x with
  | ind o ih =>
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := (mem_boundedCollapse_iff U θ a z x).mp hz
      have hm : collapse U y.val ∈ o.toZFSet := hx ▸ (collapse_mem_collapse_iff U _ _).mpr hy
      obtain ⟨α, hα, hr⟩ := Ordinal.mem_toZFSet_iff.mp hm
      rw [ih α hα (fun β hβ => hcover β (hβ.trans hα)) y hr.symm]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hα
    · intro hz
      obtain ⟨α, hα, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      obtain ⟨y, hy⟩ := hcover α hα
      apply (mem_boundedCollapse_iff U θ a _ x).mpr
      refine ⟨y, (collapse_mem_collapse_iff U _ _).mp ?_,
        ih α hα (fun β hβ => hcover β (hβ.trans hα)) y hy⟩
      rw [hy, hx]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hα

theorem boundedDiagonal_critical_image [Nonempty θ.ord.ToType] (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) :
    boundedCollapse U θ a (boundedConst U θ a κ.ord.toZFSet) = θ.ord.toZFSet := by
  apply boundedCollapse_ordinal_agrees
  · intro α hα
    let η := Ordinal.ToType.mk (⟨α,hα⟩ : Set.Iio θ.ord)
    refine ⟨⟨fineRankGerm U κ θ a η, fineRankGerm_boundedSupport U κ θ a η hf ht⟩, ?_⟩
    exact (collapse_fineRankGerm U κ θ a hf hn ht η).trans (congrArg
      (fun z : Set.Iio θ.ord => z.val.toZFSet) (Ordinal.ToType.mk.symm_apply_apply ⟨α,hα⟩))
  · exact diagonal_cardinal_eq_of_fine_order_type U κ θ a hf hn ht

omit [CountableInterFilter (U : Filter I)] in
private theorem germ_rep (x : Ground U) : ∃ X : I → ZFSet.{u}, Germ.ofFun X = x :=
  Germ.inductionOn x (fun X => ⟨X,rfl⟩)

theorem boundedCollapse_isOrdinal_of_eventually (x : BoundedHull U θ a) :
    ∀ X : I → ZFSet.{u}, Germ.ofFun X = x.val → (∀ᶠ i in U, (X i).IsOrdinal) →
      (boundedCollapse U θ a x).IsOrdinal := by
  induction x using (boundedMem_wf U θ a).induction with
  | h x ih =>
    intro X hX ho
    apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
    constructor
    · intro z hz w hw
      obtain ⟨y, hy, rfl⟩ := (mem_boundedCollapse_iff U θ a _ _).mp hz
      obtain ⟨t, ht, rfl⟩ := (mem_boundedCollapse_iff U θ a _ _).mp hw
      obtain ⟨Y, hY⟩ := germ_rep U y.val
      obtain ⟨T, hT⟩ := germ_rep U t.val
      change memRel U y.val x.val at hy
      change memRel U t.val y.val at ht
      rw [← hY, ← hX] at hy
      rw [← hT, ← hY] at ht
      refine (mem_boundedCollapse_iff U θ a _ _).mpr ⟨t, ?_, rfl⟩
      change memRel U t.val x.val
      rw [← hT, ← hX]
      exact ((ho.and ht).and hy).mono (fun i h => h.1.1.mem_trans h.1.2 h.2)
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := (mem_boundedCollapse_iff U θ a _ _).mp hz
      obtain ⟨Y, hY⟩ := germ_rep U y.val
      apply ih y hy Y hY
      change memRel U y.val x.val at hy
      rw [← hY, ← hX] at hy
      exact (ho.and hy).mono (fun i h => h.1.mem h.2)

end Erdos1172GroundUltrapower
