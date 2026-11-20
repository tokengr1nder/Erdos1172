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

private theorem small_domain_bound {D : Type u} (hθ : θ.IsRegular)
    (hD : Cardinal.mk D < θ) (F : D → ZFSet.{u}) :
    ∃ α < θ.ord, ∀ t, F t ∈ θ.ord.toZFSet → F t ∈ α.toZFSet := by
  classical
  let g (t : D) := if h : F t ∈ θ.ord.toZFSet then (Ordinal.mem_toZFSet_iff.mp h).choose else 0
  have hpos : 0 < θ.ord := by simpa using (Cardinal.aleph0_pos.trans_le hθ.aleph0_le)
  have hg (t : D) : g t < θ.ord := by
    by_cases h : F t ∈ θ.ord.toZFSet
    · simpa only [g, dif_pos h] using (Ordinal.mem_toZFSet_iff.mp h).choose_spec.1
    · simpa only [g, dif_neg h] using hpos
  refine ⟨⨆ t, g t + 1, Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hθ.cof_ord]) hg, ?_⟩
  intro t ht
  have he : (g t).toZFSet = F t := by
    simpa only [g, dif_pos ht] using (Ordinal.mem_toZFSet_iff.mp ht).choose_spec.2
  rw [← he]
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (Ordinal.lt_iSup_add_one _ t)

private theorem restricted_function_bound (hθ : θ.IsInaccessible)
    (η : θ.ord.ToType) (F : Set θ.ord.ToType → ZFSet.{u}) :
    ∃ α < θ.ord, ∀ S : Set θ.ord.ToType, F (S ∩ Set.Iio η) ∈ θ.ord.toZFSet →
      F (S ∩ Set.Iio η) ∈ α.toZFSet := by
  let expand (t : Set (Set.Iio η)) := Subtype.val '' t
  have hcard : Cardinal.mk (Set (Set.Iio η)) < θ := by
    rw [Cardinal.mk_set]
    apply hθ.isStrongPrelimit
    simpa using Cardinal.mk_Iio_lt η (by simp)
  obtain ⟨α, hα, h⟩ := small_domain_bound θ hθ.isRegular hcard (fun t => F (expand t))
  refine ⟨α, hα, ?_⟩
  intro S hs
  have he : expand (Subtype.val ⁻¹' S) = S ∩ Set.Iio η := by
    ext z
    exact ⟨fun ⟨t, ht, eq⟩ => eq ▸ And.intro ht t.property,
      fun hz => ⟨⟨z,hz.2⟩,hz.1,rfl⟩⟩
  exact he ▸ h _ (he.symm ▸ hs)

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

theorem boundedHull_mem_constant_bound (hθ : θ.IsInaccessible) (x : BoundedHull U θ a)
    (hx : memRel U x.val (Germ.const θ.ord.toZFSet)) :
    ∃ α < θ.ord, memRel U x.val (Germ.const α.toZFSet) := by
  obtain ⟨η, F, hF⟩ := x.property
  rw [← hF] at hx ⊢
  obtain ⟨α, hα, h⟩ := restricted_function_bound θ hθ η F
  exact ⟨α, hα, (show ∀ᶠ i in U, F (boundedFiber θ a η i) ∈ θ.ord.toZFSet from hx).mono
    (fun i hi => h (a i) hi)⟩

variable [CountableInterFilter (U : Filter I)]

theorem mem_boundedDiagonal_cofinal [Nonempty θ.ord.ToType] (hθ : θ.IsInaccessible) (z : ZFSet.{u})
    (hz : z ∈ boundedCollapse U θ a (boundedConst U θ a θ.ord.toZFSet)) :
    ∃ α < θ.ord, z ∈ boundedCollapse U θ a (boundedConst U θ a α.toZFSet) := by
  obtain ⟨x, hx, rfl⟩ := (mem_boundedCollapse_iff U θ a _ _).mp hz
  obtain ⟨α, hα, hm⟩ := boundedHull_mem_constant_bound U θ a hθ x hx
  exact ⟨α, hα, (mem_boundedCollapse_iff U θ a _ _).mpr ⟨x, hm, rfl⟩⟩

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

abbrev PrefixCodes (ν η : θ.ord.ToType) := Set (Set (Set.Iio ν) × Set.Iio η)

abbrev OrdinalCodes := Σ ν : θ.ord.ToType, Σ η : θ.ord.ToType, PrefixCodes θ ν η

private theorem ordinalCodes_cardinal_le (hθ : θ.IsInaccessible) : Cardinal.mk (OrdinalCodes θ) ≤ θ := by
  have hi (ν : θ.ord.ToType) : Cardinal.mk (Set.Iio ν) < θ := by
    simpa using Cardinal.mk_Iio_lt ν (by simp)
  have hb (ν η : θ.ord.ToType) : Cardinal.mk (PrefixCodes θ ν η) ≤ θ := by
    apply le_of_lt
    rw [PrefixCodes, Cardinal.mk_set, Cardinal.mk_prod, Cardinal.mk_set]
    simp only [Cardinal.lift_id]
    exact hθ.isStrongPrelimit (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le (hθ.isStrongPrelimit (hi ν)) (hi η))
  have hsum (f : θ.ord.ToType → Cardinal.{u}) (hf : ∀ i, f i ≤ θ) : Cardinal.sum f ≤ θ := by
    apply (Cardinal.sum_le_sum _ _ hf).trans
    rw [Cardinal.sum_const', Cardinal.mk_ord_toType, Cardinal.mul_eq_self hθ.aleph0_lt.le]
  rw [OrdinalCodes, Cardinal.mk_sigma]
  apply hsum
  intro ν
  rw [Cardinal.mk_sigma]
  exact hsum _ (hb ν)

def readPrefix (ν η : θ.ord.ToType) (c : PrefixCodes θ ν η) (S : Set θ.ord.ToType) : ZFSet.{u} := by
  classical
  exact if h : ∃ x : Set.Iio η, (Subtype.val ⁻¹' S, x) ∈ c
    then h.choose.val.toOrd.val.toZFSet else ∅

def codeHull (c : OrdinalCodes θ) : BoundedHull U θ a :=
  ⟨Germ.ofFun (fun i => readPrefix θ c.1 c.2.1 c.2.2 (boundedFiber θ a c.1 i)),
    c.1, readPrefix θ c.1 c.2.1 c.2.2, rfl⟩

omit [CountableInterFilter (U : Filter I)] in
private theorem boundedHull_exists_ordinalCode (hθ : θ.IsInaccessible) (x : BoundedHull U θ a)
    (hx : memRel U x.val (Germ.const θ.ord.toZFSet)) : ∃ c : OrdinalCodes θ, codeHull U θ a c = x := by
  classical
  obtain ⟨ν, F, hF⟩ := x.property
  obtain ⟨α, hα, hbound⟩ := boundedHull_mem_constant_bound U θ a hθ x hx
  let η := Ordinal.ToType.mk (⟨α,hα⟩ : Set.Iio θ.ord)
  let c : PrefixCodes θ ν η := {q | q.2.val.toOrd.val.toZFSet = F (Subtype.val '' q.1)}
  refine ⟨⟨ν,η,c⟩, Subtype.ext (hF ▸ Germ.coe_eq.mpr ?_)⟩
  rw [← hF] at hbound
  filter_upwards [show ∀ᶠ i in U, F (boundedFiber θ a ν i) ∈ α.toZFSet from hbound] with i hi
  let S := boundedFiber θ a ν i
  have hS : Subtype.val '' ((Subtype.val : Set.Iio ν → θ.ord.ToType) ⁻¹' S) = S := by
    ext z
    exact ⟨fun ⟨t, ht, eq⟩ => eq ▸ ht, fun hz => ⟨⟨z,hz.2⟩,hz,rfl⟩⟩
  have hgood : ∃ b : Set.Iio η, (Subtype.val ⁻¹' S, b) ∈ c := by
    obtain ⟨β, hβ, hf⟩ := Ordinal.mem_toZFSet_iff.mp hi
    let v : Set.Iio θ.ord := ⟨β,hβ.trans hα⟩
    have hv : (Ordinal.ToType.mk v).toOrd.val = β := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply v)
    have hvη : Ordinal.ToType.mk v < η := Ordinal.ToType.mk.lt_iff_lt.mpr hβ
    refine ⟨⟨Ordinal.ToType.mk v, hvη⟩, ?_⟩
    change (Ordinal.ToType.mk v).toOrd.val.toZFSet = F (Subtype.val '' (Subtype.val ⁻¹' S))
    rw [hS, hv]
    exact hf
  change readPrefix θ ν η c S = F S
  rw [readPrefix, dif_pos hgood]
  exact (show hgood.choose.val.toOrd.val.toZFSet = F (Subtype.val '' (Subtype.val ⁻¹' S))
    from hgood.choose_spec).trans (congrArg F hS)

/-- Every member of the image of θ is coded by two bounded ordinal
parameters and one ground relation of cardinality below θ. -/
theorem boundedDiagonal_cardinal_le [Nonempty θ.ord.ToType] (hθ : θ.IsInaccessible) :
    (boundedCollapse U θ a (boundedConst U θ a θ.ord.toZFSet)).card ≤ θ := by
  let F (c : OrdinalCodes θ) := boundedCollapse U θ a (codeHull U θ a c)
  apply (ZFSet.card_mono (y := ZFSet.range F) ?_).trans
  · apply (show (ZFSet.range F).card ≤ Cardinal.mk (OrdinalCodes θ) by
      simpa only [Cardinal.lift_id] using (ZFSet.lift_card_range_le (f := F))).trans
    exact ordinalCodes_cardinal_le θ hθ
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_boundedCollapse_iff U θ a z _).mp hz
    obtain ⟨c, hc⟩ := boundedHull_exists_ordinalCode U θ a hθ x hx
    exact ZFSet.mem_range.mpr ⟨c, congrArg (boundedCollapse U θ a) hc⟩

theorem boundedDiagonal_lt_successor [Nonempty θ.ord.ToType] (hθ : θ.IsInaccessible)
    {o : Ordinal.{u}} (ho : boundedCollapse U θ a (boundedConst U θ a θ.ord.toZFSet) = o.toZFSet) :
    o < (Order.succ θ).ord := by
  have hc := boundedDiagonal_cardinal_le U θ a hθ
  rw [ho, Ordinal.card_toZFSet] at hc
  exact Cardinal.lt_ord.mpr (Order.lt_succ_of_le hc)

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

theorem boundedDiagonal_ordinal_lt_successor [Nonempty θ.ord.ToType] (hθ : θ.IsInaccessible) :
    ∃ o < (Order.succ θ).ord, boundedCollapse U θ a (boundedConst U θ a θ.ord.toZFSet) = o.toZFSet := by
  have ho := boundedCollapse_isOrdinal_of_eventually U θ a (boundedConst U θ a θ.ord.toZFSet)
    (fun _ => θ.ord.toZFSet) rfl (Eventually.of_forall (fun _ => ZFSet.isOrdinal_toZFSet _))
  exact ⟨_, boundedDiagonal_lt_successor U θ a hθ ho.toZFSet_rank_eq.symm, ho.toZFSet_rank_eq.symm⟩

end Erdos1172GroundUltrapower
