/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerWordAgreement

@[expose] public section

/-! # Decisions at nonconstant ordinal points of the bounded ultrapower -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.UltrapowerStage
variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hθ : θ.IsInaccessible) (fine : FineOn U a) (normal : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "L" => liftCondition U a hθ fine normal ht

include hθ in
theorem total_bound : ordinalImage U a θ.ord < (Order.succ θ).ord := by
  obtain ⟨o,ho,he⟩ := boundedDiagonal_ordinal_lt_successor U θ a hθ
  exact (Ordinal.toZFSet_injective ((ordinalImage_code U a _).trans he)).trans_lt ho

/-- An arbitrary bounded ordinal point, as a position of the whole image word. -/
def pointWordIndex (w : Point U a θ.ord.ToType) :
    {α : (Order.succ θ).ord.ToType // α.toOrd.val < ordinalImage U a θ.ord} := by
  let i := indexEquiv U a θ.ord w
  let z : Set.Iio (Order.succ θ).ord := ⟨i.toOrd.val,(show i.toOrd.val < ordinalImage U a θ.ord from
    i.toOrd.property).trans (total_bound U a hθ)⟩
  exact ⟨Ordinal.ToType.mk z,(congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply z)).trans_lt i.toOrd.property⟩

theorem pointWordIndex_ord (w : Point U a θ.ord.ToType) :
    (pointWordIndex U a hθ w).val.toOrd.val = (indexEquiv U a θ.ord w).toOrd.val :=
  congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)

/-- The critical seed is a bounded point in j(κ), and its ordinal is κ. -/
def criticalOrdinalPoint (hk : κ < θ) : Point U a κ.ord.ToType := by
  have eq : ordinalImage U a κ.ord = θ.ord := Ordinal.toZFSet_injective
    ((ordinalImage_code U a _).trans (boundedDiagonal_critical_image U κ θ a fine normal ht))
  exact (indexEquiv U a κ.ord).symm (Ordinal.ToType.mk ⟨κ.ord,(Cardinal.ord_lt_ord.mpr hk).trans_eq eq.symm⟩)

theorem criticalOrdinalPoint_ord (hk : κ < θ) :
    (indexEquiv U a κ.ord (criticalOrdinalPoint U a fine normal ht hk)).toOrd.val = κ.ord := by
  unfold criticalOrdinalPoint
  rw [Equiv.apply_symm_apply]
  exact congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)

/-- Decisions at all image coordinates, including the critical seed, are
actual ultrafilter-almost-everywhere decisions made by the representative
ground conditions. -/
theorem decides_point_eventually (p : Condition κ θ) (z : Point U a p.Poset)
    (w : Point U a θ.ord.ToType) (b : Bool)
    (dec : ((L p).withPoint ((presentationIso U a hθ p).symm z)).Decides
      (pointWordIndex U a hθ w).val b) :
    ∀ᶠ i in U, (p.withPoint (repr U a z i)).Decides (repr U a w i) b := by
  obtain ⟨k,hk,hb⟩ := dec
  let len := (liftCondition_labels U a hθ fine normal ht p).2
  let k' := StringName.includeIndex len.le k
  let t := (indexEquiv U a p.length.toOrd.val).symm k'
  let incl := StringName.includeIndex (show p.length.toOrd.val < θ.ord from p.length.toOrd.property).le
  have ht' : indexEquiv U a _ t = k' := Equiv.apply_symm_apply _ _
  have hmap : map U a incl t = w := by
    apply (indexEquiv U a θ.ord).injective
    rw [show indexEquiv U a θ.ord (map U a incl t) = _ from indexEquiv_include U a _ t,ht']
    apply Ordinal.ToType.mk.symm.injective
    exact Subtype.ext ((StringName.includeIndex_toOrd _ _).trans
      ((StringName.includeIndex_toOrd len.le k).trans (hk.trans (pointWordIndex_ord U a hθ w))))
  have agree := map_repr U a incl t
  rw [hmap] at agree
  let e := presentationIso U a hθ p
  let π := PartialProjection.isoProjection (κ := θ) e
  have eval : (L p).bits k = π.booleanHom (stringBit U a p.bits t) := by
    change π.booleanHom ((liftedString U a _ p.bits).bits k') = _
    rw [← ht',liftedString_bit]
  have eventual : ∀ᶠ i in U, condition (repr U a z i) ≤
      if b then p.bits (repr U a t i) else (p.bits (repr U a t i))ᶜ := by
    cases b with
    | true =>
      change condition (e.symm z) ≤ (L p).bits k at hb
      have h := (PartialProjection.iso_condition (κ := θ) e _ _).mp (hb.trans_eq eval)
      rw [e.apply_symm_apply] at h
      exact (condition_le_stringBit U a p.bits z t).mp h
    | false =>
      change condition (e.symm z) ≤ ((L p).bits k)ᶜ at hb
      let c := map U a p.bits t
      have ec : π.booleanHom (booleanValue U a (map U a compl c)) = ((L p).bits k)ᶜ :=
        ((congrArg π.booleanHom (booleanValue_compl U a c)).trans (map_compl' π.booleanHom _)).trans
          (congrArg compl eval.symm)
      have h := (PartialProjection.iso_condition (κ := θ) e _ _).mp (hb.trans_eq ec.symm)
      rw [e.apply_symm_apply] at h
      filter_upwards [(condition_le_booleanValue U a _ _).mp h,map_repr U a compl c,
        map_repr U a p.bits t] with i hi hc hb'
      exact hi.trans_eq (hc.trans (congrArg compl hb'))
  filter_upwards [agree,eventual] with i hi hb'
  refine ⟨repr U a t i,?_,hb'⟩
  exact ((StringName.includeIndex_toOrd _ _).symm.trans (congrArg (fun x : θ.ord.ToType => x.toOrd.val) hi.symm))

variable [Fact (Cardinal.aleph0 < κ)]

/-- Internal forcing-order comparison of two repointing codes is equivalent
to comparison of their representative conditions almost everywhere. -/
theorem repointed_order_iff (p q : Condition κ θ) (z : Point U a p.Poset) (w : Point U a q.Poset) :
    ZFSet.pair (repointedCode U a hθ fine normal ht p z) (repointedCode U a hθ fine normal ht q w) ∈
      (boundedGroundEmbedding U θ a (forcingOrder κ θ)).val ↔
      ∀ᶠ i in U, p.withPoint (repr U a z i) ≤ q.withPoint (repr U a w i) := by
  refine ⟨?_,repointed_order U a hθ fine normal ht p q z w⟩
  have code (v : Condition κ θ) (s : Point U a v.Poset) :
      repointedCode U a hθ fine normal ht v s = pointCode U a conditionCode (map U a v.withPoint s) := by
    unfold repointedCode
    erw [liftCondition_repoint_code,OrderIso.apply_symm_apply,pointCode_map]
    rfl
  rw [code,code,forcingOrder,relationCode,mem_image_graph_iff]
  rintro ⟨t,he₁,he₂⟩
  let g₁ (x : {y : Condition κ θ × Condition κ θ // y.1.Refines y.2}) := x.val.1
  let g₂ (x : {y : Condition κ θ × Condition κ θ // y.1.Refines y.2}) := x.val.2
  have e₁ := pointCode_injective U a conditionCode_injective ((pointCode_map U a g₁ conditionCode t).trans he₁)
  have e₂ := pointCode_injective U a conditionCode_injective ((pointCode_map U a g₂ conditionCode t).trans he₂)
  have h₁ := map_repr U a g₁ t
  have h₂ := map_repr U a g₂ t
  rw [e₁] at h₁
  rw [e₂] at h₂
  filter_upwards [h₁,h₂,map_repr U a p.withPoint z,map_repr U a q.withPoint w] with i hi hj hx hy
  exact (hi.symm.trans hx) ▸ (hj.symm.trans hy) ▸ (repr U a t i).property

end Erdos1172Shioya.UltrapowerStage
