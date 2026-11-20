/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BoundedUltrapowerCofinality

@[expose] public section

/-! # Short sequence closure of the bounded ultrapower

For fewer than θ target parameters, regularity bounds their supports and
the indices coding them simultaneously. Fineness and normality then recover
the given target family as the range of one bounded-support name.
-/

set_option autoImplicit false
noncomputable section
open Filter
universe u
namespace Erdos1172GroundUltrapower

variable {I : Type u} (U : Ultrafilter I) (κ θ : Cardinal.{u}) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)]

private theorem bounded_range_of_full_range {L : Type u} (x : L → BoundedHull U θ a)
    (z : BoundedHull U θ a) (hz : collapse U z.val = ZFSet.range (fun t => collapse U (x t).val)) :
    boundedCollapse U θ a z = ZFSet.range (fun t => boundedCollapse U θ a (x t)) := by
  ext p
  rw [mem_boundedCollapse_iff, ZFSet.mem_range]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hm := (collapse_mem_collapse_iff U w.val z.val).mpr hw
    rw [hz, ZFSet.mem_range] at hm
    obtain ⟨t, ht⟩ := hm
    exact ⟨t, congrArg (boundedCollapse U θ a) (Subtype.ext (collapse_injective U ht))⟩
  · rintro ⟨t, rfl⟩
    refine ⟨x t, (collapse_mem_collapse_iff U _ _).mp ?_, rfl⟩
    rw [hz, ZFSet.mem_range]
    exact ⟨t,rfl⟩

/-- Closure under ranges of any externally indexed family of cardinality
below θ. An empty domain is allowed. -/
theorem boundedTarget_small_range (hθ : θ.IsRegular) (hf : FineOn U a) (hn : NormalOn U a)
    {L : Type u} (hL : Cardinal.mk L < θ) (F : L → ZFSet.{u})
    (hF : ∀ t, F t ∈ boundedTargetClass U θ a) : ZFSet.range F ∈ boundedTargetClass U θ a := by
  classical
  choose x hx using hF
  choose η f hr using fun t => (x t).property
  obtain ⟨e⟩ : Nonempty (L ↪ θ.ord.ToType) :=
    (Cardinal.le_def _ _).mp (by simpa only [Cardinal.mk_ord_toType] using hL.le)
  let h (t : L) := max (η t) (e t)
  let β := ⨆ t, (h t).toOrd.val + 1
  have hβ : β < θ.ord := Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hθ.cof_ord]) (fun t => (h t).toOrd.property)
  let ν := Ordinal.ToType.mk (⟨β,hβ⟩ : Set.Iio θ.ord)
  have hν (t : L) : h t < ν := by
    apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
    change (h t).toOrd.val < ν.toOrd.val
    rw [show ν.toOrd.val = β from congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply ⟨β,hβ⟩)]
    exact Ordinal.lt_iSup_add_one _ t
  let s (i : I) := boundedFiber θ a ν i
  let b (i : I) := e ⁻¹' s i
  let v (t : L) (i : I) := f t (s i ∩ Set.Iio (η t))
  have hrep (t : L) : Germ.ofFun (v t) = (x t).val := by
    simpa only [v,s,boundedFiber_restrict θ a ((le_max_left (η t) (e t)).trans (hν t).le)] using hr t
  have hf' : FineOn U b := fun t => (hf (e t)).mono fun _ hi =>
    ⟨hi, (le_max_right (η t) (e t)).trans_lt (hν t)⟩
  have hn' : NormalOn U b := by
    intro g hg
    obtain ⟨ξ, hξ⟩ := hn (fun i => e (g i)) (hg.mono (fun _ hi => hi.1))
    obtain ⟨i, hi⟩ := hξ.exists
    exact ⟨g i, hξ.mono (fun _ he => e.injective (he.trans hi.symm))⟩
  let z : BoundedHull U θ a := ⟨fineFamilyCode U b v, ν,
    fun S => ZFSet.range (fun t : (e ⁻¹' S) => f t.val (S ∩ Set.Iio (η t.val))), rfl⟩
  have hz : collapse U z.val = ZFSet.range (fun t => collapse U (x t).val) :=
    (collapse_fineFamilyCode U b hf' hn' v).trans (congrArg ZFSet.range (funext (fun t => congrArg (collapse U) (hrep t))))
  exact ⟨z, (bounded_range_of_full_range U θ a x z hz).trans (congrArg ZFSet.range (funext hx))⟩

private theorem bounded_doubleton (hθ : θ.IsRegular) (hf : FineOn U a) (hn : NormalOn U a)
    {x y : ZFSet.{u}} (hx : x ∈ boundedTargetClass U θ a) (hy : y ∈ boundedTargetClass U θ a) :
    ({x,y} : ZFSet.{u}) ∈ boundedTargetClass U θ a := by
  let F (b : ULift.{u} Bool) := if b.down then x else y
  have he : ZFSet.range F = ({x,y} : ZFSet.{u}) := by
    ext z
    rw [ZFSet.mem_range, ZFSet.mem_pair]
    constructor
    · rintro ⟨⟨b⟩, rfl⟩
      cases b <;> simp [F]
    · rintro (rfl | rfl)
      · exact ⟨⟨true⟩,rfl⟩
      · exact ⟨⟨false⟩,rfl⟩
  rw [← he]
  exact boundedTarget_small_range U θ a hθ hf hn (Cardinal.mk_lt_aleph0.trans_le hθ.aleph0_le) F
    (fun b => by cases b with | up b => cases b <;> simp [F,hx,hy])

theorem boundedTarget_pair (hθ : θ.IsRegular) (hf : FineOn U a) (hn : NormalOn U a)
    {x y : ZFSet.{u}} (hx : x ∈ boundedTargetClass U θ a) (hy : y ∈ boundedTargetClass U θ a) :
    ZFSet.pair x y ∈ boundedTargetClass U θ a := by
  have hs : ({x} : ZFSet.{u}) ∈ boundedTargetClass U θ a := by
    simpa only [ZFSet.pair_eq_singleton] using bounded_doubleton U θ a hθ hf hn hx hx
  exact bounded_doubleton U θ a hθ hf hn hs (bounded_doubleton U θ a hθ hf hn hx hy)

variable [Nonempty θ.ord.ToType]

theorem boundedTarget_short_sequences (hθ : θ.IsRegular) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (α : Ordinal.{u}) (hα : α < θ.ord) (S F : ZFSet.{u})
    (hF : ZFSet.IsFunc α.toZFSet S F) (hvalues : ∀ (t : α.ToType) y, ZFSet.pair t.toOrd.val.toZFSet y ∈ F →
      y ∈ boundedTargetClass U θ a) : F ∈ boundedTargetClass U θ a := by
  classical
  let o (t : α.ToType) := t.toOrd.val.toZFSet
  have hdom (t : α.ToType) : o t ∈ α.toZFSet := Ordinal.toZFSet_mem_toZFSet_iff.mpr t.toOrd.property
  choose v hv using fun t : α.ToType => (hF.2 (o t) (hdom t)).exists
  have he : ZFSet.range (fun t => ZFSet.pair (o t) (v t)) = F := by
    ext z
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨t,rfl⟩; exact hv t
    · intro hz
      obtain ⟨p, hp, y, _, rfl⟩ := ZFSet.mem_prod.mp (hF.1 hz)
      obtain ⟨β,hβ,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hp
      let t := Ordinal.ToType.mk (⟨β,hβ⟩ : Set.Iio α)
      have ho : o t = β.toZFSet := congrArg (fun z : Set.Iio α => z.val.toZFSet) (Ordinal.ToType.mk.symm_apply_apply _)
      rw [← ho] at hz ⊢
      exact ⟨t, congrArg (ZFSet.pair (o t)) ((hF.2 (o t) (hdom t)).unique (hv t) hz)⟩
  rw [← he]
  apply boundedTarget_small_range U θ a hθ hf hn
  · simpa only [← Ordinal.card_type (· < ·), Ordinal.type_toType] using Cardinal.lt_ord.mp hα
  · intro t
    apply boundedTarget_pair U θ a hθ hf hn _ (hvalues t (v t) (hv t))
    apply boundedTargetClass_transitive U θ a (x := θ.ord.toZFSet)
    · exact ⟨_, boundedDiagonal_critical_image U κ θ a hf hn ht⟩
    · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (t.toOrd.property.trans hα)

theorem boundedGroundEmbedding_moves_target (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hkθ : κ < θ) :
    θ.ord.toZFSet ∈ (boundedGroundEmbedding U θ a θ.ord.toZFSet).val := by
  rw [boundedGroundEmbedding_val]
  apply (mem_boundedCollapse_iff U θ a _ _).mpr
    ⟨boundedConst U θ a κ.ord.toZFSet, ?_, boundedDiagonal_critical_image U κ θ a hf hn ht⟩
  exact Eventually.of_forall (fun _ => Ordinal.toZFSet_mem_toZFSet_iff.mpr (Cardinal.ord_lt_ord.mpr hkθ))

theorem boundedGroundEmbedding_fix_below [CardinalInterFilter (U : Filter I) κ]
    (α : Ordinal.{u}) (hα : α < κ.ord) : (boundedGroundEmbedding U θ a α.toZFSet).val = α.toZFSet := by
  apply boundedCollapse_ordinal_agrees
  · intro β hβ
    exact ⟨boundedConst U θ a β.toZFSet, diagonal_fix_of_cardinalInterFilter U κ β (hβ.trans hα)⟩
  · exact diagonal_fix_of_cardinalInterFilter U κ α hα

theorem boundedGroundEmbedding_target_interval (hθ : θ.IsInaccessible) (hf : FineOn U a)
    (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) (hkθ : κ < θ) :
    ∃ o : Ordinal.{u}, θ.ord < o ∧ o < (Order.succ θ).ord ∧
      (boundedGroundEmbedding U θ a θ.ord.toZFSet).val = o.toZFSet ∧
      ∀ γ < o, ∃ α < θ.ord, γ.toZFSet ∈ (boundedGroundEmbedding U θ a α.toZFSet).val := by
  obtain ⟨o, hu, he⟩ := boundedDiagonal_ordinal_lt_successor U θ a hθ
  have hm := boundedGroundEmbedding_moves_target U κ θ a hf hn ht hkθ
  rw [boundedGroundEmbedding_val, he] at hm
  refine ⟨o, Ordinal.toZFSet_mem_toZFSet_iff.mp hm, hu, he, ?_⟩
  intro γ hγ
  apply mem_boundedDiagonal_cofinal U θ a hθ
  rw [he]
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hγ

end Erdos1172GroundUltrapower
