/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaUltrapowerMasterDecisions

@[expose] public section

/-! # Scheduling all coordinates of the ultrapower word along the image diagram -/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.UltrapowerStage

variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hθ : θ.IsInaccessible) (fine : FineOn U a) (normal : NormalOn U a)
variable (ht : FiberOrderType U κ θ a)

include hθ in
theorem exists_word_schedule :
    ∃ f : θ.ord.ToType → (Order.succ θ).ord.ToType,
      ∀ α, α.toOrd.val < ordinalImage U a θ.ord → ∃ j, f j = α := by
  let o := ordinalImage U a θ.ord
  obtain ⟨v,hv,he⟩ := boundedDiagonal_ordinal_lt_successor U θ a hθ
  have ho : o < (Order.succ θ).ord :=
    (Ordinal.toZFSet_injective ((ordinalImage_code U a _).trans he)).trans_lt hv
  have hc : Cardinal.mk o.ToType ≤ Cardinal.mk θ.ord.ToType := by
    rw [Cardinal.mk_toType,Cardinal.mk_ord_toType]
    exact Order.lt_succ_iff.mp (Cardinal.lt_ord.mp ho)
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hc
  let b := Classical.arbitrary θ.ord.ToType
  have pos : 0 < o := zero_le.trans_lt
    ((ordinalImage_strictMono U a) (show b.toOrd.val < θ.ord from b.toOrd.property))
  let : Nonempty o.ToType := ⟨Ordinal.ToType.mk ⟨0,pos⟩⟩
  let f := Function.invFun e
  refine ⟨fun j => StringName.includeIndex ho.le (f j),?_⟩
  intro α hα
  let β := Ordinal.ToType.mk (⟨α.toOrd.val,hα⟩ : Set.Iio o)
  obtain ⟨j,hj⟩ := Function.invFun_surjective e.injective β
  refine ⟨j,Ordinal.ToType.mk.symm.injective (Subtype.ext ?_)⟩
  exact (StringName.includeIndex_toOrd ho.le (f j)).trans
    ((congrArg (fun z : o.ToType => z.toOrd.val) hj).trans
      (congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)))

def schedule := (exists_word_schedule U a hθ).choose

variable (D : Uniformization.Diagram κ θ θ.ord.ToType)
local notation "L" => liftCondition U a hθ fine normal ht

/-- A point meets its stage task if it decides every scheduled coordinate
whose priority has arrived and whose position lies in the stage word. -/
def wordTask (j : θ.ord.ToType) : Set (Point U a (D.poset j)) :=
  {z | ∀ k : Set.Iic j, (schedule U a hθ k.val).toOrd.val < (L (D.stage j)).length.toOrd.val →
    ∃ n : Bool, ((L (D.stage j)).withPoint ((presentationIso U a hθ (D.stage j)).symm z)).Decides
      (schedule U a hθ k.val) n}

theorem wordTask_lower (j : θ.ord.ToType) : IsLowerSet (wordTask U a hθ fine normal ht D j) := by
  intro x y hy hx k hk
  obtain ⟨n,i,hi,hv⟩ := hx k hk
  exact ⟨n,i,hi,(condition_mono ((presentationIso U a hθ (D.stage j)).symm.monotone hy)).trans hv⟩

theorem wordTask_dense (j : θ.ord.ToType) (z : Point U a (D.poset j)) :
    ∃ w ≤ z, w ∈ wordTask U a hθ fine normal ht D j := by
  let q := L (D.stage j)
  let e := presentationIso U a hθ (D.stage j)
  let f (k : Set.Iic j) := schedule U a hθ k.val
  let task (k : Set.Iic j) := {x : q.Poset | (f k).toOrd.val < q.length.toOrd.val →
    ∃ n : Bool, (q.withPoint x).Decides (f k) n}
  have down (k) : IsLowerSet (task k) := by
    intro x y hy hx hk
    obtain ⟨n,i,hi,hv⟩ := hx hk
    exact ⟨n,i,hi,(condition_mono hy).trans hv⟩
  have dense (k) (x : q.Poset) : ∃ y ≤ x, y ∈ task k := by
    by_cases hk : (f k).toOrd.val < q.length.toOrd.val
    · let i := Ordinal.ToType.mk (⟨(f k).toOrd.val,hk⟩ : Set.Iio q.length.toOrd.val)
      have hi : i.toOrd.val = (f k).toOrd.val := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
      by_cases hb : condition x ⊓ q.bits i = ⊥
      · exact ⟨x,le_rfl,fun _ => ⟨false,i,hi,le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hb)⟩⟩
      · obtain ⟨y,hy⟩ := exists_condition_le hb
        obtain ⟨w,hwy,hwx⟩ := (mem_condition_iff x y).mp
          (condition_le_iff.mp (hy.trans inf_le_left)) y le_rfl
        exact ⟨w,hwx,fun _ => ⟨true,i,hi,(condition_mono hwy).trans (hy.trans inf_le_right)⟩⟩
    · exact ⟨x,le_rfl,fun h => (hk h).elim⟩
  have small : Cardinal.mk (Set.Iic j) < θ := by
    simpa using Cardinal.mk_Iic_lt j (by simp) (by simpa using hθ.aleph0_lt.le)
  obtain ⟨w,hw,hit⟩ := InverseSystem.short_dense_lower_intersection q.complete small task down dense (e.symm z)
  refine ⟨e w,e.le_symm_apply.mp hw,?_⟩
  intro k hk
  exact down k (show e.symm (e w) ≤ w from (e.symm_apply_apply w).le) (hit k) hk

/-- A coordinate in the full image word is scheduled by some stage and
fits in a later image word. Every point meeting that stage's task decides it. -/
theorem wordTask_covers
    (cofinal : ∀ (j : θ.ord.ToType) (b : Ordinal.{u}), b < θ.ord →
      ∃ k : θ.ord.ToType, j < k ∧ b ≤ (D.stage k).length.toOrd.val)
    (α : (Order.succ θ).ord.ToType) (hα : α.toOrd.val < ordinalImage U a θ.ord) :
    ∃ j, ∀ z ∈ wordTask U a hθ fine normal ht D j, ∃ n : Bool,
      ((L (D.stage j)).withPoint ((presentationIso U a hθ (D.stage j)).symm z)).Decides α n := by
  obtain ⟨i,hi⟩ := (exists_word_schedule U a hθ).choose_spec α hα
  have hmem := Ordinal.toZFSet_mem_toZFSet_iff.mpr hα
  rw [ordinalImage_code] at hmem
  obtain ⟨b,hb,he⟩ := mem_boundedDiagonal_cofinal U θ a hθ _ hmem
  obtain ⟨j,hj,hlen⟩ := cofinal i b hb
  have localBound : α.toOrd.val < ordinalImage U a b :=
    Ordinal.toZFSet_mem_toZFSet_iff.mp ((ordinalImage_code U a b).symm ▸ he)
  have fits : α.toOrd.val < (L (D.stage j)).length.toOrd.val := by
    rw [(liftCondition_labels U a hθ fine normal ht (D.stage j)).2]
    exact localBound.trans_le ((ordinalImage_strictMono U a).monotone hlen)
  have eq : schedule U a hθ i = α := hi
  exact ⟨j,fun z hz => eq ▸ hz ⟨i,hj.le⟩ (eq.symm ▸ fits)⟩

end Erdos1172Shioya.UltrapowerStage
