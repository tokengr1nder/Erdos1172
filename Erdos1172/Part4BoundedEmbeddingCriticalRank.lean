/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BoundedEmbeddingSmallRange
public import Mathlib.SetTheory.ZFC.VonNeumann

@[expose] public section

/-! # The bounded ground embedding fixes the entire critical rank -/

set_option autoImplicit false
noncomputable section
open Filter
universe u
namespace Erdos1172GroundUltrapower
variable {I : Type u} (U : Ultrafilter I) (κ θ : Cardinal.{u}) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [CardinalInterFilter (U : Filter I) κ] [Nonempty θ.ord.ToType]

/-- Every ground set below the inaccessible critical rank is fixed,
including set-theoretic codes for posets and their restrictions. -/
theorem boundedGroundEmbedding_fix_rank (hκ : κ.IsInaccessible) (x : ZFSet.{u}) :
    x.rank < κ.ord → (boundedGroundEmbedding U θ a x).val = x := by
  induction x using ZFSet.inductionOn with
  | _ x ih =>
    intro hx
    let f (i : Shrink.{u} x) : ZFSet.{u} := ((equivShrink x).symm i).val
    have hmem (i : Shrink.{u} x) : f i ∈ x := ((equivShrink x).symm i).property
    have hr : ZFSet.range f = x := by
      ext y
      rw [ZFSet.mem_range]
      exact ⟨fun ⟨i,hi⟩ => hi ▸ hmem i,fun hy => ⟨(equivShrink x) ⟨y,hy⟩,
        congrArg Subtype.val ((equivShrink x).symm_apply_apply ⟨y,hy⟩)⟩⟩
    have hs : Cardinal.mk (Shrink.{u} x) < κ := calc
      x.card ≤ (ZFSet.vonNeumann x.rank).card := ZFSet.card_mono (ZFSet.subset_vonNeumann_self x)
      _ = Cardinal.preBeth x.rank := ZFSet.card_vonNeumann _
      _ < Cardinal.preBeth κ.ord := Cardinal.preBeth_strictMono hx
      _ = κ := hκ.preBeth_ord
    calc
      (boundedGroundEmbedding U θ a x).val = (boundedGroundEmbedding U θ a (ZFSet.range f)).val :=
        congrArg (fun y => (boundedGroundEmbedding U θ a y).val) hr.symm
      _ = ZFSet.range (fun i => (boundedGroundEmbedding U θ a (f i)).val) := boundedGroundEmbedding_small_range U κ θ a hs f
      _ = ZFSet.range f := congrArg ZFSet.range (funext (fun i => ih _ (hmem i) ((ZFSet.rank_lt_of_mem (hmem i)).trans hx)))
      _ = x := hr

end Erdos1172GroundUltrapower
