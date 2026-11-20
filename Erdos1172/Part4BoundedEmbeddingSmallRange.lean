/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BoundedUltrapowerSequenceClosure

@[expose] public section

/-! # The bounded ultrapower embedding on small indexed sets -/

set_option autoImplicit false
noncomputable section
open Filter
universe u
namespace Erdos1172GroundUltrapower
variable {I : Type u} (U : Ultrafilter I) (κ θ : Cardinal.{u}) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [CardinalInterFilter (U : Filter I) κ] [Nonempty θ.ord.ToType]
local notation "j" => boundedGroundEmbedding U θ a

/-- Every element of the image of a range of size below the completeness
cardinal is the image of an element at a single ground index. -/
theorem boundedGroundEmbedding_small_range {L : Type u} (hL : Cardinal.mk L < κ) (f : L → ZFSet.{u}) :
    (j (ZFSet.range f)).val = ZFSet.range (fun t => (j (f t)).val) := by
  classical
  ext z
  rw [boundedGroundEmbedding_val,mem_boundedCollapse_iff,ZFSet.mem_range]
  constructor
  · rintro ⟨w,hw,rfl⟩
    have hc : ∃ t, w.val = Germ.const (f t) := by
      obtain ⟨v,hv⟩ : ∃ v : I → ZFSet.{u}, Germ.ofFun v = w.val :=
        Germ.inductionOn w.val (fun v => ⟨v,rfl⟩)
      have hm : memRel U (Germ.ofFun v) (Germ.const (ZFSet.range f)) := hv ▸ hw
      change ∀ᶠ i in U, v i ∈ ZFSet.range f at hm
      by_contra hn
      have hall : ∀ t, ∀ᶠ i in U, v i ≠ f t :=
        fun t => U.eventually_not.mpr (fun he => hn ⟨t,hv.symm.trans (Germ.coe_eq.mpr he)⟩)
      obtain ⟨i,hi,hi'⟩ := (hm.and ((eventually_cardinal_forall hL).mpr hall)).exists
      obtain ⟨t,ht⟩ := ZFSet.mem_range.mp hi
      exact hi' t ht.symm
    obtain ⟨t,ht⟩ := hc
    exact ⟨t,congrArg (boundedCollapse U θ a) (Subtype.ext ht.symm)⟩
  · rintro ⟨t,rfl⟩
    exact ⟨boundedConst U θ a (f t),Eventually.of_forall (fun _ => ZFSet.mem_range.mpr ⟨t,rfl⟩),rfl⟩

private theorem map_doubleton (hκ : Cardinal.aleph0 ≤ κ) (x y : ZFSet.{u}) :
    (j ({x,y} : ZFSet.{u})).val = ({(j x).val,(j y).val} : ZFSet.{u}) := by
  let f (s t : ZFSet.{u}) (b : ULift.{u} Bool) := if b.down then s else t
  have h (s t : ZFSet.{u}) : ZFSet.range (f s t) = ({s,t} : ZFSet.{u}) := by
    ext z
    rw [ZFSet.mem_range,ZFSet.mem_pair]
    constructor
    · rintro ⟨⟨b⟩,rfl⟩
      cases b <;> simp [f]
    · rintro (rfl | rfl)
      · exact ⟨⟨true⟩,rfl⟩
      · exact ⟨⟨false⟩,rfl⟩
  rw [← h x y, boundedGroundEmbedding_small_range U κ θ a (Cardinal.mk_lt_aleph0.trans_le hκ), ← h (j x).val (j y).val]
  apply congrArg ZFSet.range
  funext b
  cases b with | up b => cases b <;> rfl

theorem boundedGroundEmbedding_pair (hκ : Cardinal.aleph0 ≤ κ) (x y : ZFSet.{u}) :
    (j (ZFSet.pair x y)).val = ZFSet.pair (j x).val (j y).val := by
  have hsingle : (j ({x} : ZFSet.{u})).val = ({(j x).val} : ZFSet.{u}) := by
    simpa only [ZFSet.pair_eq_singleton] using map_doubleton U κ θ a hκ x x
  change (j ({{x},{x,y}} : ZFSet.{u})).val = ({{(j x).val},{(j x).val,(j y).val}} : ZFSet.{u})
  rw [map_doubleton U κ θ a hκ,hsingle,map_doubleton U κ θ a hκ]

end Erdos1172GroundUltrapower
