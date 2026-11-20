/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4DualShioyaForcing
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-! # The size of the dual Shioya forcing

The carrier order is coded by its binary relation. A regular Boolean
coefficient is determined by its underlying set of conditions. Fixing a
carrier and a length bounds both codes strictly below an inaccessible θ.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya.Condition

variable {κ θ : Cardinal.{u}}

abbrev Index (a : θ.ord.ToType) := a.toOrd.val.ToType

abbrev Data (a l : θ.ord.ToType) :=
  Set (Index a × Index a) × Index a × (Index l → Set (Index a))

def encode (p : Condition κ θ) :
    Σ a : θ.ord.ToType, Σ l : θ.ord.ToType, Data a l :=
  ⟨p.presentation.index, p.length,
    {v | p.presentation.order.le v.1 v.2}, p.point, fun i => ((p.bits i).val : Set p.Poset)⟩

private theorem encode_injective : Function.Injective (encode (κ := κ) (θ := θ)) := by
  rintro ⟨⟨a,o⟩, hs, hc, p, l, b⟩ ⟨⟨a',o'⟩, hs', hc', p', l', b'⟩ h
  obtain rfl : a = a' := congrArg Sigma.fst h
  have he := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  obtain rfl : l = l' := congrArg Sigma.fst he
  have hd := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  obtain rfl : o = o' := PartialOrder.ext (fun x y =>
    Set.ext_iff.mp (congrArg Prod.fst hd) (x,y))
  obtain rfl : p = p' := congrArg (fun z => z.2.1) hd
  have hb : b = b' := by
    funext i
    exact Heyting.Regular.coe_injective (SetLike.coe_injective (congrArg (fun z => z.2.2 i) hd))
  cases hb
  rfl

private theorem data_small (hθ : θ.IsInaccessible) (a l : θ.ord.ToType) :
    Cardinal.mk (Data a l) < θ := by
  have hsmall (j : θ.ord.ToType) : Cardinal.mk (Index j) < θ := by
    change Cardinal.mk j.toOrd.val.ToType < θ
    rw [Cardinal.mk_toType]
    exact Cardinal.lt_ord.mp j.toOrd.property
  have mulsmall {x y : Cardinal.{u}} (hx : x < θ) (hy : y < θ) : x*y < θ :=
    Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hx hy
  simp only [Data, Cardinal.mk_prod, Cardinal.mk_set, Cardinal.mk_arrow, Cardinal.lift_id,
    ← Cardinal.power_mul]
  exact mulsmall (hθ.isStrongLimit.isStrongPrelimit (mulsmall (hsmall a) (hsmall a)))
    (mulsmall (hsmall a) (hθ.isStrongLimit.isStrongPrelimit (mulsmall (hsmall a) (hsmall l))))

theorem cardinal_le (hθ : θ.IsInaccessible) : Cardinal.mk (Condition κ θ) ≤ θ := by
  apply (Cardinal.mk_le_of_injective encode_injective).trans
  have sum_bound (f : θ.ord.ToType → Cardinal.{u}) (h : ∀ i, f i ≤ θ) : Cardinal.sum f ≤ θ := by
    apply (Cardinal.sum_le_sum f (fun _ => θ) h).trans
    rw [Cardinal.sum_const', Cardinal.mk_ord_toType, Cardinal.mul_eq_self hθ.aleph0_lt.le]
  rw [Cardinal.mk_sigma]
  apply sum_bound
  intro a
  rw [Cardinal.mk_sigma]
  exact sum_bound _ (fun l => (data_small hθ a l).le)

theorem cardinal_eq (hθ : θ.IsInaccessible) [Nonempty (Condition κ θ)] :
    Cardinal.mk (Condition κ θ) = θ := by
  let p : Condition κ θ := Classical.arbitrary _
  let f (l : θ.ord.ToType) : Condition κ θ := { p with length := l, bits := fun _ => ⊥ }
  have hf : Function.Injective f := fun _ _ h => congrArg Condition.length h
  exact le_antisymm (cardinal_le hθ) ((Cardinal.mk_ord_toType θ).symm.le.trans
    (Cardinal.mk_le_of_injective hf))

end Erdos1172Shioya.Condition
