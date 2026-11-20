/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalOrderTransport
public import Erdos1172.Part4ShioyaStringFusion

@[expose] public section

/-! # A ground bound for countably many mixed ordinals in the preparation -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Cardinal
namespace bSet.ErdosShioyaInternal
open Erdos1172LevyCohen Erdos1172CompleteSubalgebra
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B] {κ θ : Cardinal.{u}}

/-- For a fixed mixed ordinal its nonzero checked equality pieces have distinct
Boolean coefficients. Their checked labels therefore form a bounded set. -/
theorem mixed_ordinal_bound (hθ : θ.IsInaccessible) (small : #B < θ) {Γ : B} {x : bSet B}
    (hx : Γ ≤ x ∈ᴮ ordinalCarrier θ.ord) :
    ∃ o : Ordinal.{u}, o < θ.ord ∧ Γ ≤ x ∈ᴮ ordinalCarrier o := by
  let b (i : θ.ord.ToType) := Γ ⊓ (x =ᴮ ordinalLabel i)
  let I := {i : θ.ord.ToType // b i ≠ ⊥}
  have inj : Function.Injective (fun i : I => b i.val) := by
    intro i j eq
    apply Subtype.ext
    by_contra ne
    have same : b i.val ≤ ordinalLabel i.val =ᴮ ordinalLabel j.val :=
      bv_trans (bv_symm inf_le_right) (eq.le.trans inf_le_right)
    rw [ordinalLabel_eq,if_neg ne] at same
    exact i.property (bot_unique same)
  let sup := ⨆ i : I, i.val.toOrd.val
  have hs : sup < θ.ord := by
    apply Ordinal.lift_iSup_lt_of_lt_cof _ (fun i => i.val.toOrd.property)
    simpa [hθ.isRegular.cof_ord] using
      (Cardinal.mk_le_of_injective inj).trans_lt small
  refine ⟨Order.succ sup,(Cardinal.isSuccLimit_ord hθ.aleph0_lt.le).succ_lt hs,?_⟩
  apply ordinalCarrier_cases hx
  intro i d hd hi
  by_cases pos : b i = ⊥
  · exact ((le_inf hd hi).trans pos.le).trans bot_le
  · have lt := (Ordinal.le_iSup (fun j : I => j.val.toOrd.val) (⟨i,pos⟩ : I)).trans_lt (Order.lt_succ sup)
    exact mem_congr (bv_symm hi) bv_refl (check_mem (PSet.mk_mem_mk_of_lt lt))

theorem countable_mixed_ordinal_bound (hθ : θ.IsInaccessible) (small : #B < θ) {Γ : B} (i : ℕ → bSet B)
    (hi : ∀ n, Γ ≤ i n ∈ᴮ ordinalCarrier θ.ord) :
    ∃ o : Ordinal.{u}, o < θ.ord ∧ ∀ n, Γ ≤ i n ∈ᴮ ordinalCarrier o := by
  choose a ha hv using fun n => mixed_ordinal_bound hθ small (hi n)
  let o := ⨆ n, a n
  have ho : o < θ.ord := Erdos1172Shioya.StringName.fusion_length_lt hθ ha
  refine ⟨Order.succ o,(Cardinal.isSuccLimit_ord hθ.aleph0_lt.le).succ_lt ho,fun n => mem_of_mem_Ord (hv n) ?_ (check_Ord (PSet.Ord_mk _))⟩
  exact check_mem (PSet.mk_mem_mk_of_lt ((Ordinal.le_iSup a n).trans_lt (Order.lt_succ o)))

theorem anonymous_countable_ordinal_bound (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    {Γ : anonymousAlgebra κ} (i : ℕ → bSet (anonymousAlgebra κ)) (hi : ∀ n, Γ ≤ i n ∈ᴮ ordinalCarrier θ.ord) :
    ∃ o : Ordinal.{u}, o < θ.ord ∧ ∀ n, Γ ≤ i n ∈ᴮ ordinalCarrier o :=
  countable_mixed_ordinal_bound hθ ((Cardinal.mk_le_of_injective (inclusion_injective (anonymousAlgebra κ))).trans_lt
    ((completion_cardinal_le_two_power κ hκ).trans_lt (hθ.isStrongPrelimit hk))) i hi

end bSet.ErdosShioyaInternal
