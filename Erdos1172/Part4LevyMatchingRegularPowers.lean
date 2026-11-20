/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingClosedStages

@[expose] public section

/-! # Cofinal regular cardinals supporting short-function codes -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal
namespace Erdos1172LevyCollapse.Matching

theorem succ_power_closed {κ ν : Cardinal.{u}} (hk : κ ≤ ν) (hv : ℵ₀ ≤ ν) :
    (Order.succ ((2 : Cardinal.{u}) ^ ν)) ^ κ ≤ Order.succ ((2 : Cardinal.{u}) ^ ν) := by
  classical
  let μ := Order.succ ((2 : Cardinal.{u}) ^ ν)
  let A := κ.ord.ToType
  let T := μ.ord.ToType
  have hinf := hv.trans (Cardinal.cantor ν).le
  have hreg : μ.IsRegular := Cardinal.isRegular_succ hinf
  have hlt : κ < μ := (hk.trans (Cardinal.cantor ν).le).trans_lt (Order.lt_succ _)
  have bound (f : A → T) : ∃ j : T, ∀ t, f t < j := by
    by_contra! neg
    have hc : IsCofinal (Set.range f) := fun j => by
      obtain ⟨a, ha⟩ := neg j
      exact ⟨f a, Set.mem_range_self a, le_of_not_gt ha⟩
    have h := Order.cof_le hc
    rw [show Order.cof T = μ from (Ordinal.cof_toType μ.ord).trans hreg.cof_ord] at h
    exact hlt.not_ge (h.trans (Cardinal.mk_range_le.trans_eq (Cardinal.mk_ord_toType κ)))
  let f (x : A → T) : Σ j : T, A → Set.Iio j := ⟨(bound x).choose,fun a => ⟨x a,(bound x).choose_spec a⟩⟩
  have inj : Function.Injective f := by
    intro x y eq
    let decode (z : Σ j : T, A → Set.Iio j) (a : A) := (z.2 a).val
    exact congrArg decode eq
  have size (j : T) : #(A → Set.Iio j) ≤ μ := by
    have small : #(Set.Iio j) ≤ 2 ^ ν := Order.lt_succ_iff.mp (show #(Set.Iio j) < μ from by
      simpa [T] using Cardinal.mk_Iio_lt j (by simp [T]))
    rw [← Cardinal.power_def,Cardinal.mk_ord_toType]
    calc
      #(Set.Iio j) ^ κ ≤ (2 ^ ν) ^ κ := Cardinal.power_le_power_right small
      _ = 2 ^ (ν * κ) := Cardinal.power_mul.symm
      _ ≤ 2 ^ ν := Cardinal.power_le_power_left two_ne_zero ((mul_le_mul' le_rfl hk).trans_eq (Cardinal.mul_eq_self hv))
      _ ≤ μ := Order.le_succ _
  calc
    μ ^ κ = #(A → T) := by rw [← Cardinal.power_def,Cardinal.mk_ord_toType,Cardinal.mk_ord_toType]
    _ ≤ #(Σ j : T, A → Set.Iio j) := Cardinal.mk_le_of_injective inj
    _ ≤ Cardinal.sum (fun _ : T => μ) := (Cardinal.mk_sigma _).trans_le (Cardinal.sum_le_sum _ _ size)
    _ = μ := by rw [Cardinal.sum_const',Cardinal.mk_ord_toType,Cardinal.mul_eq_self (hinf.trans (Order.le_succ _))]

theorem cofinal_regular_power_closed {κ θ : Cardinal.{u}} (hk : κ < θ) (hθ : θ.IsInaccessible)
    (ξ : Cardinal.{u}) (hξ : ξ < θ) :
    ∃ μ < θ, max ξ κ < μ ∧ ℵ₀ < μ ∧ μ.IsRegular ∧ μ ^ κ ≤ μ := by
  let ν := max (max ξ κ) ℵ₀
  have hv : ℵ₀ ≤ ν := le_max_right _ _
  have hn : ν < θ := max_lt (max_lt hξ hk) hθ.aleph0_lt
  let μ := Order.succ ((2 : Cardinal.{u}) ^ ν)
  have large : ν < μ := (Cardinal.cantor ν).trans (Order.lt_succ _)
  exact ⟨μ,hθ.isSuccLimit.succ_lt (hθ.isStrongPrelimit hn),(le_max_left _ _).trans_lt large,
    hv.trans_lt large,Cardinal.isRegular_succ (hv.trans (Cardinal.cantor ν).le),
    succ_power_closed ((le_max_right ξ κ).trans (le_max_left _ _)) hv⟩

/-- Bounded subsets can be coded by an optional enumeration, including the empty set. -/
theorem short_subsets_le {X : Type u} {κ μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hpow : μ ^ κ ≤ μ) (hX : #X ≤ μ) :
    #{s : Set X // #s ≤ κ} ≤ μ := by
  classical
  let S := {s : Set X // #s ≤ κ}
  let read : Option (κ.ord.ToType → X) → Set X := fun o => o.elim ∅ Set.range
  have exists_code (s : S) : ∃ c, read c = s.val := by
    by_cases hs : Nonempty s.val
    · obtain ⟨e⟩ : Nonempty (s.val ↪ κ.ord.ToType) := s.property.trans_eq (Cardinal.mk_ord_toType κ).symm
      let f (i : κ.ord.ToType) := (Function.invFun e i).val
      refine ⟨some f,Set.ext fun x => ⟨?_,?_⟩⟩
      · rintro ⟨i,rfl⟩
        exact (Function.invFun e i).property
      · intro hx
        refine ⟨e ⟨x,hx⟩,congrArg Subtype.val (Function.leftInverse_invFun e.injective _)⟩
    · exact ⟨none,(Set.not_nonempty_iff_eq_empty.mp (fun h => hs h.to_subtype)).symm⟩
  let code (s : S) := (exists_code s).choose
  have inj : Function.Injective code := fun s t h => Subtype.ext <|
    (exists_code s).choose_spec.symm.trans ((congrArg read h).trans (exists_code t).choose_spec)
  apply (Cardinal.mk_le_of_injective inj).trans
  rw [Cardinal.mk_option,← Cardinal.power_def,Cardinal.mk_ord_toType]
  exact (add_le_add ((Cardinal.power_le_power_right hX).trans hpow) (le_refl 1)).trans_eq (Cardinal.add_one_eq hμ)

end Erdos1172LevyCollapse.Matching
