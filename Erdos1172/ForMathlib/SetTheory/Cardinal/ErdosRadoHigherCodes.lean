/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Cardinal.ErdosRadoCodes

@[expose] public section

/-!
# Cardinal bounds for higher binary Erdős--Rado codes

This file bounds the space of all Boolean profiles on proper initial segments
of `ω₂`. Under GCH there are exactly `ℵ₂` such profiles, hence fewer than the
`ℵ₃` possible terminal vertices in the next canonical-branch construction.
-/

open Ordinal Set

namespace Cardinal

/-- Under GCH, Boolean profiles on a proper initial segment of `ω₂` have
cardinality at most `ℵ₂`. -/
theorem GCH.mk_Iio_omega_two_arrow_bool_le (h : GCH)
    (i : (ω_ 2 : Ordinal.{0}).ToType) :
    #(Set.Iio i → Bool) ≤ ℵ_ 2 := by
  rw [mk_arrow]
  simp only [lift_id, mk_fintype, Fintype.card_bool, Nat.cast_ofNat]
  have hi_lt : #(Set.Iio i) < ℵ_ 2 := by
    simpa only [mk_toType, card_omega] using
      (mk_Iio_lt i (by simp only [mk_toType, card_omega, ord_aleph, type_toType]))
  have hi_le : #(Set.Iio i) ≤ ℵ_ 1 := by
    have hsucc : (ℵ_ 2 : Cardinal.{0}) = Order.succ (ℵ_ 1) := by
      rw [Cardinal.succ_aleph]
      norm_num
    rw [hsucc, Order.lt_succ_iff] at hi_lt
    exact hi_lt
  calc
    (2 : Cardinal) ^ #(Set.Iio i) ≤ (2 : Cardinal) ^ ℵ_ 1 :=
      power_le_power_left (by norm_num) hi_le
    _ = ℵ_ 2 := h.two_power_aleph_one

/-- Under GCH, all bounded Boolean profiles on `ω₂` together have
cardinality at most `ℵ₂`. -/
theorem GCH.mk_sigma_Iio_omega_two_bool_le (h : GCH) :
    #(Σ i : (ω_ 2 : Ordinal.{0}).ToType, Set.Iio i → Bool) ≤ ℵ_ 2 := by
  rw [mk_sigma]
  calc
    sum (fun i : (ω_ 2 : Ordinal.{0}).ToType => #(Set.Iio i → Bool)) ≤
        sum (fun _ : (ω_ 2 : Ordinal.{0}).ToType => ℵ_ 2) := by
      apply sum_le_sum
      intro i
      exact h.mk_Iio_omega_two_arrow_bool_le i
    _ = #(ω_ 2 : Ordinal.{0}).ToType * ℵ_ 2 := sum_const' _ _
    _ = ℵ_ 2 := by
      rw [mk_toType, card_omega, aleph_mul_aleph, max_self]

/-- Exact GCH cardinality of the dependent sum of all bounded Boolean
profiles on `ω₂`. -/
theorem GCH.mk_sigma_Iio_omega_two_bool_eq (h : GCH) :
    #(Σ i : (ω_ 2 : Ordinal.{0}).ToType, Set.Iio i → Bool) = ℵ_ 2 := by
  apply le_antisymm h.mk_sigma_Iio_omega_two_bool_le
  have hle : #(ω_ 2 : Ordinal.{0}).ToType ≤
      #(Σ i : (ω_ 2 : Ordinal.{0}).ToType, Set.Iio i → Bool) :=
    mk_le_of_injective (f := fun i => ⟨i, fun _ => false⟩) fun _ _ hij =>
      congrArg Sigma.fst hij
  rwa [mk_toType, card_omega] at hle

/-- The `ω₂` bounded-profile code space is strictly smaller than `ℵ₃`. -/
theorem GCH.mk_sigma_Iio_omega_two_bool_lt_aleph_three (h : GCH) :
    #(Σ i : (ω_ 2 : Ordinal.{0}).ToType, Set.Iio i → Bool) < ℵ_ 3 :=
  h.mk_sigma_Iio_omega_two_bool_le.trans_lt (by norm_num)

/-- Under GCH, no map from `ω₃` into the bounded Boolean profiles on `ω₂`
is injective. -/
theorem GCH.not_injective_omega_three_to_sigma_Iio_omega_two_bool (h : GCH)
    (f : (ω_ 3 : Ordinal.{0}).ToType →
      Σ i : (ω_ 2 : Ordinal.{0}).ToType, Set.Iio i → Bool) :
    ¬Function.Injective f := by
  intro hf
  have hle := mk_le_of_injective hf
  rw [mk_toType, card_omega] at hle
  exact (h.mk_sigma_Iio_omega_two_bool_lt_aleph_three).2 hle

end Cardinal
