/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Cardinal.GCHConsequences1172

@[expose] public section

/-!
# Cardinal bounds for binary Erdős--Rado codes

This file bounds the space of all Boolean profiles on proper initial segments
of `ω₁`.  Under CH, there are at most `ℵ₁` such profiles in total.
-/

open Ordinal Set

namespace Cardinal

/-- Under CH, the Boolean profiles on any one proper initial segment of `ω₁`
form a set of cardinality at most `ℵ₁`. -/
theorem CH.mk_Iio_omega_one_arrow_bool_le (h : CH)
    (i : (ω_ 1 : Ordinal.{0}).ToType) :
    #(Set.Iio i → Bool) ≤ ℵ_ 1 := by
  rw [mk_arrow]
  simp only [lift_id, mk_fintype, Fintype.card_bool, Nat.cast_ofNat]
  calc
    (2 : Cardinal) ^ #(Set.Iio i) ≤ (2 : Cardinal) ^ ℵ₀ :=
      power_le_power_left (by norm_num) <|
        lt_aleph_one_iff.mp (by simpa using mk_Iio_lt i)
    _ = ℵ_ 1 := CH_iff.mp h

/-- Under CH, the dependent sum of all Boolean profiles on proper initial
segments of `ω₁` has cardinality at most `ℵ₁`. -/
theorem CH.mk_sigma_Iio_omega_one_bool_le (h : CH) :
    #(Σ i : (ω_ 1 : Ordinal.{0}).ToType, Set.Iio i → Bool) ≤ ℵ_ 1 := by
  rw [mk_sigma]
  calc
    sum (fun i : (ω_ 1 : Ordinal.{0}).ToType => #(Set.Iio i → Bool)) ≤
        sum (fun _ : (ω_ 1 : Ordinal.{0}).ToType => ℵ_ 1) := by
      apply sum_le_sum
      intro i
      exact h.mk_Iio_omega_one_arrow_bool_le i
    _ = #(ω_ 1 : Ordinal.{0}).ToType * ℵ_ 1 := sum_const' _ _
    _ = ℵ_ 1 := by
      rw [mk_toType, card_omega, aleph_mul_aleph, max_self]

/-- Exact CH cardinality of the dependent sum of all Boolean profiles on
proper initial segments of `ω₁`. -/
theorem CH.mk_sigma_Iio_omega_one_bool_eq (h : CH) :
    #(Σ i : (ω_ 1 : Ordinal.{0}).ToType, Set.Iio i → Bool) = ℵ_ 1 := by
  apply le_antisymm h.mk_sigma_Iio_omega_one_bool_le
  have hle : #(ω_ 1 : Ordinal.{0}).ToType ≤
      #(Σ i : (ω_ 1 : Ordinal.{0}).ToType, Set.Iio i → Bool) :=
    mk_le_of_injective (f := fun i => ⟨i, fun _ => false⟩) fun _ _ hij =>
      congrArg Sigma.fst hij
  rwa [mk_toType, card_omega] at hle

/-- In the strict form used for the Erdős--Rado signature-space
contradiction, the CH code space has cardinality below `ℵ₂`. -/
theorem CH.mk_sigma_Iio_omega_one_bool_lt_aleph_two (h : CH) :
    #(Σ i : (ω_ 1 : Ordinal.{0}).ToType, Set.Iio i → Bool) < ℵ_ 2 :=
  h.mk_sigma_Iio_omega_one_bool_le.trans_lt (by norm_num)

/-- Under CH, no map from `ω₂` into the space of all initial-segment Boolean
profiles on `ω₁` can be injective. -/
theorem CH.not_injective_omega_two_to_sigma_Iio_omega_one_bool (h : CH)
    (f : (ω_ 2 : Ordinal.{0}).ToType →
      Σ i : (ω_ 1 : Ordinal.{0}).ToType, Set.Iio i → Bool) :
    ¬Function.Injective f := by
  intro hf
  have hle := mk_le_of_injective hf
  rw [mk_toType, card_omega] at hle
  exact (h.mk_sigma_Iio_omega_one_bool_lt_aleph_two).2 hle

/-- GCH specialization of the CH code-space bound. -/
theorem GCH.mk_sigma_Iio_omega_one_bool_le (h : GCH) :
    #(Σ i : (ω_ 1 : Ordinal.{0}).ToType, Set.Iio i → Bool) ≤ ℵ_ 1 :=
  h.toCH.mk_sigma_Iio_omega_one_bool_le

/-- Strict GCH specialization of the CH code-space bound. -/
theorem GCH.mk_sigma_Iio_omega_one_bool_lt_aleph_two (h : GCH) :
    #(Σ i : (ω_ 1 : Ordinal.{0}).ToType, Set.Iio i → Bool) < ℵ_ 2 :=
  h.toCH.mk_sigma_Iio_omega_one_bool_lt_aleph_two

/-- GCH specialization of the non-injectivity form. -/
theorem GCH.not_injective_omega_two_to_sigma_Iio_omega_one_bool (h : GCH)
    (f : (ω_ 2 : Ordinal.{0}).ToType →
      Σ i : (ω_ 1 : Ordinal.{0}).ToType, Set.Iio i → Bool) :
    ¬Function.Injective f :=
  h.toCH.not_injective_omega_two_to_sigma_Iio_omega_one_bool f

end Cardinal
