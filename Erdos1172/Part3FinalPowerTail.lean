/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Tactic.NormNum.Ordinal

@[expose] public section

/-!
# A final finite-power tail below omegaOne^(omega+1)

An ordinal below omegaOne^(omega+1) with cofinality alephOne has a final
tail of exact type omegaOne^(n+1), for some finite n. Division first
removes its omegaOne^omega multiple. The remainder is nonzero because
every countable multiple of omegaOne^omega has countable cofinality.
Finite induction on the remainder then exposes its last pure-power tail.

No continuum hypothesis, covering premise, or infinitary closure
principle is used. In particular no countable union of independently
bounded covering families is asserted to remain bounded.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FinalPowerTail

noncomputable abbrev kappa : Ordinal.{0} := ω_ 1
noncomputable abbrev omegaPower : Ordinal.{0} := kappa ^ ω

theorem kappa_pos : 0 < kappa := Ordinal.omega_pos 1

theorem alephZero_lt_alephOne : (ℵ₀ : Cardinal.{0}) < ℵ_ 1 :=
  Cardinal.aleph0_lt_aleph.mpr (by norm_num)

theorem cof_le_alephZero_of_lt_kappa {a : Ordinal.{0}} (ha : a < kappa) : a.cof ≤ ℵ₀ := by
  have hcard : a.card < ℵ_ 1 := Cardinal.lt_omega_iff_card_lt.mp ha
  exact (Ordinal.cof_le_card a).trans (Cardinal.lt_aleph_one_iff.mp hcard)

theorem cof_omegaPower : omegaPower.cof = ℵ₀ := by
  have hk : (1 : Ordinal.{0}) < kappa := Ordinal.one_lt_omega0.trans_le (Ordinal.omega0_le_omega 1)
  exact (Ordinal.cof_map_of_isNormal (Ordinal.isNormal_opow hk)
    Ordinal.isSuccLimit_omega0).trans Ordinal.cof_omega0

theorem cof_omegaSuccessor : (kappa ^ (ω + 1)).cof = ℵ_ 1 := by
  rw [Ordinal.opow_add_one, Ordinal.cof_mul
    (Ordinal.opow_pos _ kappa_pos).ne' (Cardinal.isSuccLimit_omega 1).isSuccPrelimit]
  exact Cardinal.cof_omega_one

/-- A nonzero ordinal of countable cofinality still has countable
cofinality after multiplication by any countable ordinal. -/
theorem cof_mul_le_alephZero {a q : Ordinal.{0}} (ha : a ≠ 0)
    (hcof : a.cof ≤ ℵ₀) (hq : q < kappa) : (a * q).cof ≤ ℵ₀ := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit q with hqzero | ⟨r, hqr⟩ | hqlimit
  · simp only [hqzero, mul_zero, Ordinal.cof_zero, zero_le]
  · rw [← hqr, Ordinal.mul_succ, Ordinal.cof_add _ ha]
    exact hcof
  · rw [Ordinal.cof_mul ha hqlimit.isSuccPrelimit]
    exact cof_le_alephZero_of_lt_kappa hq

theorem cof_omegaPower_mul_le_alephZero {q : Ordinal.{0}} (hq : q < kappa) :
    (omegaPower * q).cof ≤ ℵ₀ :=
  cof_mul_le_alephZero (Ordinal.opow_pos _ kappa_pos).ne' cof_omegaPower.le hq

/-- Finite induction reveals a final pure-power tail. The rank is
strictly below the exponent of the original finite bound. -/
theorem exists_final_power_of_lt_finite_power (N : ℕ) {a : Ordinal.{0}}
    (ha : a < kappa ^ ((N + 1 : ℕ) : Ordinal)) (hcof : a.cof = ℵ_ 1) :
    ∃ cut : Ordinal.{0}, ∃ n : ℕ, n < N ∧ a = cut + kappa ^ ((n + 1 : ℕ) : Ordinal) := by
  induction N generalizing a with
  | zero =>
      have hak : a < kappa := by
        simpa only [Nat.zero_add, Nat.cast_one, Ordinal.opow_one] using ha
      have hsmall := cof_le_alephZero_of_lt_kappa hak
      rw [hcof] at hsmall
      exact (alephZero_lt_alephOne.not_ge hsmall).elim
  | succ N ih =>
      let power : Ordinal.{0} := kappa ^ ((N + 1 : ℕ) : Ordinal)
      have hpower : power ≠ 0 := (Ordinal.opow_pos _ kappa_pos).ne'
      have hbound : a < power * kappa := by
        simpa only [power, Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one] using ha
      let q : Ordinal.{0} := a / power
      let remainder : Ordinal.{0} := a % power
      have hq : q < kappa := (Ordinal.lt_mul_iff_div_lt hpower).mp hbound
      have hrem : remainder < power := Ordinal.mod_lt a hpower
      have hsplit : power * q + remainder = a := Ordinal.div_add_mod a power
      by_cases hzero : remainder = 0
      · have heq : a = power * q := by simpa only [hzero, add_zero] using hsplit.symm
        rcases Ordinal.zero_or_succ_or_isSuccLimit q with hqzero | ⟨r, hqr⟩ | hqlimit
        · have hsmall : a.cof ≤ ℵ₀ := by simp only [heq, hqzero, mul_zero, Ordinal.cof_zero, zero_le]
          rw [hcof] at hsmall
          exact (alephZero_lt_alephOne.not_ge hsmall).elim
        · refine ⟨power * r, N, Nat.lt_succ_self N, ?_⟩
          rw [heq, ← hqr, Ordinal.mul_succ]
        · have hsmall : a.cof ≤ ℵ₀ := by
            rw [heq, Ordinal.cof_mul hpower hqlimit.isSuccPrelimit]
            exact cof_le_alephZero_of_lt_kappa hq
          rw [hcof] at hsmall
          exact (alephZero_lt_alephOne.not_ge hsmall).elim
      · have hremCof : remainder.cof = ℵ_ 1 := by
          rw [← Ordinal.cof_add (power * q) hzero, hsplit]
          exact hcof
        obtain ⟨cut, n, hn, htail⟩ := ih hrem hremCof
        refine ⟨power * q + cut, n, hn.trans (Nat.lt_succ_self N), ?_⟩
        rw [← hsplit, htail, add_assoc]

/-- The omega-power remainder cannot vanish at cofinality alephOne. -/
theorem omegaPower_remainder_ne_zero {a : Ordinal.{0}}
    (ha : a < kappa ^ (ω + 1)) (hcof : a.cof = ℵ_ 1) :
    a % omegaPower ≠ 0 := by
  have hpower : omegaPower ≠ 0 := (Ordinal.opow_pos _ kappa_pos).ne'
  have hbound : a < omegaPower * kappa := by
    simpa only [omegaPower, Ordinal.opow_add_one] using ha
  have hq : a / omegaPower < kappa := (Ordinal.lt_mul_iff_div_lt hpower).mp hbound
  intro hzero
  have heq : a = omegaPower * (a / omegaPower) := by
    simpa only [hzero, add_zero] using (Ordinal.div_add_mod a omegaPower).symm
  have hsmall := cof_omegaPower_mul_le_alephZero hq
  rw [← heq, hcof] at hsmall
  exact alephZero_lt_alephOne.not_ge hsmall

/-- An ordinal of cofinality alephOne below omegaOne^(omega+1)
is a bounded initial part followed by one finite pure-power tail. -/
theorem exists_final_power_tail {a : Ordinal.{0}}
    (ha : a < kappa ^ (ω + 1)) (hcof : a.cof = ℵ_ 1) :
    ∃ cut : Ordinal.{0}, ∃ n : ℕ, a = cut + kappa ^ ((n + 1 : ℕ) : Ordinal) := by
  let q : Ordinal.{0} := a / omegaPower
  let remainder : Ordinal.{0} := a % omegaPower
  have hpower : omegaPower ≠ 0 := (Ordinal.opow_pos _ kappa_pos).ne'
  have hrem : remainder < omegaPower := Ordinal.mod_lt a hpower
  have hremNe : remainder ≠ 0 := omegaPower_remainder_ne_zero ha hcof
  have hsplit : omegaPower * q + remainder = a := Ordinal.div_add_mod a omegaPower
  have hremCof : remainder.cof = ℵ_ 1 := by
    rw [← Ordinal.cof_add (omegaPower * q) hremNe, hsplit]
    exact hcof
  obtain ⟨exponent, hexponent, hfinite⟩ :=
    (Ordinal.lt_opow_of_isSuccLimit kappa_pos.ne' Ordinal.isSuccLimit_omega0).mp hrem
  obtain ⟨N, rfl⟩ := Ordinal.lt_omega0.mp hexponent
  have hfinite' : remainder < kappa ^ ((N + 1 : ℕ) : Ordinal) :=
    hfinite.trans_le (Ordinal.opow_le_opow_right kappa_pos (by exact_mod_cast Nat.le_succ N))
  obtain ⟨cut, n, -, htail⟩ := exists_final_power_of_lt_finite_power N hfinite' hremCof
  refine ⟨omegaPower * q + cut, n, ?_⟩
  rw [← hsplit, htail, add_assoc]

end Erdos1172Part3FinalPowerTail
