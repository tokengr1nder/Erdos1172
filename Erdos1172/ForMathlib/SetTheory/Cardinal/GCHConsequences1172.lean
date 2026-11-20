/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Cardinal.ContinuumHypothesis
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.Tactic.NormNum.Ordinal

@[expose] public section

/-!
# Cardinal-arithmetic consequences of GCH used by Erdős Problem 1172

This file isolates the routine cardinal calculations from the genuinely
combinatorial content of Problem 1172.  In particular, it verifies the source
cardinal in the binary Erdős--Rado instance and records the finite-aleph power
identities that occur in the standard reductions.
-/

open Ordinal

namespace Cardinal

/-- GCH at `ℵ₀`, in the notation used by Problem 1172. -/
theorem GCH.two_power_aleph_zero (h : GCH) :
    (2 : Cardinal.{0}) ^ ℵ₀ = ℵ_ 1 := by
  exact h.toCH |> CH_iff.mp

/-- GCH at `ℵ₁`. -/
theorem GCH.two_power_aleph_one (h : GCH) :
    (2 : Cardinal.{0}) ^ ℵ_ 1 = ℵ_ 2 := by
  have h1 := h (1 : Ordinal)
  norm_num at h1
  exact h1

/-- GCH at `ℵ₂`. -/
theorem GCH.two_power_aleph_two (h : GCH) :
    (2 : Cardinal.{0}) ^ ℵ_ 2 = ℵ_ 3 := by
  have h2 := h (2 : Ordinal)
  norm_num at h2
  exact h2

/-- Under CH (and hence under GCH), the successor of the continuum is `ℵ₂`. -/
theorem CH.succ_continuum (h : CH) : Order.succ (𝔠 : Cardinal.{0}) = ℵ_ 2 := by
  rw [h, Cardinal.succ_aleph]
  norm_num

/-- The exact source-cardinal calculation in the binary Erdős--Rado theorem:
`(2 ^ ℵ₀)⁺ = ℵ₂`. -/
theorem GCH.erdosRado_binary_source (h : GCH) :
    Order.succ ((2 : Cardinal.{0}) ^ ℵ₀) = ℵ_ 2 := by
  rw [h.two_power_aleph_zero, Cardinal.succ_aleph]
  norm_num

/-- The next Erdős--Rado source calculation, `(2 ^ ℵ₁)⁺ = ℵ₃`. -/
theorem GCH.erdosRado_alephOne_source (h : GCH) :
    Order.succ ((2 : Cardinal.{0}) ^ ℵ_ 1) = ℵ_ 3 := by
  rw [h.two_power_aleph_one, Cardinal.succ_aleph]
  norm_num

/-- Under CH, the initial ordinal of the continuum is `ω₁`. -/
theorem CH.ord_continuum (h : CH) : (𝔠 : Cardinal.{0}).ord = ω_ 1 := by
  rw [h, Cardinal.ord_aleph]

/-- Ordinal form of the exact binary Erdős--Rado source calculation. -/
theorem GCH.erdosRado_binary_source_ord (h : GCH) :
    (Order.succ ((2 : Cardinal.{0}) ^ ℵ₀)).ord = ω_ 2 := by
  rw [h.erdosRado_binary_source, Cardinal.ord_aleph]

/-- Ordinal form of the next Erdős--Rado source calculation. -/
theorem GCH.erdosRado_alephOne_source_ord (h : GCH) :
    (Order.succ ((2 : Cardinal.{0}) ^ ℵ_ 1)).ord = ω_ 3 := by
  rw [h.erdosRado_alephOne_source, Cardinal.ord_aleph]

/-- Under CH, `ℵ₁` is closed under countable cardinal powers. -/
theorem CH.aleph_one_power_aleph_zero (h : CH) :
    (ℵ_ 1 : Cardinal.{0}) ^ ℵ₀ = ℵ_ 1 := by
  rw [← h]
  exact continuum_power_aleph0

/-- Under GCH, `ℵ₂` is closed under `ℵ₀`-powers. -/
theorem GCH.aleph_two_power_aleph_zero (h : GCH) :
    (ℵ_ 2 : Cardinal.{0}) ^ ℵ₀ = ℵ_ 2 := by
  rw [← h.two_power_aleph_one, ← power_mul, aleph_mul_aleph0]

/-- Under GCH, `ℵ₂` is closed under `ℵ₁`-powers. -/
theorem GCH.aleph_two_power_aleph_one (h : GCH) :
    (ℵ_ 2 : Cardinal.{0}) ^ ℵ_ 1 = ℵ_ 2 := by
  rw [← h.two_power_aleph_one, ← power_mul, aleph_mul_aleph, max_self]

/-- Under GCH, `ℵ₃` is closed under `ℵ₀`-powers. -/
theorem GCH.aleph_three_power_aleph_zero (h : GCH) :
    (ℵ_ 3 : Cardinal.{0}) ^ ℵ₀ = ℵ_ 3 := by
  rw [← h.two_power_aleph_two, ← power_mul, aleph_mul_aleph0]

/-- Under GCH, `ℵ₃` is closed under `ℵ₁`-powers. -/
theorem GCH.aleph_three_power_aleph_one (h : GCH) :
    (ℵ_ 3 : Cardinal.{0}) ^ ℵ_ 1 = ℵ_ 3 := by
  rw [← h.two_power_aleph_two, ← power_mul, aleph_mul_aleph,
    max_eq_left (by norm_num : (1 : Ordinal) ≤ 2)]

/-- Under GCH, `ℵ₃` is closed under `ℵ₂`-powers. -/
theorem GCH.aleph_three_power_aleph_two (h : GCH) :
    (ℵ_ 3 : Cardinal.{0}) ^ ℵ_ 2 = ℵ_ 3 := by
  rw [← h.two_power_aleph_two, ← power_mul, aleph_mul_aleph, max_self]

/-- The target order type `ω₁ + 1` in the binary Erdős--Rado instance has
cardinality `ℵ₁`. -/
theorem card_omega_one_add_one : (ω_ 1 + 1).card = ℵ_ 1 := by
  rw [card_add, card_omega, card_one, Cardinal.add_eq_left]
  · exact Cardinal.aleph0_le_aleph 1
  · exact one_le_aleph0.trans (Cardinal.aleph0_le_aleph 1)

/-- The blue target in Part 3 (`ω₁ + 2`) has cardinality `ℵ₁`. -/
theorem card_omega_one_add_two : (ω_ 1 + 2).card = ℵ_ 1 := by
  rw [card_add, card_omega, card_ofNat, Cardinal.add_eq_left]
  · exact Cardinal.aleph0_le_aleph 1
  · exact (natCast_le_aleph0 : (2 : Cardinal) ≤ ℵ₀).trans
      (Cardinal.aleph0_le_aleph 1)

/-- The red target in Part 2 has cardinality `ℵ₂`. -/
theorem card_omega_two_add_omega_one : (ω_ 2 + ω_ 1).card = ℵ_ 2 := by
  rw [card_add, card_omega, card_omega, Cardinal.aleph_add_aleph,
    max_eq_left (by norm_num : (1 : Ordinal) ≤ 2)]

/-- The blue target in Part 2 has cardinality `ℵ₂`. -/
theorem card_omega_two_add_omega : (ω_ 2 + ω).card = ℵ_ 2 := by
  rw [card_add, card_omega, card_omega0, Cardinal.add_eq_left]
  · exact Cardinal.aleph0_le_aleph 2
  · exact Cardinal.aleph0_le_aleph 2

/-- The large red target in Part 3 still has cardinality `ℵ₁`. -/
theorem card_part3_red_target :
    (ω_ 1 ^ (ω + 2) + 2).card = ℵ_ 1 := by
  have hExp : (ω + 2).card = ℵ₀ := by
    rw [card_add, card_omega0, card_ofNat, Cardinal.add_eq_left]
    · exact le_rfl
    · exact natCast_le_aleph0
  have hPow : (ω_ 1 ^ (ω + 2)).card = ℵ_ 1 := by
    rw [card_opow_eq_of_omega0_le_left, card_omega, hExp,
      max_eq_left (Cardinal.aleph0_le_aleph 1)]
    · exact omega0_le_omega 1
    · exact omega0_pos.trans_le (by simp)
  rw [card_add, hPow, card_ofNat, Cardinal.add_eq_left]
  · exact Cardinal.aleph0_le_aleph 1
  · exact (natCast_le_aleph0 : (2 : Cardinal) ≤ ℵ₀).trans
      (Cardinal.aleph0_le_aleph 1)

end Cardinal
