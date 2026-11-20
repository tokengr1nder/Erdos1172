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

/-- Under GCH, `ℵ₃` is closed under `ℵ₁`-powers. -/
theorem GCH.aleph_three_power_aleph_one (h : GCH) :
    (ℵ_ 3 : Cardinal.{0}) ^ ℵ_ 1 = ℵ_ 3 := by
  rw [← h.two_power_aleph_two, ← power_mul, aleph_mul_aleph,
    max_eq_left (by norm_num : (1 : Ordinal) ≤ 2)]

end Cardinal
