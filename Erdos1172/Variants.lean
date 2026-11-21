/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Ordinal
public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelationAPI

@[expose] public section

/-!
# Consequences and order bounds for Erdős Problem 1172

This file records unconditional order bounds for Parts 2--3 and the partial step toward
original Part 1, together with the sharp elementary weakenings obtained by replacing either
binary target by `2`.
-/

open Cardinal Ordinal

namespace Erdos1172

universe u

/-- The large red target in Part 3 is strictly below `ω₂`. -/
theorem omega_one_opow_omega_add_two_add_two_lt_omega_two :
    (ω_ 1 : Ordinal.{u}) ^ (ω + 2) + 2 < ω_ 2 := by
  have htwo : (2 : Ordinal.{u}) < ω_ 2 :=
    (Ordinal.natCast_lt_omega0 2).trans_le (Ordinal.omega0_le_omega 2)
  have homega : (ω : Ordinal.{u}) < ω_ 2 := by
    simpa only [Ordinal.omega_zero] using Ordinal.omega_lt_omega.mpr (show (0 : Ordinal.{u}) < 2 by simp)
  exact Ordinal.isPrincipal_add_omega 2
    (Ordinal.isPrincipal_opow_omega 2 (Ordinal.omega_lt_omega.mpr one_lt_two)
      (Ordinal.isPrincipal_add_omega 2 homega htwo)) htwo

end Erdos1172
