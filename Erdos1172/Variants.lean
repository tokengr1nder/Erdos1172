/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Ordinal
public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelationAPI

@[expose] public section

/-!
# Order bound for the Part (iii) target in Erdős Problem 1172

This file records the unconditional strict upper bound `(ω_ 1) ^ (ω + 2) + 2 < ω_ 2` for the
large red target in Part (iii).
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
