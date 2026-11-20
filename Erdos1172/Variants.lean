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

private theorem two_lt_three : (2 : Ordinal.{u}) < 3 :=
  Nat.cast_lt.mpr (by decide)

/-- The countable-color partial-step target `ω₂ + 1` is strictly below `ω₃`. -/
theorem omega_two_add_one_lt_omega_three : (ω_ 2 : Ordinal.{u}) + 1 < ω_ 3 :=
  Ordinal.isPrincipal_add_omega 3 (Ordinal.omega_lt_omega.mpr two_lt_three)
    (Ordinal.one_lt_omega0.trans_le (Ordinal.omega0_le_omega 3))

/-- The blue target in Part 3 is strictly below `ω₂`. -/
theorem omega_one_add_two_lt_omega_two : (ω_ 1 : Ordinal.{u}) + 2 < ω_ 2 :=
  Ordinal.isPrincipal_add_omega 2 (Ordinal.omega_lt_omega.mpr one_lt_two)
    ((Ordinal.natCast_lt_omega0 2).trans_le (Ordinal.omega0_le_omega 2))

/-- The red target in Part 2 is strictly below its source `ω₃`. -/
theorem omega_two_add_omega_one_lt_omega_three :
    (ω_ 2 : Ordinal.{u}) + ω_ 1 < ω_ 3 :=
  Ordinal.isPrincipal_add_omega 3 (Ordinal.omega_lt_omega.mpr two_lt_three)
    (Ordinal.omega_lt_omega.mpr (one_lt_two.trans two_lt_three))

/-- The blue target in Part 2 is strictly below its source `ω₃`. -/
theorem omega_two_add_omega_lt_omega_three :
    (ω_ 2 : Ordinal.{u}) + ω < ω_ 3 :=
  Ordinal.isPrincipal_add_omega 3 (Ordinal.omega_lt_omega.mpr two_lt_three)
    ((Ordinal.omega0_le_omega 2).trans_lt (Ordinal.omega_lt_omega.mpr two_lt_three))

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

/-- Part 2 with its red target weakened to `2`; this is unconditional. -/
theorem part2_red_two :
    OrdinalRamsey (ω_ 3 : Ordinal.{u}) 2 (ω_ 2 + ω) :=
  OrdinalRamsey.two_left omega_two_add_omega_lt_omega_three.le

/-- Part 2 with its blue target weakened to `2`; this is unconditional. -/
theorem part2_blue_two :
    OrdinalRamsey (ω_ 3 : Ordinal.{u}) (ω_ 2 + ω_ 1) 2 :=
  OrdinalRamsey.two_right omega_two_add_omega_one_lt_omega_three.le

/-- Part 3 with its red target weakened to `2`; this is unconditional. -/
theorem part3_red_two :
    OrdinalRamsey (ω_ 2 : Ordinal.{u}) 2 (ω_ 1 + 2) :=
  OrdinalRamsey.two_left omega_one_add_two_lt_omega_two.le

/-- Part 3 with its blue target weakened to `2`; this is unconditional. -/
theorem part3_blue_two :
    OrdinalRamsey (ω_ 2 : Ordinal.{u}) (ω_ 1 ^ (ω + 2) + 2) 2 :=
  OrdinalRamsey.two_right omega_one_opow_omega_add_two_add_two_lt_omega_two.le

end Erdos1172
