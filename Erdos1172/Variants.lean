/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Statement
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelationAPI

@[expose] public section

/-!
# Consequences and reductions for Erdős Problem 1172

This file records unconditional order bounds, logical reductions between Parts 1--3,
and the sharp elementary weakenings obtained by replacing either target by `2`.
-/

open Cardinal Ordinal

namespace Erdos1172

universe u

private theorem two_lt_three : (2 : Ordinal.{u}) < 3 :=
  Nat.cast_lt.mpr (by decide)

/-- The blue target in Part 1 is strictly below `ω₂`. -/
theorem omega_one_add_two_lt_omega_two : (ω_ 1 : Ordinal.{u}) + 2 < ω_ 2 := by
  apply Ordinal.isPrincipal_add_omega
  · exact Ordinal.omega_lt_omega.mpr one_lt_two
  · exact (Ordinal.natCast_lt_omega0 2).trans_le (Ordinal.omega0_le_omega 2)

/-- The red target in Part 2 is strictly below its source `ω₃`. -/
theorem omega_two_add_omega_one_lt_omega_three :
    (ω_ 2 : Ordinal.{u}) + ω_ 1 < ω_ 3 := by
  apply Ordinal.isPrincipal_add_omega
  · exact Ordinal.omega_lt_omega.mpr two_lt_three
  · exact Ordinal.omega_lt_omega.mpr (one_lt_two.trans two_lt_three)

/-- The blue target in Part 2 is strictly below its source `ω₃`. -/
theorem omega_two_add_omega_lt_omega_three :
    (ω_ 2 : Ordinal.{u}) + ω < ω_ 3 := by
  apply Ordinal.isPrincipal_add_omega
  · exact Ordinal.omega_lt_omega.mpr two_lt_three
  · exact (Ordinal.omega0_le_omega 2).trans_lt
      (Ordinal.omega_lt_omega.mpr two_lt_three)

/-- The large red target in Part 3 is strictly below `ω₂`. -/
theorem omega_one_opow_omega_add_two_add_two_lt_omega_two :
    (ω_ 1 : Ordinal.{u}) ^ (ω + 2) + 2 < ω_ 2 := by
  have htwo : (2 : Ordinal.{u}) < ω_ 2 :=
    (Ordinal.natCast_lt_omega0 2).trans_le (Ordinal.omega0_le_omega 2)
  have homega : (ω : Ordinal.{u}) < ω_ 2 := by
    simpa only [Ordinal.omega_zero] using
      (Ordinal.omega_lt_omega.mpr
        (show (0 : Ordinal.{u}) < 2 by simp))
  have hexponent : (ω : Ordinal.{u}) + 2 < ω_ 2 :=
    Ordinal.isPrincipal_add_omega 2 homega htwo
  have hpower : (ω_ 1 : Ordinal.{u}) ^ (ω + 2) < ω_ 2 :=
    Ordinal.isPrincipal_opow_omega 2
      (Ordinal.omega_lt_omega.mpr one_lt_two) hexponent
  exact Ordinal.isPrincipal_add_omega 2 hpower htwo

/-- Part 2 implies Part 1, without using GCH. -/
theorem part2_implies_part1
    (h : Part2.{u}) : Part1.{u} :=
  h.mono_targets le_self_add
    (omega_one_add_two_lt_omega_two.le.trans le_self_add)

/-- Adding Part 1 to Part 2 does not strengthen the assertion. -/
theorem part2_iff_part1_and_part2 :
    Part2.{u} ↔ Part1.{u} ∧ Part2.{u} := by
  constructor
  · intro h
    exact ⟨part2_implies_part1 h, h⟩
  · exact And.right

/-- The conjunction of Parts 1--3 is equivalent to the conjunction of Parts 2--3. -/
theorem parts123_iff_parts23 :
    (Part1.{u} ∧ Part2.{u} ∧ Part3.{u}) ↔ (Part2.{u} ∧ Part3.{u}) := by
  constructor
  · rintro ⟨_, h2, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    exact ⟨part2_implies_part1 h2, h2, h3⟩

/-- Part 1 with its red target weakened to `2`; this is unconditional. -/
theorem part1_red_two :
    OrdinalRamsey (ω_ 3 : Ordinal.{u}) 2 (ω_ 1 + 2) :=
  OrdinalRamsey.two_left
    (omega_one_add_two_lt_omega_two.le.trans
      (Ordinal.omega_lt_omega.mpr two_lt_three).le)

/-- Part 1 with its blue target weakened to `2`; this is unconditional. -/
theorem part1_blue_two :
    OrdinalRamsey (ω_ 3 : Ordinal.{u}) (ω_ 2) 2 :=
  OrdinalRamsey.two_right (Ordinal.omega_lt_omega.mpr two_lt_three).le

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
