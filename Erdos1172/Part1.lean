/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.ErdosRadoHigher

@[expose] public section

open Cardinal Ordinal

namespace Erdos1172

/-- Part 1 of Erdős Problem 1172 follows from the stronger symmetric
Erdős--Rado relation `ω₃ → (ω₂ + 1, ω₂ + 1)²` under GCH. -/
theorem part1_of_gch (hGCH : GCH) :
    OrdinalRamsey (ω_ 3 : Ordinal.{0}) (ω_ 2) (ω_ 1 + 2) := by
  apply (ErdosRadoHigher.ordinalRamsey_omegaThree_omegaTwo_add_one hGCH).mono_targets
  · exact le_self_add
  · have hlt : (ω_ 1 : Ordinal.{0}) + 2 < ω_ 2 := by
      apply Ordinal.isPrincipal_add_omega
      · exact Ordinal.omega_lt_omega.mpr one_lt_two
      · exact (Ordinal.natCast_lt_omega0 2).trans_le (Ordinal.omega0_le_omega 2)
    exact hlt.le.trans le_self_add

end Erdos1172
