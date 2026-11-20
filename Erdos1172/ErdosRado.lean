/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.ErdosRado

@[expose] public section

open Cardinal Ordinal

namespace Erdos1172

/-- The classical Erdős--Rado benchmark immediately below the open relations in
Problem 1172: under GCH, `ω₂ → (ω₁ + 1, ω₁ + 1)²`. -/
theorem erdosRado_binary_instance (hGCH : GCH) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0}) (ω_ 1 + 1) (ω_ 1 + 1) :=
  ErdosRado.ordinalRamsey_omegaTwo_omegaOne_add_one hGCH.toCH

/-- The same CH theorem lifted to the `ω₃` source used in Part 2 of
Problem 1172. -/
theorem erdosRado_omegaThree_instance (hCH : CH) :
    OrdinalRamsey (ω_ 3 : Ordinal.{0}) (ω_ 1 + 1) (ω_ 1 + 1) :=
  (ErdosRado.ordinalRamsey_omegaTwo_omegaOne_add_one hCH).mono_source (by norm_num)

end Erdos1172
