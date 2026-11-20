/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.ErdosRadoCHAsymmetric
public import Erdos1172.Part3FailureFiber
public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueBlockExtension
public import Mathlib.Order.WellQuasiOrder

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OneSuccessorBarrier

/-- The limit part of the red target in Part 3. -/
noncomputable abbrev RedCoreTarget : Ordinal :=
  (ω_ 1 : Ordinal.{0}) ^ (ω + 2)

end Erdos1172Part3OneSuccessorBarrier
