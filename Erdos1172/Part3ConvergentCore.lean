/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CoreObjectCode
public import Erdos1172.Part3FiniteIdealEndpoint
public import Mathlib.Order.Zorn
public import Erdos1172.ForMathlib.Combinatorics.SimpleGraph.CliqueFamilyUnion

@[expose] public section

/-!
# Cores converging to every locally named neighborhood

Countable extension constructs a homogeneous omegaOne sequence. Its tail
lies in every local named set containing the cut, so its trace upgrades
the coded ideal to the ordinary countable-set ideal on this core.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3ConvergentCore

open Erdos1172Part3CoreObjectCode
open Erdos1172Part3NeighborhoodCode (W2)
open ErdosRadoCHAsym (W1)
open Erdos1172Part3CountableRankClosure (Local mk_local_le)

variable {r : Code ↪ W2} {σ : Obj ↪ W2} {G H : SimpleGraph W2} {a : W2}

theorem mk_Iio_W1_lt (i : W1) : #(Set.Iio i) < ℵ_ 1 := by
  simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using Cardinal.mk_Iio_lt i (by simp [W1])

theorem mk_Iic_W1_lt (i : W1) : #(Set.Iic i) < ℵ_ 1 := by
  simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
    Cardinal.mk_Iic_lt i (by simp [W1]) (by simp [W1])

end Erdos1172Part3ConvergentCore
