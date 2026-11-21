/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CoreObjectCode
public import Erdos1172.Part3TwoSuccessorBootstrap

@[expose] public section

/-!
# Stationary reflection of positive red predecessors

The absence of a source-sized blue clique makes the red predecessors of
every fixed stationary source positive on a club. This applies to the
enlarged algebra naming whole blocks. No large red core is assumed.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RedPredecessorReflection

open Erdos1172Part3CoreObjectCode
open Erdos1172Part3NeighborhoodCode (W2 cof_W2 alephZero_lt_cof_W2)
open Erdos1172Part3RedCoreIdeal (mk_eq_alephTwo_of_isCofinal)
open OrdinalRamsey (HasCliqueOfType)
open Erdos1172Part3TwoSuccessorBootstrap (isCofinal_of_stationary)

theorem stationaryPressingDown : Set.StationaryPressingDown W2 := by
  have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
    convert Cardinal.isRegular_aleph_add_one 1 using 1
    norm_num
  change Set.StationaryPressingDown ((ω_ 2 : Ordinal.{0}).ToType)
  rw [← Cardinal.ord_aleph]
  exact Set.stationaryPressingDown_ord (ℵ_ 2) hreg (Cardinal.aleph0_lt_aleph.mpr (by norm_num))

end Erdos1172Part3RedPredecessorReflection
