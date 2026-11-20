/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3IteratedHechlerCentering

@[expose] public section

/-!
# Lifting earlier clique and stationary-future decisions

The projection to the earlier condition has exact lifting: any earlier
strengthening lifts without altering the new stem or its side names.
Consequently earlier persistent stationary possibilities are preserved
and reflected, while earlier clique decisions lift unchanged.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3IteratedHechlerPreservation

open ErdosRadoCHAsym (W2)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3IteratedHechlerOrder

variable {P : Type} [Preorder P]

def liftClique {I V : Type} [LinearOrder I] [LinearOrder V] {G : SimpleGraph V}
    (sys : CliqueDecisions P I V G) : CliqueDecisions (Condition P) I V G where
  decides p i v := sys.decides p.base i v
  dense := by
    intro p i
    obtain ⟨q, hqp, v, hv⟩ := sys.dense p.base i
    exact ⟨liftBase p q, liftBase_le p hqp, v, hv⟩
  persistent hqp hv := sys.persistent (base_le hqp) hv
  unique hv hw := sys.unique hv hw
  ordered hij hv hw := sys.ordered hij hv hw
  adjacent hij hv hw := sys.adjacent hij hv hw

end Erdos1172Part3IteratedHechlerPreservation
