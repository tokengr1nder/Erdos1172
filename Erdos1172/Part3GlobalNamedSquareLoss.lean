/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedBlockFlattening
public import Erdos1172.Part3NamedCliqueMixing

@[expose] public section

/-!
# Square trace losses on the original decision order

Cone extraction is extended and normalized on the fixed original order.
Its square trace witnesses transfer at the same row and inner indices.
The resulting regular future retains source membership and stationarity.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3GlobalNamedSquareLoss

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3NamedTraceIdeal
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3StationarySquareDecisions (Square)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

theorem row_trace_from_cone (p0 : P) (core : CliqueDecisions (Set.Iic p0) W1 W2 G)
    (global : CliqueDecisions P W1 W2 G)
    (hbelow : ∀ p : Set.Iic p0, ∀ i x, global.decides p.val i x → core.decides p i x)
    (p : Set.Iic p0) (U : RegularName P W2)
    (hsmall : (traceName core).holds p (onCone p0 U)) : (traceName global).holds p.val U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hsmall ⟨q, hqp.trans p.property⟩ hqp
  refine ⟨s.val, hsq, bound, ?_⟩
  intro t hts i hi x hx hUx
  exact hs ⟨t, hts.trans s.property⟩ hts i hi x
    (hbelow ⟨t, hts.trans s.property⟩ i x hx) hUx

end Erdos1172Part3GlobalNamedSquareLoss
