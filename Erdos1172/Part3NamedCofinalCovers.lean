/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CofinalPowerCovers
public import Erdos1172.Part3NamedFinalTail
public import Erdos1172.Part3NamedLineCover

@[expose] public section

/-!
# Cofinal cover families with an explicit named covering property

The strengthened interface retains all ground cofinal-cover guarantees
and additionally covers an actual, densely enumerated cofinal regular
name on every countably closed condition order. Its covering function is
itself a decision name; no ground dominating function is assumed.

The zero-rank construction is proved here using the canonical line
family and its named lift. No higher-rank induction is postulated.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedCofinalCovers

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FiniteTraceSchemes (Index)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3NamedCofinality (OrderedDecisions CofinalDecisions)
open Erdos1172Part3NamedFinalTail (DenseCoverage)
open Erdos1172Part3SupportedCoverRealization (coverName)
open Erdos1172Part3CofinalPowerCovers (CofinalCovers)

/-- Ground cofinal covers whose same family also covers actual regular
names with ordered, cofinal, dense exact enumerations. -/
structure NamedCofinalCovers (n : ℕ) (V : Type)
    [LinearOrder V] [WellFoundedLT V] extends CofinalCovers n V where
  named_covers : ∀ (P : Type) [Preorder P] (hclosed : CountablyClosed P)
    (U : RegularName P V) (E : FunctionDecisions P (Index n) V),
    OrderedDecisions E → CofinalDecisions E → DenseCoverage E U →
    (∀ p j x, E.decides p j x → U.holds p x) →
      ∃ F : FunctionDecisions P W1 W1,
        ∀ p x, U.holds p x → (coverName F family).holds p x

end Erdos1172Part3NamedCofinalCovers
