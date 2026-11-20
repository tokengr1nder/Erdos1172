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

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

/-- At rank zero, the canonical line cover already has the required
named lifting property. Its exact cover type is omegaOne. -/
theorem exists_namedCofinalCovers_zero (hV : #V ≤ ℵ_ 1)
    (hseed : ∃ A : Set V, IsCofinal A ∧ typeLT A = ω_ 1) :
    Nonempty (NamedCofinalCovers 0 V) := by
  obtain ⟨A, hA, htype⟩ := hseed
  obtain ⟨data⟩ := Erdos1172Part3CofinalLineCover.exists_lineCoverData hV A hA htype
  refine ⟨{
    family := data.cover
    mono := data.cover_mono
    supported := Erdos1172Part3CofinalCoverSupport.line_supported data
    cofinal := data.cover_cofinal
    orderType := ?_
    covers := ?_
    named_covers := ?_ }⟩
  · intro f
    simpa only [Nat.zero_add, Nat.cast_one, Ordinal.opow_one] using data.cover_type f
  · intro B hB hBtype
    apply data.covers B hB
    simpa only [Nat.zero_add, Nat.cast_one, Ordinal.opow_one] using hBtype
  · intro P instP hclosed U E hordered hcofinal hcoverage _hmem
    exact Erdos1172Part3NamedLineCover.exists_named_line_cover data U E hclosed
      (fun p j k x y hjk hx hy => hordered hjk hx hy) hcoverage hcofinal

end Erdos1172Part3NamedCofinalCovers
