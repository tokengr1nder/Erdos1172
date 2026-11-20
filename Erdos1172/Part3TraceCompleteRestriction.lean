/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ProductStationaryTraceLoss
public import Erdos1172.Part3CubeTraceSubsequence

@[expose] public section

/-!
# Exact restriction of iterated regular trace ideals

Exact lifting transfers dense witnesses and universal tail avoidance.
Consequently trace restriction commutes with the whole-row product
operation. The line, square, and cube traces all restrict exactly when
their clique decisions do; their trace-loss futures then factor through
the same earlier order as the source and clique.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3TraceCompleteRestriction

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3CompleteRestriction (CompleteRestriction)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3NamedTraceIdeal (TailAvoid)
open Erdos1172Part3ProductTraceIdeal
open Erdos1172Part3FullSourceCubes (Cube)
open Erdos1172Part3StationarySquareDecisions (Square)

variable {P Q I X : Type} [Preorder P] [Preorder Q] [LinearOrder I] {G : SimpleGraph W2}

theorem regularize_restrict_iff (r : CompleteRestriction P Q) (A : P → X → Prop) (B : Q → X → Prop)
    (hAB : ∀ p x, A p x ↔ B (r.restrict p) x) (p : P) (x : X) :
    (regularize A).holds p x ↔ (regularize B).holds (r.restrict p) x := by
  constructor
  · intro h q hqp
    obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
    obtain ⟨t, hts, ht⟩ := h s hsp
    refine ⟨r.restrict t, ?_, (hAB t x).mp ht⟩
    have hle := r.restrict.monotone hts
    rwa [hs] at hle
  · intro h q hqp
    obtain ⟨s, hsq, hs⟩ := h (r.restrict q) (r.restrict.monotone hqp)
    obtain ⟨t, htq, ht⟩ := r.lift q s hsq
    refine ⟨t, htq, (hAB t x).mpr ?_⟩
    rwa [ht]

def SameDecisions (r : CompleteRestriction P Q) (full : CliqueDecisions P I W2 G)
    (earlier : CliqueDecisions Q I W2 G) : Prop :=
  ∀ p i x, full.decides p i x ↔ earlier.decides (r.restrict p) i x

def TracesCommute (r : CompleteRestriction P Q) (TP : CoreTrace P I G) (TQ : CoreTrace Q I G) : Prop :=
  ∀ full earlier, SameDecisions r full earlier → ∀ p : P, ∀ U : RegularName Q W2,
    (TP.trace full).holds p (r.liftRegular U) ↔ (TQ.trace earlier).holds (r.restrict p) U

theorem tailAvoid_restrict_iff (r : CompleteRestriction P Q)
    (full : CliqueDecisions P W1 W2 G) (earlier : CliqueDecisions Q W1 W2 G)
    (hdec : SameDecisions r full earlier) (p : P) (U : RegularName Q W2) (bound : W1) :
    TailAvoid full p (r.liftRegular U) bound ↔ TailAvoid earlier (r.restrict p) U bound := by
  constructor
  · intro h q hqp i hi x hx hUx
    obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
    apply h s hsp i hi x ((hdec s i x).mpr (by rwa [hs]))
    change U.holds (r.restrict s) x
    rwa [hs]
  · intro h q hqp i hi x hx hUx
    exact h (r.restrict q) (r.restrict.monotone hqp) i hi x ((hdec q i x).mp hx) hUx

theorem line_tracesCommute (r : CompleteRestriction P Q) :
    TracesCommute r (lineTrace (P := P) (G := G)) (lineTrace (P := Q) (G := G)) := by
  intro full earlier hdec p U
  exact regularize_restrict_iff r
    (fun p U => ∃ bound, TailAvoid full p (r.liftRegular U) bound)
    (fun q U => ∃ bound, TailAvoid earlier q U bound)
    (fun p U => exists_congr (fun bound => tailAvoid_restrict_iff r full earlier hdec p U bound)) p U

theorem product_tracesCommute (r : CompleteRestriction P Q) {TP : CoreTrace P I G}
    {TQ : CoreTrace Q I G} (h : TracesCommute r TP TQ) :
    TracesCommute r TP.product TQ.product := by
  intro full earlier hdec p U
  apply regularize_restrict_iff r
    (fun p U => WitnessProductSmall TP full p (r.liftRegular U))
    (fun q U => WitnessProductSmall TQ earlier q U)
  intro p U
  apply exists_congr
  intro bound
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact h (rowCore full i) (rowCore earlier i) (fun p j x => hdec p (toLex (i, j)) x) p U

end Erdos1172Part3TraceCompleteRestriction
