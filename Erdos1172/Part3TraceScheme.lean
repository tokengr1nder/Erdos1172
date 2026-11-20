/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TraceCompleteRestriction

@[expose] public section

/-!
# Trace schemes natural in the decision order

The cone transfer laws and exact complete-restriction law are retained
alongside each trace ideal. Whole-row products preserve this structure.
The extraction predicate records actual membership and transfer of every
small trace, not merely existence of a clique in the positive source.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3TraceScheme

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3ProductTraceIdeal (CoreTrace rowCore lineTrace)
open Erdos1172Part3CompleteRestriction (CompleteRestriction)
open Erdos1172Part3TraceCompleteRestriction (TracesCommute)

structure TraceScheme (I : Type) [LinearOrder I] (G : SimpleGraph W2) where
  forOrder : (P : Type) → [Preorder P] → CoreTrace P I G
  toCone : ∀ {P : Type} [Preorder P] (p0 : P) (core : CliqueDecisions P I W2 G)
    (sub : CliqueDecisions (Set.Iic p0) I W2 G) (p : Set.Iic p0) (U : RegularName P W2),
    (∀ q : Set.Iic p0, q ≤ p → ∀ i x, sub.decides q i x → core.decides q.val i x) →
    ((forOrder P).trace core).holds p.val U →
      ((forOrder (Set.Iic p0)).trace sub).holds p (onCone p0 U)
  fromCone : ∀ {P : Type} [Preorder P] (p0 : P)
    (core : CliqueDecisions (Set.Iic p0) I W2 G) (global : CliqueDecisions P I W2 G),
    (∀ q : Set.Iic p0, ∀ i x, global.decides q.val i x → core.decides q i x) →
    ∀ p : Set.Iic p0, ∀ U : RegularName P W2,
    ((forOrder (Set.Iic p0)).trace core).holds p (onCone p0 U) →
      ((forOrder P).trace global).holds p.val U
  restrict : ∀ {P Q : Type} [Preorder P] [Preorder Q] (r : CompleteRestriction P Q),
    TracesCommute r (forOrder P) (forOrder Q)

variable {I : Type} [LinearOrder I] {G : SimpleGraph W2}

noncomputable def TraceScheme.product (T : TraceScheme I G) : TraceScheme (W1 ×ₗ I) G where
  forOrder P := (T.forOrder P).product
  toCone := by
    intro P inst p0 core sub p U hdec hsmall q hqp
    obtain ⟨s, hsq, bound, hs⟩ := hsmall q.val hqp
    refine ⟨⟨s, hsq.trans q.property⟩, hsq, bound, ?_⟩
    intro i hi
    exact T.toCone p0 (rowCore core i) (rowCore sub i) ⟨s, hsq.trans q.property⟩ U
      (fun t hts j x hx => hdec t ((hts.trans hsq).trans hqp) (toLex (i, j)) x hx) (hs i hi)
  fromCone := by
    intro P inst p0 core global hbelow p U hsmall q hqp
    obtain ⟨s, hsq, bound, hs⟩ := hsmall ⟨q, hqp.trans p.property⟩ hqp
    exact ⟨s.val, hsq, bound, fun i hi => T.fromCone p0 (rowCore core i) (rowCore global i)
      (fun t j x hx => hbelow t (toLex (i, j)) x hx) s U (hs i hi)⟩
  restrict r := Erdos1172Part3TraceCompleteRestriction.product_tracesCommute r (T.restrict r)

noncomputable def line (G : SimpleGraph W2) : TraceScheme W1 G where
  forOrder _ := lineTrace
  toCone := Erdos1172Part3CubeTraceSubsequence.line_trace_to_cone
  fromCone := Erdos1172Part3GlobalNamedSquareLoss.row_trace_from_cone
  restrict := Erdos1172Part3TraceCompleteRestriction.line_tracesCommute

def Extracts (T : TraceScheme I G) : Prop :=
  ∀ {P : Type} [Preorder P], CountablyClosed P →
    ∀ (core : CliqueDecisions P I W2 G) (p0 : P) (U : RegularName P W2),
    ¬((T.forOrder P).trace core).holds p0 U →
      ∃ q : P, q ≤ p0 ∧ ∃ out : CliqueDecisions (Set.Iic q) I W2 G,
        (∀ p i x, out.decides p i x → U.holds p.val x ∧ ∃ j, core.decides p.val j x) ∧
        ∀ p : Set.Iic q, ∀ V : RegularName P W2,
          ((T.forOrder P).trace core).holds p.val V →
            ((T.forOrder (Set.Iic q)).trace out).holds p (onCone q V)

theorem line_extracts (G : SimpleGraph W2) : Extracts (line G) := by
  intro P inst hclosed core p0 U hU
  obtain ⟨q, hqp0, out, hout⟩ :=
    Erdos1172Part3NamedTraceSubsequence.exists_cone_subsequence hclosed core p0 U hU
  refine ⟨q, hqp0, out, ?_, ?_⟩
  · intro p i x hx
    obtain ⟨hUx, j, _, hj⟩ := hout p i x hx
    exact ⟨hUx, j, hj⟩
  · exact Erdos1172Part3NamedTraceSubsequence.traceName_transfer core q out
      (fun p i x hx => (hout p i x hx).2)

end Erdos1172Part3TraceScheme
