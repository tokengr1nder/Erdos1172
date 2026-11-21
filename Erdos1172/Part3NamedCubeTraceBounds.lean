/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ProductStationaryTraceLoss
public import Erdos1172.Part3CubeTraceSubsequence

@[expose] public section

/-!
# Coherent three-level cutoff names for cubic trace losses

An outer decision specifies the late square rows. Each active row has
the previously constructed middle and inner cutoff systems. Transposing
these systems gives total coherent function decisions for all three
coordinates, without simultaneously deciding uncountably many bounds.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedCubeTraceBounds

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3ProductTraceIdeal (CoreTrace productTrace rowCore)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3DecisionSelection (exists_function_decisions_of_dense)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P I : Type} [Preorder P] [LinearOrder I] {G H : SimpleGraph W2}

theorem exists_named_outer_cutoff (T : CoreTrace P I G)
    (core : CliqueDecisions P (W1 ×ₗ I) W2 G) (future : RegularName P W2)
    (hloss : ∀ p a, future.holds p a → (productTrace T core).holds p (ground {x | H.Adj x a})) :
    ∃ K : FunctionDecisions P W2 W1, ∀ p a, future.holds p a →
      ∀ cutoff : W1, K.decides p a cutoff → ∀ i : W1, cutoff < i →
        (T.trace (rowCore core i)).holds p (ground {x | H.Adj x a}) := by
  classical
  obtain ⟨fallback, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
  let R (p : P) (a : W2) (bound : W1) : Prop := (neg future).holds p a ∨
    ∀ i : W1, bound < i → (T.trace (rowCore core i)).holds p (ground {x | H.Adj x a})
  have hR : ∀ {p q a bound}, q ≤ p → R p a bound → R q a bound := by
    intro p q a bound hqp h
    rcases h with hn | hb
    · exact Or.inl ((neg future).persistent hqp hn)
    · exact Or.inr (fun i hi => (T.trace (rowCore core i)).persistent hqp (hb i hi))
  have hRdense : ∀ p a, ∃ q : P, q ≤ p ∧ ∃ bound : W1, R q a bound := by
    intro p a
    obtain ⟨q, hqp, hq⟩ := exists_deciding_refinement future p a
    rcases hq with hq | hn
    · obtain ⟨s, hsq, bound, hs⟩ := hloss q a hq q le_rfl
      exact ⟨s, hsq.trans hqp, bound, Or.inr hs⟩
    · exact ⟨q, hqp, fallback, Or.inl hn⟩
  obtain ⟨K, hK⟩ := exists_function_decisions_of_dense R hR hRdense
  exact ⟨K, fun p a hp cutoff hc => (hK p a cutoff hc).resolve_left (fun hn => hn p le_rfl hp)⟩

def activeRowFuture (future : RegularName P W2) (K : FunctionDecisions P W2 W1) (i : W1) :
    RegularName P W2 := regularize (fun p a => future.holds p a ∧
      ∃ cutoff : W1, K.decides p a cutoff ∧ cutoff < i)

theorem activeRowFuture_of_decision (future : RegularName P W2) (K : FunctionDecisions P W2 W1)
    (p : P) (a : W2) (hp : future.holds p a) (cutoff : W1) (hc : K.decides p a cutoff)
    (i : W1) (hi : cutoff < i) : (activeRowFuture future K i).holds p a :=
  fun q hqp => ⟨q, le_rfl, future.persistent hqp hp, cutoff, K.persistent hqp hc, hi⟩

def transposeDecisions {A B V : Type} (F : A → FunctionDecisions P B V) (b : B) :
    FunctionDecisions P A V where
  decides p a v := (F a).decides p b v
  dense p a := (F a).dense p b
  persistent hqp h := (F _).persistent hqp h
  unique h h' := (F _).unique h h'

end Erdos1172Part3NamedCubeTraceBounds
