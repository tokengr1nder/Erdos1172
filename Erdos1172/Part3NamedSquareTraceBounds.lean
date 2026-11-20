/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedStationarySquareLoss
public import Erdos1172.Part3NamedCutoffRefinement

@[expose] public section

/-!
# Selecting named cutoffs from regular square trace losses

Outer and inner bounds are total coherent decision systems. Inactive
future conditions have harmless fallback values. At actual future
members, every late-row blue edge lies strictly below its inner bound.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedSquareTraceBounds

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3NamedTraceIdeal
open Erdos1172Part3NamedSquareTraceIdeal
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3DecisionSelection (exists_function_decisions_of_dense)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions (possible)
open Erdos1172Part3NamedCliqueThinning (StationaryCliqueDecisions)
open Erdos1172Part3IteratedHechlerOrder (Condition)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P : Type} [Preorder P] {G H : SimpleGraph W2}

theorem exists_named_trace_cutoffs (core : CliqueDecisions P Square W2 G)
    (future : RegularName P W2)
    (hloss : ∀ p a, future.holds p a → (squareTraceName core).holds p (ground {x | H.Adj x a})) :
    ∃ K : FunctionDecisions P W2 W1, ∃ F : W2 → FunctionDecisions P W1 W1,
      ∀ p a, future.holds p a → ∀ cutoff : W1, K.decides p a cutoff →
        ∀ i : W1, cutoff < i → ∀ j : W1, ∀ x : W2,
          core.decides p (toLex (i, j)) x → H.Adj x a →
            ∀ v : W1, (F a).decides p i v → j < v := by
  classical
  obtain ⟨fallback, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
  let R (p : P) (a : W2) (bound : W1) : Prop := (neg future).holds p a ∨
    ∀ i : W1, bound < i → (traceName (rowCore core i)).holds p (ground {x | H.Adj x a})
  have hR : ∀ {p q a bound}, q ≤ p → R p a bound → R q a bound := by
    intro p q a bound hqp h
    rcases h with hn | hb
    · exact Or.inl ((neg future).persistent hqp hn)
    · exact Or.inr (fun i hi => (traceName (rowCore core i)).persistent hqp (hb i hi))
  have hRdense : ∀ p a, ∃ q : P, q ≤ p ∧ ∃ bound : W1, R q a bound := by
    intro p a
    obtain ⟨q, hqp, hq⟩ := exists_deciding_refinement future p a
    rcases hq with hq | hn
    · obtain ⟨s, hsq, bound, hs⟩ := hloss q a hq q le_rfl
      exact ⟨s, hsq.trans hqp, bound, Or.inr hs⟩
    · exact ⟨q, hqp, fallback, Or.inl hn⟩
  obtain ⟨K, hK⟩ := exists_function_decisions_of_dense R hR hRdense
  let T (a : W2) (p : P) (i bound : W1) : Prop := (neg future).holds p a ∨
    ∃ cutoff : W1, K.decides p a cutoff ∧
      (i ≤ cutoff ∨ ∃ innerBound : W1, innerBound < bound ∧
        TailAvoid (rowCore core i) p (ground {x | H.Adj x a}) innerBound)
  have hT (a : W2) : ∀ {p q i bound}, q ≤ p → T a p i bound → T a q i bound := by
    intro p q i bound hqp h
    rcases h with hn | ⟨cutoff, hc, hb⟩
    · exact Or.inl ((neg future).persistent hqp hn)
    · refine Or.inr ⟨cutoff, K.persistent hqp hc, ?_⟩
      rcases hb with hi | ⟨innerBound, hib, hb⟩
      · exact Or.inl hi
      · exact Or.inr ⟨innerBound, hib, tailAvoid_persistent hqp hb⟩
  have hTdense (a : W2) : ∀ p i, ∃ q : P, q ≤ p ∧ ∃ bound : W1, T a q i bound := by
    intro p i
    obtain ⟨q, hqp, hq⟩ := exists_deciding_refinement future p a
    rcases hq with hq | hn
    · obtain ⟨s, hsq, cutoff, hcut⟩ := K.dense q a
      have hf : future.holds s a := future.persistent hsq hq
      have hrows := (hK s a cutoff hcut).resolve_left (fun hn => hn s le_rfl hf)
      by_cases hi : i ≤ cutoff
      · exact ⟨s, hsq.trans hqp, fallback, Or.inr ⟨cutoff, hcut, Or.inl hi⟩⟩
      · obtain ⟨t, hts, innerBound, ht⟩ := hrows i (lt_of_not_ge hi) s le_rfl
        obtain ⟨bound, hbound⟩ := exists_bound_of_countable ({innerBound} : Set W1) (by simp)
        exact ⟨t, (hts.trans hsq).trans hqp, bound,
          Or.inr ⟨cutoff, K.persistent hts hcut,
            Or.inr ⟨innerBound, hbound innerBound (by simp), ht⟩⟩⟩
    · exact ⟨q, hqp, fallback, Or.inl hn⟩
  choose F hF using fun a => exists_function_decisions_of_dense (T a) (hT a) (hTdense a)
  refine ⟨K, F, ?_⟩
  intro p a hp cutoff hcut i hi j x hx hH v hv
  obtain ⟨otherCutoff, hother, hb⟩ :=
    (hF a p i v hv).resolve_left (fun hn => hn p le_rfl hp)
  have heq : otherCutoff = cutoff := K.unique hother hcut
  subst otherCutoff
  obtain ⟨innerBound, hib, hb⟩ := hb.resolve_left (not_le_of_gt hi)
  have hj : j ≤ innerBound := by
    by_contra hj
    exact hb p le_rfl j (lt_of_not_ge hj) x hx hH
  exact hj.trans_lt hib

theorem exists_stationary_square_from_trace_losses (center : CountablyCenteredCode P)
    (hclosed : CountablyClosed P) (hCH : CH) (p0 : Condition P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (core : CliqueDecisions P Square W2 G) (future : RegularName P W2)
    (hstat : IsStationary (possible future.holds p0.base))
    (hafter : ∀ p a, future.holds p a → ∀ z x, core.decides p z x → x < a)
    (hloss : ∀ p a, future.holds p a → (squareTraceName core).holds p (ground {x | H.Adj x a})) :
    ∃ sys : StationaryCliqueDecisions (Condition P) Square G,
      sys.start ≤ p0 ∧ (∀ q a, sys.future q a → future.holds q.base a) ∧
        ∀ q z x, sys.clique.decides q z x → ∃ old : Square, core.decides q.base old x := by
  obtain ⟨K, F, hbounds⟩ := exists_named_trace_cutoffs core future hloss
  exact Erdos1172Part3NamedCutoffRefinement.exists_stationary_square_from_named_cutoffs
    center hclosed hCH p0 G H hcompl core future.holds future.persistent hstat hafter K F hbounds

end Erdos1172Part3NamedSquareTraceBounds
