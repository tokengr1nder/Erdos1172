/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FiniteTraceSchemes
public import Erdos1172.Part3NamedCubeTraceBounds

@[expose] public section

/-!
# Coherent cutoff trees for all finite trace depths

A cutoff is named at every proper prefix of a finite product index.
Clearing all cutoffs on a path rules out a blue loss at that vertex.
The construction makes only dense finite decisions along any one path.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FiniteTraceCutoffs

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3FiniteTraceSchemes (Index Prefix root scheme)
open Erdos1172Part3ProductTraceIdeal (rowCore)
open Erdos1172Part3NamedTraceIdeal (TailAvoid tailAvoid_persistent)
open Erdos1172Part3NamedCubeTraceBounds (exists_named_outer_cutoff activeRowFuture activeRowFuture_of_decision)
open Erdos1172Part3DecisionSelection (exists_function_decisions_of_dense)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P : Type} [Preorder P]

def reindexBounds {A B : Type} (F : FunctionDecisions P A W1) (f : B → A) :
    FunctionDecisions P B W1 where
  decides p i v := F.decides p (f i) v
  dense p i := F.dense p (f i)
  persistent := F.persistent
  unique := F.unique

def subBounds {n : ℕ} (F : FunctionDecisions P (Prefix (n + 1)) W1) (i : W1) :
    FunctionDecisions P (Prefix n) W1 := reindexBounds F (fun z => Sum.inr (i, z))

def Clears : (n : ℕ) → FunctionDecisions P (Prefix n) W1 → P → Index n → Prop
  | 0, F, p, z => ∃ v : W1, F.decides p () v ∧ v < z
  | n + 1, F, p, z => ∃ v : W1, F.decides p (Sum.inl ()) v ∧ v < (ofLex z).1 ∧
      Clears n (subBounds F (ofLex z).1) p (ofLex z).2

def assembleBounds {n : ℕ} (K : FunctionDecisions P Unit W1)
    (B : W1 → FunctionDecisions P (Prefix n) W1) : FunctionDecisions P (Prefix (n + 1)) W1 where
  decides p z v := match z with
    | Sum.inl u => K.decides p u v
    | Sum.inr w => (B w.1).decides p w.2 v
  dense := by
    intro p z
    rcases z with u | ⟨i, z⟩
    · exact K.dense p u
    · exact (B i).dense p z
  persistent := by
    intro p q z v hqp hv
    rcases z with u | ⟨i, z⟩
    · exact K.persistent hqp hv
    · exact (B i).persistent hqp hv
  unique := by
    intro p z v w hv hw
    rcases z with u | ⟨i, z⟩
    · exact K.unique hv hw
    · exact (B i).unique hv hw

theorem subBounds_assemble {n : ℕ} (K : FunctionDecisions P Unit W1)
    (B : W1 → FunctionDecisions P (Prefix n) W1) (i : W1) :
    subBounds (assembleBounds K B) i = B i := rfl

theorem exists_finite_trace_cutoffs (n : ℕ) {G H : SimpleGraph W2}
    (core : CliqueDecisions P (Index n) W2 G) (future : RegularName P W2)
    (hloss : ∀ p a, future.holds p a →
      (((scheme G n).forOrder P).trace core).holds p (ground {x | H.Adj x a})) :
    ∃ B : W2 → FunctionDecisions P (Prefix n) W1, ∀ p a, future.holds p a →
      ∀ z x, core.decides p z x → Clears n (B a) p z → ¬H.Adj x a := by
  classical
  induction n generalizing future with
  | zero =>
    obtain ⟨fallback, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
    let R (p : P) (a : W2) (bound : W1) : Prop := (neg future).holds p a ∨
      TailAvoid core p (ground {x | H.Adj x a}) bound
    have hR : ∀ {p q a bound}, q ≤ p → R p a bound → R q a bound := by
      intro p q a bound hqp h
      exact h.imp ((neg future).persistent hqp) (tailAvoid_persistent hqp)
    have hRdense : ∀ p a, ∃ q : P, q ≤ p ∧ ∃ bound : W1, R q a bound := by
      intro p a
      obtain ⟨q, hqp, hq | hn⟩ := exists_deciding_refinement future p a
      · obtain ⟨s, hsq, bound, hs⟩ := hloss q a hq q le_rfl
        exact ⟨s, hsq.trans hqp, bound, Or.inr hs⟩
      · exact ⟨q, hqp, fallback, Or.inl hn⟩
    obtain ⟨K, hK⟩ := exists_function_decisions_of_dense R hR hRdense
    refine ⟨fun a => reindexBounds K (fun _ : Unit => a), ?_⟩
    intro p a hp z x hx hclear hblue
    obtain ⟨v, hv, hvz⟩ := hclear
    exact ((hK p a v hv).resolve_left (fun hn => hn p le_rfl hp)) p le_rfl z hvz x hx hblue
  | succ n ih =>
    obtain ⟨K, hK⟩ := exists_named_outer_cutoff ((scheme G n).forOrder P) core future hloss
    have hrow (i : W1) : ∀ p a, (activeRowFuture future K i).holds p a →
        (((scheme G n).forOrder P).trace (rowCore core i)).holds p (ground {x | H.Adj x a}) := by
      intro p a hp
      apply (((scheme G n).forOrder P).trace (rowCore core i)).of_dense p (ground {x | H.Adj x a})
      intro q hqp
      obtain ⟨s, hsq, hs, cutoff, hc, hi⟩ := hp q hqp
      exact ⟨s, hsq, hK s a hs cutoff hc i hi⟩
    choose bounds hbounds using fun i => ih (rowCore core i) (activeRowFuture future K i) (hrow i)
    refine ⟨fun a => assembleBounds (reindexBounds K (fun _ : Unit => a)) (fun i => bounds i a), ?_⟩
    intro p a hp z x hx hclear
    obtain ⟨v, hv, hvz, hinner⟩ := hclear
    have hactive := activeRowFuture_of_decision future K p a hp v hv (ofLex z).1 hvz
    rw [subBounds_assemble] at hinner
    exact hbounds (ofLex z).1 p a hactive (ofLex z).2 x hx hinner

end Erdos1172Part3FiniteTraceCutoffs
