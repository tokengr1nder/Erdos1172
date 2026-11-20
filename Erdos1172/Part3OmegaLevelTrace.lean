/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3WeakProductTrace
public import Erdos1172.Part3OmegaPowerIndex

@[expose] public section

/-!
# The eventual finite-level trace on an omega core

Smallness means that, after one natural-number level cutoff, every
finite component has small finite trace. This trace is regular and
monotone, but no countable-completeness law is assumed. Positivity
supplies arbitrarily high positive finite components below every
condition. The outer omegaOne product inherits the weak trace laws.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3OmegaLevelTrace

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3FiniteTraceSchemes (Index scheme)
open Erdos1172Part3OmegaPowerIndex (OmegaIndex)
open Erdos1172Part3WeakProductTrace (WeakCoreTrace)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

def levelCore (core : CliqueDecisions P OmegaIndex W2 G) (n : ℕ) :
    CliqueDecisions P (Index n) W2 G where
  decides p i x := core.decides p (toLex ⟨n, i⟩) x
  dense p i := core.dense p (toLex ⟨n, i⟩)
  persistent := core.persistent
  unique := core.unique
  ordered hij hx hy := core.ordered (Sigma.Lex.right _ _ hij) hx hy
  adjacent hij hx hy := core.adjacent (by
    intro h
    have heq : (⟨n, _⟩ : Sigma Index) = ⟨n, _⟩ := congrArg ofLex h
    exact hij (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)) hx hy

noncomputable def LevelSmall (core : CliqueDecisions P OmegaIndex W2 G)
    (p : P) (U : RegularName P W2) : Prop :=
  ∃ bound : ℕ, ∀ n : ℕ, bound < n → (((scheme G n).forOrder P).trace (levelCore core n)).holds p U

theorem levelSmall_persistent {core : CliqueDecisions P OmegaIndex W2 G} {p q : P}
    {U : RegularName P W2} (hqp : q ≤ p) (h : LevelSmall core p U) : LevelSmall core q U := by
  obtain ⟨bound, hb⟩ := h
  exact ⟨bound, fun n hn => (((scheme G n).forOrder P).trace (levelCore core n)).persistent hqp (hb n hn)⟩

noncomputable def omegaTrace (core : CliqueDecisions P OmegaIndex W2 G) :
    RegularName P (RegularName P W2) := regularize (LevelSmall core)

theorem omegaTrace_of_witness (core : CliqueDecisions P OmegaIndex W2 G) (p : P)
    (U : RegularName P W2) (h : LevelSmall core p U) : (omegaTrace core).holds p U :=
  fun q hqp => ⟨q, le_rfl, levelSmall_persistent hqp h⟩

theorem omegaTrace_empty (core : CliqueDecisions P OmegaIndex W2 G) (p : P) :
    (omegaTrace core).holds p (ground ∅) :=
  omegaTrace_of_witness core p (ground ∅) ⟨0, fun n _ => ((scheme G n).forOrder P).empty (levelCore core n) p⟩

theorem omegaTrace_mono (core : CliqueDecisions P OmegaIndex W2 G) (p : P)
    (U V : RegularName P W2) (hsub : ∀ x, (implication U V).holds p x)
    (hV : (omegaTrace core).holds p V) : (omegaTrace core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hV q hqp
  exact ⟨s, hsq, bound, fun n hn => ((scheme G n).forOrder P).mono (levelCore core n) s U V
    (fun x => (implication U V).persistent (hsq.trans hqp) (hsub x)) (hs n hn)⟩

theorem omegaTrace_on_decisions (core : CliqueDecisions P OmegaIndex W2 G) (p : P)
    (U V : RegularName P W2)
    (hsub : ∀ q : P, q ≤ p → ∀ z x, core.decides q z x → U.holds q x → V.holds q x)
    (hV : (omegaTrace core).holds p V) : (omegaTrace core).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hV q hqp
  refine ⟨s, hsq, bound, fun n hn => ((scheme G n).forOrder P).on_decisions (levelCore core n) s U V ?_ (hs n hn)⟩
  intro t hts i x hx hUx
  exact hsub t ((hts.trans hsq).trans hqp) (toLex ⟨n, i⟩) x hx hUx

theorem omegaTrace_of_avoids (core : CliqueDecisions P OmegaIndex W2 G) (p : P)
    (U : RegularName P W2)
    (h : ∀ q : P, q ≤ p → ∀ z x, core.decides q z x → ¬U.holds q x) :
    (omegaTrace core).holds p U :=
  omegaTrace_of_witness core p U ⟨0, fun n _ => ((scheme G n).forOrder P).of_avoids (levelCore core n) p U
    (fun q hqp i x hx => h q hqp (toLex ⟨n, i⟩) x hx)⟩

theorem omegaTrace_not_small_of_cover (core : CliqueDecisions P OmegaIndex W2 G) (p : P)
    (U : RegularName P W2) (h : ∀ q : P, q ≤ p → ∀ z x, core.decides q z x → U.holds q x) :
    (neg (omegaTrace core)).holds p U := by
  intro q hqp hsmall
  obtain ⟨s, hsq, bound, hs⟩ := hsmall q le_rfl
  exact ((scheme G (bound + 1)).forOrder P).not_small_of_cover (levelCore core (bound + 1)) s U
    (fun t hts i x hx => h t ((hts.trans hsq).trans hqp) (toLex ⟨bound + 1, i⟩) x hx)
    s le_rfl (hs (bound + 1) (Nat.lt_succ_self bound))

noncomputable def omegaWeakTrace : WeakCoreTrace P OmegaIndex G where
  trace := omegaTrace
  empty := omegaTrace_empty
  mono := omegaTrace_mono
  on_decisions := omegaTrace_on_decisions
  of_avoids := omegaTrace_of_avoids
  not_small_of_cover := omegaTrace_not_small_of_cover

theorem exists_positive_level (core : CliqueDecisions P OmegaIndex W2 G) (p : P)
    (U : RegularName P W2) (hU : (neg (omegaTrace core)).holds p U)
    (q : P) (hqp : q ≤ p) (bound : ℕ) :
    ∃ s : P, s ≤ q ∧ ∃ n : ℕ, bound < n ∧
      (neg (((scheme G n).forOrder P).trace (levelCore core n))).holds s U := by
  classical
  by_contra h
  have hlevels : ∀ n : ℕ, bound < n → (((scheme G n).forOrder P).trace (levelCore core n)).holds q U := by
    intro n hn
    by_contra hlevel
    obtain ⟨s, hsq, hs⟩ := (not_holds_iff_exists_neg (((scheme G n).forOrder P).trace (levelCore core n)) q U).mp hlevel
    exact h ⟨s, hsq, n, hn, hs⟩
  exact hU q hqp (omegaTrace_of_witness core q U ⟨bound, hlevels⟩)

noncomputable def omegaProductTrace : WeakCoreTrace P (W1 ×ₗ OmegaIndex) G := omegaWeakTrace.product

end Erdos1172Part3OmegaLevelTrace
