/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedBlockSequence

@[expose] public section

/-!
# Flattening coherent outer block choices into a red product

Each outer choice selects an inner core with an arbitrary linear index
order. The regular complete join relation between compatible choices
gives all cross-row order and edges. Outer and inner density are combined
at the same strengthening.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedBlockFlattening

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique containedIn cliqueFunction)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3StationarySquareDecisions (Square)

variable {P L I : Type} [Preorder P] [LinearOrder I] {G : SimpleGraph W2}

noncomputable def joinedCores (left right : CliqueDecisions P I W2 G) : RegularName P Unit :=
  containedIn (cliqueFunction right) (afterClique left)

def flatDecides (blocks : L → CliqueDecisions P I W2 G) (F : FunctionDecisions P W1 L)
    (p : P) (z : W1 ×ₗ I) (x : W2) : Prop :=
  ∃ N : L, F.decides p (ofLex z).1 N ∧ (blocks N).decides p (ofLex z).2 x

theorem flat_ordered_pair (blocks : L → CliqueDecisions P I W2 G)
    (F : FunctionDecisions P W1 L)
    (hcross : ∀ p i j N M, i < j → F.decides p i N → F.decides p j M →
      (joinedCores (blocks N) (blocks M)).holds p ())
    {p : P} {i j : W1 ×ₗ I} {x y : W2} (hij : i < j)
    (hx : flatDecides blocks F p i x) (hy : flatDecides blocks F p j y) :
    x < y ∧ G.Adj x y := by
  obtain ⟨N, hN, hx⟩ := hx
  obtain ⟨M, hM, hy⟩ := hy
  rw [Prod.Lex.lt_iff] at hij
  rcases hij with hfirst | ⟨hfirst, hsecond⟩
  · exact hcross p (ofLex i).1 (ofLex j).1 N M hfirst hN hM
      p le_rfl (ofLex j).2 y hy p le_rfl (ofLex i).2 x hx
  · have hNM : N = M := F.unique (by simpa only [hfirst] using hN) hM
    subst M
    exact ⟨(blocks N).ordered hsecond hx hy, (blocks N).adjacent hsecond.ne hx hy⟩

noncomputable def flatten (blocks : L → CliqueDecisions P I W2 G)
    (F : FunctionDecisions P W1 L)
    (hcross : ∀ p i j N M, i < j → F.decides p i N → F.decides p j M →
      (joinedCores (blocks N) (blocks M)).holds p ()) : CliqueDecisions P (W1 ×ₗ I) W2 G where
  decides := flatDecides blocks F
  dense := by
    intro p z
    obtain ⟨q, hqp, N, hN⟩ := F.dense p (ofLex z).1
    obtain ⟨s, hsq, x, hx⟩ := (blocks N).dense q (ofLex z).2
    exact ⟨s, hsq.trans hqp, x, N, F.persistent hsq hN, hx⟩
  persistent := by
    rintro p q z x hqp ⟨N, hN, hx⟩
    exact ⟨N, F.persistent hqp hN, (blocks N).persistent hqp hx⟩
  unique := by
    rintro p z x y ⟨N, hN, hx⟩ ⟨M, hM, hy⟩
    have heq : N = M := F.unique hN hM
    subst M
    exact (blocks N).unique hx hy
  ordered hij hx hy := (flat_ordered_pair blocks F hcross hij hx hy).1
  adjacent := by
    intro p i j x y hij hx hy
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (flat_ordered_pair blocks F hcross hlt hx hy).2
    · exact (flat_ordered_pair blocks F hcross hgt hy hx).2.symm

def onConeCore (p0 : P) (core : CliqueDecisions P I W2 G) :
    CliqueDecisions (Set.Iic p0) I W2 G where
  decides p i x := core.decides p.val i x
  dense := by
    intro p i
    obtain ⟨q, hqp, x, hx⟩ := core.dense p.val i
    exact ⟨⟨q, hqp.trans p.property⟩, hqp, x, hx⟩
  persistent := core.persistent
  unique := core.unique
  ordered := core.ordered
  adjacent := core.adjacent

theorem joinedCores_onCone (p0 : P) (left right : CliqueDecisions P I W2 G)
    (p : Set.Iic p0) (h : (joinedCores left right).holds p.val ()) :
    (joinedCores (onConeCore p0 left) (onConeCore p0 right)).holds p () := by
  intro q hqp i x hx s hsq j y hy
  exact h q.val hqp i x hx s.val hsq j y hy

end Erdos1172Part3NamedBlockFlattening
