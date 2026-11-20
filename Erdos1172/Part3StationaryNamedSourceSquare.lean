/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3GlobalNamedSquareLoss
public import Erdos1172.Part3NamedSquareTraceBounds

@[expose] public section

/-!
# A stationary common-red future for a constructed source square

The square, regular row trace ideal, named cutoffs, and dominating-stage
thinning are all constructed. The resulting nice square lives on the
fixed next Hechler order. Actual source membership and a regular stationary
common-red future are retained. This is an omegaOne-squared result, not
the omegaOne-to-the-omega-plus-two Part 3 target.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3StationaryNamedSourceSquare

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3GlobalNamedSquareLoss (exists_global_square_trace_loss traceFuture)
open Erdos1172Part3NamedSquareTraceBounds (exists_stationary_square_from_trace_losses)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3IteratedHechlerOrder (Condition liftBase liftBase_le base_le)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3StationarySquareDecisions (Square)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

/-- Exact base lifting preserves dense stability of regular membership. -/
def liftRegular {X : Type} (U : RegularName P X) : RegularName (Condition P) X where
  holds p x := U.holds p.base x
  persistent hqp h := U.persistent (base_le hqp) h
  of_dense p x h := by
    apply U.of_dense p.base x
    intro q hqp
    obtain ⟨s, hs, hU⟩ := h (liftBase p q) (liftBase_le p hqp)
    exact ⟨s.base, base_le hs, hU⟩

noncomputable def squareRedFuture (source : RegularName P W2)
    (N : NiceCliqueName (Condition P) Square W2 G) (a : W2) : RegularName (Condition P) W2 :=
  meet (liftRegular source) (meet (ground {b | a < b}) (afterClique N.toClique))

theorem exists_stationary_named_source_square (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName P W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a)
    (p0 : Condition P) (hstat : StationaryAt source.holds p0.base) :
    ∃ a : W2, ∃ q : Condition P, q ≤ p0 ∧ source.holds q.base a ∧
      ∃ N : NiceCliqueName (Condition P) Square W2 G,
        (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
        (∀ p : Condition P, p ≤ q → ∀ z x, N.toClique.decides p z x → source.holds p.base x) ∧
        StationaryAt (squareRedFuture source N a).holds q := by
  obtain ⟨a, start, hstart, hcut, core, hgeometry, hsource, hlater⟩ :=
    exists_global_square_trace_loss hGCH hP hclosed center G H hcompl hred hblue
      source hsup p0.base hstat
  let future := traceFuture source core.toClique H a
  obtain ⟨sys, hsys, hfuture, horigin⟩ := exists_stationary_square_from_trace_losses center
    hclosed hGCH.toCH (liftBase p0 start) G H hcompl core.toClique future
    (hlater start le_rfl)
    (fun p b hb z x hx => (hgeometry p z x hx).1.trans hb.2.1)
    (fun p b hb => hb.2.2)
  obtain ⟨N, hN⟩ := exists_nice_clique_name (center.extend hGCH.toCH).omegaTwoCC sys.clique
  refine ⟨a, sys.start, hsys.trans (liftBase_le p0 hstart),
    source.persistent (base_le hsys) hcut, N, ?_, ?_, ?_⟩
  · intro p z x hx
    obtain ⟨old, hold⟩ := horigin p z x (hN p z x hx)
    exact hgeometry p.base old x hold
  · intro p hps z x hx
    obtain ⟨old, hold⟩ := horigin p z x (hN p z x hx)
    exact hsource p.base ((base_le hps).trans (base_le hsys)) old x hold
  · intro p hps
    apply (sys.stationary p hps).mono
    rintro b ⟨q, hqp, hq⟩
    have hb := hfuture q b hq
    refine ⟨q, hqp, hb.1, hb.2.1, ?_⟩
    intro t htq z x hx
    exact sys.cross t b (sys.persistent htq hq) z x (hN t z x hx)

theorem stationary_named_source_square_after_limit (hGCH : GCH) (n : ℕ)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName
      (Erdos1172Part3HechlerStagesAfterLimit.afterLimit hGCH n).Carrier W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a)
    (p0 : Condition (Erdos1172Part3HechlerStagesAfterLimit.afterLimit hGCH n).Carrier)
    (hstat : StationaryAt source.holds p0.base) :
    let P := (Erdos1172Part3HechlerStagesAfterLimit.afterLimit hGCH n).Carrier
    ∃ a : W2, ∃ q : Condition P, q ≤ p0 ∧ source.holds q.base a ∧
      ∃ N : NiceCliqueName (Condition P) Square W2 G,
        (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
        (∀ p : Condition P, p ≤ q → ∀ z x, N.toClique.decides p z x → source.holds p.base x) ∧
        StationaryAt (squareRedFuture source N a).holds q := by
  let order := Erdos1172Part3HechlerStagesAfterLimit.afterLimit hGCH n
  exact exists_stationary_named_source_square hGCH order.small order.closed order.centered
    G H hcompl hred hblue source hsup p0 hstat

end Erdos1172Part3StationaryNamedSourceSquare
