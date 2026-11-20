/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedStationarySquareLoss

@[expose] public section

/-!
# Square trace losses on the original decision order

Cone extraction is extended and normalized on the fixed original order.
Its square trace witnesses transfer at the same row and inner indices.
The resulting regular future retains source membership and stationarity.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3GlobalNamedSquareLoss

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3NamedTraceIdeal
open Erdos1172Part3NamedSquareTraceIdeal
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3CliqueNameCoding (mk_square_le)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

theorem row_trace_from_cone (p0 : P) (core : CliqueDecisions (Set.Iic p0) W1 W2 G)
    (global : CliqueDecisions P W1 W2 G)
    (hbelow : ∀ p : Set.Iic p0, ∀ i x, global.decides p.val i x → core.decides p i x)
    (p : Set.Iic p0) (U : RegularName P W2)
    (hsmall : (traceName core).holds p (onCone p0 U)) : (traceName global).holds p.val U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hsmall ⟨q, hqp.trans p.property⟩ hqp
  refine ⟨s.val, hsq, bound, ?_⟩
  intro t hts i hi x hx hUx
  exact hs ⟨t, hts.trans s.property⟩ hts i hi x
    (hbelow ⟨t, hts.trans s.property⟩ i x hx) hUx

theorem square_trace_from_cone (p0 : P) (core : CliqueDecisions (Set.Iic p0) Square W2 G)
    (global : CliqueDecisions P Square W2 G)
    (hbelow : ∀ p : Set.Iic p0, ∀ z x, global.decides p.val z x → core.decides p z x)
    (p : Set.Iic p0) (U : RegularName P W2)
    (hsmall : (squareTraceName core).holds p (onCone p0 U)) :
    (squareTraceName global).holds p.val U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hsmall ⟨q, hqp.trans p.property⟩ hqp
  exact ⟨s.val, hsq, bound, fun i hi => row_trace_from_cone p0 (rowCore core i)
    (rowCore global i) (fun t j x hx => hbelow t (toLex (i, j)) x hx) s U (hs i hi)⟩

noncomputable def traceFuture (source : RegularName P W2)
    (core : CliqueDecisions P Square W2 G) (H : SimpleGraph W2) (a : W2) : RegularName P W2 :=
  meet source (meet (ground {b | a < b})
    (reindex (squareTraceName core) (fun b => ground {x | H.Adj x b})))

theorem exists_global_square_trace_loss (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName P W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a)
    (p0 : P) (hstat : StationaryAt source.holds p0) :
    ∃ a : W2, ∃ q : P, q ≤ p0 ∧ source.holds q a ∧
      ∃ N : NiceCliqueName P Square W2 G,
        (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
        (∀ p : P, p ≤ q → ∀ z x, N.toClique.decides p z x → source.holds p x) ∧
        StationaryAt (traceFuture source N.toClique H a).holds q := by
  obtain ⟨a, q, hqp0, hcut, core, later, hcore, hstatCore, hloss⟩ :=
    Erdos1172Part3NamedStationarySquareLoss.exists_stationary_square_trace_loss hGCH hP hclosed
      center G H hcompl hred hblue source hsup p0 hstat
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed q core mk_square_le
  obtain ⟨N, hN⟩ := exists_nice_clique_name center.omegaTwoCC global
  have hNbelow (p : Set.Iic q) (z : Square) (x : W2) (hx : N.toClique.decides p.val z x) :
      core.decides p z x := (hbelow p.val p.property z x).mp (hN p.val z x hx)
  refine ⟨a, q, hqp0, hcut, N, ?_, ?_, ?_⟩
  · intro p z x hx
    obtain ⟨s, hs⟩ := horigin p z x (hN p z x hx)
    exact (hcore s z x hs).2
  · intro p hpq z x hx
    exact (hcore ⟨p, hpq⟩ z x (hNbelow ⟨p, hpq⟩ z x hx)).1
  · intro p hpq
    apply (hstatCore ⟨p, hpq⟩ hpq).mono
    rintro b ⟨s, hsp, hs⟩
    have hb := hloss s b hs
    exact ⟨s.val, hsp, hb.1, hb.2.1,
      square_trace_from_cone q core N.toClique hNbelow s (ground {x | H.Adj x b}) hb.2.2⟩

end Erdos1172Part3GlobalNamedSquareLoss
