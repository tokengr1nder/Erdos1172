/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedRedTail

@[expose] public section

/-!
# A nice red omegaOne block in a stationary regular source

The complete construction runs through guarded red traces, the derived
ideal dichotomy, increasing-index extraction, and one stationary tail
bound. Cone extension and nice-name normalization preserve actual source
truth below the selected start and the stationary common-red future.
The index type is omegaOne, not the high-power Part 3 target.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedStationaryRedBlock

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3NamedRedTail (tailCore centerOnCone exists_stationary_red_tail)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3StationaryDecisions (possible StationaryAt)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

noncomputable def redFuture (source : RegularName P W2)
    (N : NiceCliqueName P W1 W2 G) (a : W2) : RegularName P W2 :=
  meet source (meet (ground {b | a < b}) (afterClique N.toClique))

/-- All core and ideal construction premises are discharged. Actual
membership is retained below the selected start, and every actual
future point is joined to every compatible decision of the nice core. -/
theorem exists_stationary_named_red_block (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName P W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a)
    (p0 : P) (hstat : StationaryAt source.holds p0) :
    ∃ a : W2, ∃ q : P, q ≤ p0 ∧ source.holds q a ∧
      ∃ N : NiceCliqueName P W1 W2 G,
        (∀ p i x, N.toClique.decides p i x → x < a ∧ G.Adj x a) ∧
        (∀ p : P, p ≤ q → ∀ i x, N.toClique.decides p i x → source.holds p x) ∧
        StationaryAt (redFuture source N a).holds q := by
  obtain ⟨a, q0, hq0, hcut, core, later, hcore, hlater, hloss⟩ :=
    Erdos1172Part3NamedStationaryRedLoss.exists_stationary_red_trace_loss
      hGCH hP hclosed center G H hcompl hred hblue source hsup p0 hstat
  obtain ⟨bound, start, hstart, hfuture⟩ := exists_stationary_red_tail
    (centerOnCone center q0).omegaTwoCC G H hcompl core later
    ⟨q0, (show q0 ≤ q0 from le_rfl)⟩
    (hlater ⟨q0, (show q0 ≤ q0 from le_rfl)⟩ le_rfl)
    (fun p b hb i x hx => (hcore p i x hx).2.1.trans (hloss p b hb).2.1)
    (fun p b hb => (hloss p b hb).2.2)
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed q0
      (tailCore core bound)
      (by simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl])
  obtain ⟨N, hN⟩ := exists_nice_clique_name center.omegaTwoCC global
  refine ⟨a, start.val, start.property.trans hq0, source.persistent start.property hcut,
    N, ?_, ?_, ?_⟩
  · intro p i x hx
    obtain ⟨s, hs⟩ := horigin p i x (hN p i x hx)
    exact (hcore s (Erdos1172Part3StationarySquareDecisions.tail bound i) x hs).2
  · intro p hps i x hx
    have hp0 : p ≤ q0 := hps.trans start.property
    have hc := (hbelow p hp0 i x).mp (hN p i x hx)
    exact (hcore ⟨p, hp0⟩ (Erdos1172Part3StationarySquareDecisions.tail bound i) x hc).1
  · intro p hps
    have hp0 : p ≤ q0 := hps.trans start.property
    apply (hfuture ⟨p, hp0⟩ hps).mono
    rintro b ⟨s, hsp, hs⟩
    have hb := hloss s b hs.1
    refine ⟨s.val, hsp, hb.1, hb.2.1, ?_⟩
    intro t hts i x hx
    have ht0 : t ≤ q0 := hts.trans s.property
    have hc := (hbelow t ht0 i x).mp (hN t i x hx)
    exact hs.2 ⟨t, ht0⟩ hts i x hc

end Erdos1172Part3NamedStationaryRedBlock
