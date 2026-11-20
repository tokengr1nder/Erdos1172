/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ProductStationaryTraceLoss
public import Erdos1172.Part3CubeTraceSubsequence

@[expose] public section

/-!
# Constructed cubes with stationary cubic-trace-small blue losses

A positive trace yields a whole cubic subsequence. Its exact trace
transfer laws survive cone extension and nice-name normalization. The
resulting stationary future has small blue losses; those losses have
not yet been removed by a dominating-stage thinning argument.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3GlobalCubeTraceLoss

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3ProductTraceIdeal (rowCore cubeTrace squareTrace_eq)
open Erdos1172Part3CubeTraceSubsequence (exists_cube_subsequence_data)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3FullSourceCubes (Cube mk_cube_le)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3RegularStageLocality (EventuallyLocal)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

theorem cube_trace_from_cone (p0 : P) (core : CliqueDecisions (Set.Iic p0) Cube W2 G)
    (global : CliqueDecisions P Cube W2 G)
    (hbelow : ∀ p : Set.Iic p0, ∀ z x, global.decides p.val z x → core.decides p z x)
    (p : Set.Iic p0) (U : RegularName P W2)
    (hsmall : (cubeTrace.trace core).holds p (onCone p0 U)) :
    (cubeTrace.trace global).holds p.val U := by
  intro q hqp
  obtain ⟨s, hsq, bound, hs⟩ := hsmall ⟨q, hqp.trans p.property⟩ hqp
  refine ⟨s.val, hsq, bound, ?_⟩
  intro i hi
  rw [squareTrace_eq]
  apply Erdos1172Part3GlobalNamedSquareLoss.square_trace_from_cone p0
    (rowCore core i) (rowCore global i)
    (fun t z x hx => hbelow t (toLex (i, z)) x hx) s U
  rw [← squareTrace_eq]
  exact hs i hi

noncomputable def traceFuture (source : RegularName P W2)
    (core : CliqueDecisions P Cube W2 G) (H : SimpleGraph W2) (a : W2) : RegularName P W2 :=
  meet source (meet (ground {b | a < b})
    (reindex (cubeTrace.trace core) (fun b => ground {x | H.Adj x b})))

theorem exists_global_cube_trace_loss (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source)
    (p0 : Full hGCH) (hstat : StationaryAt source.holds p0) :
    ∃ a : W2, ∃ q : Full hGCH, q ≤ p0 ∧ source.holds q a ∧
      ∃ N : NiceCliqueName (Full hGCH) Cube W2 G,
        (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
        (∀ p : Full hGCH, p ≤ q → ∀ z x, N.toClique.decides p z x → source.holds p x) ∧
        StationaryAt (traceFuture source N.toClique H a).holds q := by
  obtain ⟨a, q, hqp0, hcut, data, X, out, hXsub, hXpos, hout, hloss⟩ :=
    Erdos1172Part3ProductStationaryTraceLoss.exists_positive_stationary_cube_trace_loss
      hGCH G H hcompl hred hblue source hsup hlocal p0 hstat
  obtain ⟨start, hstart, ⟨sub⟩⟩ := exists_cube_subsequence_data
    (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH)
    data.name.toClique q X (hXpos q le_rfl)
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone
      (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH) start sub.toCube mk_cube_le
  obtain ⟨N, hN⟩ := exists_nice_clique_name
    (Erdos1172Part3TransfiniteHechlerCentering.omegaTwoCC hGCH ⊤) global
  have hNbelow (p : Set.Iic start) (z : Cube) (x : W2) (hx : N.toClique.decides p.val z x) :
      sub.toCube.decides p z x := (hbelow p.val p.property z x).mp (hN p.val z x hx)
  refine ⟨a, start, hstart.trans hqp0, source.persistent hstart hcut, N, ?_, ?_, ?_⟩
  · intro p z x hx
    obtain ⟨s, hs⟩ := horigin p z x (hN p z x hx)
    obtain ⟨_, oldRow, oldInner, _, hdec⟩ := sub.membership s z x hs
    exact data.geometry s.val (toLex (oldRow, oldInner)) x hdec
  · intro p hpstart z x hx
    exact (hXsub p x (sub.membership ⟨p, hpstart⟩ z x (hNbelow ⟨p, hpstart⟩ z x hx)).1).1
  · intro p hpstart
    apply (hout p (hpstart.trans hstart)).mono
    rintro b ⟨s, hsp, hs⟩
    have hb := hloss s b hs
    let t : Set.Iic start := ⟨s, hsp.trans hpstart⟩
    have htransfer := sub.cube_trace_transfer t (Erdos1172Part3NamedBlueDerivedIdeal.fiber H b X) hb.2.2
    have hsmall : (cubeTrace.trace sub.toCube).holds t (onCone start (ground {x | H.Adj x b})) := by
      apply cubeTrace.on_decisions sub.toCube t (onCone start (ground {x | H.Adj x b}))
        (onCone start (Erdos1172Part3NamedBlueDerivedIdeal.fiber H b X)) ?_ htransfer
      intro v hvt z x hx hHxb
      exact ⟨(sub.membership v z x hx).1, hHxb⟩
    exact ⟨s, hsp, hb.1, hb.2.1,
      cube_trace_from_cone start sub.toCube N.toClique hNbelow t (ground {x | H.Adj x b}) hsmall⟩

end Erdos1172Part3GlobalCubeTraceLoss
