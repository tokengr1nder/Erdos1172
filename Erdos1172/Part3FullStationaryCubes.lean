/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TraceCompleteRestriction
public import Erdos1172.Part3StationaryCubeThinning

@[expose] public section

/-!
# Stationary source cubes inside the full transfinite order

The constructed source cube and its trace-loss future restrict to one
earlier stage. Cubic thinning runs at that stage's actual Hechler
successor. Exact lifting returns the result below the original full-order
condition, retaining actual source membership and a stationary completely
red common future.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FullStationaryCubes

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3SparseIterationCarriers (Cut)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction exists_name_restriction)
open Erdos1172Part3TransfiniteHechlerSuccessorOrder (fullSuccessorRestriction fullSuccessorRestriction_base)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularStageLocality (EventuallyLocal)
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3CompleteRestrictionNames (pushClique pushClique_decides_iff)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3FullSourceCubes (Cube mk_cube_le)
open Erdos1172Part3GlobalCubeTraceLoss (traceFuture exists_global_cube_trace_loss)
open Erdos1172Part3TraceCompleteRestriction (SameDecisions cube_traceFuture_lift)
open OrdinalRamsey (HasCliqueOfType)

theorem exists_cube_trace_restriction (hGCH : GCH) {G : SimpleGraph W2}
    (source : RegularName (Full hGCH) W2)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source)
    (N : NiceCliqueName (Full hGCH) Cube W2 G) (H : SimpleGraph W2) (a : W2) :
    ∃ b : W2, ∃ V : RegularName (Earlier hGCH b) W2,
      ∃ M : NiceCliqueName (Earlier hGCH b) Cube W2 G,
        (restriction hGCH b).liftRegular V = source ∧
        SameDecisions (restriction hGCH b) N.toClique M.toClique ∧
        (restriction hGCH b).liftRegular (traceFuture V M.toClique H a) =
          traceFuture source N.toClique H a := by
  obtain ⟨nameBound, hname⟩ := exists_name_restriction hGCH N mk_cube_le
  obtain ⟨sourceBound, hsource⟩ := hlocal
  let b := max nameBound sourceBound
  obtain ⟨M, hM⟩ := hname b (le_max_left _ _)
  obtain ⟨V, hV⟩ := hsource b (le_max_right _ _)
  have hdec : SameDecisions (restriction hGCH b) N.toClique M.toClique :=
    fun p z x => (hM p z x).symm
  refine ⟨b, V, M, hV, hdec, ?_⟩
  rw [cube_traceFuture_lift (restriction hGCH b) N.toClique M.toClique hdec V H a, hV]

noncomputable def redFuture {P : Type} [Preorder P] {G : SimpleGraph W2}
    (source : RegularName P W2) (N : NiceCliqueName P Cube W2 G) (a : W2) : RegularName P W2 :=
  meet source (meet (ground {b | a < b}) (afterClique N.toClique))

theorem stationary_source_cube (hGCH : GCH)
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
        StationaryAt (redFuture source N a).holds q := by
  obtain ⟨a, start, hstart, hcut, old, hgeometry, hsource, hfuture⟩ :=
    exists_global_cube_trace_loss hGCH G H hcompl hred hblue source hsup hlocal p0 hstat
  obtain ⟨b, V, M, hV, hdec, hfutureEq⟩ := exists_cube_trace_restriction hGCH source hlocal old H a
  let r := restriction hGCH b
  let s := fullSuccessorRestriction hGCH b
  have hstatEarlier : StationaryAt (traceFuture V M.toClique H a).holds (r.restrict start) := by
    apply (r.stationary_lift_iff (traceFuture V M.toClique H a).holds start).mp
    change StationaryAt (r.liftRegular (traceFuture V M.toClique H a)).holds start
    rw [hfutureEq]
    exact hfuture
  have hMgeometry (p : Earlier hGCH b) (z : Cube) (x : W2) (hx : M.toClique.decides p z x) :
      x < a ∧ G.Adj x a := hgeometry (r.embed p) z x
        ((hdec (r.embed p) z x).mpr (by rwa [r.restrict_embed]))
  have hMsource (p : Earlier hGCH b) (hp : p ≤ r.restrict start) (z : Cube) (x : W2)
      (hx : M.toClique.decides p z x) : V.holds p x := by
    obtain ⟨t, htstart, ht⟩ := r.lift start p hp
    have hactual := hsource t htstart z x ((hdec t z x).mpr (by rwa [ht]))
    have hVt : V.holds (r.restrict t) x := by
      change (r.liftRegular V).holds t x
      rw [hV]
      exact hactual
    rwa [ht] at hVt
  obtain ⟨sys, hsys, hsysFuture, hsysOrigin⟩ :=
    Erdos1172Part3StationaryCubeThinning.exists_stationary_cube_from_trace_losses
      (Erdos1172Part3TransfiniteHechlerCentering.centered hGCH (b : Cut))
      (Erdos1172Part3TransfiniteHechlerClosure.countablyClosed hGCH (b : Cut))
      hGCH.toCH (s.restrict start) G H hcompl M.toClique (traceFuture V M.toClique H a)
      (by rw [fullSuccessorRestriction_base hGCH b start]; exact hstatEarlier _ le_rfl)
      (fun p c hp z x hx => (hMgeometry p z x hx).1.trans hp.2.1)
      (fun p c hp => hp.2.2)
  obtain ⟨N, hN⟩ := exists_nice_clique_name
    ((Erdos1172Part3TransfiniteHechlerCentering.centered hGCH (b : Cut)).extend hGCH.toCH).omegaTwoCC
    sys.clique
  obtain ⟨q, hqstart, hq⟩ := s.lift start sys.start hsys
  refine ⟨a, q, hqstart.trans hstart, source.persistent hqstart hcut, pushClique s N, ?_, ?_, ?_⟩
  · intro p z x hx
    obtain ⟨oldIndex, hOld⟩ := hsysOrigin (s.restrict p) z x
      (hN (s.restrict p) z x ((pushClique_decides_iff s N p z x).mp hx))
    exact hMgeometry (s.restrict p).base oldIndex x hOld
  · intro p hpq z x hx
    obtain ⟨oldIndex, hOld⟩ := hsysOrigin (s.restrict p) z x
      (hN (s.restrict p) z x ((pushClique_decides_iff s N p z x).mp hx))
    have hps : (s.restrict p).base ≤ r.restrict start := by
      rw [fullSuccessorRestriction_base hGCH b p]
      exact r.restrict.monotone (hpq.trans hqstart)
    have hv := hMsource (s.restrict p).base hps oldIndex x hOld
    rw [fullSuccessorRestriction_base hGCH b p] at hv
    change (r.liftRegular V).holds p x at hv
    rwa [hV] at hv
  · have hs : StationaryAt (fun p c => sys.future (s.restrict p) c) q :=
      (s.stationary_lift_iff sys.future q).mpr (by rw [hq]; exact sys.stationary)
    intro p hpq
    apply (hs p hpq).mono
    rintro c ⟨t, htp, ht⟩
    have hc := hsysFuture (s.restrict t) c ht
    refine ⟨t, htp, ?_, hc.2.1, ?_⟩
    · have hv := hc.1
      rw [fullSuccessorRestriction_base hGCH b t] at hv
      change (r.liftRegular V).holds t c at hv
      rwa [hV] at hv
    · intro u hut z x hx
      exact sys.cross (s.restrict u) c (sys.persistent (s.restrict.monotone hut) ht) z x
        (hN (s.restrict u) z x ((pushClique_decides_iff s N u z x).mp hx))

end Erdos1172Part3FullStationaryCubes
