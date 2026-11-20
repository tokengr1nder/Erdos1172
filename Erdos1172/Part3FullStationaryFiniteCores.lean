/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FullFiniteTraceLoss

@[expose] public section

/-!
# Constructed stationary source factories at every finite power

The successor step uses exact earlier-stage localization and finite
thinning at that stage's actual Hechler successor. Induction begins
with the already proved one-dimensional stationary red source theorem.
No factory is left as a hypothesis in the finite-depth conclusion.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FullStationaryFiniteCores

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3SparseIterationCarriers (Cut)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3TransfiniteHechlerSuccessorOrder (fullSuccessorRestriction fullSuccessorRestriction_base)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3NiceCliqueNames (exists_nice_clique_name)
open Erdos1172Part3CompleteRestrictionNames (pushClique pushClique_decides_iff)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3FiniteTraceSchemes (Index)
open Erdos1172Part3FullFiniteTraceLoss (traceFuture exists_global_finite_trace_loss exists_finite_trace_restriction)
open Erdos1172Part3FullRankedCoreReflection (LocalCoreFactory coreFuture)
open OrdinalRamsey (HasCliqueOfType)

theorem factory_succ (n : ℕ) (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (factory : LocalCoreFactory hGCH (Index n) G) : LocalCoreFactory hGCH (Index (n + 1)) G := by
  intro source hsup hlocal p0 hstat
  obtain ⟨a, start, hstart, hcut, old, hgeometry, hsource, hfuture⟩ :=
    exists_global_finite_trace_loss n hGCH G H hcompl hred hblue factory source hsup hlocal p0 hstat
  obtain ⟨b, V, M, hV, hdec, hfutureEq⟩ :=
    exists_finite_trace_restriction (n + 1) hGCH source hlocal old H a
  let r := restriction hGCH b
  let s := fullSuccessorRestriction hGCH b
  have hstatEarlier : StationaryAt (traceFuture (n + 1) V M.toClique H a).holds (r.restrict start) := by
    apply (r.stationary_lift_iff (traceFuture (n + 1) V M.toClique H a).holds start).mp
    change StationaryAt (r.liftRegular (traceFuture (n + 1) V M.toClique H a)).holds start
    rw [hfutureEq]
    exact hfuture
  have hMgeometry (p : Earlier hGCH b) (z : Index (n + 1)) (x : W2) (hx : M.toClique.decides p z x) :
      x < a ∧ G.Adj x a := hgeometry (r.embed p) z x
        ((hdec (r.embed p) z x).mpr (by rwa [r.restrict_embed]))
  have hMsource (p : Earlier hGCH b) (hp : p ≤ r.restrict start) (z : Index (n + 1)) (x : W2)
      (hx : M.toClique.decides p z x) : V.holds p x := by
    obtain ⟨t, htstart, ht⟩ := r.lift start p hp
    have hactual := hsource t htstart z x ((hdec t z x).mpr (by rwa [ht]))
    have hVt : V.holds (r.restrict t) x := by
      change (r.liftRegular V).holds t x
      rw [hV]
      exact hactual
    rwa [ht] at hVt
  obtain ⟨sys, hsys, hsysFuture, hsysOrigin⟩ :=
    Erdos1172Part3StationaryFiniteThinning.exists_stationary_finite_from_trace_losses n
      (Erdos1172Part3TransfiniteHechlerCentering.centered hGCH (b : Cut))
      (Erdos1172Part3TransfiniteHechlerClosure.countablyClosed hGCH (b : Cut))
      hGCH.toCH (s.restrict start) G H hcompl M.toClique (traceFuture (n + 1) V M.toClique H a)
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

theorem finite_factory (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (n : ℕ) : LocalCoreFactory hGCH (Index n) G := by
  induction n with
  | zero =>
    intro source hsup hlocal p0 hstat
    exact Erdos1172Part3NamedStationaryRedBlock.exists_stationary_named_red_block hGCH
      (Erdos1172Part3TransfiniteHechlerOrder.mk_stage_le hGCH ⊤)
      (Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH)
      (Erdos1172Part3TransfiniteHechlerCentering.centered hGCH ⊤)
      G H hcompl hred hblue source hsup p0 hstat
  | succ n ih => exact factory_succ n hGCH G H hcompl hred hblue ih

end Erdos1172Part3FullStationaryFiniteCores
