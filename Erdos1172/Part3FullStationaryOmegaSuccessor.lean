/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FullOrderedTraceLoss
public import Erdos1172.Part3StationaryOrderedThinning

@[expose] public section

/-!
# A stationary local core factory at omegaOne^(omega+1)

Hereditary ordered-small loss is extracted, localized exactly, and removed
at the actual Hechler successor. Cone globalization retains point geometry
everywhere, actual source membership on the starting cone, and a stationary
common red future. No stationary omega-successor factory is a hypothesis.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FullStationaryOmegaSuccessor

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3SparseIterationCarriers (Cut)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3TransfiniteHechlerSuccessorOrder
  (fullSuccessorRestriction fullSuccessorRestriction_base)
open Erdos1172Part3RegularMembership
open Erdos1172Part3NiceCliqueNames (exists_nice_clique_name)
open Erdos1172Part3CompleteRestrictionNames (pushClique pushClique_decides_iff)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3OmegaSuccessorCore (OmegaSuccessor mk_omegaSuccessor_le)
open Erdos1172Part3ExactOmegaIndex (typeLT_omegaSuccessor)
open Erdos1172Part3FullOrderedTraceLoss
  (traceFuture exists_global_ordered_trace_loss exists_ordered_trace_restriction)
open Erdos1172Part3FullRankedCoreReflection (LocalCoreFactory)
open OrdinalRamsey (HasCliqueOfType)

theorem omega_successor_factory (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    LocalCoreFactory hGCH OmegaSuccessor G := by
  intro source hsup hlocal p0 hstat
  obtain ⟨a, start, hstart, hcut, old, hgeometry, hsource, hfuture⟩ :=
    exists_global_ordered_trace_loss hGCH G H hcompl hred hblue source hsup hlocal p0 hstat
  obtain ⟨b, V, M, hV, hdec, hfutureEq⟩ :=
    exists_ordered_trace_restriction hGCH source hlocal old H a
  let r := restriction hGCH b
  let s := fullSuccessorRestriction hGCH b
  have hstatEarlier : StationaryAt (traceFuture V M.toClique H a).holds (r.restrict start) := by
    apply (r.stationary_lift_iff (traceFuture V M.toClique H a).holds start).mp
    change StationaryAt (r.liftRegular (traceFuture V M.toClique H a)).holds start
    rw [hfutureEq]
    exact hfuture
  have hMgeometry (p : Earlier hGCH b) (z : OmegaSuccessor) (x : W2)
      (hx : M.toClique.decides p z x) : x < a ∧ G.Adj x a :=
    hgeometry (r.embed p) z x ((hdec (r.embed p) z x).mpr (by rwa [r.restrict_embed]))
  have hMsource (p : Earlier hGCH b) (hp : p ≤ r.restrict start) (z : OmegaSuccessor)
      (x : W2) (hx : M.toClique.decides p z x) : V.holds p x := by
    obtain ⟨t, htstart, ht⟩ := r.lift start p hp
    have hactual := hsource t htstart z x ((hdec t z x).mpr (by rwa [ht]))
    have hVt : V.holds (r.restrict t) x := by
      change (r.liftRegular V).holds t x
      rw [hV]
      exact hactual
    rwa [ht] at hVt
  obtain ⟨selected, hselected, sys, hsysStart, hsysFuture, hsysOrigin⟩ :=
    Erdos1172Part3StationaryOrderedThinning.exists_stationary_clique_from_ordered_losses
      (Erdos1172Part3TransfiniteHechlerCentering.centered hGCH (b : Cut))
      (Erdos1172Part3TransfiniteHechlerClosure.countablyClosed hGCH (b : Cut))
      hGCH.toCH (s.restrict start) G H hcompl M.toClique mk_omegaSuccessor_le typeLT_omegaSuccessor
      (traceFuture V M.toClique H a)
      (by rw [fullSuccessorRestriction_base hGCH b start]; exact hstatEarlier _ le_rfl)
      (fun p c hp z x hx => (hMgeometry p z x hx).1.trans hp.2.1)
      (fun p c hp => hp.2.2)
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone
      (Erdos1172Part3IteratedHechlerClosure.countablyClosed
        (Erdos1172Part3TransfiniteHechlerClosure.countablyClosed hGCH (b : Cut)))
      selected sys.clique mk_omegaSuccessor_le
  obtain ⟨N, hN⟩ := exists_nice_clique_name
    ((Erdos1172Part3TransfiniteHechlerCentering.centered hGCH (b : Cut)).extend hGCH.toCH).omegaTwoCC
    global
  obtain ⟨q, hqstart, hq⟩ := s.lift start selected hselected
  have hrestrict (p : Full hGCH) (hpq : p ≤ q) : s.restrict p ≤ selected := by
    rw [← hq]
    exact s.restrict.monotone hpq
  refine ⟨a, q, hqstart.trans hstart, source.persistent hqstart hcut, pushClique s N, ?_, ?_, ?_⟩
  · intro p z x hx
    obtain ⟨t, ht⟩ := horigin (s.restrict p) z x
      (hN (s.restrict p) z x ((pushClique_decides_iff s N p z x).mp hx))
    obtain ⟨oldIndex, hOld⟩ := hsysOrigin t z x ht
    exact hMgeometry t.val.base oldIndex x hOld
  · intro p hpq z x hx
    let t : Iic selected := ⟨s.restrict p, hrestrict p hpq⟩
    have hsub : sys.clique.decides t z x :=
      (hbelow (s.restrict p) t.property z x).mp
        (hN (s.restrict p) z x ((pushClique_decides_iff s N p z x).mp hx))
    obtain ⟨oldIndex, hOld⟩ := hsysOrigin t z x hsub
    have hps : (s.restrict p).base ≤ r.restrict start := by
      rw [fullSuccessorRestriction_base hGCH b p]
      exact r.restrict.monotone (hpq.trans hqstart)
    have hv := hMsource (s.restrict p).base hps oldIndex x hOld
    rw [fullSuccessorRestriction_base hGCH b p] at hv
    change (r.liftRegular V).holds p x at hv
    rwa [hV] at hv
  · let future := fun t c => ∃ ht : t ≤ selected, sys.future ⟨t, ht⟩ c
    have hlocalStat : StationaryAt future selected := by
      intro p hps
      have hstat := sys.stationary
      rw [hsysStart] at hstat
      apply (hstat ⟨p, hps⟩ hps).mono
      rintro c ⟨t, htp, ht⟩
      exact ⟨t.val, htp, t.property, ht⟩
    have hs : StationaryAt (fun p c => future (s.restrict p) c) q :=
      (s.stationary_lift_iff future q).mpr (by rw [hq]; exact hlocalStat)
    intro p hpq
    apply (hs p hpq).mono
    rintro c ⟨t, htp, hts, ht⟩
    let t' : Iic selected := ⟨s.restrict t, hts⟩
    have hc := hsysFuture t' c ht
    refine ⟨t, htp, ?_, hc.2.1, ?_⟩
    · have hv := hc.1
      rw [fullSuccessorRestriction_base hGCH b t] at hv
      change (r.liftRegular V).holds t c at hv
      rwa [hV] at hv
    · intro u hut z x hx
      let u' : Iic selected := ⟨s.restrict u, (s.restrict.monotone hut).trans hts⟩
      have hu : sys.clique.decides u' z x :=
        (hbelow (s.restrict u) u'.property z x).mp
          (hN (s.restrict u) z x ((pushClique_decides_iff s N u z x).mp hx))
      exact sys.cross u' c (sys.persistent (s.restrict.monotone hut) ht) z x hu

end Erdos1172Part3FullStationaryOmegaSuccessor
