/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteHechlerSuccessorOrder
public import Erdos1172.Part3StationaryNamedSourceSquare

@[expose] public section

/-!
# Earlier-function domination and stationary squares in the full order

These applications use the actual successor order isomorphisms and exact
full-order lifting. They verify that the existing named Hechler tools run
inside the constructed omegaTwo tower, retaining source membership and
stationary common-red futures. The square target is still omegaOne
squared; the higher-core reflection and recursion are not asserted here.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FullHechlerConsequences

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3SparseIterationCarriers (Cut)
open Erdos1172Part3SparseIterationUnions (stemAt)
open Erdos1172Part3TransfiniteHechlerOrder (mk_stage_le)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3TransfiniteHechlerSuccessorOrder
open Erdos1172Part3FunctionDecisions (FunctionDecisions BoundedAt)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3CompleteRestrictionNames (pushClique pushClique_decides_iff pushClique_after_iff)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3StationarySquareDecisions (Square)
open OrdinalRamsey (HasCliqueOfType)

theorem bounds_earlier_function (hGCH : GCH) (i : W2) (p0 : Full hGCH)
    (F : FunctionDecisions (Earlier hGCH i) W1 W1) :
    ∃ q : Full hGCH, q ≤ p0 ∧ ∃ bound : W1,
      ∀ r : Full hGCH, r ≤ q → ∀ j : W1, bound < j → ∀ v : W1,
        (stemAt r i).val j = some v → BoundedAt F ((restriction hGCH i).restrict r) j v := by
  let r := fullSuccessorRestriction hGCH i
  obtain ⟨t, htp, bound, hb⟩ :=
    Erdos1172Part3IteratedHechlerClosure.exists_eventual_bound_for_function
      (Erdos1172Part3TransfiniteHechlerCentering.omegaTwoCC hGCH (i : Cut)) (r.restrict p0) F
  obtain ⟨q, hqp, hq⟩ := r.lift p0 t htp
  refine ⟨q, hqp, bound, ?_⟩
  intro s hsq j hj v hv
  have hst : r.restrict s ≤ t := by
    have h := r.restrict.monotone hsq
    rwa [hq] at h
  have hsv : (r.restrict s).stem j = some v := by
    rw [fullSuccessorRestriction_stem hGCH i s]
    exact hv
  have h := hb (r.restrict s) hst j hj v hsv
  rwa [fullSuccessorRestriction_base hGCH i s] at h

noncomputable def fullSquareFuture (hGCH : GCH) (i : W2) {G : SimpleGraph W2}
    (source : RegularName (Earlier hGCH i) W2)
    (N : NiceCliqueName (Full hGCH) Square W2 G) (a : W2) : RegularName (Full hGCH) W2 :=
  meet ((restriction hGCH i).liftRegular source)
    (meet (ground {b | a < b}) (afterClique N.toClique))

theorem stationary_source_square (hGCH : GCH) (i : W2)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName (Earlier hGCH i) W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a)
    (p0 : Full hGCH) (hstat : StationaryAt source.holds ((restriction hGCH i).restrict p0)) :
    ∃ a : W2, ∃ q : Full hGCH, q ≤ p0 ∧ source.holds ((restriction hGCH i).restrict q) a ∧
      ∃ N : NiceCliqueName (Full hGCH) Square W2 G,
        (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
        (∀ p : Full hGCH, p ≤ q → ∀ z x, N.toClique.decides p z x →
          source.holds ((restriction hGCH i).restrict p) x) ∧
        StationaryAt (fullSquareFuture hGCH i source N a).holds q := by
  let r := fullSuccessorRestriction hGCH i
  have hstat' : StationaryAt source.holds (r.restrict p0).base := by
    rwa [fullSuccessorRestriction_base hGCH i p0]
  obtain ⟨a, t, htp, hta, N, hgeometry, hsource, hfuture⟩ :=
    Erdos1172Part3StationaryNamedSourceSquare.exists_stationary_named_source_square
      hGCH (mk_stage_le hGCH (i : Cut))
      (Erdos1172Part3TransfiniteHechlerClosure.countablyClosed hGCH (i : Cut))
      (Erdos1172Part3TransfiniteHechlerCentering.centered hGCH (i : Cut))
      G H hcompl hred hblue source hsup (r.restrict p0) hstat'
  obtain ⟨q, hqp, hq⟩ := r.lift p0 t htp
  refine ⟨a, q, hqp, ?_, pushClique r N, ?_, ?_, ?_⟩
  · rw [← fullSuccessorRestriction_base hGCH i q, hq]
    exact hta
  · intro p z x hx
    exact hgeometry (r.restrict p) z x ((pushClique_decides_iff r N p z x).mp hx)
  · intro p hpq z x hx
    have hpt : r.restrict p ≤ t := by
      have h := r.restrict.monotone hpq
      rwa [hq] at h
    have hs := hsource (r.restrict p) hpt z x ((pushClique_decides_iff r N p z x).mp hx)
    rwa [fullSuccessorRestriction_base hGCH i p] at hs
  · have hf := (r.stationary_lift_iff
      (Erdos1172Part3StationaryNamedSourceSquare.squareRedFuture source N a).holds q).mpr
        (by rwa [hq])
    have heq : (fun p b =>
        (Erdos1172Part3StationaryNamedSourceSquare.squareRedFuture source N a).holds
          (r.restrict p) b) = (fullSquareFuture hGCH i source (pushClique r N) a).holds := by
      funext p b
      apply propext
      change (source.holds (r.restrict p).base b ∧ a < b ∧
        (afterClique N.toClique).holds (r.restrict p) b) ↔
          (source.holds ((restriction hGCH i).restrict p) b ∧ a < b ∧
            (afterClique (pushClique r N).toClique).holds p b)
      rw [fullSuccessorRestriction_base hGCH i p, pushClique_after_iff r N p b]
    rwa [heq] at hf

end Erdos1172Part3FullHechlerConsequences
