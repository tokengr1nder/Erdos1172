/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TraceCompleteRestriction
public import Erdos1172.Part3NamedCubeTraceBounds

@[expose] public section

/-!
# Reflecting any constructed stationary local core factory

An eventually local full-order source factory gives locally ranked
witnesses on a club. Actual failures are first pulled to an earlier
stage, then lifted to an eventually local source. This avoids assuming
that the globally ranked failure predicate itself has bounded support.
The cubic factory is supplied by its construction, not postulated.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FullRankedCoreReflection

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3SparseIterationCarriers (Cut)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3TransfiniteHechlerOrder (mk_stage_le)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularStageLocality (EventuallyLocal)
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RankedWitnessRestriction (rankedAvailability)
open Erdos1172Part3CompleteRestrictionNames (pullRegular lift_pull_implies)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3RegularNeighborhoodCode (Code eval rank blockRank)
open Erdos1172Part3RankedCoreBlockAssembly (GoodCoreCut)
open Erdos1172Part3FullSourceCubes (Cube)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open OrdinalRamsey (HasCliqueOfType)

noncomputable def coreFuture {P I : Type} [Preorder P] [LinearOrder I] {G : SimpleGraph W2}
    (source : RegularName P W2) (N : NiceCliqueName P I W2 G) (a : W2) : RegularName P W2 :=
  meet source (meet (ground {b | a < b}) (afterClique N.toClique))

def LocalCoreFactory (hGCH : GCH) (I : Type) [LinearOrder I] (G : SimpleGraph W2) : Prop :=
  ∀ source : RegularName (Full hGCH) W2,
    (∀ p a, source.holds p a → IsOmegaOneSup a) →
    EventuallyLocal (Earlier hGCH) (restriction hGCH) source →
    ∀ p0 : Full hGCH, StationaryAt source.holds p0 →
      ∃ a : W2, ∃ q : Full hGCH, q ≤ p0 ∧ source.holds q a ∧
        ∃ N : NiceCliqueName (Full hGCH) I W2 G,
          (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
          (∀ p : Full hGCH, p ≤ q → ∀ z x, N.toClique.decides p z x → source.holds p x) ∧
          StationaryAt (coreFuture source N a).holds q

theorem eventuallyLocal_lift (hGCH : GCH) (b : W2) (U : RegularName (Earlier hGCH b) W2) :
    EventuallyLocal (Earlier hGCH) (restriction hGCH) ((restriction hGCH b).liftRegular U) := by
  refine ⟨b, ?_⟩
  intro a hba
  let r := Erdos1172Part3TransfiniteHechlerRestrictions.complete hGCH (WithTop.coe_le_coe.mpr hba)
  refine ⟨r.liftRegular U, ?_⟩
  apply RegularName.ext
  intro p x
  change U.holds (Erdos1172Part3TransfiniteHechlerRestrictions.restrict hGCH (a := (b : Cut))
    (Erdos1172Part3TransfiniteHechlerRestrictions.restrict hGCH (a := (a : Cut)) p)) x ↔
    U.holds (Erdos1172Part3TransfiniteHechlerRestrictions.restrict hGCH (a := (b : Cut)) p) x
  rw [Erdos1172Part3TransfiniteHechlerRestrictions.restrict_restrict hGCH
    (WithTop.coe_le_coe.mpr hba) p]

variable {I : Type} [LinearOrder I]

theorem exists_club_local_cores (hGCH : GCH) (hI : #I ≤ ℵ_ 1) {G : SimpleGraph W2}
    (factory : LocalCoreFactory hGCH I G) (σ : NiceCliqueName (Full hGCH) I W2 G ↪ W2)
    (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ p : Full hGCH, source.holds p a →
      (rankedAvailability σ source).holds p a := by
  let B := meet source (neg (rankedAvailability σ source))
  let bad : Set W2 := {a | ∃ p : Full hGCH, B.holds p a}
  obtain ⟨readable, hreadable, hread⟩ :=
    Erdos1172Part3TransfiniteRankedFailures.club_reads_ranked_failure hGCH hI σ source hlocal
  have hnonstat : ¬IsStationary bad := by
    intro hbad
    obtain ⟨b, u, hu⟩ := Erdos1172Part3TransfinitePressingDown.exists_stationary_earlier_source
      hGCH B (fun p a hp => hsup p a hp.1) hbad readable hreadable hread
    let r := restriction hGCH b
    let lifted := r.liftRegular (pullRegular r B)
    have hstart : StationaryAt lifted.holds (r.embed u) :=
      (r.stationary_lift_iff (pullRegular r B).holds (r.embed u)).mpr (by rw [r.restrict_embed]; exact hu)
    obtain ⟨cut, q, _, _, N, hgeometry, hactual, hfuture⟩ := factory lifted
      (fun p a hp => hsup p a (lift_pull_implies r B p a hp).1)
      (eventuallyLocal_lift hGCH b (pullRegular r B)) (r.embed u) hstart
    obtain ⟨a, ⟨s, hsq, hs⟩, hlocalRank⟩ := (hfuture q le_rfl)
      (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 (σ N))
    have hBs : B.holds s a := lift_pull_implies r B s a hs.1
    apply hBs.2 s le_rfl
    apply Erdos1172Part3TransfiniteRankedFailures.availability_of_witness
    refine ⟨N, hlocalRank, ?_, ?_, hs.2.2⟩
    · intro t z x hx
      exact (hgeometry t z x hx).1.trans hs.2.1
    · intro t hts z x hx
      exact (lift_pull_implies r B t x (hactual t (hts.trans hsq) z x hx)).1
  obtain ⟨club, hclub, hdisjoint⟩ := not_isStationary_iff.mp hnonstat
  refine ⟨club, hclub, ?_⟩
  intro a ha p hp
  by_contra hnot
  obtain ⟨q, hqp, hq⟩ := (not_holds_iff_exists_neg (rankedAvailability σ source) p a).mp hnot
  exact Set.disjoint_left.mp hdisjoint ⟨q, source.persistent hqp hp, hq⟩ ha

theorem exists_club_local_core_family {C : Type} (hGCH : GCH) (hI : #I ≤ ℵ_ 1)
    {G : SimpleGraph W2} (factory : LocalCoreFactory hGCH I G)
    (r : C ↪ W2) (σ : NiceCliqueName (Full hGCH) I W2 G ↪ W2)
    (source : C → RegularName (Full hGCH) W2)
    (hsup : ∀ c p a, (source c).holds p a → IsOmegaOneSup a)
    (hlocal : ∀ c, EventuallyLocal (Earlier hGCH) (restriction hGCH) (source c)) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ c : C, r c < a →
      ∀ p : Full hGCH, (source c).holds p a → (rankedAvailability σ (source c)).holds p a := by
  classical
  choose clubs hclubs hcores using fun c =>
    exists_club_local_cores hGCH hI factory σ (source c) (hsup c) (hlocal c)
  let allClubs (a : W2) : Set W2 :=
    if h : ∃ c, r c = a then clubs h.choose else Set.univ
  have hallClubs (a : W2) : IsClub (allClubs a) := by
    dsimp only [allClubs]
    split_ifs with h
    · exact hclubs h.choose
    · exact IsClub.univ
  refine ⟨Set.diagonalInter allClubs,
    Erdos1172Part3TwoSuccessorBootstrap.isClub_diagonalInter allClubs hallClubs, ?_⟩
  intro a ha c hc p hp
  have hex : ∃ d, r d = r c := ⟨c, rfl⟩
  have heq : hex.choose = c := r.injective hex.choose_spec
  have hac : a ∈ clubs c := by
    simpa only [allClubs, dif_pos hex, heq] using ha (r c) hc
  exact hcores c a hac p hp

theorem exists_club_goodCoreCut (hGCH : GCH) (hI : #I ≤ ℵ_ 1)
    (G H : SimpleGraph W2) (factory : LocalCoreFactory hGCH I G)
    (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, IsOmegaOneSup a →
      GoodCoreCut (rank hGCH (mk_stage_le hGCH ⊤) hI G)
        (blockRank hGCH (mk_stage_le hGCH ⊤) hI G) H source a := by
  let r := rank hGCH (mk_stage_le hGCH ⊤) hI G
  let σ := blockRank hGCH (mk_stage_le hGCH ⊤) hI G
  obtain ⟨cg, hcg, hg⟩ := Erdos1172Part3RegularNeighborhoodCode.exists_club_goodCut
    hGCH.toCH (Erdos1172Part3TransfiniteHechlerCentering.omegaTwoCC hGCH ⊤) hI G H r σ source
  obtain ⟨cb, hcb, hb⟩ := exists_club_local_core_family hGCH hI factory r σ
    (fun c => meet source (eval G H c)) (fun _ p a hp => hsup p a hp.1)
    (fun c => Erdos1172Part3TransfiniteRankedFailures.eventuallyLocal_meet hGCH hlocal
      (Erdos1172Part3TransfiniteStageLocality.eventually_local_code hGCH G H hI c))
  refine ⟨cg ∩ cb, hcg.inter alephZero_lt_cof_W2.ne' hcb, ?_⟩
  intro a ha hsa
  exact ⟨hg a ha.1 hsa, fun c hc p hp he => hb a ha.2 c hc p ⟨hp, he⟩⟩

end Erdos1172Part3FullRankedCoreReflection
