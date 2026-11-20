/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteRankedFailures

@[expose] public section

/-!
# Locally ranked square witnesses in the full iteration

A stationary set of actual ranked failures presses down to one earlier
stage. Its pulled-back source has a constructed stationary square in the
full order. A late actual common-red endpoint has a rank cutoff allowing
that same square, contradicting the supposed failure. Thus local square
availability holds on a club, and a diagonal club treats all locally
coded sources at once. No higher ordinal target is substituted for or
claimed to equal this square target.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3LocalSquareReflection

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3TransfinitePressingDown
open Erdos1172Part3TransfiniteRankedFailures
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularStageLocality (EventuallyLocal)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RankedWitnessRestriction (RankedWitness rankedAvailability)
open Erdos1172Part3CompleteRestrictionNames (pullRegular lift_pull_implies)
open Erdos1172Part3StationaryDecisions (StationaryAt)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open Erdos1172Part3TwoSuccessorBootstrap (isClub_diagonalInter)
open Erdos1172Part3RegularNeighborhoodCode (Code eval rank blockRank)
open Erdos1172Part3TransfiniteHechlerOrder (mk_stage_le)
open Erdos1172Part3CliqueNameCoding (mk_square_le)
open OrdinalRamsey (HasCliqueOfType)

theorem exists_club_local_squares (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (σ : NiceCliqueName (Full hGCH) Square W2 G ↪ W2)
    (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ p : Full hGCH, source.holds p a →
      (rankedAvailability σ source).holds p a := by
  let B := meet source (neg (rankedAvailability σ source))
  let bad : Set W2 := {a | ∃ p : Full hGCH, B.holds p a}
  obtain ⟨readable, hreadable, hread⟩ := club_reads_ranked_failure hGCH mk_square_le σ source hlocal
  have hnonstat : ¬IsStationary bad := by
    intro hbad
    obtain ⟨b, u, hu⟩ := exists_stationary_earlier_source hGCH B
      (fun p a hp => hsup p a hp.1) hbad readable hreadable hread
    let earlierSource := pullRegular (restriction hGCH b) B
    have hstart : StationaryAt earlierSource.holds
        ((restriction hGCH b).restrict ((restriction hGCH b).embed u)) := by
      rw [(restriction hGCH b).restrict_embed]
      exact hu
    obtain ⟨cut, q, hqp, hcut, N, hgeometry, hactual, hfuture⟩ :=
      Erdos1172Part3FullHechlerConsequences.stationary_source_square hGCH b G H hcompl hred hblue
        earlierSource (fun p a hp => hsup ((restriction hGCH b).embed p) a hp.1)
        ((restriction hGCH b).embed u) hstart
    obtain ⟨a, ⟨s, hsq, hs⟩, hlocalRank⟩ := (hfuture q le_rfl)
      (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 (σ N))
    have hBs : B.holds s a := lift_pull_implies (restriction hGCH b) B s a hs.1
    apply hBs.2 s le_rfl
    apply availability_of_witness
    refine ⟨N, hlocalRank, ?_, ?_, hs.2.2⟩
    · intro t z x hx
      exact (hgeometry t z x hx).1.trans hs.2.1
    · intro t hts z x hx
      exact (lift_pull_implies (restriction hGCH b) B t x
        (hactual t (hts.trans hsq) z x hx)).1
  obtain ⟨club, hclub, hdisjoint⟩ := not_isStationary_iff.mp hnonstat
  refine ⟨club, hclub, ?_⟩
  intro a ha p hp
  by_contra hnot
  obtain ⟨q, hqp, hq⟩ := (not_holds_iff_exists_neg (rankedAvailability σ source) p a).mp hnot
  exact Set.disjoint_left.mp hdisjoint ⟨q, source.persistent hqp hp, hq⟩ ha

theorem exists_club_local_square_family {C : Type} (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (r : C ↪ W2) (σ : NiceCliqueName (Full hGCH) Square W2 G ↪ W2)
    (source : C → RegularName (Full hGCH) W2)
    (hsup : ∀ c p a, (source c).holds p a → IsOmegaOneSup a)
    (hlocal : ∀ c, EventuallyLocal (Earlier hGCH) (restriction hGCH) (source c)) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ c : C, r c < a →
      ∀ p : Full hGCH, (source c).holds p a → (rankedAvailability σ (source c)).holds p a := by
  classical
  choose clubs hclubs hlocalSquare using fun c =>
    exists_club_local_squares hGCH G H hcompl hred hblue σ (source c) (hsup c) (hlocal c)
  let allClubs (a : W2) : Set W2 :=
    if h : ∃ c, r c = a then clubs h.choose else Set.univ
  have hallClubs (a : W2) : IsClub (allClubs a) := by
    dsimp only [allClubs]
    split_ifs with h
    · exact hclubs h.choose
    · exact IsClub.univ
  refine ⟨Set.diagonalInter allClubs, isClub_diagonalInter allClubs hallClubs, ?_⟩
  intro a ha c hc p hp
  have hex : ∃ d, r d = r c := ⟨c, rfl⟩
  have heq : hex.choose = c := r.injective hex.choose_spec
  have hac : a ∈ clubs c := by
    simpa only [allClubs, dif_pos hex, heq] using ha (r c) hc
  exact hlocalSquare c a hac p hp

noncomputable def guardedCode (hGCH : GCH) (G H : SimpleGraph W2)
    (c : Code (Full hGCH) Square G) :
    RegularName (Full hGCH) W2 := meet (ground {a : W2 | IsOmegaOneSup a}) (eval G H c)

/-- The stage system, ranks, source family, and source-locality premise
are all supplied by their constructed definitions. -/
theorem exists_club_guarded_code_squares (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ c : Code (Full hGCH) Square G,
      rank hGCH (mk_stage_le hGCH ⊤) mk_square_le G c < a →
        ∀ p : Full hGCH, (guardedCode hGCH G H c).holds p a →
          (rankedAvailability (blockRank hGCH (mk_stage_le hGCH ⊤) mk_square_le G)
            (guardedCode hGCH G H c)).holds p a :=
  exists_club_local_square_family hGCH G H hcompl hred hblue
    (rank hGCH (mk_stage_le hGCH ⊤) mk_square_le G)
    (blockRank hGCH (mk_stage_le hGCH ⊤) mk_square_le G) (guardedCode hGCH G H)
    (fun _ _ _ hp => hp.1) (eventually_local_guarded_code hGCH G H mk_square_le)

end Erdos1172Part3LocalSquareReflection
