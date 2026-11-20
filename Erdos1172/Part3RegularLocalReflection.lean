/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularLocalBlock

@[expose] public section

/-!
# Local red-block reflection for arbitrary regular sources

An alleged stationary family of actual failures is itself a regular
source. Its constructed stationary red block has a sufficiently late
actual common-red point, contradicting failure there. A diagonal club
then handles every locally coded source simultaneously, with no bound
on the code of the starting condition.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RegularLocalReflection

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularLocalBlock
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3StationaryDecisions (exists_stationary_condition)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open Erdos1172Part3TwoSuccessorBootstrap (isClub_diagonalInter)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P]

theorem exists_club_local_blocks (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (σ : NiceCliqueName P W1 W2 G ↪ W2) (source : RegularName P W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ p : P, source.holds p a →
      (localBlockName σ source).holds p a := by
  let B := meet source (neg (localBlockName σ source))
  let bad : Set W2 := {a | ∃ p : P, B.holds p a}
  have hnonstat : ¬IsStationary bad := by
    intro hbad
    obtain ⟨p, hp⟩ := exists_stationary_condition center.omegaTwoCC B.holds
      (fun hqp h => B.persistent hqp h) hbad
    obtain ⟨cut, q, hqp, hcut, N, hgeometry, hactual, hfuture⟩ :=
      Erdos1172Part3NamedStationaryRedBlock.exists_stationary_named_red_block
        hGCH hP hclosed center G H hcompl hred hblue B
        (fun p a ha => hsup p a ha.1) p hp
    obtain ⟨a, ⟨s, hsq, hs⟩, hlocal⟩ := (hfuture q le_rfl)
      (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 (σ N))
    apply hs.1.2 s le_rfl
    apply localBlock_of_witness
    refine ⟨N, hlocal, ?_, ?_, hs.2.2⟩
    · intro t i x hx
      exact (hgeometry t i x hx).1.trans hs.2.1
    · intro t hts i x hx
      exact (hactual t (hts.trans hsq) i x hx).1
  obtain ⟨club, hclub, hdisjoint⟩ := not_isStationary_iff.mp hnonstat
  refine ⟨club, hclub, ?_⟩
  intro a hac p hsource
  by_contra hnot
  obtain ⟨q, hqp, hq⟩ := (not_holds_iff_exists_neg (localBlockName σ source) p a).mp hnot
  exact Set.disjoint_left.mp hdisjoint ⟨q, source.persistent hqp hsource, hq⟩ hac

theorem exists_club_local_block_family {C : Type} (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (r : C ↪ W2) (σ : NiceCliqueName P W1 W2 G ↪ W2) (source : C → RegularName P W2)
    (hsup : ∀ c p a, (source c).holds p a → ErdosRadoCHAsym.IsOmegaOneSup a) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ c : C, r c < a →
      ∀ p : P, (source c).holds p a → (localBlockName σ (source c)).holds p a := by
  classical
  choose clubs hclubs hlocal using fun c => exists_club_local_blocks hGCH hP hclosed center
    G H hcompl hred hblue σ (source c) (hsup c)
  let allClubs (a : W2) : Set W2 :=
    if h : ∃ c, r c = a then clubs h.choose else Set.univ
  have hallClubs (a : W2) : IsClub (allClubs a) := by
    dsimp only [allClubs]
    split_ifs with h
    · exact hclubs h.choose
    · exact IsClub.univ
  refine ⟨Set.diagonalInter allClubs, isClub_diagonalInter allClubs hallClubs, ?_⟩
  intro a ha c hc p hp
  have h : ∃ d, r d = r c := ⟨c, rfl⟩
  have heq : h.choose = c := r.injective h.choose_spec
  have hac : a ∈ clubs c := by
    simpa only [allClubs, dif_pos h, heq] using ha (r c) hc
  exact hlocal c a hac p hp

end Erdos1172Part3RegularLocalReflection
