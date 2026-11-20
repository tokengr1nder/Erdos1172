/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3LocallyRankedOmegaTower

@[expose] public section

/-!
# Local omega-core availability from finite factories and countable gluing

The output name is canonically determined by its countable sequence of
finite names. Countable rank closure therefore keeps its rank below the
cut, independently of the starting condition. This proves local omega
availability directly, without a stationary omega-core factory premise.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3LocalOmegaReflection

open ErdosRadoCHAsym (W2 IsOmegaOneSup)
open Erdos1172Part3RegularMembership
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3TransfiniteHechlerOrder (mk_stage_le)
open Erdos1172Part3RegularStageLocality (EventuallyLocal)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RankedWitnessRestriction (rankedAvailability)
open Erdos1172Part3OmegaPowerIndex (OmegaIndex mk_omegaIndex_le)
open Erdos1172Part3FiniteHistorySources (rankAt exists_club_historyCut)
open Erdos1172Part3CanonicalOmegaGluing (glue? exists_glue_some)
open Erdos1172Part3LocallyRankedOmegaTower (exists_ranked_tower)
open Erdos1172Part3CountableFamilyRankClosure (exists_club_partial_countable_map)
open Erdos1172Part3RegularNeighborhoodCode (rank blockRank eval)
open Erdos1172Part3RankedCoreBlockAssembly (GoodCoreCut)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open OrdinalRamsey (HasCliqueOfType)

theorem exists_club_local_omega_cores (hGCH : GCH) (G H : SimpleGraph W2)
    (hcompl : IsCompl G H) (hred : ¬HasCliqueOfType G (ω_ 2))
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (σ : NiceCliqueName (Full hGCH) OmegaIndex W2 G ↪ W2)
    (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ p : Full hGCH, source.holds p a →
      (rankedAvailability σ source).holds p a := by
  let hclosed := Erdos1172Part3TransfiniteHechlerClosure.full_countablyClosed hGCH
  let hcc := Erdos1172Part3TransfiniteHechlerCentering.omegaTwoCC hGCH ⊤
  obtain ⟨ct, hct, hhist⟩ := exists_club_historyCut hGCH G H hcompl hred hblue source hsup hlocal
  obtain ⟨cg, hcg, hglue⟩ := exists_club_partial_countable_map hGCH.toCH (rankAt hGCH G)
    σ (glue? hclosed hcc)
  refine ⟨ct ∩ cg, hct.inter alephZero_lt_cof_W2.ne' hcg, ?_⟩
  intro a ha p hp q hqp
  have hsa := hsup p a hp
  obtain ⟨tower, htower⟩ := exists_ranked_tower (hhist a ha.1 hsa) q (source.persistent hqp hp)
  obtain ⟨N, hN, hspec⟩ := exists_glue_some hclosed hcc tower.names ⟨tower.start, tower.joined⟩
  exact ⟨tower.start, htower,
    hspec.rankedWitness σ source (hglue a ha.2 hsa tower.names tower.rank_lt N hN)
      tower.joined tower.geometry tower.points tower.future⟩

theorem exists_club_local_omega_family {C : Type} (hGCH : GCH) (G H : SimpleGraph W2)
    (hcompl : IsCompl G H) (hred : ¬HasCliqueOfType G (ω_ 2))
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) (r : C ↪ W2)
    (σ : NiceCliqueName (Full hGCH) OmegaIndex W2 G ↪ W2)
    (source : C → RegularName (Full hGCH) W2)
    (hsup : ∀ c p a, (source c).holds p a → IsOmegaOneSup a)
    (hlocal : ∀ c, EventuallyLocal (Earlier hGCH) (restriction hGCH) (source c)) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ c : C, r c < a →
      ∀ p : Full hGCH, (source c).holds p a → (rankedAvailability σ (source c)).holds p a := by
  classical
  choose clubs hclubs hcores using fun c =>
    exists_club_local_omega_cores hGCH G H hcompl hred hblue σ (source c) (hsup c) (hlocal c)
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

theorem exists_club_goodOmegaCut (hGCH : GCH) (G H : SimpleGraph W2)
    (hcompl : IsCompl G H) (hred : ¬HasCliqueOfType G (ω_ 2))
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, IsOmegaOneSup a →
      GoodCoreCut (rank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G)
        (blockRank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G) H source a := by
  let r := rank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G
  let σ := blockRank hGCH (mk_stage_le hGCH ⊤) mk_omegaIndex_le G
  obtain ⟨cg, hcg, hg⟩ := Erdos1172Part3RegularNeighborhoodCode.exists_club_goodCut
    hGCH.toCH (Erdos1172Part3TransfiniteHechlerCentering.omegaTwoCC hGCH ⊤) mk_omegaIndex_le G H r σ source
  obtain ⟨cb, hcb, hb⟩ := exists_club_local_omega_family hGCH G H hcompl hred hblue r σ
    (fun c => meet source (eval G H c)) (fun _ p a hp => hsup p a hp.1)
    (fun c => Erdos1172Part3TransfiniteRankedFailures.eventuallyLocal_meet hGCH hlocal
      (Erdos1172Part3TransfiniteStageLocality.eventually_local_code hGCH G H mk_omegaIndex_le c))
  refine ⟨cg ∩ cb, hcg.inter alephZero_lt_cof_W2.ne' hcb, ?_⟩
  intro a ha hsa
  exact ⟨hg a ha.1 hsa, fun c hc p hp he => hb a ha.2 c hc p ⟨hp, he⟩⟩

end Erdos1172Part3LocalOmegaReflection
