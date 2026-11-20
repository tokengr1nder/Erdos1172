/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RankedCoreBlockAssembly

@[expose] public section

/-!
# Cubic source cores in the full transfinite order

The constructed local square witnesses supply whole square blocks in
every locally coded neighborhood. Fusion assembles omegaOne such blocks
into a cubic core. The source remains an actual regular-name membership
requirement, and the endpoint bounds every possible decided vertex.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FullSourceCubes

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction)
open Erdos1172Part3TransfiniteHechlerOrder (mk_stage_le)
open Erdos1172Part3TransfiniteHechlerCentering (omegaTwoCC)
open Erdos1172Part3TransfiniteHechlerClosure (full_countablyClosed)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3CliqueNameCoding (mk_square_le)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularStageLocality (EventuallyLocal eventuallyLocal_ground)
open Erdos1172Part3RegularNeighborhoodCode (Code eval rank blockRank)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RankedCoreBlockAssembly
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open OrdinalRamsey (HasCliqueOfType)

abbrev Cube := W1 ×ₗ Square

theorem mk_cube_le : #Cube ≤ ℵ_ 1 := mk_product_le mk_square_le

theorem typeLT_cube : typeLT Cube = (ω_ 1) ^ (3 : Ordinal.{0}) := by
  change Ordinal.type (Prod.Lex ((· < ·) : W1 → W1 → Prop)
    ((· < ·) : Square → Square → Prop)) = _
  rw [Ordinal.type_prod_lex]
  change (typeLT Square) * (typeLT W1) = _
  rw [Erdos1172Part3SquareLossBounds.typeLT_square]
  change (ω_ 1) ^ (2 : Ordinal.{0}) * (typeLT (ω_ 1).ToType) = _
  rw [Ordinal.type_toType]
  rw [show (3 : Ordinal.{0}) = 2 + 1 by norm_num, Ordinal.opow_add_one]

theorem exists_club_goodSquareCut (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, IsOmegaOneSup a →
      GoodCoreCut (rank hGCH (mk_stage_le hGCH ⊤) mk_square_le G)
        (blockRank hGCH (mk_stage_le hGCH ⊤) mk_square_le G) H source a := by
  let r := rank hGCH (mk_stage_le hGCH ⊤) mk_square_le G
  let σ := blockRank hGCH (mk_stage_le hGCH ⊤) mk_square_le G
  obtain ⟨cg, hcg, hg⟩ := Erdos1172Part3RegularNeighborhoodCode.exists_club_goodCut
    hGCH.toCH (omegaTwoCC hGCH ⊤) mk_square_le G H r σ source
  obtain ⟨cb, hcb, hb⟩ := Erdos1172Part3LocalSquareReflection.exists_club_local_square_family
    hGCH G H hcompl hred hblue r σ (fun c => meet source (eval G H c))
    (fun _ p a hp => hsup p a hp.1)
    (fun c => Erdos1172Part3TransfiniteRankedFailures.eventuallyLocal_meet hGCH hlocal
      (Erdos1172Part3TransfiniteStageLocality.eventually_local_code hGCH G H mk_square_le c))
  refine ⟨cg ∩ cb, hcg.inter alephZero_lt_cof_W2.ne' hcb, ?_⟩
  intro a ha hsa
  exact ⟨hg a ha.1 hsa, fun c hc p hp he => hb a ha.2 c hc p ⟨hp, he⟩⟩

theorem exists_club_source_cubes (hGCH : GCH)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ p0 : Full hGCH,
      source.holds p0 a → ∃ N : NiceCliqueName (Full hGCH) Cube W2 G,
        (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
        (∀ p : Full hGCH, p ≤ p0 → ∀ z x,
          N.toClique.decides p z x → source.holds p x) := by
  obtain ⟨club, hclub, hc⟩ := exists_club_goodSquareCut hGCH G H hcompl hred hblue
    source hsup hlocal
  refine ⟨club, hclub, ?_⟩
  intro a ha p0 hp0
  exact exists_nice_source_product (full_countablyClosed hGCH) (omegaTwoCC hGCH ⊤)
    mk_square_le (hc a ha (hsup p0 a hp0)) p0 hp0

theorem exists_ground_cube (hGCH : GCH) (G H : SimpleGraph W2)
    (hcompl : IsCompl G H) (hred : ¬HasCliqueOfType G (ω_ 2))
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    HasCliqueOfType G ((ω_ 1) ^ (3 : Ordinal.{0})) := by
  let source : RegularName (Full hGCH) W2 := ground {a : W2 | IsOmegaOneSup a}
  obtain ⟨club, hclub, hc⟩ := exists_club_source_cubes hGCH G H hcompl hred hblue source
    (fun _ _ hp => hp) (eventuallyLocal_ground (Earlier hGCH) (restriction hGCH) _)
  obtain ⟨a, ha, hac⟩ := ErdosRadoCHAsym.isStationary_isOmegaOneSup_omegaTwo hclub
  let p0 : Full hGCH := default
  obtain ⟨N, _, _⟩ := hc a hac p0 ha
  obtain ⟨C, hC, ht⟩ := N.toClique.exists_clique_type (full_countablyClosed hGCH) p0 mk_cube_le
  exact ⟨C, hC, ht.trans typeLT_cube⟩

end Erdos1172Part3FullSourceCubes
