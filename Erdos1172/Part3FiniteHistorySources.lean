/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CanonicalOmegaGluing
public import Erdos1172.Part3CountableFamilyRankClosure

@[expose] public section

/-!
# Locally ranked finite cores in finite-history sources

A history imposes the common-red future of each previously chosen block.
Only finite histories are reflected. Every finite output index uses its
already constructed stationary factory, and one club handles all indices.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3FiniteHistorySources

open ErdosRadoCHAsym (W2 IsOmegaOneSup)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3FiniteTraceSchemes (Index mk_index_le)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction eventually_local_code)
open Erdos1172Part3TransfiniteHechlerOrder (mk_stage_le)
open Erdos1172Part3TransfiniteRankedFailures (eventuallyLocal_meet)
open Erdos1172Part3RegularStageLocality (EventuallyLocal)
open Erdos1172Part3RankedWitnessRestriction (rankedAvailability)
open Erdos1172Part3RegularNeighborhoodCode (blockName eval_blockName)
open Erdos1172Part3FullRankedCoreReflection (exists_club_local_core_family)
open Erdos1172Part3FullStationaryFiniteCores (finite_factory)
open Erdos1172Part3CountableFamilyRankClosure (exists_club_binary_map)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open OrdinalRamsey (HasCliqueOfType)

abbrev AnyFiniteName (hGCH : GCH) (G : SimpleGraph W2) :=
  Σ n : ℕ, NiceCliqueName (Full hGCH) (Index n) W2 G

abbrev History (hGCH : GCH) (G : SimpleGraph W2) := List (AnyFiniteName hGCH G)

theorem mk_anyFiniteName_le (hGCH : GCH) (G : SimpleGraph W2) :
    #(AnyFiniteName hGCH G) ≤ ℵ_ 2 := by
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun n => #(NiceCliqueName (Full hGCH) (Index n) W2 G)) ≤
        Cardinal.sum (fun _ : ℕ => ℵ_ 2) := Cardinal.sum_le_sum _ _ (fun n =>
      Erdos1172Part3CliqueNameCoding.mk_nice_clique_name_le hGCH (mk_stage_le hGCH ⊤)
        (mk_index_le n) (by simp only [W2, Cardinal.mk_toType, Ordinal.card_omega, le_refl]) G)
    _ = ℵ₀ * ℵ_ 2 := by simp only [Cardinal.sum_const, Cardinal.mk_nat, Cardinal.lift_id]
    _ ≤ ℵ_ 2 := (mul_le_mul' (Cardinal.aleph0_le_aleph 2) le_rfl).trans_eq
      (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 2))

theorem mk_history_le (hGCH : GCH) (G : SimpleGraph W2) : #(History hGCH G) ≤ ℵ_ 2 :=
  (Cardinal.mk_list_le_max _).trans (max_le (Cardinal.aleph0_le_aleph 2) (mk_anyFiniteName_le hGCH G))

noncomputable def nameRank (hGCH : GCH) (G : SimpleGraph W2) : AnyFiniteName hGCH G ↪ W2 :=
  Classical.choice ((Cardinal.le_def _ _).mp (by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using mk_anyFiniteName_le hGCH G))

noncomputable def historyRank (hGCH : GCH) (G : SimpleGraph W2) : History hGCH G ↪ W2 :=
  Classical.choice ((Cardinal.le_def _ _).mp (by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using mk_history_le hGCH G))

noncomputable def rankAt (hGCH : GCH) (G : SimpleGraph W2) (n : ℕ) :
    NiceCliqueName (Full hGCH) (Index n) W2 G ↪ W2 where
  toFun N := nameRank hGCH G ⟨n, N⟩
  inj' := by
    intro N M h
    exact eq_of_heq (Sigma.mk.inj_iff.mp ((nameRank hGCH G).injective h)).2

noncomputable def historySource {hGCH : GCH} {G : SimpleGraph W2}
    (source : RegularName (Full hGCH) W2) : History hGCH G → RegularName (Full hGCH) W2
  | [] => source
  | N :: rest => meet (historySource source rest) (afterClique N.2.toClique)

theorem historySource_base {hGCH : GCH} {G : SimpleGraph W2}
    (source : RegularName (Full hGCH) W2) (history : History hGCH G)
    (p : Full hGCH) (a : W2) (hp : (historySource source history).holds p a) : source.holds p a := by
  induction history with
  | nil => exact hp
  | cons N rest ih => exact ih hp.1

theorem historySource_local {hGCH : GCH} {G : SimpleGraph W2}
    (source : RegularName (Full hGCH) W2)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) (history : History hGCH G) :
    EventuallyLocal (Earlier hGCH) (restriction hGCH) (historySource source history) := by
  induction history with
  | nil => exact hlocal
  | cons N rest ih =>
    apply eventuallyLocal_meet hGCH ih
    simpa only [eval_blockName] using eventually_local_code hGCH G G (mk_index_le N.1) (blockName N.2)

structure HistoryCut (hGCH : GCH) (G : SimpleGraph W2)
    (source : RegularName (Full hGCH) W2) (a : W2) : Prop where
  isOmegaOneSup : IsOmegaOneSup a
  empty_lt : historyRank hGCH G [] < a
  cons_lt : ∀ history N, historyRank hGCH G history < a → nameRank hGCH G N < a →
    historyRank hGCH G (N :: history) < a
  available : ∀ n history, historyRank hGCH G history < a → ∀ p : Full hGCH,
    (historySource source history).holds p a →
      (rankedAvailability (rankAt hGCH G n) (historySource source history)).holds p a

theorem exists_club_historyCut (hGCH : GCH) (G H : SimpleGraph W2)
    (hcompl : IsCompl G H) (hred : ¬HasCliqueOfType G (ω_ 2))
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) (source : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, source.holds p a → IsOmegaOneSup a)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, IsOmegaOneSup a → HistoryCut hGCH G source a := by
  classical
  choose clubs hclubs havail using fun n => exists_club_local_core_family hGCH (mk_index_le n)
    (finite_factory hGCH G H hcompl hred hblue n) (historyRank hGCH G) (rankAt hGCH G n)
    (historySource source) (fun history p a hp => hsup p a (historySource_base source history p a hp))
    (historySource_local source hlocal)
  obtain ⟨cc, hcc, hcons⟩ := exists_club_binary_map hGCH.toCH (historyRank hGCH G) (nameRank hGCH G)
    (fun history N => historyRank hGCH G (N :: history))
  let ci : Set W2 := Set.Ioi (historyRank hGCH G [])
  have hci : IsClub ci := Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 _
  have hi : IsClub (⋂ n, clubs n) := IsClub.iInter_of_countable alephZero_lt_cof_W2.ne' hclubs
  refine ⟨ci ∩ (cc ∩ ⋂ n, clubs n), hci.inter alephZero_lt_cof_W2.ne'
    (hcc.inter alephZero_lt_cof_W2.ne' hi), ?_⟩
  intro a ha hsa
  exact ⟨hsa, ha.1, hcons a ha.2.1 hsa, fun n => havail n a (Set.mem_iInter.mp ha.2.2 n)⟩

end Erdos1172Part3FiniteHistorySources
