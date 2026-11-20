/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteHechlerCentering
public import Erdos1172.Part3RankedWitnessRestriction

@[expose] public section

/-!
# Locality in the actual omegaTwo iteration

The stage-system and bounded-support inclusion premises of the generic
locality theorems are discharged here by the constructed sparse orders.
Small names eventually restrict with exactly the same decisions, and
ranked availability tests (including their negations) are readable at
earlier stages on a club. This is locality, not existence of the requested
higher-core witnesses.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3TransfiniteStageLocality

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3CountableSupportProfiles (support)
open Erdos1172Part3SparseIterationCarriers
open Erdos1172Part3TransfiniteHechlerOrder
open Erdos1172Part3TransfiniteHechlerRestrictions (complete complete_range_iff extend)
open Erdos1172Part3CompleteRestriction (CompleteRestriction)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RegularMembership (RegularName neg)
open Erdos1172Part3RegularNeighborhoodCode (Code eval rank blockRank)
open Erdos1172Part3RankedWitnessRestriction (rankedAvailability)

abbrev Full (hGCH : GCH) := Stage hGCH ⊤

abbrev Earlier (hGCH : GCH) (a : W2) := Stage hGCH (a : Cut)

noncomputable def restriction (hGCH : GCH) (a : W2) :
    CompleteRestriction (Full hGCH) (Earlier hGCH a) := complete hGCH le_top

def conditionSupport (hGCH : GCH) (p : Full hGCH) : Set W2 := support p.val

theorem support_countable (hGCH : GCH) (p : Full hGCH) :
    (conditionSupport hGCH p).Countable := p.val.property

theorem bounded_support_in_range (hGCH : GCH) (a : W2) (p : Full hGCH)
    (hp : ∀ b ∈ conditionSupport hGCH p, b < a) :
    p ∈ Set.range (restriction hGCH a).embed := by
  apply (complete_range_iff hGCH le_top p).mpr
  intro i hi
  exact WithTop.coe_lt_coe.mpr (hp i hi)

theorem full_condition_bounded (hGCH : GCH) (p : Full hGCH) :
    ∃ a : W2, ∃ q : Earlier hGCH a, (restriction hGCH a).embed q = p := by
  obtain ⟨a, ha⟩ := Erdos1172Part3CoreObjectCode.exists_objectBound
    ⟨conditionSupport hGCH p,
      (Cardinal.le_aleph0_iff_set_countable.mpr (support_countable hGCH p)).trans
        (Cardinal.aleph0_le_aleph 1)⟩
  exact ⟨a, bounded_support_in_range hGCH a p ha⟩

/-- At a cut of cofinality omegaOne, a condition already belongs to a
strictly earlier stage. This is literal inclusion, not compatibility. -/
theorem earlier_condition_bounded (hGCH : GCH) {a : W2} (ha : IsOmegaOneSup a)
    (p : Earlier hGCH a) :
    ∃ (b : W2) (hb : b < a), ∃ q : Earlier hGCH b,
      extend hGCH (WithTop.coe_le_coe.mpr hb.le) q = p := by
  obtain ⟨b, hb, hbound⟩ := ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup
    ha (Cardinal.le_aleph0_iff_set_countable.mpr p.val.property)
      (fun i hi => WithTop.coe_lt_coe.mp (p.property i hi))
  refine ⟨b, hb, ?_⟩
  exact (complete_range_iff hGCH (WithTop.coe_le_coe.mpr hb.le) p).mpr
    (fun i hi => WithTop.coe_lt_coe.mpr (hbound i hi))

variable {I V : Type} [LinearOrder I] [LinearOrder V]

theorem exists_name_restriction (hGCH : GCH) {G : SimpleGraph V}
    (N : NiceCliqueName (Full hGCH) I V G) (hI : #I ≤ ℵ_ 1) :
    ∃ bound : W2, ∀ a : W2, bound ≤ a →
      ∃ M : NiceCliqueName (Earlier hGCH a) I V G,
        ∀ p i x, M.toClique.decides ((restriction hGCH a).restrict p) i x ↔
          N.toClique.decides p i x :=
  Erdos1172Part3NiceNameSupport.exists_supported_restriction
    (conditionSupport hGCH) (support_countable hGCH) (Earlier hGCH) (restriction hGCH)
    (bounded_support_in_range hGCH) N hI

theorem eventually_local_code (hGCH : GCH) (G H : SimpleGraph W2)
    (hI : #I ≤ ℵ_ 1) (c : Code (Full hGCH) I G) :
    Erdos1172Part3RegularStageLocality.EventuallyLocal
      (Earlier hGCH) (restriction hGCH) (eval G H c) :=
  Erdos1172Part3RegularStageLocality.eventuallyLocal_eval
    (Earlier hGCH) (restriction hGCH) (conditionSupport hGCH) (support_countable hGCH)
    (bounded_support_in_range hGCH) G H hI c

theorem club_local_sources (hGCH : GCH) (G H : SimpleGraph W2) (hI : #I ≤ ℵ_ 1) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ c : Code (Full hGCH) I G,
      rank hGCH (mk_stage_le hGCH ⊤) hI G c < a →
        Erdos1172Part3RegularStageLocality.Factors (restriction hGCH a) (eval G H c) :=
  Erdos1172Part3RegularStageLocality.exists_club_local_code_sources
    (Earlier hGCH) (restriction hGCH) (conditionSupport hGCH) (support_countable hGCH)
    (bounded_support_in_range hGCH) G H hI (rank hGCH (mk_stage_le hGCH ⊤) hI G)

/-- Canonical ranks and actual constructed stages: no abstract support
system, projection, or locality assumption remains in this statement. -/
theorem club_ranked_tests_local (hGCH : GCH) (G H : SimpleGraph W2) (hI : #I ≤ ℵ_ 1) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ c : Code (Full hGCH) I G,
      rank hGCH (mk_stage_le hGCH ⊤) hI G c < a →
        ∃ U : RegularName (Earlier hGCH a) Unit,
          (∀ p : Full hGCH,
            (rankedAvailability (blockRank hGCH (mk_stage_le hGCH ⊤) hI G)
              (eval G H c)).holds p a ↔ U.holds ((restriction hGCH a).restrict p) ()) ∧
          ∀ p : Full hGCH,
            (neg (rankedAvailability (blockRank hGCH (mk_stage_le hGCH ⊤) hI G)
              (eval G H c))).holds p a ↔ (neg U).holds ((restriction hGCH a).restrict p) () :=
  Erdos1172Part3RankedWitnessRestriction.exists_club_ranked_tests_local
    (Earlier hGCH) (restriction hGCH) (conditionSupport hGCH) (support_countable hGCH)
    (bounded_support_in_range hGCH) G H hI
    (rank hGCH (mk_stage_le hGCH ⊤) hI G) (blockRank hGCH (mk_stage_le hGCH ⊤) hI G)

end Erdos1172Part3TransfiniteStageLocality
