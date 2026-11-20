/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FullHechlerConsequences

@[expose] public section

/-!
# Pressing a locally readable stationary source down to one earlier stage

At a cut of cofinality omegaOne, its restricted condition is included
from a strictly earlier stage. Local readability preserves actual source
membership after that inclusion into the full order. Pressing down then
fixes the earlier stage, and its proved chain condition supplies an actual
condition at which the pulled-back source remains stationary.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3TransfinitePressingDown

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3SparseIterationCarriers (Cut embed truncate_self)
open Erdos1172Part3TransfiniteStageLocality (Full Earlier restriction earlier_condition_bounded)
open Erdos1172Part3TransfiniteHechlerRestrictions (extend)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularStageLocality (Factors)
open Erdos1172Part3CompleteRestrictionNames (pullRegular)
open Erdos1172Part3StationaryDecisions (StationaryAt exists_stationary_condition)
open Erdos1172Part3RedPredecessorReflection (stationaryPressingDown)
open Erdos1172Part3TwoSuccessorBootstrap (stationary_inter_club)

def ReadsAt (hGCH : GCH) (U : RegularName (Full hGCH) W2) (a : W2) : Prop :=
  ∀ p q : Full hGCH, (restriction hGCH a).restrict p = (restriction hGCH a).restrict q →
    (U.holds p a ↔ U.holds q a)

theorem readsAt_of_factors (hGCH : GCH) {U : RegularName (Full hGCH) W2} {a : W2}
    (hU : Factors (restriction hGCH a) U) : ReadsAt hGCH U a := by
  obtain ⟨V, rfl⟩ := hU
  intro p q hpq
  change V.holds ((restriction hGCH a).restrict p) a ↔
    V.holds ((restriction hGCH a).restrict q) a
  rw [hpq]

theorem readsAt_meet (hGCH : GCH) {U V : RegularName (Full hGCH) W2} {a : W2}
    (hU : ReadsAt hGCH U a) (hV : ReadsAt hGCH V a) : ReadsAt hGCH (meet U V) a := by
  intro p q hpq
  exact and_congr (hU p q hpq) (hV p q hpq)

theorem readsAt_neg (hGCH : GCH) {U : RegularName (Full hGCH) W2} {a : W2}
    (hU : ReadsAt hGCH U a) : ReadsAt hGCH (neg U) a := by
  have transfer (p q : Full hGCH)
      (hpq : (restriction hGCH a).restrict p = (restriction hGCH a).restrict q)
      (hp : (neg U).holds p a) : (neg U).holds q a := by
    intro s hsq hs
    have hsp : (restriction hGCH a).restrict s ≤ (restriction hGCH a).restrict p := by
      rw [hpq]
      exact (restriction hGCH a).restrict.monotone hsq
    obtain ⟨t, htp, ht⟩ := (restriction hGCH a).lift p ((restriction hGCH a).restrict s) hsp
    exact hp t htp ((hU s t ht.symm).mp hs)
  intro p q hpq
  exact ⟨transfer p q hpq, transfer q p hpq.symm⟩

theorem restrict_embed_earlier (hGCH : GCH) {a b : W2} (hba : b ≤ a)
    (q : Earlier hGCH b) :
    (restriction hGCH a).restrict ((restriction hGCH b).embed q) =
      extend hGCH (WithTop.coe_le_coe.mpr hba) q :=
  truncate_self (embed (WithTop.coe_le_coe.mpr hba) q)

theorem exists_earlier_actual_member (hGCH : GCH) (U : RegularName (Full hGCH) W2)
    {a : W2} (ha : IsOmegaOneSup a) (hread : ReadsAt hGCH U a)
    (p : Full hGCH) (hp : U.holds p a) :
    ∃ b : W2, b < a ∧ ∃ q : Earlier hGCH b, U.holds ((restriction hGCH b).embed q) a := by
  obtain ⟨b, hba, q, hq⟩ := earlier_condition_bounded hGCH ha ((restriction hGCH a).restrict p)
  refine ⟨b, hba, q, (hread p ((restriction hGCH b).embed q) ?_).mp hp⟩
  rw [restrict_embed_earlier hGCH hba.le q, hq]

/-- The source is allowed to be globally nonlocal: only its reading at
the corresponding cut is required on a club. -/
theorem exists_stationary_earlier_source (hGCH : GCH) (U : RegularName (Full hGCH) W2)
    (hsup : ∀ p a, U.holds p a → IsOmegaOneSup a)
    (hstat : IsStationary {a : W2 | ∃ p : Full hGCH, U.holds p a})
    (club : Set W2) (hclub : IsClub club) (hread : ∀ a ∈ club, ReadsAt hGCH U a) :
    ∃ b : W2, ∃ p : Earlier hGCH b,
      StationaryAt (pullRegular (restriction hGCH b) U).holds p := by
  classical
  let S : Set W2 := {a | ∃ p : Full hGCH, U.holds p a} ∩ club
  have hS : IsStationary S := stationary_inter_club hstat hclub
  have witness (a : W2) (ha : a ∈ S) :
      ∃ b : W2, b < a ∧ ∃ q : Earlier hGCH b, U.holds ((restriction hGCH b).embed q) a := by
    obtain ⟨p, hp⟩ := ha.1
    exact exists_earlier_actual_member hGCH U (hsup p a hp) (hread a ha.2) p hp
  let chosen (a : W2) : W2 := if ha : a ∈ S then (witness a ha).choose else a
  have hchosen (a : W2) (ha : a ∈ S) :
      chosen a < a ∧ ∃ q : Earlier hGCH (chosen a),
        U.holds ((restriction hGCH (chosen a)).embed q) a := by
    have heq : chosen a = (witness a ha).choose := dif_pos ha
    rw [heq]
    exact (witness a ha).choose_spec
  obtain ⟨b, hfiber⟩ := stationaryPressingDown S chosen hS (fun a ha => (hchosen a ha).1)
  have hsource : IsStationary {a : W2 | ∃ q : Earlier hGCH b,
      (pullRegular (restriction hGCH b) U).holds q a} := by
    apply hfiber.mono
    intro a ha
    have h := (hchosen a ha.1).2
    rw [ha.2] at h
    exact h
  obtain ⟨p, hp⟩ := exists_stationary_condition
    (Erdos1172Part3TransfiniteHechlerCentering.omegaTwoCC hGCH (b : Cut))
    (pullRegular (restriction hGCH b) U).holds
    (fun hqp hx => (pullRegular (restriction hGCH b) U).persistent hqp hx) hsource
  exact ⟨b, p, hp⟩

end Erdos1172Part3TransfinitePressingDown
