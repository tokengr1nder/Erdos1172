/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfinitePressingDown

@[expose] public section

/-!
# Club readability of actual ranked failures

For an eventually local source, its conjunction with the regular
negation of ranked availability is readable at the corresponding cut
on a club. All allowed names retain their full-order ranks. This supplies
the exact readability premise needed by transfinite pressing down.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3TransfiniteRankedFailures

open ErdosRadoCHAsym (W1 W2 IsOmegaOneSup)
open Erdos1172Part3TransfiniteStageLocality
open Erdos1172Part3TransfinitePressingDown
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularStageLocality (EventuallyLocal Factors)
open Erdos1172Part3CompleteRestriction (CompleteRestriction Supported)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RankedWitnessRestriction
open Erdos1172Part3RegularCliqueNeighborhoods (containedIn cliqueFunction afterClique)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)

variable {P Q X I : Type} [Preorder P] [Preorder Q] [LinearOrder I]

theorem factors_meet (r : CompleteRestriction P Q) {U V : RegularName P X}
    (hU : Factors r U) (hV : Factors r V) : Factors r (meet U V) := by
  obtain ⟨U', rfl⟩ := hU
  obtain ⟨V', rfl⟩ := hV
  exact ⟨meet U' V', RegularName.ext (fun _ _ => Iff.rfl)⟩

theorem eventuallyLocal_meet (hGCH : GCH) {U V : RegularName (Full hGCH) X}
    (hU : EventuallyLocal (Earlier hGCH) (restriction hGCH) U)
    (hV : EventuallyLocal (Earlier hGCH) (restriction hGCH) V) :
    EventuallyLocal (Earlier hGCH) (restriction hGCH) (meet U V) := by
  obtain ⟨b, hb⟩ := hU
  obtain ⟨c, hc⟩ := hV
  exact ⟨max b c, fun a ha => factors_meet (restriction hGCH a)
    (hb a ((le_max_left b c).trans ha)) (hc a ((le_max_right b c).trans ha))⟩

theorem rankedWitness_persistent {G : SimpleGraph W2}
    {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2}
    {p q : P} {a : W2} (hqp : q ≤ p) (h : RankedWitness σ source p a) :
    RankedWitness σ source q a := by
  obtain ⟨N, hN, hbelow, hsource, hafter⟩ := h
  exact ⟨N, hN, hbelow, (containedIn (cliqueFunction N.toClique) source).persistent hqp hsource,
    (afterClique N.toClique).persistent hqp hafter⟩

theorem availability_of_witness {G : SimpleGraph W2}
    {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2}
    {p : P} {a : W2} (h : RankedWitness σ source p a) :
    (rankedAvailability σ source).holds p a :=
  fun q hqp => ⟨q, le_rfl, rankedWitness_persistent hqp h⟩

theorem readsAt_rankedAvailability (hGCH : GCH) {G : SimpleGraph W2}
    (σ : NiceCliqueName (Full hGCH) I W2 G ↪ W2) (source : RegularName (Full hGCH) W2)
    (a : W2) (hsource : Factors (restriction hGCH a) source)
    (hs : ∀ N, σ N < a → Supported (restriction hGCH a) N.function) :
    ReadsAt hGCH (rankedAvailability σ source) a := by
  obtain ⟨V, rfl⟩ := hsource
  intro p q hpq
  rw [rankedAvailability_restrict_iff (restriction hGCH a) σ a hs V p,
    rankedAvailability_restrict_iff (restriction hGCH a) σ a hs V q, hpq]

theorem club_reads_ranked_failure (hGCH : GCH) {G : SimpleGraph W2}
    (hI : #I ≤ ℵ_ 1) (σ : NiceCliqueName (Full hGCH) I W2 G ↪ W2)
    (source : RegularName (Full hGCH) W2)
    (hlocal : EventuallyLocal (Earlier hGCH) (restriction hGCH) source) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club,
      ReadsAt hGCH (meet source (neg (rankedAvailability σ source))) a := by
  obtain ⟨bound, hbound⟩ := hlocal
  obtain ⟨names, hnames, hn⟩ := Erdos1172Part3NiceNameSupport.exists_club_supported_names
    (conditionSupport hGCH) (support_countable hGCH) (Earlier hGCH) (restriction hGCH)
    (bounded_support_in_range hGCH) hI σ
  refine ⟨names ∩ Set.Ioi bound,
    hnames.inter alephZero_lt_cof_W2.ne'
      (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 bound), ?_⟩
  intro a ha
  exact readsAt_meet hGCH (readsAt_of_factors hGCH (hbound a ha.2.le))
    (readsAt_neg hGCH (readsAt_rankedAvailability hGCH σ source a (hbound a ha.2.le) (hn a ha.1)))

end Erdos1172Part3TransfiniteRankedFailures
