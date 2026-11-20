/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteHechlerClosure
public import Erdos1172.Part3CountableProfileAmalgamation

@[expose] public section

/-!
# Countable centering through the full omegaTwo length

The universal omegaOne family covers whole active stems on omegaTwo
coordinates. Within one class a countable union adds no new stem values
at any previously active coordinate, so all the old side bounds are
preserved. This supplies an actual centering of the constructed orders,
not a hypothetical history-amalgamation premise.
-/

open Cardinal Ordinal Set

namespace Erdos1172Part3TransfiniteHechlerCentering

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3HechlerCentering (Stem)
open Erdos1172Part3CountableSupportProfiles (StemProfile)
open Erdos1172Part3SparseIterationCarriers
open Erdos1172Part3SparseIterationUnions
open Erdos1172Part3TransfiniteHechlerOrder
open Erdos1172Part3CountableProfileAmalgamation
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)

def SameActiveStems {a : Cut} (C : Set (Carrier a)) : Prop :=
  ∀ p ∈ C, ∀ q ∈ C, ∀ i d e, value p i = some d → value q i = some e → d.val.1 = e.val.1

theorem coordinateChains_of_sameActiveStems {a : Cut} {C : Set (Carrier a)}
    (hc : SameActiveStems C) : CoordinateChains C := by
  intro i r hr s hs _
  obtain ⟨p, hp, rfl⟩ := hr
  obtain ⟨q, hq, rfl⟩ := hs
  cases hd : value p i with
  | none =>
    right
    refine ⟨?_, Set.Subset.rfl, fun _ _ _ _ _ h => h.elim⟩
    intro j v hv
    have he : stemAt p i = emptyStem := congrArg Prod.fst (dataAt_of_none hd)
    change (stemAt p i).val j = some v at hv
    rw [he] at hv
    cases hv
  | some d =>
    left
    refine ⟨?_, Set.Subset.rfl, fun _ _ _ _ _ h => h.elim⟩
    intro j v hv
    change (stemAt q i).val j = some v at hv
    change (stemAt p i).val j = some v
    cases he : value q i with
    | none =>
      have heq : stemAt q i = emptyStem := congrArg Prod.fst (dataAt_of_none he)
      rw [heq] at hv
      cases hv
    | some e =>
      rw [stemAt_of_some hd, hc p hp q hq i d e hd he]
      rwa [stemAt_of_some he] at hv

theorem merge_same_active_stem {a : Cut} {C : Set (Carrier a)} (hC : C.Countable)
    (hc : SameActiveStems C) {p : Carrier a} (hp : p ∈ C) {i : W2} {d : Datum}
    (hd : value p i = some d) : stemAt (merge C hC) i = d.val.1 := by
  apply Subtype.ext
  funext j
  cases hdj : d.val.1.val j with
  | some v =>
    apply merge_stem_extends hC (coordinateChains_of_sameActiveStems hc) hp
    rw [stemAt_of_some hd]
    exact hdj
  | none =>
    cases hv : (stemAt (merge C hC) i).val j with
    | none => rfl
    | some v =>
      obtain ⟨r, hr, hrv⟩ := merge_stem_origin hC hv
      cases he : value r i with
      | none =>
        have heq : stemAt r i = emptyStem := congrArg Prod.fst (dataAt_of_none he)
        rw [heq] at hrv
        cases hrv
      | some e =>
        have hde := hc p hp r hr i d e hd he
        rw [stemAt_of_some he, ← hde, hdj] at hrv
        cases hrv

theorem merge_sameStem_lower (hGCH : GCH) {a : Cut} (C : Set (Stage hGCH a))
    (hC : C.Countable) (hc : SameActiveStems C) (p : Stage hGCH a) (hp : p ∈ C) :
    (stage hGCH a).Le (merge C hC) p := by
  apply (stage_le_iff hGCH a _ _).mpr
  intro i hi d hd
  obtain ⟨e, he⟩ := merge_active hC (coordinateChains_of_sameActiveStems hc) hp hd
  have hes : e.val.1 = d.val.1 :=
    (stemAt_of_some he).symm.trans (merge_same_active_stem hC hc hp hd)
  refine ⟨e, he, ?_, ?_, ?_⟩
  · intro j v hv
    rwa [hes]
  · have hside := side_subset_merge hC hp i
    rwa [sideAt_of_some hd, sideAt_of_some he] at hside
  · intro j hdj v hev _ _
    rw [hes, hdj] at hev
    cases hev

def stemProfile {a : Cut} (p : Carrier a) : StemProfile W2 := by
  let f (i : W2) := (value p i).map (fun d => d.val.1)
  refine ⟨f, p.val.property.mono ?_⟩
  intro i hi hn
  change f i ≠ none at hi
  change value p i = none at hn
  exact hi (by simp only [f, hn, Option.map_none])

theorem stemProfile_some {a : Cut} {p : Carrier a} {i : W2} {d : Datum}
    (hd : value p i = some d) : (stemProfile p).val i = some d.val.1 := by
  change (value p i).map (fun d => d.val.1) = some d.val.1
  rw [hd]
  rfl

noncomputable def centered (hGCH : GCH) (a : Cut) : CountablyCenteredCode (Stage hGCH a) :=
  centered_of_profile_amalgamation
    (stemCover hGCH (by simp [W2, Cardinal.mk_toType, Ordinal.card_omega]))
    (fun p : Stage hGCH a => stemProfile p) (by
      intro C hC hc
      have hs : SameActiveStems C := by
        intro p hp q hq i d e hd he
        exact hc p hp q hq i d.val.1 e.val.1 (stemProfile_some hd) (stemProfile_some he)
      exact ⟨merge C hC, fun p hp => merge_sameStem_lower hGCH C hC hs p hp⟩)

theorem omegaTwoCC (hGCH : GCH) (a : Cut) : OmegaTwoCC (Stage hGCH a) :=
  (centered hGCH a).omegaTwoCC

end Erdos1172Part3TransfiniteHechlerCentering
