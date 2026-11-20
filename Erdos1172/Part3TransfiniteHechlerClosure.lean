/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteHechlerRestrictions
public import Erdos1172.Part3SparseIterationUnions

@[expose] public section

/-!
# Countable closure of every constructed transfinite stage

The common strengthening is the sparse coordinatewise union, not an
assumed limit condition. Induction on the cutoff proves that its earlier
parts are below the earlier parts of every chain member. Each newly
merged stem value comes from a real chain member, whose side-name bound
therefore persists to the merged earlier part.
-/

open Cardinal Ordinal Set

namespace Erdos1172Part3TransfiniteHechlerClosure

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3SparseIterationCarriers
open Erdos1172Part3SparseIterationUnions
open Erdos1172Part3TransfiniteHechlerOrder
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)

theorem stemAt_mono (hGCH : GCH) {a : Cut} {q p : Stage hGCH a} (hqp : q ≤ p)
    {i : W2} {j v : W1} (hpv : (stemAt p i).val j = some v) :
    (stemAt q i).val j = some v := by
  cases hd : value p i with
  | none =>
    have hs : stemAt p i = emptyStem := congrArg Prod.fst (dataAt_of_none hd)
    rw [hs] at hpv
    cases hpv
  | some d =>
    obtain ⟨e, he, hed⟩ := (le_iff hGCH q p).mp hqp i (lt_of_value_some hd) d hd
    rw [stemAt_of_some he]
    apply hed.1 j v
    rwa [stemAt_of_some hd] at hpv

theorem forgetAt_mono (hGCH : GCH) (a : Cut) (i : W2) :
    Monotone (fun p : Stage hGCH a => forgetAt p i) := by
  intro q p hqp
  exact ⟨fun _ _ hv => stemAt_mono hGCH hqp hv, Set.Subset.rfl,
    fun _ _ _ _ _ h => h.elim⟩

theorem coordinateChains_of_chain (hGCH : GCH) {a : Cut} {C : Set (Stage hGCH a)}
    (hchain : IsChain (· ≤ ·) C) : CoordinateChains C := by
  intro i
  let f : Stage hGCH a →o Erdos1172Part3HechlerOrder.Condition :=
    ⟨fun p => forgetAt p i, forgetAt_mono hGCH a i⟩
  exact hchain.image f

/-- The same sparse union is a lower bound simultaneously at all
earlier cutoffs. No uncountable chain closure is used. -/
theorem merge_restrictions_lower (hGCH : GCH) {a : Cut} (C : Set (Stage hGCH a))
    (hC : C.Countable) (hchain : IsChain (· ≤ ·) C) :
    ∀ (b : Cut), b ≤ a → ∀ p ∈ C,
      (stage hGCH b).Le (truncate (merge C hC).val b) (truncate p.val b) := by
  classical
  have hc : CoordinateChains C := coordinateChains_of_chain hGCH hchain
  let q : Carrier a := merge C hC
  change ∀ b : Cut, b ≤ a → ∀ p ∈ C,
    (stage hGCH b).Le (truncate q.val b) (truncate p.val b)
  intro b
  induction b using WellFoundedLT.induction with
  | ind b ih =>
    intro hba p hp
    apply (stage_le_iff hGCH b _ _).mpr
    intro i hi d hd
    have hia : (i : Cut) < a := hi.trans_le hba
    have hpd : value p i = some d := by
      rwa [value_truncate p.val b i, if_pos hi] at hd
    obtain ⟨e, he⟩ := merge_active hC hc hp hpd
    change value q i = some e at he
    refine ⟨e, ?_, ?_⟩
    · rw [value_truncate q.val b i, if_pos hi]
      exact he
    · rw [truncate_truncate q.val hi.le]
      refine ⟨?_, ?_, ?_⟩
      · intro j v hdv
        have hpv : (stemAt p i).val j = some v := by
          rw [stemAt_of_some hpd]
          exact hdv
        have hqv := merge_stem_extends hC hc hp hpv
        change (stemAt q i).val j = some v at hqv
        rwa [stemAt_of_some he] at hqv
      · have hside := side_subset_merge hC hp i
        change (sideAt p i).val ⊆ (sideAt q i).val at hside
        rwa [sideAt_of_some hpd, sideAt_of_some he] at hside
      · intro j hdj v hev c hcd
        have hqv : (stemAt q i).val j = some v := by
          rw [stemAt_of_some he]
          exact hev
        obtain ⟨r, hr, hrv⟩ := merge_stem_origin hC hqv
        rcases hchain.total hr hp with hrp | hpr
        · obtain ⟨f, hf, hfd⟩ := (le_iff hGCH r p).mp hrp i hia d hpd
          have hfv : f.val.1.val j = some v := by rwa [stemAt_of_some hf] at hrv
          exact (stage hGCH (i : Cut)).bound_mono
            (hfd.2.2 j hdj v hfv c hcd) (ih (i : Cut) hi hia.le r hr)
        · have hpv := stemAt_mono hGCH hpr hrv
          rw [stemAt_of_some hpd, hdj] at hpv
          cases hpv

theorem merge_lower (hGCH : GCH) {a : Cut} (C : Set (Stage hGCH a))
    (hC : C.Countable) (hchain : IsChain (· ≤ ·) C) (p : Stage hGCH a) (hp : p ∈ C) :
    (stage hGCH a).Le (merge C hC) p := by
  have h := merge_restrictions_lower hGCH C hC hchain a le_rfl p hp
  rwa [truncate_self (merge C hC), truncate_self p] at h

theorem countablyClosed (hGCH : GCH) (a : Cut) : CountablyClosed (Stage hGCH a) := by
  intro C _ hC hchain
  exact ⟨merge C hC, fun p hp => merge_lower hGCH C hC hchain p hp⟩

theorem full_countablyClosed (hGCH : GCH) : CountablyClosed (Stage hGCH ⊤) :=
  countablyClosed hGCH ⊤

end Erdos1172Part3TransfiniteHechlerClosure
