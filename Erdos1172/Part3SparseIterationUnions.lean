/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3SparseIterationCarriers

@[expose] public section

/-!
# Countable unions of sparse iteration conditions

The union retains every side code. Stem values have actual origins in
the input family; when the stems form coordinatewise chains, every old
stem value is retained as well. These are structural facts about the
fixed carriers, independent of the recursively defined decision order.
-/

open Cardinal Ordinal Set

namespace Erdos1172Part3SparseIterationUnions

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3HechlerCentering (Stem)
open Erdos1172Part3CountableSupportProfiles (support)
open Erdos1172Part3SparseIterationCarriers

def unpack : Option Datum → Stem × SideCodes
  | none => (emptyStem, emptySide)
  | some d => d.val

noncomputable def pack (d : Stem × SideCodes) : Option Datum := by
  classical
  exact if h : d = (emptyStem, emptySide) then none else some ⟨d, h⟩

@[simp] theorem unpack_pack (d : Stem × SideCodes) : unpack (pack d) = d := by
  classical
  by_cases h : d = (emptyStem, emptySide)
  · rw [pack, dif_pos h]
    exact h.symm
  · rw [pack, dif_neg h]
    rfl

@[simp] theorem pack_unpack (d : Option Datum) : pack (unpack d) = d := by
  classical
  cases d with
  | none =>
    change pack (emptyStem, emptySide) = none
    rw [pack, dif_pos rfl]
  | some d =>
    change pack d.val = some d
    rw [pack, dif_neg d.property]

theorem pack_eq_none_iff (d : Stem × SideCodes) :
    pack d = none ↔ d = (emptyStem, emptySide) := by
  constructor
  · intro h
    have heq := congrArg unpack h
    rw [unpack_pack] at heq
    exact heq
  · rintro rfl
    exact pack_unpack none

def dataAt {a : Cut} (p : Carrier a) (i : W2) : Stem × SideCodes := unpack (value p i)

def stemAt {a : Cut} (p : Carrier a) (i : W2) : Stem := (dataAt p i).1

def sideAt {a : Cut} (p : Carrier a) (i : W2) : SideCodes := (dataAt p i).2

theorem dataAt_of_some {a : Cut} {p : Carrier a} {i : W2} {d : Datum}
    (h : value p i = some d) : dataAt p i = d.val := by rw [dataAt, h]; rfl

theorem dataAt_of_none {a : Cut} {p : Carrier a} {i : W2}
    (h : value p i = none) : dataAt p i = (emptyStem, emptySide) := by rw [dataAt, h]; rfl

theorem stemAt_of_some {a : Cut} {p : Carrier a} {i : W2} {d : Datum}
    (h : value p i = some d) : stemAt p i = d.val.1 := congrArg Prod.fst (dataAt_of_some h)

theorem sideAt_of_some {a : Cut} {p : Carrier a} {i : W2} {d : Datum}
    (h : value p i = some d) : sideAt p i = d.val.2 := congrArg Prod.snd (dataAt_of_some h)

def forgetAt {a : Cut} (p : Carrier a) (i : W2) : Erdos1172Part3HechlerOrder.Condition where
  stem := (stemAt p i).val
  stem_countable := (stemAt p i).property
  side := ∅
  side_countable := Set.countable_empty

def supportUnion {a : Cut} (C : Set (Carrier a)) : Set W2 := ⋃ p ∈ C, support p.val

theorem supportUnion_countable {a : Cut} {C : Set (Carrier a)} (hC : C.Countable) :
    (supportUnion C).Countable := hC.biUnion (fun p _ => p.val.property)

theorem none_of_not_mem_supportUnion {a : Cut} {C : Set (Carrier a)} {i : W2}
    (hi : i ∉ supportUnion C) {p : Carrier a} (hp : p ∈ C) : value p i = none := by
  by_contra h
  exact hi (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, h⟩⟩)

noncomputable def unionData {a : Cut} (C : Set (Carrier a)) (hC : C.Countable)
    (i : W2) : Stem × SideCodes :=
  let stems := Erdos1172Part3HechlerOrder.unionCondition ((fun p => forgetAt p i) '' C)
    (hC.image (fun p => forgetAt p i))
  (⟨stems.stem, stems.stem_countable⟩,
    ⟨⋃ p ∈ C, (sideAt p i).val, hC.biUnion (fun p _ => (sideAt p i).property)⟩)

theorem unionData_stem_origin {a : Cut} {C : Set (Carrier a)} (hC : C.Countable)
    {i : W2} {j v : W1} (h : (unionData C hC i).1.val j = some v) :
    ∃ p ∈ C, (stemAt p i).val j = some v := by
  obtain ⟨r, ⟨p, hp, rfl⟩, hv⟩ := Erdos1172Part3HechlerOrder.unionStem_some h
  exact ⟨p, hp, hv⟩

theorem unionData_empty_of_not_mem {a : Cut} {C : Set (Carrier a)} (hC : C.Countable)
    {i : W2} (hi : i ∉ supportUnion C) :
    unionData C hC i = (emptyStem, emptySide) := by
  apply Prod.ext
  · apply Subtype.ext
    funext j
    cases hv : (unionData C hC i).1.val j with
    | none => rfl
    | some v =>
      obtain ⟨p, hp, hpv⟩ := unionData_stem_origin hC hv
      have hn := none_of_not_mem_supportUnion hi hp
      have hs := congrArg Prod.fst (dataAt_of_none hn)
      change stemAt p i = emptyStem at hs
      rw [hs] at hpv
      cases hpv
  · apply Subtype.ext
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hc
    obtain ⟨hpC, hcp⟩ := Set.mem_iUnion.mp hp
    have ht := congrArg Prod.snd (dataAt_of_none (none_of_not_mem_supportUnion hi hpC))
    change sideAt p i = emptySide at ht
    rw [ht] at hcp
    exact hcp

noncomputable def merge {a : Cut} (C : Set (Carrier a)) (hC : C.Countable) : Carrier a := by
  let f (i : W2) := pack (unionData C hC i)
  have hs : {i | f i ≠ none} ⊆ supportUnion C := by
    intro i hi
    by_contra hn
    exact hi ((pack_eq_none_iff _).mpr (unionData_empty_of_not_mem hC hn))
  refine ⟨⟨f, (supportUnion_countable hC).mono hs⟩, ?_⟩
  intro i hi
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hs hi)
  obtain ⟨hpC, hip⟩ := Set.mem_iUnion.mp hp
  exact p.property i hip

theorem dataAt_merge {a : Cut} (C : Set (Carrier a)) (hC : C.Countable) (i : W2) :
    dataAt (merge C hC) i = unionData C hC i := unpack_pack _

theorem merge_stem_origin {a : Cut} {C : Set (Carrier a)} (hC : C.Countable)
    {i : W2} {j v : W1} (h : (stemAt (merge C hC) i).val j = some v) :
    ∃ p ∈ C, (stemAt p i).val j = some v := unionData_stem_origin hC (by
  simpa only [stemAt, dataAt_merge] using h)

theorem side_subset_merge {a : Cut} {C : Set (Carrier a)} (hC : C.Countable)
    {p : Carrier a} (hp : p ∈ C) (i : W2) :
    (sideAt p i).val ⊆ (sideAt (merge C hC) i).val := by
  intro c hc
  rw [sideAt, dataAt_merge]
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hc⟩⟩

def CoordinateChains {a : Cut} (C : Set (Carrier a)) : Prop :=
  ∀ i : W2, IsChain (· ≤ ·) ((fun p => forgetAt p i) '' C)

theorem merge_stem_extends {a : Cut} {C : Set (Carrier a)} (hC : C.Countable)
    (hc : CoordinateChains C) {p : Carrier a} (hp : p ∈ C)
    {i : W2} {j v : W1} (hv : (stemAt p i).val j = some v) :
    (stemAt (merge C hC) i).val j = some v := by
  rw [stemAt, dataAt_merge]
  exact Erdos1172Part3HechlerOrder.unionStem_extends (hc i) ⟨p, hp, rfl⟩ hv

theorem merge_active {a : Cut} {C : Set (Carrier a)} (hC : C.Countable)
    (hc : CoordinateChains C) {p : Carrier a} (hp : p ∈ C)
    {i : W2} {d : Datum} (hd : value p i = some d) :
    ∃ e : Datum, value (merge C hC) i = some e := by
  cases he : value (merge C hC) i with
  | some e => exact ⟨e, rfl⟩
  | none =>
    have hedata := dataAt_of_none he
    have hes : stemAt (merge C hC) i = emptyStem := congrArg Prod.fst hedata
    have het : sideAt (merge C hC) i = emptySide := congrArg Prod.snd hedata
    apply False.elim
    apply d.property
    apply Prod.ext
    · apply Subtype.ext
      funext j
      cases hv : d.val.1.val j with
      | none => rfl
      | some v =>
        have hpv : (stemAt p i).val j = some v := by rw [stemAt_of_some hd]; exact hv
        have hmv := merge_stem_extends hC hc hp hpv
        rw [hes] at hmv
        cases hmv
    · apply Subtype.ext
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro c hc
      have hcp : c ∈ (sideAt p i).val := by rw [sideAt_of_some hd]; exact hc
      have hce := side_subset_merge hC hp i hcp
      rw [het] at hce
      exact hce

end Erdos1172Part3SparseIterationUnions
