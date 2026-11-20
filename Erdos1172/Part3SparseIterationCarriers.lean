/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableSupportProfiles
public import Mathlib.Order.WithBot

@[expose] public section

/-!
# Fixed carriers for a sparse transfinite iteration

The carriers do not depend on any recursively constructed order. Each
active coordinate has a countable stem and countably many omegaTwo codes.
The wholly empty datum is represented by an absent coordinate, uniquely.
Cutoffs include the full omegaTwo length. Restriction is literal truncation.
No order or preservation theorem is asserted by this file.
-/

open Cardinal Ordinal Set
open Function (Injective)

namespace Erdos1172Part3SparseIterationCarriers

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3HechlerCentering (Stem mk_Stem_le)
open Erdos1172Part3CountableSupportProfiles (Profile support graph graph_countable graph_injective)

abbrev Cut := WithTop W2

abbrev SideCodes := {s : Set W2 // s.Countable}

def emptyStem : Stem := ⟨fun _ => none, by simp⟩

def emptySide : SideCodes := ⟨∅, Set.countable_empty⟩

abbrev Datum := {d : Stem × SideCodes // d ≠ (emptyStem, emptySide)}

abbrev Raw := Profile W2 Datum

abbrev Carrier (a : Cut) := {p : Raw // ∀ i ∈ support p, (i : Cut) < a}

def emptyRaw : Raw := ⟨fun _ => none, by simp⟩

def empty (a : Cut) : Carrier a := ⟨emptyRaw, by simp [support, emptyRaw]⟩

instance (a : Cut) : Inhabited (Carrier a) := ⟨empty a⟩

def value {a : Cut} (p : Carrier a) (i : W2) : Option Datum := p.val.val i

@[ext] theorem carrier_ext {a : Cut} {p q : Carrier a}
    (h : ∀ i, value p i = value q i) : p = q :=
  Subtype.ext (Subtype.ext (funext h))

@[simp] theorem value_empty (a : Cut) (i : W2) : value (empty a) i = none := rfl

theorem value_none_of_not_lt {a : Cut} (p : Carrier a) {i : W2}
    (hi : ¬ (i : Cut) < a) : value p i = none := by
  by_contra h
  exact hi (p.property i h)

theorem lt_of_value_some {a : Cut} {p : Carrier a} {i : W2} {d : Datum}
    (h : value p i = some d) : (i : Cut) < a := by
  apply p.property
  change value p i ≠ none
  rw [h]
  exact Option.some_ne_none d

noncomputable def truncate (p : Raw) (a : Cut) : Carrier a := by
  classical
  let f (i : W2) := if (i : Cut) < a then p.val i else none
  have hf : {i | f i ≠ none} ⊆ support p := by
    intro i hi
    change f i ≠ none at hi
    change p.val i ≠ none
    by_cases hia : (i : Cut) < a
    · simpa only [f, if_pos hia] using hi
    · simp only [f, if_neg hia, ne_eq, not_true_eq_false] at hi
  exact ⟨⟨f, p.property.mono hf⟩, fun i hi => by
    change f i ≠ none at hi
    by_contra hia
    exact hi (if_neg hia)⟩

@[simp] theorem value_truncate (p : Raw) (a : Cut) (i : W2) :
    value (truncate p a) i = if (i : Cut) < a then p.val i else none := by
  classical
  rfl

@[simp] theorem truncate_self {a : Cut} (p : Carrier a) : truncate p.val a = p := by
  classical
  apply carrier_ext
  intro i
  by_cases hi : (i : Cut) < a
  · rw [value_truncate, if_pos hi]
    rfl
  · simp only [value_truncate, if_neg hi, value_none_of_not_lt p hi]

@[simp] theorem truncate_empty (a b : Cut) : truncate (empty a).val b = empty b := by
  classical
  apply carrier_ext
  intro i
  simp only [value_truncate, empty, emptyRaw]
  split <;> rfl

theorem truncate_truncate (p : Raw) {a b : Cut} (hab : a ≤ b) :
    truncate (truncate p b).val a = truncate p a := by
  classical
  apply carrier_ext
  intro i
  by_cases hia : (i : Cut) < a
  · simp only [value_truncate, if_pos hia]
    change value (truncate p b) i = p.val i
    simp only [value_truncate, if_pos (hia.trans_le hab)]
  · simp only [value_truncate, if_neg hia]

def embed {a b : Cut} (hab : a ≤ b) (p : Carrier a) : Carrier b :=
  ⟨p.val, fun i hi => (p.property i hi).trans_le hab⟩

@[simp] theorem value_embed {a b : Cut} (hab : a ≤ b) (p : Carrier a) (i : W2) :
    value (embed hab p) i = value p i := rfl

@[simp] theorem truncate_embed {a b : Cut} (hab : a ≤ b) (p : Carrier a) :
    truncate (embed hab p).val a = p := truncate_self p

theorem embed_truncate_eq_iff {a b : Cut} (hab : a ≤ b) (p : Carrier b) :
    embed hab (truncate p.val a) = p ↔ ∀ i ∈ support p.val, (i : Cut) < a := by
  constructor
  · intro h i hi
    have heq : (truncate p.val a).val = p.val := congrArg Subtype.val h
    exact (truncate p.val a).property i (heq.symm ▸ hi)
  · intro h
    exact carrier_ext (fun i => congrArg (fun q : Carrier a => value q i)
      (truncate_self (⟨p.val, h⟩ : Carrier a)))

theorem mem_range_embed_iff {a b : Cut} (hab : a ≤ b) (p : Carrier b) :
    p ∈ Set.range (embed hab) ↔ ∀ i ∈ support p.val, (i : Cut) < a := by
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property
  · intro h
    exact ⟨truncate p.val a, (embed_truncate_eq_iff hab p).mpr h⟩

theorem mk_profile_le_alephTwo {I V : Type} (hGCH : GCH)
    (hI : #I ≤ ℵ_ 2) (hV : #V ≤ ℵ_ 2) : #(Profile I V) ≤ ℵ_ 2 := by
  let graphCode (p : Profile I V) : {s : Set (I × V) // #s ≤ ℵ₀} :=
    ⟨graph p, graph_countable p⟩
  have hgraph : #(Profile I V) ≤ #{s : Set (I × V) // #s ≤ ℵ₀} :=
    Cardinal.mk_le_of_injective (f := graphCode)
      (fun _ _ h => graph_injective (congrArg Subtype.val h))
  have hprod : #(I × V) ≤ ℵ_ 2 := by
    rw [Cardinal.mk_prod]
    simp only [Cardinal.lift_id]
    exact (mul_le_mul' hI hV).trans_eq
      (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 2))
  apply hgraph.trans
  apply (Cardinal.mk_bounded_set_le (I × V) ℵ₀).trans
  exact (Cardinal.power_le_power_right (max_le hprod (Cardinal.aleph0_le_aleph 2))).trans_eq
    hGCH.aleph_two_power_aleph_zero

theorem mk_sideCodes_le (hGCH : GCH) : #SideCodes ≤ ℵ_ 2 := by
  let encode (s : SideCodes) : {s : Set W2 // #s ≤ ℵ₀} :=
    ⟨s.val, Cardinal.le_aleph0_iff_set_countable.mpr s.property⟩
  have hinj : Injective encode :=
    fun _ _ h => Subtype.ext (congrArg (fun c : {s : Set W2 // #s ≤ ℵ₀} => c.val) h)
  apply (Cardinal.mk_le_of_injective hinj).trans
  simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega,
    max_eq_left (Cardinal.aleph0_le_aleph 2), hGCH.aleph_two_power_aleph_zero]
    using Cardinal.mk_bounded_set_le W2 ℵ₀

theorem mk_datum_le (hGCH : GCH) : #Datum ≤ ℵ_ 2 := by
  apply (Cardinal.mk_le_of_injective Subtype.val_injective).trans
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id]
  have hs : #Stem ≤ ℵ_ 2 := (mk_Stem_le hGCH.toCH).trans
    (Cardinal.aleph_le_aleph.mpr (by norm_num : (1 : Ordinal) ≤ 2))
  exact (mul_le_mul' hs (mk_sideCodes_le hGCH)).trans_eq
    (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 2))

theorem mk_raw_le (hGCH : GCH) : #Raw ≤ ℵ_ 2 :=
  mk_profile_le_alephTwo hGCH
    (by simp [W2, Cardinal.mk_toType, Ordinal.card_omega]) (mk_datum_le hGCH)

theorem mk_carrier_le (hGCH : GCH) (a : Cut) : #(Carrier a) ≤ ℵ_ 2 :=
  (Cardinal.mk_le_of_injective Subtype.val_injective).trans (mk_raw_le hGCH)

end Erdos1172Part3SparseIterationCarriers
