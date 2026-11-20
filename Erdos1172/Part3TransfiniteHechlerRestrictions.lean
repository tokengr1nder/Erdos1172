/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteHechlerOrder
public import Erdos1172.Part3CompleteRestriction

@[expose] public section

/-!
# Complete restrictions between the constructed transfinite stages

Restriction is truncation, inclusion is the unchanged sparse function,
and lifting replaces only the earlier part. All three are constructed
here for arbitrary cutoffs, including the full omegaTwo stage. Bounded
support is consequently equivalent to literal membership in the earlier
inclusion range, as required for restricting nice names.
-/

open Cardinal Ordinal Set

namespace Erdos1172Part3TransfiniteHechlerRestrictions

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3CountableSupportProfiles (support)
open Erdos1172Part3SparseIterationCarriers
open Erdos1172Part3TransfiniteHechlerOrder
open Erdos1172Part3CompleteRestriction (CompleteRestriction)

noncomputable def replace {a b : Cut} (hab : a ≤ b) (p : Carrier b)
    (q : Carrier a) : Carrier b := by
  classical
  let f (i : W2) := if (i : Cut) < a then value q i else value p i
  have hf : {i | f i ≠ none} ⊆ support q.val ∪ support p.val := by
    intro i hi
    change f i ≠ none at hi
    by_cases hia : (i : Cut) < a
    · apply Or.inl
      change value q i ≠ none
      simpa only [f, if_pos hia] using hi
    · apply Or.inr
      change value p i ≠ none
      simpa only [f, if_neg hia] using hi
  refine ⟨⟨f, (q.val.property.union p.val.property).mono hf⟩, ?_⟩
  intro i hi
  rcases hf hi with hq | hp
  · exact (q.property i hq).trans_le hab
  · exact p.property i hp

@[simp] theorem value_replace {a b : Cut} (hab : a ≤ b) (p : Carrier b)
    (q : Carrier a) (i : W2) :
    value (replace hab p q) i = if (i : Cut) < a then value q i else value p i := by
  classical
  rfl

theorem truncate_replace {a b c : Cut} (hab : a ≤ b) (hca : c ≤ a)
    (p : Carrier b) (q : Carrier a) :
    truncate (replace hab p q).val c = truncate q.val c := by
  classical
  apply carrier_ext
  intro i
  by_cases hic : (i : Cut) < c
  · simp only [value_truncate, if_pos hic]
    change value (replace hab p q) i = value q i
    rw [value_replace, if_pos (hic.trans_le hca)]
  · simp only [value_truncate, if_neg hic]

@[simp] theorem truncate_replace_self {a b : Cut} (hab : a ≤ b)
    (p : Carrier b) (q : Carrier a) : truncate (replace hab p q).val a = q := by
  rw [truncate_replace hab le_rfl, truncate_self]

noncomputable def restrict (hGCH : GCH) {a b : Cut} (p : Stage hGCH b) : Stage hGCH a :=
  truncate p.val a

def extend (hGCH : GCH) {a b : Cut} (hab : a ≤ b) (q : Stage hGCH a) : Stage hGCH b :=
  embed hab q

theorem restrict_le (hGCH : GCH) {a b : Cut} (hab : a ≤ b)
    {q p : Stage hGCH b} (hqp : q ≤ p) :
    restrict hGCH (a := a) q ≤ restrict hGCH p := by
  rcases hab.eq_or_lt with rfl | hab
  · change (stage hGCH a).Le (truncate q.val a) (truncate p.val a)
    rw [truncate_self q, truncate_self p]
    exact hqp
  · exact stage_restrict_le hGCH hqp a hab

theorem extend_le (hGCH : GCH) {a b : Cut} (hab : a ≤ b)
    {q p : Stage hGCH a} (hqp : q ≤ p) : extend hGCH hab q ≤ extend hGCH hab p := by
  apply (le_iff hGCH _ _).mpr
  intro i hi d hd
  have hip : (i : Cut) < a := lt_of_value_some hd
  exact (le_iff hGCH q p).mp hqp i hip d hd

theorem below_extend_restrict (hGCH : GCH) {a b : Cut} (hab : a ≤ b)
    (p : Stage hGCH b) : p ≤ extend hGCH hab (restrict hGCH p) := by
  classical
  apply (le_iff hGCH _ _).mpr
  intro i hi d hd
  have hia : (i : Cut) < a := lt_of_value_some (p := truncate p.val a) hd
  have hp : value p i = some d := by
    change value (truncate p.val a) i = some d at hd
    rwa [value_truncate, if_pos hia] at hd
  exact ⟨d, hp, datumExtends_refl _ _ d⟩

theorem replace_le (hGCH : GCH) {a b : Cut} (hab : a ≤ b)
    (p : Stage hGCH b) (q : Stage hGCH a) (hqp : q ≤ restrict hGCH p) :
    (stage hGCH b).Le (replace hab p q) p := by
  classical
  apply (stage_le_iff hGCH b _ _).mpr
  intro i hi d hd
  by_cases hia : (i : Cut) < a
  · have hpd : value (restrict hGCH (a := a) p) i = some d := by
      change value (truncate p.val a) i = some d
      rw [value_truncate, if_pos hia]
      exact hd
    obtain ⟨e, he, hed⟩ := (le_iff hGCH _ _).mp hqp i hia d hpd
    refine ⟨e, ?_, ?_⟩
    · rw [value_replace hab p q i, if_pos hia]
      exact he
    · rw [truncate_replace hab hia.le p q]
      exact hed
  · exact ⟨d, by rw [value_replace hab p q i, if_neg hia]; exact hd,
      datumExtends_refl _ _ d⟩

noncomputable def complete (hGCH : GCH) {a b : Cut} (hab : a ≤ b) :
    CompleteRestriction (Stage hGCH b) (Stage hGCH a) where
  restrict := ⟨restrict hGCH, fun _ _ => restrict_le hGCH hab⟩
  embed := ⟨extend hGCH hab, fun _ _ => extend_le hGCH hab⟩
  restrict_embed := truncate_embed hab
  below_embed := below_extend_restrict hGCH hab
  lift p q hqp := ⟨replace hab p q, replace_le hGCH hab p q hqp, truncate_replace_self hab p q⟩

theorem complete_range_iff (hGCH : GCH) {a b : Cut} (hab : a ≤ b)
    (p : Stage hGCH b) :
    p ∈ Set.range (complete hGCH hab).embed ↔ ∀ i ∈ support p.val, (i : Cut) < a :=
  mem_range_embed_iff hab p

theorem restrict_restrict (hGCH : GCH) {a b c : Cut} (hab : a ≤ b)
    (p : Stage hGCH c) :
    restrict hGCH (a := a) (restrict hGCH (a := b) p) = restrict hGCH (a := a) p :=
  truncate_truncate p.val hab

theorem extend_extend (hGCH : GCH) {a b c : Cut} (hab : a ≤ b) (hbc : b ≤ c)
    (p : Stage hGCH a) :
    extend hGCH hbc (extend hGCH hab p) = extend hGCH (hab.trans hbc) p := rfl

end Erdos1172Part3TransfiniteHechlerRestrictions
