/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.NeighborhoodIdealCore

@[expose] public section

/-!
# Finite-word derived ideals from the constructed neighborhood system

The list is read from the outside inward: `b :: word` tests predecessor
sections in color `b` for positivity in the ideal indexed by `word`.
All derived ideals are closed under fewer than `alephTwo` unions and contain
the base ideal. They may be improper. No nontrivial mixed-color word is
assumed to be positive, and no endpoint transfer is asserted.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172NeighborhoodDerivedIdeal

open Erdos1172NeighborhoodCode Erdos1172NeighborhoodIdeal Erdos1172NeighborhoodIdealCore

def sectionAt (G H : SimpleGraph W3) (b : Bool) (a β : W3) (s : Set W3) : Set W3 :=
  (s ∩ {x | (colorGraph G H b).Adj x a}) ∩ Set.Iio β

def DerivedSmall (r : Code ↪ W3) (G H : SimpleGraph W3) :
    List Bool → W3 → Set W3 → Prop
  | [], a, s => Small r G H a s
  | b :: word, a, s => Small r G H a
      {β | β < a ∧ GoodCut r G H β ∧
        ¬DerivedSmall r G H word β (sectionAt G H b a β s)}

theorem sectionAt_mono (G H : SimpleGraph W3) (b : Bool) (a β : W3)
    {s t : Set W3} (hst : s ⊆ t) :
    sectionAt G H b a β s ⊆ sectionAt G H b a β t :=
  Set.inter_subset_inter_left _ (Set.inter_subset_inter_left _ hst)

theorem sectionAt_iUnion (G H : SimpleGraph W3) (b : Bool) (a β : W3)
    {J : Type} (s : J → Set W3) :
    sectionAt G H b a β (⋃ j, s j) = ⋃ j, sectionAt G H b a β (s j) := by
  simp only [sectionAt, Set.iUnion_inter]

variable {r : Code ↪ W3} {G H : SimpleGraph W3}

theorem derivedSmall_mono (word : List Bool) {a : W3} (ha : GoodCut r G H a)
    {s t : Set W3} (hst : s ⊆ t) (ht : DerivedSmall r G H word a t) :
    DerivedSmall r G H word a s := by
  induction word generalizing a s t with
  | nil => exact small_mono hst ht
  | cons b word ih =>
      apply small_mono (t := {β | β < a ∧ GoodCut r G H β ∧
        ¬DerivedSmall r G H word β (sectionAt G H b a β t)}) _ ht
      intro β hβ
      exact ⟨hβ.1, hβ.2.1, fun h => hβ.2.2
        (ih hβ.2.1 (sectionAt_mono G H b a β hst) h)⟩

theorem derivedSmall_iUnion (word : List Bool) {a : W3} (ha : GoodCut r G H a)
    {J : Type} (s : J → Set W3) (hJ : #J < ℵ_ 2)
    (hs : ∀ j, DerivedSmall r G H word a (s j)) :
    DerivedSmall r G H word a (⋃ j, s j) := by
  classical
  induction word generalizing a s with
  | nil => exact iUnion_small ha s hJ hs
  | cons b word ih =>
      let supports : J → Set W3 := fun j =>
        {β | β < a ∧ GoodCut r G H β ∧
          ¬DerivedSmall r G H word β (sectionAt G H b a β (s j))}
      have hsmall : Small r G H a (⋃ j, supports j) := iUnion_small ha supports hJ hs
      apply small_mono (t := ⋃ j, supports j) _ hsmall
      intro β hβ
      by_contra hnot
      have hall : ∀ j, DerivedSmall r G H word β (sectionAt G H b a β (s j)) := by
        intro j
        by_contra hnotj
        exact hnot (Set.mem_iUnion.mpr ⟨j, hβ.1, hβ.2.1, hnotj⟩)
      apply hβ.2.2
      rw [sectionAt_iUnion]
      exact ih hβ.2.1 _ hall

/-- The rank of a witnessing name is bounded below the current cut. Above
that rank, any later good cut omitting the name sees the same witness as
small. This supplies the coherence needed for inclusion in every derived ideal. -/
theorem base_le_derived (word : List Bool) {a : W3} (ha : GoodCut r G H a)
    {s : Set W3} (hs : Small r G H a s) : DerivedSmall r G H word a s := by
  classical
  induction word generalizing a s with
  | nil => exact hs
  | cons b word ih =>
      rcases hs with ⟨c, hc, hac, hsub⟩
      have hnamed : Small r G H a (eval G H c) := ⟨c, hc, hac, Set.Subset.rfl⟩
      have hsmall : Small r G H a (eval G H c ∪ Set.Iic (r c)) :=
        union_small ha hnamed (bounded_interval_small ha hc)
      apply small_mono (t := eval G H c ∪ Set.Iic (r c)) _ hsmall
      intro β hβ
      by_cases hmem : β ∈ eval G H c
      · exact Or.inl hmem
      by_cases hle : β ≤ r c
      · exact Or.inr hle
      exact (hβ.2.2 (ih hβ.2.1
        ⟨c, lt_of_not_ge hle, hmem, fun x hx => hsub hx.1.1⟩)).elim

/-- Adding innermost colors only enlarges the ideal. Equivalently, positivity
of a longer word implies positivity of every outer initial segment. -/
theorem derivedSmall_append (outer inner : List Bool) {a : W3}
    (ha : GoodCut r G H a) {s : Set W3}
    (hs : DerivedSmall r G H outer a s) :
    DerivedSmall r G H (outer ++ inner) a s := by
  induction outer generalizing a s with
  | nil => exact base_le_derived inner ha hs
  | cons b outer ih =>
      apply small_mono (t := {β | β < a ∧ GoodCut r G H β ∧
        ¬DerivedSmall r G H outer β (sectionAt G H b a β s)}) _ hs
      intro β hβ
      exact ⟨hβ.1, hβ.2.1, fun h => hβ.2.2 (ih hβ.2.1 h)⟩

/-- The derived ideals satisfy the existing smallness interface, without
asserting that they are proper. -/
def derivedSmallness (word : List Bool) {a : W3} (ha : GoodCut r G H a) :
    Erdos1172BHTAsymmetricEndpointFavorableOrder.AlephTwoSmallness W3 where
  small := DerivedSmall r G H word a
  mono := derivedSmall_mono word ha
  iUnion_small := derivedSmall_iUnion word ha
  union_small := by
    intro s t hs ht
    have h := derivedSmall_iUnion word ha (fun b : Bool => if b then s else t)
      (show #Bool < ℵ_ 2 by
        simp only [Cardinal.mk_fintype, Fintype.card_bool, Nat.cast_ofNat]
        exact (Cardinal.natCast_lt_aleph0 : (2 : Cardinal) < ℵ₀).trans_le
          (Cardinal.aleph0_le_aleph 2))
      (by intro b; cases b <;> assumption)
    have heq : (⋃ b : Bool, if b then s else t) = s ∪ t := by
      ext x
      simp only [Set.mem_iUnion, Bool.exists_bool, Bool.false_eq_true,
        ↓reduceIte, Set.mem_union, or_comm]
    rwa [heq] at h

theorem derivedSmall_cons_inter (b : Bool) (word : List Bool) (a : W3) (s : Set W3) :
    DerivedSmall r G H (b :: word) a (s ∩ {x | (colorGraph G H b).Adj x a}) ↔
      DerivedSmall r G H (b :: word) a s := by
  simp only [DerivedSmall, sectionAt, Set.inter_assoc, Set.inter_self]

/-- A positive derived set contains a full homogeneous core for every color
occurring in its word. Positivity remains a premise: mixed-word properness
and the future endpoint construction are separate obligations. -/
theorem exists_core_of_derived_positive (word : List Bool) {a : W3}
    (ha : GoodCut r G H a) (s : Set W3) (hsBelow : s ⊆ Set.Iio a)
    (hs : ¬DerivedSmall r G H word a s) (color : Bool) (hcolor : color ∈ word) :
    ∃ core : Set W3, core ⊆ s ∧ (colorGraph G H color).IsClique core ∧
      typeLT core = ω_ 2 := by
  classical
  induction word generalizing a s with
  | nil => simp only [List.not_mem_nil] at hcolor
  | cons b word ih =>
      rcases List.mem_cons.mp hcolor with rfl | hcolor
      · let fiber := s ∩ {x | (colorGraph G H color).Adj x a}
        have hpos : ¬DerivedSmall r G H (color :: word) a fiber := by
          rwa [derivedSmall_cons_inter]
        have hbase : ¬Small r G H a fiber := fun h =>
          hpos (base_le_derived (color :: word) ha h)
        obtain ⟨core, hc, hclique, htype⟩ := exists_core ha color fiber hbase
          (fun x hx => hsBelow hx.1) (fun x hx => hx.2)
        exact ⟨core, hc.trans Set.inter_subset_left, hclique, htype⟩
      · let support : Set W3 := {β | β < a ∧ GoodCut r G H β ∧
          ¬DerivedSmall r G H word β (sectionAt G H b a β s)}
        have hnonempty : support.Nonempty := by
          by_contra h
          apply hs
          change Small r G H a support
          rw [Set.not_nonempty_iff_eq_empty.mp h]
          exact empty_small ha
        obtain ⟨β, hβ⟩ := hnonempty
        obtain ⟨core, hc, hclique, htype⟩ := ih hβ.2.1
          (sectionAt G H b a β s) (fun _ hx => hx.2) hβ.2.2 hcolor
        exact ⟨core, hc.trans (fun _ hx => hx.1.1), hclique, htype⟩

end Erdos1172NeighborhoodDerivedIdeal
