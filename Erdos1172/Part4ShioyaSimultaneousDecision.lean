/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ClosedPartialProjection

@[expose] public section

/-! # Simultaneous decisions along a short well-order

A common extension of a short descending chain preserves each decision
made during the recursion. The empty index order allows any starting point.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya

variable {κ : Cardinal.{u}} {P L : Type u} [PartialOrder P]
variable [LinearOrder L] [WellFoundedLT L]

private theorem short_lower_bound_below (hP : ShortInfima κ P) (hL : Cardinal.mk L < κ)
    (p : P) (g : L → P) (hg : Antitone g) (hp : ∀ i, g i ≤ p) :
    ∃ b ≤ p, ∀ i, b ≤ g i := by
  classical
  by_cases hex : Nonempty L
  · obtain ⟨i⟩ := hex
    obtain ⟨b, hb⟩ := hP L hL g hg
    exact ⟨b, (hb.1 (Set.mem_range_self i)).trans (hp i), fun j => hb.1 (Set.mem_range_self j)⟩
  · exact ⟨p, le_rfl, fun i => (hex ⟨i⟩).elim⟩

/-- The full recursion only needs small proper initial segments. This
also allows a run of length κ without a final common lower bound. -/
theorem exists_dense_meeting_chain (hP : ShortInfima κ P) (hL : ∀ i : L, Cardinal.mk (Set.Iio i) < κ)
    (D : L → Set P)
    (dense : ∀ i p, ∃ q ≤ p, q ∈ D i) (p : P) :
    ∃ q : L → P, Antitone q ∧ (∀ i, q i ≤ p) ∧ ∀ i, q i ∈ D i := by
  classical
  let stage (i : L) (prior : ∀ j, j < i → P) (z : P) : Prop :=
    z ≤ p ∧ (∀ j hj, z ≤ prior j hj) ∧ z ∈ D i
  let _ : Nonempty P := ⟨p⟩
  let step (i : L) (prior : ∀ j, j < i → P) : P := Classical.epsilon (stage i prior)
  let q : L → P := wellFounded_lt.fix step
  have equation (i : L) : q i = step i (fun j _ => q j) := WellFounded.fix_eq _ _ _
  have stages (i : L) : stage i (fun j _ => q j) (q i) := by
    induction i using (wellFounded_lt : WellFounded ((· < ·) : L → L → Prop)).induction with
    | h i ih =>
      let g : Set.Iio i → P := fun j => q j.val
      have hg : Antitone g := by
        intro j k hjk
        rcases lt_or_eq_of_le hjk with h | rfl
        · exact (ih k.val k.property).2.1 j.val h
        · exact le_rfl
      obtain ⟨b, hbp, hb⟩ := short_lower_bound_below hP (hL i) p g hg (fun j => (ih j.val j.property).1)
      obtain ⟨z, hzb, hz⟩ := dense i b
      have hex : ∃ z, stage i (fun j _ => q j) z :=
        ⟨z, hzb.trans hbp, fun j hj => hzb.trans (hb ⟨j, hj⟩), hz⟩
      exact (equation i).symm ▸ Classical.epsilon_spec hex
  have hq : Antitone q := by
    intro i j hij
    rcases lt_or_eq_of_le hij with h | rfl
    · exact (stages j).2.1 i h
    · exact le_rfl
  exact ⟨q,hq,fun i => (stages i).1,fun i => (stages i).2.2⟩

/-- Any short well-ordered family of downward-closed dense sets has dense intersection. -/
theorem exists_short_dense_intersection (hP : ShortInfima κ P) (hL : Cardinal.mk L < κ)
    (D : L → Set P) (down : ∀ i, IsLowerSet (D i))
    (dense : ∀ i p, ∃ q ≤ p, q ∈ D i) (p : P) :
    ∃ r ≤ p, ∀ i, r ∈ D i := by
  obtain ⟨q,hq,hp,hD⟩ := exists_dense_meeting_chain hP (fun i => (Cardinal.mk_set_le (Set.Iio i)).trans_lt hL) D dense p
  obtain ⟨r,hrp,hr⟩ := short_lower_bound_below hP hL p q hq hp
  exact ⟨r,hrp,fun i => down i (hr i) (hD i)⟩

/-- A single strengthening decides its compatibility with each member of a short family. -/
theorem exists_short_simultaneous_decision (hP : ShortInfima κ P) (hL : Cardinal.mk L < κ)
    (f : L → P) (p : P) :
    ∃ r ≤ p, ∀ i, r ≤ f i ∨ ¬ ∃ t, t ≤ r ∧ t ≤ f i := by
  classical
  apply exists_short_dense_intersection hP hL
    (fun i => {r | r ≤ f i ∨ ¬ ∃ t, t ≤ r ∧ t ≤ f i}) _ _ p
  · intro i a b hab h
    rcases h with h | h
    · exact Or.inl (hab.trans h)
    · exact Or.inr (fun ⟨t, ht, htf⟩ => h ⟨t, ht.trans hab, htf⟩)
  · intro i b
    by_cases h : ∃ t, t ≤ b ∧ t ≤ f i
    · obtain ⟨t, htb, htf⟩ := h
      exact ⟨t, htb, Or.inl htf⟩
    · exact ⟨b, le_rfl, Or.inr h⟩

/-- All letters strictly before a position in κ can be decided at once. -/
theorem exists_simultaneous_decision_below (hP : ShortInfima κ P) (l : κ.ord.ToType)
    (f : Set.Iio l → P) (p : P) :
    ∃ r ≤ p, ∀ i, r ≤ f i ∨ ¬ ∃ t, t ≤ r ∧ t ≤ f i :=
  exists_short_simultaneous_decision hP (by simpa using Cardinal.mk_Iio_lt l (by simp)) f p

end Erdos1172Shioya
