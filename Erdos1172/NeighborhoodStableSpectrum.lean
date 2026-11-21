/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.NeighborhoodFavorableClosure

@[expose] public section

/-!
# Stationary stabilization of the four relevant color words

The spectrum records positivity of the trace of the specified stationary
set, not merely properness of the ideal on the entire initial interval.
This distinction is retained through every stationary thinning.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172NeighborhoodStableSpectrum

open Erdos1172NeighborhoodCode Erdos1172NeighborhoodIdeal Erdos1172NeighborhoodIdealCore Erdos1172NeighborhoodDerivedIdeal

abbrev WordCode := Fin 4

def word : WordCode → List Bool
  | 0 => [false]
  | 1 => [true]
  | 2 => [false, true]
  | 3 => [true, false]

noncomputable def spectrum (r : Code ↪ W3) (G H : SimpleGraph W3)
    (a : W3) (s : Set W3) : Finset WordCode := by
  classical
  exact Finset.univ.filter (fun p => ¬DerivedSmall r G H (word p) a (s ∩ Set.Iio a))

@[simp] theorem mem_spectrum {r : Code ↪ W3} {G H : SimpleGraph W3}
    {a : W3} {s : Set W3} {p : WordCode} :
    p ∈ spectrum r G H a s ↔ ¬DerivedSmall r G H (word p) a (s ∩ Set.Iio a) := by
  classical
  simp only [spectrum, Finset.mem_filter, Finset.mem_univ, true_and]

theorem spectrum_mono {r : Code ↪ W3} {G H : SimpleGraph W3}
    {a : W3} (ha : GoodCut r G H a) {s t : Set W3} (hst : s ⊆ t) :
    spectrum r G H a s ⊆ spectrum r G H a t := by
  intro p hp
  rw [mem_spectrum] at hp ⊢
  exact fun h => hp (derivedSmall_mono _ ha (Set.inter_subset_inter_left _ hst) h)

theorem exists_stable_spectrum {r : Code ↪ W3} {G H : SimpleGraph W3}
    (domain : Set W3) (hstationary : IsStationary domain)
    (hgood : ∀ a ∈ domain, GoodCut r G H a) :
    ∃ s : Set W3, s ⊆ domain ∧ IsStationary s ∧ ∃ patterns : Finset WordCode,
      (∀ a ∈ s, spectrum r G H a s ⊆ patterns) ∧
      ∀ t : Set W3, t ⊆ s → IsStationary t →
        ∃ club : Set W3, IsClub club ∧ ∀ a ∈ t, a ∈ club → spectrum r G H a t = patterns := by
  classical
  let admissible : Nat → Prop := fun n =>
    ∃ s : Set W3, s ⊆ domain ∧ IsStationary s ∧ ∃ p : Finset WordCode,
      p.card = n ∧ ∀ a ∈ s, spectrum r G H a s ⊆ p
  have hex : ∃ n, admissible n :=
    ⟨(Finset.univ : Finset WordCode).card, domain, Set.Subset.rfl,
      hstationary, Finset.univ, rfl, fun _ _ => Finset.subset_univ _⟩
  obtain ⟨s, hsDomain, hs, patterns, hcard, hbound⟩ := Nat.find_spec hex
  have hminimal (t : Set W3) (htDomain : t ⊆ domain) (ht : IsStationary t)
      (q : Finset WordCode) (hq : ∀ a ∈ t, spectrum r G H a t ⊆ q) :
      patterns.card ≤ q.card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨t, htDomain, ht, q, rfl, hq⟩
  refine ⟨s, hsDomain, hs, patterns, hbound, ?_⟩
  intro t hts ht
  let bad : Set W3 := {a | a ∈ t ∧ spectrum r G H a t ≠ patterns}
  have hbad : ¬IsStationary bad := by
    intro hbad
    let fiber : Finset WordCode → Set W3 := fun q =>
      {a | a ∈ bad ∧ spectrum r G H a t = q}
    have hunion : (⋃ q, fiber q) = bad := by
      ext a
      simp only [fiber, Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨fun ⟨_, ha, _⟩ => ha, fun ha => ⟨spectrum r G H a t, ha, rfl⟩⟩
    have hstatUnion : IsStationary (⋃ q, fiber q) := hunion.symm ▸ hbad
    obtain ⟨q, hq⟩ := (isStationary_iUnion_iff_of_countable alephZero_lt_cof_W3.ne').mp hstatUnion
    have hqt : fiber q ⊆ t := fun _ hx => hx.1.1
    have hqdomain : fiber q ⊆ domain := hqt.trans (hts.trans hsDomain)
    have hqbound : ∀ a ∈ fiber q, spectrum r G H a (fiber q) ⊆ q := by
      intro a ha p hp
      have hp' := spectrum_mono (hgood a (hqdomain ha)) hqt hp
      rwa [ha.2] at hp'
    obtain ⟨a, ha⟩ := hq.nonempty
    have hqsub : q ⊆ patterns := by
      rw [← ha.2]
      exact (spectrum_mono (hgood a (hqdomain ha)) hts).trans (hbound a (hts ha.1.1))
    have hqne : q ≠ patterns := by
      simpa only [ha.2] using ha.1.2
    have hlt : q.card < patterns.card := Finset.card_lt_card (lt_of_le_of_ne hqsub hqne)
    exact hlt.not_ge (hminimal (fiber q) hqdomain hq q hqbound)
  obtain ⟨club, hclub, hdisj⟩ := not_isStationary_iff.mp hbad
  refine ⟨club, hclub, ?_⟩
  intro a hat hac
  by_contra hne
  exact Set.disjoint_left.mp hdisj ⟨hat, hne⟩ hac

/-- Reflection of the stationary source at both levels forces at least
one singleton word to be positive on a club of source points. -/
theorem exists_club_singleton_positive {r : Code ↪ W3}
    (G H : SimpleGraph W3) (hcompl : IsCompl G H) (s : Set W3)
    (hgood : ∀ a ∈ s, GoodCut r G H a) :
    ∃ club : Set W3, IsClub club ∧ ∀ a ∈ s, a ∈ club →
      ∃ b : Bool, ¬DerivedSmall r G H [b] a (s ∩ Set.Iio a) := by
  classical
  obtain ⟨c₀, hc₀, hr₀⟩ := exists_club_positive_trace r G H s
  obtain ⟨c₁, hc₁, hr₁⟩ := exists_club_positive_trace r G H (s ∩ c₀)
  refine ⟨c₀ ∩ c₁, hc₀.inter alephZero_lt_cof_W3.ne' hc₁, ?_⟩
  intro a has ha
  by_contra h
  push Not at h
  let support (b : Bool) : Set W3 := {β | β < a ∧ GoodCut r G H β ∧
    ¬Small r G H β (sectionAt G H b a β (s ∩ Set.Iio a))}
  have hsupp (b : Bool) : Small r G H a (support b) := h b
  have hsmall : Small r G H a (support false ∪ support true) :=
    union_small (hgood a has) (hsupp false) (hsupp true)
  apply hr₁ a ha.2 ⟨has, ha.1⟩
  apply small_mono (t := support false ∪ support true) _ hsmall
  intro β hβ
  have hβgood := hgood β hβ.1.1
  have hβpositive := hr₀ β hβ.1.2 hβ.1.1
  by_contra hnot
  have hfalse : Small r G H β (sectionAt G H false a β (s ∩ Set.Iio a)) := by
    by_contra hn
    exact hnot (Or.inl ⟨hβ.2, hβgood, hn⟩)
  have htrue : Small r G H β (sectionAt G H true a β (s ∩ Set.Iio a)) := by
    by_contra hn
    exact hnot (Or.inr ⟨hβ.2, hβgood, hn⟩)
  apply hβpositive
  apply small_mono (t := sectionAt G H false a β (s ∩ Set.Iio a) ∪
    sectionAt G H true a β (s ∩ Set.Iio a)) _ (union_small hβgood hfalse htrue)
  intro x hx
  have hxa : x < a := hx.2.trans hβ.2
  by_cases hred : G.Adj x a
  · exact Or.inr ⟨⟨⟨hx.1, hxa⟩, hred⟩, hx.2⟩
  · have hblue : H.Adj x a := by
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      exact ⟨hxa.ne, hred⟩
    exact Or.inl ⟨⟨⟨hx.1, hxa⟩, hblue⟩, hx.2⟩

structure StableSystem (r : Code ↪ W3) (G H : SimpleGraph W3) where
  source : Set W3
  stationary : IsStationary source
  good : ∀ a ∈ source, GoodCut r G H a
  patterns : Finset WordCode
  nonempty : patterns.Nonempty
  bound : ∀ a ∈ source, spectrum r G H a source ⊆ patterns
  stable : ∀ t : Set W3, t ⊆ source → IsStationary t →
    ∃ club : Set W3, IsClub club ∧ ∀ a ∈ t, a ∈ club →
      spectrum r G H a t = patterns

/-- GCH supplies a nonempty stationary stable spectrum for every coloring. -/
theorem exists_stableSystem (hGCH : GCH) (r : Code ↪ W3)
    (G H : SimpleGraph W3) (hcompl : IsCompl G H) :
    Nonempty (StableSystem r G H) := by
  obtain ⟨s, hsgood, hs, patterns, hbound, hstable⟩ := exists_stable_spectrum
    {a | GoodCut r G H a} (isStationary_goodCut hGCH r G H) (fun _ h => h)
  have hgood : ∀ a ∈ s, GoodCut r G H a := fun _ h => hsgood h
  obtain ⟨club, hclub, hsingle⟩ := exists_club_singleton_positive G H hcompl s hgood
  obtain ⟨a, has, hac⟩ := hs hclub
  obtain ⟨b, hb⟩ := hsingle a has hac
  have hnonempty : patterns.Nonempty := by
    cases b
    · exact ⟨0, hbound a has (mem_spectrum.mpr hb)⟩
    · exact ⟨1, hbound a has (mem_spectrum.mpr hb)⟩
  exact ⟨⟨s, hs, hgood, patterns, hnonempty, hbound, hstable⟩⟩

end Erdos1172NeighborhoodStableSpectrum
