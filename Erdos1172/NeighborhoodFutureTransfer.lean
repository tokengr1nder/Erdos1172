/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.NeighborhoodStableSpectrum
public import Erdos1172.ForMathlib.SetTheory.Ordinal.ClubTails

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172NeighborhoodFutureTransfer

open Erdos1172NeighborhoodCode Erdos1172NeighborhoodIdeal
  Erdos1172NeighborhoodIdealCore Erdos1172NeighborhoodDerivedIdeal
  Erdos1172NeighborhoodStableSpectrum

theorem stationary_inter_club {s club : Set W3} (hs : IsStationary s)
    (hc : IsClub club) : IsStationary (s ∩ club) := by
  intro test htest
  obtain ⟨a, has, hac, hat⟩ := hs (hc.inter alephZero_lt_cof_W3.ne' htest)
  exact ⟨a, ⟨has, hac⟩, hat⟩

theorem isClub_diagonalInter (clubs : W3 → Set W3) (hc : ∀ a, IsClub (clubs a)) :
    IsClub (Set.diagonalInter clubs) := by
  have hreg : (ℵ_ 3 : Cardinal.{0}).IsRegular := by
    convert Cardinal.isRegular_aleph_add_one 2 using 1 <;> norm_num
  have hunc : (ℵ₀ : Cardinal.{0}) < ℵ_ 3 := by
    simpa only [cof_W3] using alephZero_lt_cof_W3
  suffices h : ∀ C : (ω_ 3 : Ordinal.{0}).ToType → Set (ω_ 3 : Ordinal.{0}).ToType,
      (∀ a, IsClub (C a)) → IsClub (Set.diagonalInter C) from h clubs hc
  rw [← Cardinal.ord_aleph 3]
  exact Set.isClub_diagonalInter_ord (ℵ_ 3 : Cardinal.{0}) hreg hunc

def colorLoss (G H : SimpleGraph W3) (color : Bool) (source : Set W3)
    (a b : W3) : Set W3 :=
  (source ∩ Set.Iio a) ∩ {x | (colorGraph G H color).Adj x b}

/-- Absence of one outer-word extension forces a stationary future on
which the corresponding color loss is small in one earlier ideal.
The losses retain the same source trace throughout the argument. -/
theorem exists_stationary_smallLoss {r : Code ↪ W3} {G H : SimpleGraph W3}
    (word : List Bool) (color : Bool) (source domain : Set W3)
    (hd : IsStationary domain) (hgood : ∀ a ∈ domain, GoodCut r G H a)
    (hext : ∀ a ∈ domain,
      DerivedSmall r G H (color :: word) a (source ∩ Set.Iio a)) :
    ∃ a ∈ domain, ∃ future : Set W3, future ⊆ domain ∧ IsStationary future ∧
      ∀ b ∈ future, a < b ∧ DerivedSmall r G H word a
        (colorLoss G H color source a b) := by
  classical
  let goodFuture (a : W3) : Set W3 :=
    {b | b ∈ domain ∧ a < b ∧ DerivedSmall r G H word a
      (colorLoss G H color source a b)}
  by_contra hnone
  have hnonstat : ∀ a : domain, ¬IsStationary (goodFuture a.val) := by
    intro a hstat
    apply hnone
    exact ⟨a.val, a.property, goodFuture a.val, fun _ h => h.1, hstat,
      fun _ h => h.2⟩
  choose clubs hclubs hdisjoint using fun a : domain =>
    not_isStationary_iff.mp (hnonstat a)
  let allClubs : W3 → Set W3 := fun a => if h : a ∈ domain then clubs ⟨a, h⟩ else Set.univ
  have hallClubs : ∀ a, IsClub (allClubs a) := by
    intro a
    dsimp only [allClubs]
    split_ifs with h
    · exact hclubs ⟨a, h⟩
    · exact IsClub.univ
  let diagonal := Set.diagonalInter allClubs
  have hdiagonal : IsClub diagonal := isClub_diagonalInter allClubs hallClubs
  obtain ⟨reflectClub, hreflectClub, hreflect⟩ :=
    exists_club_positive_trace r G H (domain ∩ diagonal)
  obtain ⟨a, had, haDiag, haReflect⟩ := hd
    (hdiagonal.inter alephZero_lt_cof_W3.ne' hreflectClub)
  have hpositive := hreflect a haReflect ⟨had, haDiag⟩
  apply hpositive
  apply small_mono (t := {β | β < a ∧ GoodCut r G H β ∧
    ¬DerivedSmall r G H word β (sectionAt G H color a β (source ∩ Set.Iio a))})
    _ (hext a had)
  intro β hβ
  have hβd : β ∈ domain := hβ.1.1
  have hβa : β < a := hβ.2
  have hac : a ∈ clubs ⟨β, hβd⟩ := by
    have h := haDiag β hβa
    simpa only [allClubs, dif_pos hβd] using h
  have hloss : ¬DerivedSmall r G H word β (colorLoss G H color source β a) := by
    intro h
    exact Set.disjoint_left.mp (hdisjoint ⟨β, hβd⟩) ⟨had, hβa, h⟩ hac
  refine ⟨hβa, hgood β hβd, ?_⟩
  intro hsection
  apply hloss
  apply derivedSmall_mono word (hgood β hβd) _ hsection
  intro x hx
  exact ⟨⟨⟨hx.1.1, hx.1.2.trans hβa⟩, hx.2⟩, hx.1.2⟩

theorem adj_of_not_other_color (G H : SimpleGraph W3) (hcompl : IsCompl G H)
    (color : Bool) {x y : W3} (hne : x ≠ y)
    (hnot : ¬(colorGraph G H (!color)).Adj x y) :
    (colorGraph G H color).Adj x y := by
  cases color
  · change ¬G.Adj x y at hnot
    change H.Adj x y
    rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
    exact ⟨hne, hnot⟩
  · change ¬H.Adj x y at hnot
    change G.Adj x y
    rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
    exact ⟨hne, hnot⟩

/-- The stationary small-loss future closes any tail below the ideal's
completeness threshold in a color occurring in the stable word. -/
theorem target_of_stationary_smallLoss {r : Code ↪ W3}
    (G H : SimpleGraph W3) (hcompl : IsCompl G H) (system : StableSystem r G H)
    (p : WordCode) (hp : p ∈ system.patterns) (color : Bool)
    (hcolor : color ∈ word p) (γ : Ordinal.{0}) (hγ : γ ≤ ω_ 2)
    (hγcard : γ.card < ℵ_ 2) {a : W3} (ha : GoodCut r G H a)
    (rows : Set W3) (hrows : rows ⊆ Set.Iio a)
    (hpositive : ¬DerivedSmall r G H (word p) a rows)
    (future : Set W3) (hfSub : future ⊆ system.source) (hf : IsStationary future)
    (hloss : ∀ b ∈ future, a < b ∧ DerivedSmall r G H (word p) a
      (rows ∩ {x | (colorGraph G H (!color)).Adj x b})) :
    OrdinalRamsey.HasCliqueOfType (colorGraph G H color) (ω_ 2 + γ) := by
  obtain ⟨club, hclub, hstable⟩ := system.stable future hfSub hf
  obtain ⟨b, hbf, hbc⟩ := hf hclub
  have hpattern : p ∈ spectrum r G H b future := by
    rwa [hstable b hbf hbc]
  have hbGood := system.good b (hfSub hbf)
  obtain ⟨longTail, hlongSub, hlongClique, hlongType⟩ :=
    exists_core_of_derived_positive (word p) hbGood (future ∩ Set.Iio b)
      Set.inter_subset_right (mem_spectrum.mp hpattern) color hcolor
  obtain ⟨tail, htailLong, htailType⟩ := Ordinal.exists_subset_typeLT_eq longTail
    (show γ ≤ typeLT longTail by rwa [hlongType])
  have htailSub : tail ⊆ future := fun _ h => (hlongSub (htailLong h)).1
  have htailCard : #tail < ℵ_ 2 := by
    have ht : #tail = γ.card := by
      simpa only [Ordinal.card_type] using congrArg Ordinal.card htailType
    rwa [ht]
  let bad : Set W3 := ⋃ y : tail, rows ∩ {x | (colorGraph G H (!color)).Adj x y.val}
  have hbad : DerivedSmall r G H (word p) a bad :=
    derivedSmall_iUnion (word p) ha _ htailCard
      (fun y => (hloss y.val (htailSub y.property)).2)
  have hremaining : ¬DerivedSmall r G H (word p) a (rows \ bad) :=
    (derivedSmallness (word p) ha).positive_sdiff hpositive hbad
  obtain ⟨core, hcoreSub, hcoreClique, hcoreType⟩ :=
    exists_core_of_derived_positive (word p) ha (rows \ bad)
      (fun _ h => hrows h.1) hremaining color hcolor
  apply Erdos1172BlockCriterion.exists_clique_type_omegaTwo_add_of_later_block
    (colorGraph G H color) hcoreClique hcoreType
  refine ⟨tail, hlongClique.subset htailLong, htailType, ?_, ?_⟩
  · intro x hx y hy
    exact (hrows (hcoreSub hx).1).trans (hloss y (htailSub hy)).1
  · intro x hx y hy
    apply adj_of_not_other_color G H hcompl color
      ((hrows (hcoreSub hx).1).trans (hloss y (htailSub hy)).1).ne
    intro hxy
    exact (hcoreSub hx).2 (Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hcoreSub hx).1, hxy⟩)

end Erdos1172NeighborhoodFutureTransfer
