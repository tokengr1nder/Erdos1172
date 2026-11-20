/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RedCoreDerivedIdeal
public import Erdos1172.ForMathlib.SetTheory.Ordinal.ClubTails

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part3TwoSuccessorBootstrap

open Erdos1172Part3NeighborhoodCode Erdos1172Part3NeighborhoodIdeal Erdos1172Part3FiniteIdealEndpoint Erdos1172Part3RedCoreIdeal Erdos1172Part3RedCoreDerivedIdeal

theorem stationary_inter_club {s club : Set W2} (hs : IsStationary s)
    (hc : IsClub club) : IsStationary (s ∩ club) := by
  intro test htest
  obtain ⟨a, has, hac, hat⟩ := hs (hc.inter alephZero_lt_cof_W2.ne' htest)
  exact ⟨a, ⟨has, hac⟩, hat⟩

theorem isClub_diagonalInter (clubs : W2 → Set W2) (hc : ∀ a, IsClub (clubs a)) :
    IsClub (Set.diagonalInter clubs) := by
  have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
    convert Cardinal.isRegular_aleph_add_one 1 using 1
    norm_num
  have hunc : (ℵ₀ : Cardinal.{0}) < ℵ_ 2 := by
    simpa only [cof_W2] using alephZero_lt_cof_W2
  suffices h : ∀ C : (ω_ 2 : Ordinal.{0}).ToType → Set (ω_ 2 : Ordinal.{0}).ToType,
      (∀ a, IsClub (C a)) → IsClub (Set.diagonalInter C) from h clubs hc
  rw [← Cardinal.ord_aleph 2]
  exact Set.isClub_diagonalInter_ord (ℵ_ 2 : Cardinal.{0}) hreg hunc

/-- The absence of the blue extension supplies small blue losses in one
earlier red-core ideal on a stationary future. The source trace is kept
fixed; no intersection of arbitrary positive sets is taken. -/
theorem exists_stationary_redSmall_loss {r : Code ↪ W2} {G H : SimpleGraph W2}
    (δ : Ordinal) (source domain : Set W2)
    (hd : IsStationary domain) (hgood : ∀ a ∈ domain, GoodCut r G H a)
    (hext : ∀ a ∈ domain, BlueSmall r G H δ a (source ∩ Set.Iio a)) :
    ∃ a ∈ domain, ∃ future : Set W2, future ⊆ domain ∧ IsStationary future ∧
      ∀ b ∈ future, a < b ∧ RedSmall r G H δ a
        ((source ∩ Set.Iio a) ∩ {x | H.Adj x b}) := by
  classical
  let goodFuture (a : W2) : Set W2 :=
    {b | b ∈ domain ∧ a < b ∧ RedSmall r G H δ a
      ((source ∩ Set.Iio a) ∩ {x | H.Adj x b})}
  by_contra hnone
  have hnonstat : ∀ a : domain, ¬IsStationary (goodFuture a.val) := by
    intro a hstat
    apply hnone
    exact ⟨a.val, a.property, goodFuture a.val, fun _ h => h.1, hstat, fun _ h => h.2⟩
  choose clubs hclubs hdisjoint using fun a : domain =>
    not_isStationary_iff.mp (hnonstat a)
  let allClubs : W2 → Set W2 := fun a => if h : a ∈ domain then clubs ⟨a, h⟩ else Set.univ
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
    (hdiagonal.inter alephZero_lt_cof_W2.ne' hreflectClub)
  have hpositive := hreflect a haReflect ⟨had, haDiag⟩
  apply hpositive
  apply small_mono (t := {b | b < a ∧ GoodCut r G H b ∧
    ¬RedSmall r G H δ b (blueSection H a b (source ∩ Set.Iio a))}) _ (hext a had)
  intro b hb
  have hbd : b ∈ domain := hb.1.1
  have hba : b < a := hb.2
  have hac : a ∈ clubs ⟨b, hbd⟩ := by
    have h := haDiag b hba
    simpa only [allClubs, dif_pos hbd] using h
  refine ⟨hba, hgood b hbd, ?_⟩
  intro hsection
  have hloss : RedSmall r G H δ b
      ((source ∩ Set.Iio b) ∩ {x | H.Adj x a}) :=
    redSmall_mono (show ((source ∩ Set.Iio b) ∩ {x | H.Adj x a}) ⊆
      blueSection H a b (source ∩ Set.Iio a) from
        fun _ hx => ⟨⟨⟨hx.1.1, hx.1.2.trans hba⟩, hx.2⟩, hx.1.2⟩) hsection
  exact Set.disjoint_left.mp (hdisjoint ⟨b, hbd⟩) ⟨had, hba, hloss⟩ hac

theorem isCofinal_of_stationary {s : Set W2} (hs : IsStationary s) : IsCofinal s := by
  intro a
  obtain ⟨b, hb, hab⟩ := hs (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 a)
  exact ⟨b, hb, hab.le⟩

theorem targets_of_stationary_small_loss {r : Code ↪ W2}
    (G H : SimpleGraph W2) (hcompl : IsCompl G H) (e : Ordinal)
    {a : W2} (ha : GoodCut r G H a) (rows : Set W2)
    (hrows : rows ⊆ Set.Iio a) (hpos : ¬RedSmall r G H (ω ^ e) a rows)
    (future : Set W2) (hf : IsStationary future)
    (hloss : ∀ b ∈ future, a < b ∧ RedSmall r G H (ω ^ e) a
      (rows ∩ {x | H.Adj x b})) : Targets G H (ω ^ e) := by
  classical
  by_cases hpair : ∃ p ∈ future, ∃ q ∈ future, p < q ∧ G.Adj p q
  · obtain ⟨p, hp, q, hq, hpq, hpqG⟩ := hpair
    let bad := (rows ∩ {x | H.Adj x p}) ∪ (rows ∩ {x | H.Adj x q})
    have hbad : RedSmall r G H (ω ^ e) a bad :=
      redSmall_union ha e (hloss p hp).2 (hloss q hq).2
    have hremain := (redSmallness ha e).positive_sdiff hpos hbad
    obtain ⟨c, hc, hcl, hct⟩ := core_of_red_positive ha hremain
    have hredp : ∀ x ∈ c, G.Adj x p := by
      intro x hx
      rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
      exact ⟨((hrows (hc hx).1).trans (hloss p hp).1).ne,
        fun h => (hc hx).2 (Or.inl ⟨(hc hx).1, h⟩)⟩
    have hredq : ∀ x ∈ c, G.Adj x q := by
      intro x hx
      rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
      exact ⟨((hrows (hc hx).1).trans (hloss q hq).1).ne,
        fun h => (hc hx).2 (Or.inr ⟨(hc hx).1, h⟩)⟩
    exact Or.inl (clique_add_two hcl hct
      (fun x hx => (hrows (hc hx).1).trans (hloss p hp).1) hpq hpqG hredp hredq)
  · have hH : H.IsClique future := by
      intro x hx y hy hxy
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      refine ⟨hxy, ?_⟩
      intro hG
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · exact hpair ⟨x, hx, y, hy, hlt, hG⟩
      · exact hpair ⟨y, hy, x, hx, hgt, hG.symm⟩
    have htype : typeLT future = ω_ 2 :=
      Erdos1172Part3Failure.typeLT_eq_omegaTwo_of_mk_eq
        (mk_eq_alephTwo_of_isCofinal (isCofinal_of_stationary hf))
    obtain ⟨c, hc, hct⟩ := Ordinal.exists_subset_typeLT_eq future
      (show (ω_ 1 : Ordinal) + 2 ≤ typeLT future by
        rw [htype]; exact blue_target_le_omegaTwo)
    exact Or.inr ⟨c, hH.subset hc, hct⟩

/-- Under GCH the two final red points can be supplied from the core
relation, for any additive-indecomposable red core below `omegaTwo`.
The core relation remains an explicit hypothesis. -/
theorem ordinalRamsey_add_two_of_core (hGCH : GCH) (e : Ordinal.{0})
    (hδ : ω ^ e + 2 ≤ ω_ 2)
    (hcore : OrdinalRamsey (ω_ 2) (ω ^ e) (ω_ 1 + 2)) :
    OrdinalRamsey (ω_ 2) (ω ^ e + 2) (ω_ 1 + 2) := by
  classical
  intro G H hcompl
  by_contra hno
  have hδlt : ω ^ e < ω_ 2 := by
    apply lt_of_lt_of_le _ hδ
    calc
      ω ^ e < (ω ^ e + 1) + 1 := (lt_add_one _).trans (lt_add_one _)
      _ = ω ^ e + 2 := by rw [add_assoc, one_add_one_eq_two]
  have hcard : (ω ^ e).card < ℵ_ 2 := by
    rwa [Cardinal.lt_omega_iff_card_lt] at hδlt
  have hlarge : ∀ s : Set W2, #s = ℵ_ 2 → HasCore G (ω ^ e) s := by
    intro s hs
    obtain hred | ⟨c, _, hc, hct⟩ := hcore.on_set_of_type G H hcompl s
      (Erdos1172Part3Failure.typeLT_eq_omegaTwo_of_mk_eq hs)
    · exact hred
    · exact (hno (Or.inr ⟨c, hc, hct⟩)).elim
  let r := rank hGCH
  let source := {a | GoodCut r G H a}
  have hsource : IsStationary source := isStationary_goodCut hGCH.toCH r G H
  obtain ⟨club, hclub, hpositive⟩ := exists_club_red_positive_trace r G H
    (ω ^ e) hcard hlarge source
  let domain := source ∩ club
  have hd : IsStationary domain := stationary_inter_club hsource hclub
  obtain ⟨a, had, future, _, hf, hloss⟩ := exists_stationary_redSmall_loss
    (ω ^ e) source domain hd (fun _ h => h.1) (by
      intro a ha
      exact blueSmall_mono Set.inter_subset_right
        (blueSmall_prior_of_no_targets G H hcompl e hδ hno ha.1))
  exact hno (targets_of_stationary_small_loss G H hcompl e had.1
    (source ∩ Set.Iio a) Set.inter_subset_right (hpositive a had.2 had.1)
    future hf hloss)

theorem ordinalRamsey_add_two_iff_core (hGCH : GCH) (e : Ordinal.{0})
    (hδ : ω ^ e + 2 ≤ ω_ 2) :
    OrdinalRamsey (ω_ 2) (ω ^ e + 2) (ω_ 1 + 2) ↔
      OrdinalRamsey (ω_ 2) (ω ^ e) (ω_ 1 + 2) :=
  ⟨fun h => h.mono_targets le_self_add le_rfl, ordinalRamsey_add_two_of_core hGCH e hδ⟩

/-- Exact Part 3 is equivalent to its red-core version under GCH. The
right-hand statement, not a second-maximum extension premise, is the
remaining obligation of this route. -/
theorem part3_iff_core (hGCH : GCH) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0}) ((ω_ 1) ^ (ω + 2) + 2) (ω_ 1 + 2) ↔
      OrdinalRamsey (ω_ 2 : Ordinal.{0}) ((ω_ 1) ^ (ω + 2)) (ω_ 1 + 2) := by
  obtain ⟨e, he⟩ := Erdos1172Part3BHTExactBlueColumns.exists_redCoreTarget_eq_omega_opow
  have hbound : ω ^ e + 2 ≤ ω_ 2 := by
    rw [← he]
    exact Erdos1172Part3Failure.part3_red_target_lt_omegaTwo.le
  simpa only [← he, Erdos1172Part3OneSuccessorBarrier.RedCoreTarget] using
    ordinalRamsey_add_two_iff_core hGCH e hbound

end Erdos1172Part3TwoSuccessorBootstrap
