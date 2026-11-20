/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CenteredStationaryLoss

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part3TraceDerivedIdeal

open Erdos1172Part3CoreObjectCode Erdos1172Part3CoreObjectIdeal
open Erdos1172Part3CoreObjectIdealCore Erdos1172Part3FiniteIdealEndpoint
open Erdos1172Part3NeighborhoodCode (W2 alephZero_lt_cof_W2)
open Erdos1172Part3RedCoreDerivedIdeal (blueSection)
open Erdos1172Part3TwoSuccessorBootstrap (isClub_diagonalInter stationary_inter_club)
open Erdos1172Part3CenteredStationaryLoss (exists_stationary_fiber_of_small)
open OrdinalRamsey (HasCliqueOfType)

def BlueSmall (r : Code ↪ W2) (G H : SimpleGraph W2) (domain : Set W2)
    (J : W2 → FiniteSmallness W2) (a : W2) (s : Set W2) : Prop :=
  Small r G H a {b | b < a ∧ b ∈ domain ∧ ¬(J b).small (blueSection H a b s)}

variable {r : Code ↪ W2} {σ : Obj ↪ W2} {G H : SimpleGraph W2}
  {domain : Set W2} {J : W2 → FiniteSmallness W2} {a : W2}

theorem blueSmall_mono {s t : Set W2} (hst : s ⊆ t)
    (ht : BlueSmall r G H domain J a t) : BlueSmall r G H domain J a s := by
  apply small_mono (t := {b | b < a ∧ b ∈ domain ∧
    ¬(J b).small (blueSection H a b t)}) _ ht
  intro b hb
  exact ⟨hb.1, hb.2.1, fun h => hb.2.2 ((J b).mono
    (show blueSection H a b s ⊆ blueSection H a b t from
      fun _ hx => ⟨⟨hst hx.1.1, hx.1.2⟩, hx.2⟩) h)⟩

theorem blueSmall_union (ha : GoodCut r σ G H a) {s t : Set W2}
    (hs : BlueSmall r G H domain J a s) (ht : BlueSmall r G H domain J a t) :
    BlueSmall r G H domain J a (s ∪ t) := by
  let left := {b | b < a ∧ b ∈ domain ∧ ¬(J b).small (blueSection H a b s)}
  let right := {b | b < a ∧ b ∈ domain ∧ ¬(J b).small (blueSection H a b t)}
  apply small_mono (t := left ∪ right) _ (union_small ha hs ht)
  intro b hb
  by_contra hnot
  have hleft : (J b).small (blueSection H a b s) := by
    by_contra h
    exact hnot (Or.inl ⟨hb.1, hb.2.1, h⟩)
  have hright : (J b).small (blueSection H a b t) := by
    by_contra h
    exact hnot (Or.inr ⟨hb.1, hb.2.1, h⟩)
  apply hb.2.2
  have heq : blueSection H a b (s ∪ t) =
      blueSection H a b s ∪ blueSection H a b t := by
    simp only [blueSection, Set.union_inter_distrib_right]
  rw [heq]
  exact (J b).union_small hleft hright

theorem base_le_blue (ha : GoodCut r σ G H a)
    (hbase : ∀ b ∈ domain, ∀ x : Set W2, Small r G H b x → (J b).small x)
    {s : Set W2} (hs : Small r G H a s) : BlueSmall r G H domain J a s := by
  obtain ⟨c, hc, hac, hsub⟩ := hs
  have hnamed : Small r G H a (eval G H c) := ⟨c, hc, hac, Set.Subset.rfl⟩
  apply small_mono (t := eval G H c ∪ Set.Iic (r c)) _
    (union_small ha hnamed (bounded_interval_small ha hc))
  intro b hb
  by_cases hmem : b ∈ eval G H c
  · exact Or.inl hmem
  by_cases hle : b ≤ r c
  · exact Or.inr hle
  exact (hb.2.2 (hbase b hb.2.1 _
    ⟨c, lt_of_not_ge hle, hmem, fun _ hx => hsub hx.1.1⟩)).elim

def blueSmallness (ha : GoodCut r σ G H a)
    (hbase : ∀ b ∈ domain, ∀ x : Set W2, Small r G H b x → (J b).small x) :
    FiniteSmallness W2 where
  small := BlueSmall r G H domain J a
  empty_small := base_le_blue ha hbase (empty_small ha)
  mono := blueSmall_mono
  union_small := blueSmall_union ha

theorem blueSmall_inter (s : Set W2) :
    BlueSmall r G H domain J a (s ∩ {x | H.Adj x a}) ↔ BlueSmall r G H domain J a s := by
  simp only [BlueSmall, blueSection, Set.inter_assoc, Set.inter_self]

theorem blue_core_of_positive (ha : GoodCut r σ G H a)
    (hbase : ∀ b ∈ domain, ∀ x : Set W2, Small r G H b x → (J b).small x)
    {s : Set W2} (hsub : s ⊆ Set.Iio a) (hs : ¬BlueSmall r G H domain J a s) :
    ∃ c : Set W2, c ⊆ s ∧ H.IsClique c ∧ typeLT c = ω_ 1 := by
  let fiber := s ∩ {x | H.Adj x a}
  have hf : ¬BlueSmall r G H domain J a fiber := by rwa [blueSmall_inter]
  have hpos : ¬Small r G H a fiber := fun h => hf (base_le_blue ha hbase h)
  obtain ⟨c, hc, hcl, hct⟩ := exists_core ha false fiber hpos
    (fun _ hx => hsub hx.1) (fun _ hx => hx.2)
  exact ⟨c, hc.trans Set.inter_subset_left, hcl, hct⟩

/-- If all source traces are derived-small, diagonal reflection supplies
stationarily many small losses in one earlier ideal. -/
theorem exists_loss_of_all_blueSmall (source : Set W2) (hd : IsStationary domain)
    (hext : ∀ a ∈ domain, BlueSmall r G H domain J a (source ∩ Set.Iio a)) :
    ∃ a ∈ domain, ∃ future : Set W2, future ⊆ domain ∧ IsStationary future ∧
      ∀ b ∈ future, a < b ∧ (J a).small ((source ∩ Set.Iio a) ∩ {x | H.Adj x b}) := by
  classical
  let goodFuture (a : W2) : Set W2 := {b | b ∈ domain ∧ a < b ∧
    (J a).small ((source ∩ Set.Iio a) ∩ {x | H.Adj x b})}
  by_contra hnone
  have hnonstat : ∀ a : domain, ¬IsStationary (goodFuture a.val) := by
    intro a hstat
    exact hnone ⟨a.val, a.property, goodFuture a.val, fun _ h => h.1, hstat, fun _ h => h.2⟩
  choose clubs hclubs hdisjoint using fun a : domain => not_isStationary_iff.mp (hnonstat a)
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
  apply hreflect a haReflect ⟨had, haDiag⟩
  apply small_mono (t := {b | b < a ∧ b ∈ domain ∧
    ¬(J b).small (blueSection H a b (source ∩ Set.Iio a))}) _ (hext a had)
  intro b hb
  have hbd : b ∈ domain := hb.1.1
  have hba : b < a := hb.2
  have hac : a ∈ clubs ⟨b, hbd⟩ := by
    simpa only [allClubs, dif_pos hbd] using haDiag b hba
  refine ⟨hba, hbd, ?_⟩
  intro hsection
  have hloss : (J b).small ((source ∩ Set.Iio b) ∩ {x | H.Adj x a}) :=
    (J b).mono (show ((source ∩ Set.Iio b) ∩ {x | H.Adj x a}) ⊆
      blueSection H a b (source ∩ Set.Iio a) from
        fun _ hx => ⟨⟨⟨hx.1.1, hx.1.2.trans hba⟩, hx.2⟩, hx.1.2⟩) hsection
  exact Set.disjoint_left.mp (hdisjoint ⟨b, hbd⟩) ⟨had, hba, hloss⟩ hac

/-- Pull stationary derived-small losses back to one earlier ideal while
preserving positivity of the fixed row set. -/
theorem exists_earlier_positive_loss {s future : Set W2}
    (hs : ¬BlueSmall r G H domain J a s) (hf : IsStationary future)
    (hloss : ∀ b ∈ future, BlueSmall r G H domain J a (s ∩ {x | H.Adj x b})) :
    ∃ b ∈ domain, b < a ∧ ¬(J b).small (blueSection H a b s) ∧
      ∃ later : Set W2, later ⊆ future ∧ IsStationary later ∧
        ∀ c ∈ later, (J b).small (blueSection H a b s ∩ {x | H.Adj x c}) := by
  classical
  let support := {b | b < a ∧ b ∈ domain ∧ ¬(J b).small (blueSection H a b s)}
  have chooseEarlier (c : future) : ∃ b : Set.Iio a, b.val ∈ domain ∧
      ¬(J b.val).small (blueSection H a b.val s) ∧
        (J b.val).small (blueSection H a b.val s ∩ {x | H.Adj x c.val}) := by
    let bad := {b | b < a ∧ b ∈ domain ∧
      ¬(J b).small (blueSection H a b (s ∩ {x | H.Adj x c.val}))}
    have hnot : ¬support ⊆ bad := fun h => hs (small_mono h (hloss c.val c.property))
    obtain ⟨b, hb, hbad⟩ := Set.not_subset.mp hnot
    have hsmall : (J b).small (blueSection H a b (s ∩ {x | H.Adj x c.val})) := by
      by_contra h
      exact hbad ⟨hb.1, hb.2.1, h⟩
    refine ⟨⟨b, hb.1⟩, hb.2.1, hb.2.2, (J b).mono ?_ hsmall⟩
    intro x hx
    exact ⟨⟨⟨hx.1.1.1, hx.2⟩, hx.1.1.2⟩, hx.1.2⟩
  let chosen : future → Set.Iio a := fun c => (chooseEarlier c).choose
  have hiio : #(Set.Iio a) < ℵ_ 2 := by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using
      Cardinal.mk_Iio_lt a (Cardinal.ord_cardinalMk (α := W2))
  obtain ⟨b, hb⟩ := exists_stationary_fiber_of_small hiio hf chosen
  obtain ⟨sample, hsamp, heq⟩ := hb.nonempty
  have hsample := (chooseEarlier ⟨sample, hsamp⟩).choose_spec
  have hval : (chooseEarlier ⟨sample, hsamp⟩).choose = b := heq
  rw [hval] at hsample
  refine ⟨b.val, hsample.1, b.property, hsample.2.1,
    {c | ∃ hc : c ∈ future, chosen ⟨c, hc⟩ = b}, fun _ h => h.choose, hb, ?_⟩
  rintro c ⟨hc, heq⟩
  have h := (chooseEarlier ⟨c, hc⟩).choose_spec.2.2
  have hval : (chooseEarlier ⟨c, hc⟩).choose = b := heq
  rwa [hval] at h

/-- Either the derived ideal is proper somewhere, or diagonal reflection
applies everywhere. Both cases give the same stationary small-loss data. -/
theorem exists_positive_stationary_loss (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (source : Set W2) (hd : IsStationary domain)
    (hgood : ∀ a ∈ domain, GoodCut r σ G H a)
    (hbase : ∀ b ∈ domain, ∀ x : Set W2, Small r G H b x → (J b).small x)
    (hpos : ∀ a ∈ domain, ¬(J a).small (source ∩ Set.Iio a))
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) :
    ∃ a ∈ domain, ∃ x : Set W2, x ⊆ source ∩ Set.Iio a ∧ ¬(J a).small x ∧
      ∃ future : Set W2, future ⊆ domain ∧ IsStationary future ∧
        ∀ b ∈ future, a < b ∧ (J a).small (x ∩ {v | H.Adj v b}) := by
  classical
  by_cases hext : ∀ a ∈ domain, BlueSmall r G H domain J a (source ∩ Set.Iio a)
  · obtain ⟨a, had, future, hfd, hf, hloss⟩ := exists_loss_of_all_blueSmall source hd hext
    exact ⟨a, had, source ∩ Set.Iio a, Set.Subset.rfl, hpos a had,
      future, hfd, hf, hloss⟩
  · push Not at hext
    obtain ⟨a, had, hpositive⟩ := hext
    let prior := source ∩ Set.Iio a
    let later := domain ∩ Set.Ioi a
    have hlater : IsStationary later := stationary_inter_club hd
      (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W2 a)
    obtain ⟨x, hxp, hxpos, future, hfl, hf, hloss⟩ :=
      Erdos1172Part3CenteredStationaryLoss.exists_stationary_small_loss
        (blueSmallness (hgood a had) hbase) G H hcompl prior later a
        Set.inter_subset_right Set.inter_subset_right hpositive hlater hred hblue
        (fun s hsp hspPos => blue_core_of_positive (hgood a had) hbase
          (hsp.trans Set.inter_subset_right) hspPos)
    obtain ⟨b, hbd, hba, hbpos, final, hff, hfinal, hfinalLoss⟩ :=
      exists_earlier_positive_loss hxpos hf hloss
    refine ⟨b, hbd, blueSection H a b x, ?_, hbpos, final,
      hff.trans (hfl.trans Set.inter_subset_left), hfinal, ?_⟩
    · intro v hv
      exact ⟨(hxp hv.1.1).1, hv.2⟩
    · intro c hc
      exact ⟨hba.trans (hfl (hff hc)).2, hfinalLoss c hc⟩

end Erdos1172Part3TraceDerivedIdeal
