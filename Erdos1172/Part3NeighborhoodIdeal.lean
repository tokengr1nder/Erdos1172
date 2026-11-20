/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NeighborhoodCode
public import Erdos1172.Part3FiniteIdealEndpoint

@[expose] public section

/-!
# Countably complete local neighborhood ideals on omegaTwo
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NeighborhoodIdeal

open Erdos1172Part3NeighborhoodCode

def Small (r : Code ↪ W2) (G H : SimpleGraph W2) (a : W2) (s : Set W2) : Prop :=
  ∃ c : Code, r c < a ∧ a ∉ eval G H c ∧ s ⊆ eval G H c

variable {r : Code ↪ W2} {G H : SimpleGraph W2} {a : W2}

theorem small_mono {s t : Set W2} (hst : s ⊆ t)
    (ht : Small r G H a t) : Small r G H a s := by
  rcases ht with ⟨c, hc, hca, ht⟩
  exact ⟨c, hc, hca, hst.trans ht⟩

theorem empty_small (ha : GoodCut r G H a) : Small r G H a ∅ :=
  ⟨SmallUnionCode.empty, ha.empty_lt, by simp [eval], Set.empty_subset _⟩

theorem iUnion_small (ha : GoodCut r G H a) {J : Type} (s : J → Set W2)
    (hJ : #J < ℵ_ 1) (hs : ∀ j, Small r G H a (s j)) :
    Small r G H a (⋃ j, s j) := by
  classical
  choose c hc hca hcs using hs
  obtain ⟨e⟩ := (Cardinal.le_def J ℕ).mp
    (by simpa only [Cardinal.mk_nat] using Cardinal.lt_aleph_one_iff.mp hJ)
  let t : ℕ → Code := fun i =>
    if h : ∃ j, e j = i then c h.choose else SmallUnionCode.empty
  have ht (i : ℕ) : r (t i) < a ∧ a ∉ eval G H (t i) := by
    dsimp only [t]; split_ifs with h
    · exact ⟨hc h.choose, hca h.choose⟩
    · exact ⟨ha.empty_lt, by simp [eval]⟩
  refine ⟨SmallUnionCode.union t, ha.union_lt t (fun i => (ht i).1), ?_, ?_⟩
  · change a ∉ ⋃ i, eval G H (t i)
    simp only [Set.mem_iUnion, not_exists]
    exact fun i => (ht i).2
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    change x ∈ ⋃ i, eval G H (t i)
    refine Set.mem_iUnion.mpr ⟨e j, ?_⟩
    have h : ∃ j', e j' = e j := ⟨j, rfl⟩
    simpa only [t, dif_pos h, e.injective h.choose_spec] using hcs j hj

theorem union_small (ha : GoodCut r G H a) {s t : Set W2}
    (hs : Small r G H a s) (ht : Small r G H a t) :
    Small r G H a (s ∪ t) := by
  have h := iUnion_small ha (fun b : Bool => if b then s else t)
    (by simp only [Cardinal.mk_fintype, Fintype.card_bool, Nat.cast_ofNat]
        exact (Cardinal.natCast_lt_aleph0 : (2 : Cardinal) < ℵ₀).trans_le (Cardinal.aleph0_le_aleph 1))
    (fun b => by cases b <;> assumption)
  rwa [show (⋃ b : Bool, if b then s else t) = s ∪ t by ext; simp [Bool.exists_bool, or_comm]] at h

theorem bounded_interval_small (ha : GoodCut r G H a) {x : W2} (hx : x < a) :
    Small r G H a (Set.Iic x) :=
  ⟨SmallUnionCode.atom (2, x), ha.atom_lt 2 x hx, hx.not_ge, Set.Subset.rfl⟩

theorem named_compl_small (ha : GoodCut r G H a) {c : Code}
    (hc : r c < a) (hac : a ∈ eval G H c) :
    Small r G H a (eval G H c)ᶜ :=
  ⟨SmallUnionCode.compl c, ha.compl_lt c hc, not_not.mpr hac, Set.Subset.rfl⟩

theorem exists_club_positive_trace (r : Code ↪ W2) (G H : SimpleGraph W2)
    (s : Set W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, a ∈ s →
      ¬Small r G H a (s ∩ Set.Iio a) := by
  obtain ⟨club, hclub, hreflect⟩ := ClubClosure.exists_club_reflects
    r (eval G H) s alephZero_lt_cof_W2
  exact ⟨club, hclub, fun a ha has ⟨c, hc, hca, hsub⟩ => hca (hreflect a ha c hc hsub has)⟩

end Erdos1172Part3NeighborhoodIdeal
