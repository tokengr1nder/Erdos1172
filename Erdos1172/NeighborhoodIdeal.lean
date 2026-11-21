/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.NeighborhoodCode
public import Erdos1172.BHTAsymmetricEndpointFavorableOrder

@[expose] public section

/-!
# Proper, small-union-complete neighborhood ideals
-/

open Cardinal Ordinal Set Order

namespace Erdos1172NeighborhoodIdeal

open Erdos1172NeighborhoodCode

theorem codedSmall_iUnion {B : Type} {r : SmallUnionCode.Code W1 B ↪ W3}
    {atms : B → Set W3} {a : W3}
    (hempty : r SmallUnionCode.empty < a)
    (hunion : ∀ c : W1 → SmallUnionCode.Code W1 B, (∀ i, r (c i) < a) →
      r (SmallUnionCode.union c) < a)
    {J : Type} (s : J → Set W3) (hJ : #J < ℵ_ 2)
    (hs : ∀ j, ∃ c, r c < a ∧ a ∉ SmallUnionCode.eval atms c ∧ s j ⊆ SmallUnionCode.eval atms c) :
    ∃ c, r c < a ∧ a ∉ SmallUnionCode.eval atms c ∧ (⋃ j, s j) ⊆ SmallUnionCode.eval atms c := by
  classical
  choose c hc hca hcs using hs
  obtain ⟨e⟩ := (Cardinal.le_def J W1).mp
    (by simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_le_alephOne_of_lt_alephTwo hJ)
  let t : W1 → SmallUnionCode.Code W1 B := fun i =>
    if h : ∃ j, e j = i then c h.choose else SmallUnionCode.empty
  have ht (i : W1) : r (t i) < a ∧ a ∉ SmallUnionCode.eval atms (t i) := by
    dsimp only [t]; split_ifs with h
    · exact ⟨hc h.choose, hca h.choose⟩
    · exact ⟨hempty, by simp⟩
  refine ⟨SmallUnionCode.union t, hunion t (fun i => (ht i).1), ?_, ?_⟩
  · simp only [SmallUnionCode.eval_union, Set.mem_iUnion, not_exists]
    exact fun i => (ht i).2
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rw [SmallUnionCode.eval_union]
    refine Set.mem_iUnion.mpr ⟨e j, ?_⟩
    have h : ∃ j', e j' = e j := ⟨j, rfl⟩
    simpa only [t, dif_pos h, e.injective h.choose_spec] using hcs j hj

theorem codedSmall_union {B : Type} {r : SmallUnionCode.Code W1 B ↪ W3}
    {atms : B → Set W3} {a : W3}
    (hempty : r SmallUnionCode.empty < a)
    (hunion : ∀ c : W1 → SmallUnionCode.Code W1 B, (∀ i, r (c i) < a) →
      r (SmallUnionCode.union c) < a)
    {s t : Set W3}
    (hs : ∃ c, r c < a ∧ a ∉ SmallUnionCode.eval atms c ∧ s ⊆ SmallUnionCode.eval atms c)
    (ht : ∃ c, r c < a ∧ a ∉ SmallUnionCode.eval atms c ∧ t ⊆ SmallUnionCode.eval atms c) :
    ∃ c, r c < a ∧ a ∉ SmallUnionCode.eval atms c ∧ (s ∪ t) ⊆ SmallUnionCode.eval atms c := by
  have h := codedSmall_iUnion hempty hunion (fun b : Bool => if b then s else t)
    (by simp only [Cardinal.mk_fintype, Fintype.card_bool, Nat.cast_ofNat]
        exact (Cardinal.natCast_lt_aleph0 : (2 : Cardinal) < ℵ₀).trans_le (Cardinal.aleph0_le_aleph 2))
    (fun b => by cases b <;> assumption)
  rwa [show (⋃ b : Bool, if b then s else t) = s ∪ t by ext; simp [Bool.exists_bool, or_comm]] at h

def Small (r : Code ↪ W3) (G H : SimpleGraph W3) (a : W3) (s : Set W3) : Prop :=
  ∃ c : Code, r c < a ∧ a ∉ eval G H c ∧ s ⊆ eval G H c

variable {r : Code ↪ W3} {G H : SimpleGraph W3} {a : W3}

theorem small_mono {s t : Set W3} (hst : s ⊆ t) (ht : Small r G H a t) : Small r G H a s := by
  rcases ht with ⟨c, hc, hca, ht⟩
  exact ⟨c, hc, hca, hst.trans ht⟩

theorem empty_small (ha : GoodCut r G H a) : Small r G H a ∅ :=
  ⟨SmallUnionCode.empty, ha.empty_lt, by simp [eval], Set.empty_subset _⟩

theorem iUnion_small (ha : GoodCut r G H a) {J : Type} (s : J → Set W3)
    (hJ : #J < ℵ_ 2) (hs : ∀ j, Small r G H a (s j)) :
    Small r G H a (⋃ j, s j) :=
  codedSmall_iUnion ha.empty_lt ha.union_lt s hJ hs

theorem union_small (ha : GoodCut r G H a) {s t : Set W3}
    (hs : Small r G H a s) (ht : Small r G H a t) :
    Small r G H a (s ∪ t) :=
  codedSmall_union ha.empty_lt ha.union_lt hs ht

def smallness (ha : GoodCut r G H a) :
    Erdos1172BHTAsymmetricEndpointFavorableOrder.AlephTwoSmallness W3 where
  small := Small r G H a
  mono := fun hst ht => small_mono hst ht
  union_small := union_small ha
  iUnion_small := iUnion_small ha

theorem bounded_interval_small (ha : GoodCut r G H a) {x : W3} (hx : x < a) :
    Small r G H a (Set.Iic x) :=
  ⟨SmallUnionCode.atom (2, x), ha.atom_lt 2 x hx, hx.not_ge, Set.Subset.rfl⟩

theorem named_compl_small (ha : GoodCut r G H a) {c : Code}
    (hc : r c < a) (hac : a ∈ eval G H c) :
    Small r G H a (eval G H c)ᶜ :=
  ⟨SmallUnionCode.compl c, ha.compl_lt c hc, not_not.mpr hac, Set.Subset.rfl⟩

theorem exists_club_positive_trace (r : Code ↪ W3) (G H : SimpleGraph W3)
    (s : Set W3) :
    ∃ club : Set W3, IsClub club ∧ ∀ a ∈ club, a ∈ s → ¬Small r G H a (s ∩ Set.Iio a) := by
  obtain ⟨club, hclub, hreflect⟩ := ClubClosure.exists_club_reflects
    r (eval G H) s alephZero_lt_cof_W3
  exact ⟨club, hclub, fun a ha has ⟨c, hc, hca, hsub⟩ => hca (hreflect a ha c hc hsub has)⟩

end Erdos1172NeighborhoodIdeal
