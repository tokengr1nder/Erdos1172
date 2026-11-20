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

The codes use countable unions. At the good cuts the local ideals are
proper, closed under countable unions, contain bounded sets, and reflect
arbitrary fixed traces on a club.
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

theorem empty_small (ha : GoodCut r G H a) : Small r G H a ∅ := by
  refine ⟨SmallUnionCode.empty, ha.empty_lt, ?_, ?_⟩
  · simp only [eval, SmallUnionCode.eval_empty, Set.notMem_empty, not_false_eq_true]
  · exact Set.empty_subset _

theorem iUnion_small (ha : GoodCut r G H a) {J : Type} (s : J → Set W2)
    (hJ : #J < ℵ_ 1) (hs : ∀ j, Small r G H a (s j)) :
    Small r G H a (⋃ j, s j) := by
  classical
  choose c hc hca hcs using hs
  have hcard : #J ≤ #ℕ := by
    simpa only [Cardinal.mk_nat] using
      Cardinal.lt_aleph_one_iff.mp hJ
  obtain ⟨e⟩ := (Cardinal.le_def J ℕ).mp hcard
  let t : ℕ → Code := fun i =>
    if h : ∃ j, e j = i then c h.choose else SmallUnionCode.empty
  have ht : ∀ i, r (t i) < a ∧ a ∉ eval G H (t i) := by
    intro i
    dsimp only [t]
    split_ifs with h
    · exact ⟨hc h.choose, hca h.choose⟩
    · exact ⟨ha.empty_lt, by simp only [eval, SmallUnionCode.eval_empty,
        Set.notMem_empty, not_false_eq_true]⟩
  refine ⟨SmallUnionCode.union t, ha.union_lt t (fun i => (ht i).1), ?_, ?_⟩
  · change a ∉ ⋃ i, eval G H (t i)
    simp only [Set.mem_iUnion, not_exists]
    exact fun i => (ht i).2
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    change x ∈ ⋃ i, eval G H (t i)
    apply Set.mem_iUnion.mpr
    refine ⟨e j, ?_⟩
    have h : ∃ j', e j' = e j := ⟨j, rfl⟩
    have he : h.choose = j := e.injective h.choose_spec
    simpa only [t, dif_pos h, he] using hcs j hj

theorem union_small (ha : GoodCut r G H a) {s t : Set W2}
    (hs : Small r G H a s) (ht : Small r G H a t) :
    Small r G H a (s ∪ t) := by
  have h := iUnion_small ha (fun b : Bool => if b then s else t)
    (show #Bool < ℵ_ 1 by
      simp only [Cardinal.mk_fintype, Fintype.card_bool, Nat.cast_ofNat]
      exact (Cardinal.natCast_lt_aleph0 : (2 : Cardinal) < ℵ₀).trans_le
        (Cardinal.aleph0_le_aleph 1))
    (by intro b; cases b <;> assumption)
  have heq : (⋃ b : Bool, if b then s else t) = s ∪ t := by
    ext x
    simp only [Set.mem_iUnion, Bool.exists_bool, Bool.false_eq_true,
      ↓reduceIte, Set.mem_union, or_comm]
  rwa [heq] at h

/-- The finite-ideal interface; countable closure is proved separately. -/
def smallness (ha : GoodCut r G H a) :
    Erdos1172Part3FiniteIdealEndpoint.FiniteSmallness W2 where
  small := Small r G H a
  empty_small := empty_small ha
  mono := fun hst ht => small_mono hst ht
  union_small := union_small ha

theorem bounded_interval_small (ha : GoodCut r G H a) {x : W2} (hx : x < a) :
    Small r G H a (Set.Iic x) := by
  refine ⟨SmallUnionCode.atom (2, x), ha.atom_lt 2 x hx, ?_, ?_⟩
  · change ¬a ≤ x
    exact hx.not_ge
  · exact Set.Subset.rfl

theorem prior_not_small (ha : GoodCut r G H a) :
    ¬Small r G H a (Set.Iio a) := by
  rintro ⟨c, hc, hca, hsub⟩
  exact hca (ha.reflects_univ c hc hsub (Set.mem_univ a))

theorem cardinal_small (ha : GoodCut r G H a) {s : Set W2}
    (hs : s ⊆ Set.Iio a) (hcard : #s < ℵ_ 1) : Small r G H a s := by
  obtain ⟨b, hba, hb⟩ :=
    ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup ha.isOmegaOneSup
      (Cardinal.lt_aleph_one_iff.mp hcard) (fun x hx => hs hx)
  exact small_mono (fun x hx => (hb x hx).le) (bounded_interval_small ha hba)

/-- A locally named set containing the cut has ideal-small complement. -/
theorem named_compl_small (ha : GoodCut r G H a) {c : Code}
    (hc : r c < a) (hac : a ∈ eval G H c) :
    Small r G H a (eval G H c)ᶜ := by
  refine ⟨SmallUnionCode.compl c, ha.compl_lt c hc, ?_, Set.Subset.rfl⟩
  change ¬a ∈ (eval G H c)ᶜ
  exact not_not.mpr hac

/-- Every fixed set reflects positively at its own points on a club. The
set need not belong to the coded neighborhood algebra. -/
theorem exists_club_positive_trace (r : Code ↪ W2) (G H : SimpleGraph W2)
    (s : Set W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, a ∈ s →
      ¬Small r G H a (s ∩ Set.Iio a) := by
  obtain ⟨club, hclub, hreflect⟩ := ClubClosure.exists_club_reflects
    r (eval G H) s alephZero_lt_cof_W2
  refine ⟨club, hclub, ?_⟩
  intro a ha has hs
  rcases hs with ⟨c, hc, hca, hsub⟩
  exact hca (hreflect a ha c hc hsub has)

end Erdos1172Part3NeighborhoodIdeal
