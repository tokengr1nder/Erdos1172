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

The generators are globally coded sets whose codes precede the cut but which
omit the cut. The preceding module constructs a stationary set of cuts at
which this definition is a proper `alephTwo`-complete ideal and contains every
bounded initial interval. This file proves those properties, including the
stationary reflection property for arbitrary sets.

These are base ideals. No two-color derived-ideal or endpoint-transfer
property is claimed here.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172NeighborhoodIdeal

open Erdos1172NeighborhoodCode

def Small (r : Code ↪ W3) (G H : SimpleGraph W3) (a : W3) (s : Set W3) : Prop :=
  ∃ c : Code, r c < a ∧ a ∉ eval G H c ∧ s ⊆ eval G H c

variable {r : Code ↪ W3} {G H : SimpleGraph W3} {a : W3}

theorem small_mono {s t : Set W3} (hst : s ⊆ t)
    (ht : Small r G H a t) : Small r G H a s := by
  rcases ht with ⟨c, hc, hca, ht⟩
  exact ⟨c, hc, hca, hst.trans ht⟩

theorem empty_small (ha : GoodCut r G H a) : Small r G H a ∅ := by
  refine ⟨SmallUnionCode.empty, ha.empty_lt, ?_, ?_⟩
  · simp only [eval, SmallUnionCode.eval_empty, Set.notMem_empty, not_false_eq_true]
  · exact Set.empty_subset _

theorem iUnion_small (ha : GoodCut r G H a) {J : Type} (s : J → Set W3)
    (hJ : #J < ℵ_ 2) (hs : ∀ j, Small r G H a (s j)) :
    Small r G H a (⋃ j, s j) := by
  classical
  choose c hc hca hcs using hs
  have hcard : #J ≤ #W1 := by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
      mk_le_alephOne_of_lt_alephTwo hJ
  obtain ⟨e⟩ := (Cardinal.le_def J W1).mp hcard
  let t : W1 → Code := fun i =>
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

theorem union_small (ha : GoodCut r G H a) {s t : Set W3}
    (hs : Small r G H a s) (ht : Small r G H a t) :
    Small r G H a (s ∪ t) := by
  have h := iUnion_small ha (fun b : Bool => if b then s else t)
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

/-- The exact ideal-completeness interface previously appearing as abstract
data in the endpoint reductions is now instantiated for the base ideal. -/
def smallness (ha : GoodCut r G H a) :
    Erdos1172BHTAsymmetricEndpointFavorableOrder.AlephTwoSmallness W3 where
  small := Small r G H a
  mono := fun hst ht => small_mono hst ht
  union_small := union_small ha
  iUnion_small := iUnion_small ha

theorem bounded_interval_small (ha : GoodCut r G H a) {x : W3} (hx : x < a) :
    Small r G H a (Set.Iic x) := by
  refine ⟨SmallUnionCode.atom (2, x), ha.atom_lt 2 x hx, ?_, ?_⟩
  · change ¬a ≤ x
    exact hx.not_ge
  · exact Set.Subset.rfl

theorem prior_not_small (ha : GoodCut r G H a) :
    ¬Small r G H a (Set.Iio a) := by
  rintro ⟨c, hc, hca, hsub⟩
  exact hca (ha.reflects_univ c hc hsub (Set.mem_univ a))

theorem cardinal_small (ha : GoodCut r G H a) {s : Set W3}
    (hs : s ⊆ Set.Iio a) (hcard : #s < ℵ_ 2) : Small r G H a s := by
  obtain ⟨b, hba, hb⟩ :=
    ErdosRadoGCHAsym.exists_strict_bound_of_small_of_IsOmegaTwoSup ha.isOmegaTwoSup
      (mk_le_alephOne_of_lt_alephTwo hcard) (fun x hx => hs hx)
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
theorem exists_club_positive_trace (r : Code ↪ W3) (G H : SimpleGraph W3)
    (s : Set W3) :
    ∃ club : Set W3, IsClub club ∧ ∀ a ∈ club, a ∈ s →
      ¬Small r G H a (s ∩ Set.Iio a) := by
  obtain ⟨club, hclub, hreflect⟩ := ClubClosure.exists_club_reflects
    r (eval G H) s alephZero_lt_cof_W3
  refine ⟨club, hclub, ?_⟩
  intro a ha has hs
  rcases hs with ⟨c, hc, hca, hsub⟩
  exact hca (hreflect a ha c hc hsub has)

/-- Stationary reflection on the cofinality-`omegaTwo` domain, with all
ideal closure and properness data constructed from GCH. -/
theorem isStationary_goodCut_positive_trace (hGCH : GCH) (r : Code ↪ W3)
    (G H : SimpleGraph W3) (s : Set W3) (hs : IsStationary s)
    (hcof : ∀ a ∈ s, ErdosRadoGCHAsym.IsOmegaTwoSup a) :
    IsStationary {a | a ∈ s ∧ GoodCut r G H a ∧
      ¬Small r G H a (s ∩ Set.Iio a)} := by
  obtain ⟨cg, hcg, hg⟩ := exists_club_goodCut hGCH r G H
  obtain ⟨cr, hcr, hr⟩ := exists_club_positive_trace r G H s
  intro test htest
  obtain ⟨a, has, ⟨hag, har⟩, hat⟩ := hs
    ((hcg.inter alephZero_lt_cof_W3.ne' hcr).inter alephZero_lt_cof_W3.ne' htest)
  exact ⟨a, ⟨has, hg a hag (hcof a has), hr a har has⟩, hat⟩

end Erdos1172NeighborhoodIdeal
