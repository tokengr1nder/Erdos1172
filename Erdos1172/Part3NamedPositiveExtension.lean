/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularNamedIdeal

@[expose] public section

/-!
# Actual fresh points in positive named color fibers

Countably many non-neighbor exclusions and one bounded interval are small.
Positivity yields a strengthening and an actual source member outside
their union. The source is not replaced by its set of possible values.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedPositiveExtension

open ErdosRadoCHAsym (W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)

variable {P I : Type} [Preorder P] [LinearOrder I]
variable {G H : SimpleGraph W2} {r : Code P I G ↪ W2}
variable {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2} {a : W2}

theorem small_ground_iUnion (hclosed : CountablyClosed P)
    (ha : GoodCut r σ H source a) {J : Type} (p : P) (s : J → Set W2)
    (hJ : #J ≤ ℵ₀) (hs : ∀ j, (smallName r H a).holds p (ground (s j))) :
    (smallName r H a).holds p (ground (⋃ j, s j)) := by
  classical
  obtain ⟨e⟩ : Nonempty (J ↪ ℕ) := (Cardinal.le_def _ _).mp (by
    simpa only [Cardinal.mk_nat] using hJ)
  let t (n : ℕ) : Set W2 := if h : ∃ j, e j = n then s h.choose else ∅
  have ht : ∀ n, (smallName r H a).holds p (ground (t n)) := by
    intro n
    dsimp only [t]
    split_ifs with h
    · exact hs h.choose
    · exact smallName_empty ha p
  have heq : (⋃ n, t n) = ⋃ j, s j := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      dsimp only [t] at hn
      split_ifs at hn with h
      · exact ⟨h.choose, hn⟩
      · exact hn.elim
    · rintro ⟨j, hj⟩
      refine ⟨e j, ?_⟩
      have h : ∃ k, e k = e j := ⟨j, rfl⟩
      have hk : h.choose = j := e.injective h.choose_spec
      simpa only [t, dif_pos h, hk] using hj
  have h := smallName_countable_join hclosed ha p (fun n => ground (t n)) ht
  rwa [ground_join, heq] at h

theorem small_ground_bounded_interval (ha : GoodCut r σ H source a)
    (p : P) {x : W2} (hx : x < a) :
    (smallName r H a).holds p (ground (Set.Iic x)) := by
  apply smallName_of_witness
  refine ⟨pointName G 2 x, ha.point_lt 2 x hx, ?_, ?_⟩
  · intro q hqp hq
    exact hx.not_ge hq
  · intro y hy q hqp hq
    exact hq

def colorGraph (G H : SimpleGraph W2) (b : Bool) : SimpleGraph W2 :=
  if b then G else H

def colorPointCode (G : SimpleGraph W2) (b : Bool) (x : W2) : Code P I G :=
  pointName G (if b then 0 else 1) x

theorem eval_colorPointCode (G H : SimpleGraph W2) (b : Bool) (x : W2) :
    eval (P := P) (I := I) G H (colorPointCode G b x) =
      ground {y | (colorGraph G H b).Adj x y} := by
  cases b <;> rfl

theorem small_ground_nonneighbors (ha : GoodCut r σ H source a)
    (p : P) (b : Bool) {x : W2} (hx : x < a)
    (hxa : (colorGraph G H b).Adj x a) :
    (smallName r H a).holds p (ground {y | ¬(colorGraph G H b).Adj x y}) := by
  apply smallName_of_witness
  refine ⟨SmallUnionCode.compl (colorPointCode G b x), ha.compl_lt _ (ha.point_lt _ x hx), ?_, ?_⟩
  · rw [eval_compl, eval_colorPointCode, Erdos1172Part3RegularMembership.neg_neg]
    exact hxa
  · intro y hy q hqp hq
    rw [eval_compl, eval_colorPointCode]
    exact fun t htq => hq

theorem exists_actual_extension (hclosed : CountablyClosed P)
    (ha : GoodCut r σ H source a) (b : Bool) (U : RegularName P W2)
    (p : P) (hpositive : ¬(smallName r H a).holds p U)
    (selected : Set W2) (hcount : selected.Countable)
    (hbelow : selected ⊆ Set.Iio a)
    (hcolor : ∀ x ∈ selected, (colorGraph G H b).Adj x a) :
    ∃ q : P, q ≤ p ∧ ∃ y : W2, y < a ∧ U.holds q y ∧
      ∀ x ∈ selected, x < y ∧ (colorGraph G H b).Adj x y := by
  classical
  have hcard : #selected ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.mpr hcount
  obtain ⟨cutoff, hcutoff, hbound⟩ :=
    ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup
      ha.isOmegaOneSup hcard (fun x hx => hbelow hx)
  let losses : Option selected → Set W2
    | none => Set.Iic cutoff
    | some x => {y | ¬(colorGraph G H b).Adj x.val y}
  have hindex : #(Option selected) ≤ ℵ₀ := by
    rw [Cardinal.mk_option]
    exact (add_le_add hcard Cardinal.one_le_aleph0).trans_eq (Cardinal.add_eq_self le_rfl)
  have hsmall : (smallName r H a).holds p (ground (⋃ j, losses j)) :=
    small_ground_iUnion hclosed ha p losses hindex (by
      intro j
      cases j with
      | none => exact small_ground_bounded_interval ha p hcutoff
      | some x =>
          exact small_ground_nonneighbors ha p b (hbelow x.property) (hcolor x.val x.property))
  have hnot : ¬∀ y < a, ∀ q : P, q ≤ p → U.holds q y → y ∈ ⋃ j, losses j := by
    intro h
    exact hpositive (smallName_mono_set (V := ground (⋃ j, losses j)) h hsmall)
  push Not at hnot
  obtain ⟨y, hya, q, hqp, hqy, hy⟩ := hnot
  refine ⟨q, hqp, y, hya, hqy, ?_⟩
  intro x hx
  constructor
  · exact (hbound x hx).trans (lt_of_not_ge (fun h =>
      hy (Set.mem_iUnion.mpr ⟨none, h⟩)))
  · by_contra hxy
    exact hy (Set.mem_iUnion.mpr ⟨some ⟨x, hx⟩, hxy⟩)

end Erdos1172Part3NamedPositiveExtension
