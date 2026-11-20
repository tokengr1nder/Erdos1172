/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedPositiveExtension

@[expose] public section

/-!
# Avoiding small condition-dependent sets

Subtracting a small regular name preserves positive named membership.
The resulting fresh-point choice refutes the avoided name at its deciding
condition, rather than merely failing to have decided membership in it.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedAvoidance

open ErdosRadoCHAsym (W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3NamedPositiveExtension (colorGraph exists_actual_extension)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)

variable {P I : Type} [Preorder P] [LinearOrder I]
variable {G H : SimpleGraph W2} {r : Code P I G ↪ W2}
variable {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2} {a : W2}

theorem small_iJoin (hclosed : CountablyClosed P) (ha : GoodCut r σ H source a)
    {J : Type} (hJ : #J ≤ ℵ₀) (p : P) (U : J → RegularName P W2)
    (hU : ∀ j, (smallName r H a).holds p (U j)) :
    (smallName r H a).holds p (join U) := by
  classical
  obtain ⟨e⟩ : Nonempty (J ↪ ℕ) := (Cardinal.le_def _ _).mp (by
    simpa only [Cardinal.mk_nat] using hJ)
  let V (n : ℕ) : RegularName P W2 :=
    if h : ∃ j, e j = n then U h.choose else ground ∅
  have hV : ∀ n, (smallName r H a).holds p (V n) := by
    intro n
    dsimp only [V]
    split_ifs with h
    · exact hU h.choose
    · exact smallName_empty ha p
  have hex (q : P) (x : W2) : (∃ n, (V n).holds q x) ↔ ∃ j, (U j).holds q x := by
    constructor
    · rintro ⟨n, hn⟩
      dsimp only [V] at hn
      split_ifs at hn with h
      · exact ⟨h.choose, hn⟩
      · exact hn.elim
    · rintro ⟨j, hj⟩
      refine ⟨e j, ?_⟩
      have h : ∃ k, e k = e j := ⟨j, rfl⟩
      have hk : h.choose = j := e.injective h.choose_spec
      simpa only [V, dif_pos h, hk] using hj
  have heq : join V = join U := by
    apply RegularName.ext
    intro q x
    constructor
    · intro h t htq
      obtain ⟨s, hst, hs⟩ := h t htq
      exact ⟨s, hst, (hex s x).mp hs⟩
    · intro h t htq
      obtain ⟨s, hst, hs⟩ := h t htq
      exact ⟨s, hst, (hex s x).mpr hs⟩
  have h := smallName_countable_join hclosed ha p V hV
  rwa [heq] at h

theorem named_complement_small (ha : GoodCut r σ H source a)
    (p : P) {c : Code P I G} (hc : r c < a) (hac : (eval G H c).holds p a) :
    (smallName r H a).holds p (neg (eval G H c)) := by
  apply smallName_of_witness
  refine ⟨SmallUnionCode.compl c, ha.compl_lt c hc, ?_, ?_⟩
  · rw [eval_compl, Erdos1172Part3RegularMembership.neg_neg]
    exact hac
  · intro x hx q hqp hq
    rw [eval_compl]
    exact hq

theorem positive_sdiff (hclosed : CountablyClosed P) (ha : GoodCut r σ H source a)
    (p : P) (U V : RegularName P W2)
    (hU : (neg (smallName r H a)).holds p U)
    (hV : (smallName r H a).holds p V) :
    (neg (smallName r H a)).holds p (meet U (neg V)) := by
  intro q hqp hsmall
  let family (n : ℕ) : RegularName P W2 := if n = 0 then V else meet U (neg V)
  have hjoin : (smallName r H a).holds q (join family) :=
    smallName_countable_join hclosed ha q family (by
      intro n
      dsimp only [family]
      split_ifs
      · exact (smallName r H a).persistent hqp hV
      · exact hsmall)
  apply hU q hqp
  apply smallName_mono_set (V := join family) (p := q) (U := U) ?_ hjoin
  intro x hx t htq hUt s hst
  obtain ⟨v, hvs, hv⟩ := exists_deciding_refinement V s x
  rcases hv with hVx | hnVx
  · exact ⟨v, hvs, 0, hVx⟩
  · exact ⟨v, hvs, 1, ⟨U.persistent (hvs.trans hst) hUt, hnVx⟩⟩

theorem exists_actual_extension_avoiding (hclosed : CountablyClosed P)
    (ha : GoodCut r σ H source a) (b : Bool) (U avoid : RegularName P W2)
    (p : P) (hpositive : (neg (smallName r H a)).holds p U)
    (havoid : (smallName r H a).holds p avoid)
    (selected : Set W2) (hcount : selected.Countable)
    (hbelow : selected ⊆ Set.Iio a)
    (hcolor : ∀ x ∈ selected, (colorGraph G H b).Adj x a) :
    ∃ q : P, q ≤ p ∧ ∃ y : W2, y < a ∧ U.holds q y ∧ (neg avoid).holds q y ∧
      ∀ x ∈ selected, x < y ∧ (colorGraph G H b).Adj x y := by
  have hpos := positive_sdiff hclosed ha p U avoid hpositive havoid
  obtain ⟨q, hqp, y, hya, hy, hcross⟩ := exists_actual_extension hclosed ha b
    (meet U (neg avoid)) p (hpos p le_rfl) selected hcount hbelow hcolor
  exact ⟨q, hqp, y, hya, hy.1, hy.2, hcross⟩

end Erdos1172Part3NamedAvoidance
