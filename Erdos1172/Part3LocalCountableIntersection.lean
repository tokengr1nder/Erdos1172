/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularBlockEnvironment

@[expose] public section

/-!
# Locally coded countable intersections of named neighborhoods

Complement and countable-union closure code the exact regular
intersection. In particular, the actual common-red neighborhoods of
countably many locally ranked block names have one local code.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3LocalCountableIntersection

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)

variable {P I : Type} [Preorder P] [LinearOrder I] {G H : SimpleGraph W2}
variable {r : Code P I G ↪ W2} {σ : NiceCliqueName P I W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

theorem exists_local_intersection_code (ha : GoodCut r σ H source a)
    {J : Type} (hJ : #J ≤ ℵ₀) (codes : J → Code P I G) (hcodes : ∀ j, r (codes j) < a) :
    ∃ c : Code P I G, r c < a ∧ eval G H c = all (fun j => eval G H (codes j)) := by
  classical
  obtain ⟨e⟩ : Nonempty (J ↪ ℕ) := (Cardinal.le_def _ _).mp (by
    simpa only [Cardinal.mk_nat] using hJ)
  let cover (n : ℕ) : Code P I G :=
    if h : ∃ j, e j = n then SmallUnionCode.compl (codes h.choose) else SmallUnionCode.empty
  have hcover (n : ℕ) : r (cover n) < a := by
    dsimp only [cover]
    split_ifs with h
    · exact ha.compl_lt _ (hcodes h.choose)
    · exact ha.empty_lt
  refine ⟨SmallUnionCode.compl (SmallUnionCode.union cover),
    ha.compl_lt _ (ha.union_lt cover hcover), ?_⟩
  rw [eval_compl, eval_union, neg_join]
  apply RegularName.ext
  intro p x
  constructor
  · intro h j
    have hj : ∃ k, e k = e j := ⟨j, rfl⟩
    have heq : hj.choose = j := e.injective hj.choose_spec
    have hmem := h (e j)
    simpa only [cover, dif_pos hj, heq, eval_compl,
      Erdos1172Part3RegularMembership.neg_neg] using hmem
  · intro h n
    dsimp only [cover]
    split_ifs with hn
    · simpa only [eval_compl, Erdos1172Part3RegularMembership.neg_neg] using h hn.choose
    · rw [eval_empty]
      intro q hqp hq
      exact hq

theorem exists_local_after_code (ha : GoodCut r σ H source a)
    (selected : Set (NiceCliqueName P I W2 G)) (hcount : selected.Countable)
    (hrank : ∀ N ∈ selected, σ N < a) :
    ∃ c : Code P I G, r c < a ∧ ∀ p x, (eval G H c).holds p x ↔
      ∀ N ∈ selected, (afterClique N.toClique).holds p x := by
  obtain ⟨c, hc, heval⟩ := exists_local_intersection_code ha
    (Cardinal.le_aleph0_iff_set_countable.mpr hcount)
    (fun N : selected => blockName N.val)
    (fun N => ha.block_lt N.val (hrank N.val N.property))
  refine ⟨c, hc, ?_⟩
  intro p x
  rw [heval]
  constructor
  · intro h N hN
    simpa only [eval_blockName] using h ⟨N, hN⟩
  · intro h N
    simpa only [eval_blockName] using h N.val N.property

end Erdos1172Part3LocalCountableIntersection
