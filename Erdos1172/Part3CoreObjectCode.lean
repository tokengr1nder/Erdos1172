/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableRankClosure

@[expose] public section

open Cardinal Ordinal Set Function Order

namespace Erdos1172Part3CoreObjectCode

open Erdos1172Part3NeighborhoodCode (W2 cof_W2 alephZero_lt_cof_W2)
open Erdos1172Part3CountableRankClosure

/-- Whole candidate blocks, including blocks of cardinality `alephOne`. -/
abbrev Obj : Type := {s : Set W2 // #s ≤ ℵ_ 1}

def objEmpty : Obj := ⟨∅, by simp⟩

def objSingleton (x : W2) : Obj :=
  ⟨{x}, by
    rw [Cardinal.mk_singleton]
    exact Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_aleph 1)⟩

def objUnion (s : ℕ → Obj) : Obj := ⟨⋃ n, (s n).val, by
  calc
    #(⋃ n, (s n).val) ≤ Cardinal.sum (fun n => #(s n).val) := Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : ℕ => (ℵ_ 1 : Cardinal)) :=
      Cardinal.sum_le_sum _ _ (fun n => (s n).property)
    _ = #ℕ * ℵ_ 1 := Cardinal.sum_const' ℕ (ℵ_ 1)
    _ ≤ ℵ_ 1 * ℵ_ 1 := mul_le_mul' (by simp) le_rfl
    _ = ℵ_ 1 := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)⟩

theorem mk_Obj_le (hGCH : GCH) : #Obj ≤ ℵ_ 2 := by
  have h := Cardinal.mk_bounded_set_le W2 (ℵ_ 1)
  simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega,
    max_eq_left (Cardinal.aleph0_le_aleph 2), hGCH.aleph_two_power_aleph_one] using h

theorem exists_objectBound (s : Obj) : ∃ b : W2, ∀ x ∈ s.val, x < b := by
  have hsmall : #s.val < Order.cof W2 := by
    rw [cof_W2]
    exact s.property.trans_lt (Cardinal.aleph_lt_aleph.mpr (by norm_num))
  exact not_isCofinal_iff.mp (fun h => hsmall.not_ge (Order.cof_le h))

noncomputable def objectBound (s : Obj) : W2 := (exists_objectBound s).choose

theorem objectBound_spec (s : Obj) : ∀ x ∈ s.val, x < objectBound s :=
  (exists_objectBound s).choose_spec

abbrev Atom : Type := (Fin 3 × W2) ⊕ Obj
abbrev Code : Type := SmallUnionCode.Code ℕ Atom

def pointName (k : Fin 3) (x : W2) : Code := SmallUnionCode.atom (.inl (k, x))
def objectName (s : Obj) : Code := SmallUnionCode.atom (.inr s)

/-- A later common red neighborhood of an entire block. -/
def afterRed (G : SimpleGraph W2) (s : Obj) : Set W2 :=
  {y | ∀ x ∈ s.val, x < y ∧ G.Adj x y}

def atoms (G H : SimpleGraph W2) : Atom → Set W2
  | .inl (0, x) => {y | G.Adj x y}
  | .inl (1, x) => {y | H.Adj x y}
  | .inl (2, x) => Set.Iic x
  | .inr s => afterRed G s

def eval (G H : SimpleGraph W2) : Code → Set W2 := SmallUnionCode.eval (atoms G H)

theorem mk_Code_le (hGCH : GCH) : #Code ≤ ℵ_ 2 := by
  apply SmallUnionCode.mk_code_le (μ := ℵ₀) Cardinal.one_le_aleph0
    (Cardinal.aleph0_le_aleph 2) Cardinal.mk_nat.le
  · have hp : #(Fin 3 × W2) ≤ ℵ_ 2 := by
      simp only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_fin,
        W2, Cardinal.mk_toType, Ordinal.card_omega]
      exact (mul_le_mul' (Cardinal.natCast_le_aleph0.trans
        (Cardinal.aleph0_le_aleph 2)) le_rfl).trans_eq
          (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 2))
    change #((Fin 3 × W2) ⊕ Obj) ≤ ℵ_ 2
    rw [Cardinal.mk_sum]
    simp only [Cardinal.lift_id]
    exact (add_le_add hp (mk_Obj_le hGCH)).trans_eq
      (Cardinal.add_eq_self (Cardinal.aleph0_le_aleph 2))
  · exact hGCH.aleph_two_power_aleph_zero.le

noncomputable def rank (hGCH : GCH) : Code ↪ W2 :=
  Classical.choice ((Cardinal.le_def Code W2).mp (by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using mk_Code_le hGCH))

/-- The code and block-object closure needed for whole-block fusion.
All these fields are constructed on a stationary set below. -/
structure GoodCut (r : Code ↪ W2) (σ : Obj ↪ W2)
    (G H : SimpleGraph W2) (a : W2) : Prop where
  isOmegaOneSup : ErdosRadoCHAsym.IsOmegaOneSup a
  empty_lt : r SmallUnionCode.empty < a
  compl_lt : ∀ c, r c < a → r (SmallUnionCode.compl c) < a
  union_lt : ∀ c : ℕ → Code, (∀ i, r (c i) < a) → r (SmallUnionCode.union c) < a
  point_lt : ∀ k : Fin 3, ∀ x < a, r (pointName k x) < a
  reflects_univ : ∀ c, r c < a → Set.Iio a ⊆ eval G H c → Set.univ ⊆ eval G H c
  object_empty_lt : σ objEmpty < a
  object_union_lt : ∀ s : ℕ → Obj, (∀ i, σ (s i) < a) → σ (objUnion s) < a
  object_singleton_lt : ∀ x < a, σ (objSingleton x) < a
  object_bound_lt : ∀ s, σ s < a → objectBound s < a
  object_name_lt : ∀ s, σ s < a → r (objectName s) < a

end Erdos1172Part3CoreObjectCode
