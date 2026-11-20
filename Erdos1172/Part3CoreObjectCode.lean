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

noncomputable def objectRank (hGCH : GCH) : Obj ↪ W2 :=
  Classical.choice ((Cardinal.le_def Obj W2).mp (by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using mk_Obj_le hGCH))

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

@[simp] theorem eval_objectName (G H : SimpleGraph W2) (s : Obj) :
    eval G H (objectName s) = afterRed G s := rfl

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

theorem exists_club_goodCut (hCH : CH) (r : Code ↪ W2) (σ : Obj ↪ W2)
    (G H : SimpleGraph W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club,
      ErdosRadoCHAsym.IsOmegaOneSup a → GoodCut r σ G H a := by
  let c0 := {a | ClubClosure.ClosedUnder (fun _ => r SmallUnionCode.empty) a}
  have hc0 : IsClub c0 := ClubClosure.isClub_closedUnder _ alephZero_lt_cof_W2
  let c1 := {a | ∀ c, r c < a → r (SmallUnionCode.compl c) < a}
  have hc1 : IsClub c1 := ClubClosure.isClub_rankClosed r _ alephZero_lt_cof_W2
  obtain ⟨c2, hc2, h2⟩ := exists_club_countableClosed hCH r SmallUnionCode.union
  let c3 := ⋂ k : Fin 3, {a | ClubClosure.ClosedUnder (fun x => r (pointName k x)) a}
  have hc3 : IsClub c3 := IsClub.iInter_of_countable alephZero_lt_cof_W2.ne'
    (fun k => ClubClosure.isClub_closedUnder _ alephZero_lt_cof_W2)
  obtain ⟨c4, hc4, h4⟩ := ClubClosure.exists_club_reflects r (eval G H)
    Set.univ alephZero_lt_cof_W2
  let c5 := {a | ClubClosure.ClosedUnder (fun _ => σ objEmpty) a}
  have hc5 : IsClub c5 := ClubClosure.isClub_closedUnder _ alephZero_lt_cof_W2
  obtain ⟨c6, hc6, h6⟩ := exists_club_countableClosed hCH σ objUnion
  let c7 := {a | ClubClosure.ClosedUnder (fun x => σ (objSingleton x)) a}
  have hc7 : IsClub c7 := ClubClosure.isClub_closedUnder _ alephZero_lt_cof_W2
  let c8 := {a | ∀ s, σ s < a → objectBound s < a}
  have hc8 : IsClub c8 := ClubClosure.isClub_rankClosed σ objectBound alephZero_lt_cof_W2
  let c9 := {a | ∀ s, σ s < a → r (objectName s) < a}
  have hc9 : IsClub c9 := ClubClosure.isClub_rankClosed σ _ alephZero_lt_cof_W2
  let clubs : Fin 10 → Set W2
    | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4
    | 5 => c5 | 6 => c6 | 7 => c7 | 8 => c8 | 9 => c9
  have hclubs : ∀ i, IsClub (clubs i) := by
    intro i
    fin_cases i <;> assumption
  refine ⟨⋂ i, clubs i, IsClub.iInter_of_countable alephZero_lt_cof_W2.ne' hclubs, ?_⟩
  intro a ha hsup
  have hmem (i : Fin 10) : a ∈ clubs i := Set.mem_iInter.mp ha i
  obtain ⟨b, hba, _⟩ := ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup
    hsup (seed := ∅) (by simp) (by simp)
  refine ⟨hsup, hmem 0 b hba, hmem 1, h2 a (hmem 2) hsup, ?_, ?_,
    hmem 5 b hba, h6 a (hmem 6) hsup, hmem 7, hmem 8, hmem 9⟩
  · intro k x hx
    exact Set.mem_iInter.mp (hmem 3) k x hx
  · intro c hc hsub
    exact h4 a (hmem 4) c hc (by simpa only [Set.univ_inter] using hsub)

theorem isStationary_goodCut (hCH : CH) (r : Code ↪ W2) (σ : Obj ↪ W2)
    (G H : SimpleGraph W2) : IsStationary {a | GoodCut r σ G H a} := by
  obtain ⟨club, hc, hg⟩ := exists_club_goodCut hCH r σ G H
  intro test htest
  obtain ⟨a, hsup, ha, hat⟩ := ErdosRadoCHAsym.isStationary_isOmegaOneSup_omegaTwo
    (hc.inter alephZero_lt_cof_W2.ne' htest)
  exact ⟨a, hg a ha hsup, hat⟩

theorem goodCut_object_bounded {r : Code ↪ W2} {σ : Obj ↪ W2}
    {G H : SimpleGraph W2} {a : W2} (ha : GoodCut r σ G H a)
    {s : Obj} (hs : σ s < a) : ∃ b < a, ∀ x ∈ s.val, x < b :=
  ⟨objectBound s, ha.object_bound_lt s hs, objectBound_spec s⟩

end Erdos1172Part3CoreObjectCode
