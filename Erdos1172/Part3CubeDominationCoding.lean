/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCubeTraceBounds

@[expose] public section

/-!
# Coding both levels of cubic cutoff functions into one dominating name

A bijection codes square coordinates by omegaOne. Its bounded code sets
involve only boundedly many outer rows. Pointwise maxima combine the
middle and coded inner cutoff functions, so one eventual dominating
function controls both levels on every sufficiently late whole row.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CubeDominationCoding

open ErdosRadoCHAsym (W1)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3FunctionDecisions (FunctionDecisions BoundedAt)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

noncomputable def pairEquiv : Square ≃ W1 := Classical.choice (Cardinal.eq.mp (by
  change #(W1 × W1) = #W1
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
  exact Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)))

theorem exists_late_rows_above_code_bound (bound : W1) :
    ∃ rowBound : W1, ∀ i : W1, rowBound < i → ∀ j : W1, bound < pairEquiv (toLex (i, j)) := by
  have hcount : (Set.Iic bound).Countable := Cardinal.le_aleph0_iff_set_countable.mp
    (Cardinal.lt_aleph_one_iff.mp (Erdos1172Part3ConvergentCore.mk_Iic_W1_lt bound))
  obtain ⟨rowBound, hrow⟩ := exists_bound_of_countable
    ((fun k : W1 => (ofLex (pairEquiv.symm k)).1) '' Set.Iic bound) (hcount.image _)
  refine ⟨rowBound, ?_⟩
  intro i hi j
  by_contra h
  have hmem : i ∈ (fun k : W1 => (ofLex (pairEquiv.symm k)).1) '' Set.Iic bound :=
    ⟨pairEquiv (toLex (i, j)), le_of_not_gt h, by
      change (ofLex (pairEquiv.symm (pairEquiv (toLex (i, j))))).1 = i
      rw [pairEquiv.symm_apply_apply]
      rfl⟩
  exact (hrow i hmem).asymm hi

variable {P A B V : Type} [Preorder P]

def reindexDecisions (F : FunctionDecisions P A V) (f : B → A) : FunctionDecisions P B V where
  decides p i v := F.decides p (f i) v
  dense p i := F.dense p (f i)
  persistent := F.persistent
  unique := F.unique

def maxDecisions (F B : FunctionDecisions P W1 W1) : FunctionDecisions P W1 W1 where
  decides p i u := ∃ v w : W1, F.decides p i v ∧ B.decides p i w ∧ u = max v w
  dense := by
    intro p i
    obtain ⟨q, hqp, v, hv⟩ := F.dense p i
    obtain ⟨s, hsq, w, hw⟩ := B.dense q i
    exact ⟨s, hsq.trans hqp, max v w, v, w, F.persistent hsq hv, hw, rfl⟩
  persistent := by
    rintro p q i u hqp ⟨v, w, hv, hw, hu⟩
    exact ⟨v, w, F.persistent hqp hv, B.persistent hqp hw, hu⟩
  unique := by
    rintro p i u u' ⟨v, w, hv, hw, rfl⟩ ⟨v', w', hv', hw', rfl⟩
    rw [F.unique hv hv', B.unique hw hw']

theorem boundedAt_max_left {F B : FunctionDecisions P W1 W1} {p : P} {i bound : W1}
    (h : BoundedAt (maxDecisions F B) p i bound) : BoundedAt F p i bound := by
  intro q hqp v hv
  obtain ⟨s, hsq, w, hw⟩ := B.dense q i
  exact (le_max_left v w).trans_lt (h s (hsq.trans hqp) (max v w)
    ⟨v, w, F.persistent hsq hv, hw, rfl⟩)

theorem boundedAt_max_right {F B : FunctionDecisions P W1 W1} {p : P} {i bound : W1}
    (h : BoundedAt (maxDecisions F B) p i bound) : BoundedAt B p i bound := by
  intro q hqp w hw
  obtain ⟨s, hsq, v, hv⟩ := F.dense q i
  exact (le_max_right v w).trans_lt (h s (hsq.trans hqp) (max v w)
    ⟨v, w, hv, B.persistent hsq hw, rfl⟩)

noncomputable def combinedBounds (F : FunctionDecisions P W1 W1) (B : FunctionDecisions P Square W1) :
    FunctionDecisions P W1 W1 := maxDecisions F (reindexDecisions B pairEquiv.symm)

theorem combinedBounds_left {F : FunctionDecisions P W1 W1} {B : FunctionDecisions P Square W1}
    {p : P} {i bound : W1} (h : BoundedAt (combinedBounds F B) p i bound) :
    BoundedAt F p i bound := boundedAt_max_left h

theorem combinedBounds_right {F : FunctionDecisions P W1 W1} {B : FunctionDecisions P Square W1}
    {p : P} {z : Square} {bound : W1} (h : BoundedAt (combinedBounds F B) p (pairEquiv z) bound) :
    ∀ q : P, q ≤ p → ∀ v : W1, B.decides q z v → v < bound := by
  intro q hqp v hv
  apply boundedAt_max_right h q hqp v
  change B.decides q (pairEquiv.symm (pairEquiv z)) v
  simpa only [pairEquiv.symm_apply_apply] using hv

end Erdos1172Part3CubeDominationCoding
