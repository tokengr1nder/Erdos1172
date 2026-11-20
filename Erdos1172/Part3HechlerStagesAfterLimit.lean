/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableHechlerLimitCentering

@[expose] public section

/-!
# Small countable-limit orders and subsequent stages

The countable limit retains the size, closure, and centering data needed
by the successor construction. This supplies further decision orders,
not the missing higher red-clique recursion of Part 3.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3HechlerStagesAfterLimit

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3FiniteHechlerStages (SmallClosedCenteredOrder stage)
open Erdos1172Part3CountableHechlerLimit
open Erdos1172Part3FunctionDecisions (FunctionDecisions BoundedAt)
open Erdos1172Part3IteratedHechlerOrder (Condition)

theorem mk_Limit_le (hGCH : GCH) : #(Limit hGCH) ≤ ℵ_ 2 := by
  classical
  have emb (n : ℕ) : Nonempty (At hGCH n ↪ W2) := (Cardinal.le_def _ _).mp (by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using (stage hGCH n).small)
  let codes (n : ℕ) : At hGCH n ↪ W2 := Classical.choice (emb n)
  let encode (p : Limit hGCH) : ℕ → W2 := fun n => codes n (p.point n)
  have hinj : Injective encode := by
    intro p q h
    apply limit_ext
    funext n
    exact (codes n).injective (congrFun h n)
  apply (Cardinal.mk_le_of_injective hinj).trans
  simp only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_nat, W2,
    Cardinal.mk_toType, Ordinal.card_omega, hGCH.aleph_two_power_aleph_zero, le_refl]

noncomputable def limitOrder (hGCH : GCH) : SmallClosedCenteredOrder where
  Carrier := Limit hGCH
  order := inferInstance
  closed := Erdos1172Part3CountableHechlerLimitClosure.countablyClosed
  centered := Erdos1172Part3CountableHechlerLimitCentering.centered
  small := mk_Limit_le hGCH

noncomputable def afterLimit (hGCH : GCH) : ℕ → SmallClosedCenteredOrder
  | 0 => limitOrder hGCH
  | n + 1 => Erdos1172Part3FiniteHechlerStages.extend hGCH (afterLimit hGCH n)

theorem afterLimit_countablyClosed (hGCH : GCH) (n : ℕ) :
    Erdos1172Part3ClosedDecisionSystem.CountablyClosed (afterLimit hGCH n).Carrier :=
  (afterLimit hGCH n).closed

theorem afterLimit_omegaTwoCC (hGCH : GCH) (n : ℕ) :
    Erdos1172Part3StationaryDecisions.OmegaTwoCC (afterLimit hGCH n).Carrier :=
  (afterLimit hGCH n).centered.omegaTwoCC

theorem afterLimit_card_le (hGCH : GCH) (n : ℕ) : #(afterLimit hGCH n).Carrier ≤ ℵ_ 2 :=
  (afterLimit hGCH n).small

theorem afterLimit_bounds_earlier_functions (hGCH : GCH) (n : ℕ)
    (p0 : Condition (afterLimit hGCH n).Carrier)
    (F : FunctionDecisions (afterLimit hGCH n).Carrier W1 W1) :
    ∃ p : Condition (afterLimit hGCH n).Carrier, p ≤ p0 ∧ ∃ bound : W1,
      ∀ q : Condition (afterLimit hGCH n).Carrier, q ≤ p → ∀ i : W1, bound < i →
        ∀ v : W1, q.stem i = some v → BoundedAt F q.base i v :=
  Erdos1172Part3IteratedHechlerClosure.exists_eventual_bound_for_function
    (afterLimit_omegaTwoCC hGCH n) p0 F

end Erdos1172Part3HechlerStagesAfterLimit
