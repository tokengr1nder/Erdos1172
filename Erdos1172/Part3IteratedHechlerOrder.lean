/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NiceFunctionNames

@[expose] public section

/-!
# A dominating-function stage over an earlier decision order

Side conditions are small names for earlier-stage functions, not merely
ground functions. A new stem value must bound every later decision of
each previously tracked name. This gives an explicit ground-type order;
no external forcing universe or global domination axiom is postulated.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3IteratedHechlerOrder

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed DenseBelow)
open Erdos1172Part3FunctionDecisions
open Erdos1172Part3NiceFunctionNames
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

structure Condition (P : Type) [Preorder P] where
  base : P
  stem : W1 → Option W1
  stem_countable : {i | stem i ≠ none}.Countable
  side : Set (NiceFunctionName P W1 W1)
  side_countable : side.Countable

variable {P : Type} [Preorder P]

def Stronger (q p : Condition P) : Prop :=
  q.base ≤ p.base ∧
    (∀ i v, p.stem i = some v → q.stem i = some v) ∧ p.side ⊆ q.side ∧
      ∀ i, p.stem i = none → ∀ v, q.stem i = some v → ∀ F ∈ p.side,
        BoundedAt F.toDecisions q.base i v

theorem stronger_refl (p : Condition P) : Stronger p p := by
  refine ⟨le_rfl, fun _ _ h => h, Set.Subset.rfl, ?_⟩
  intro i hi v hv _ _
  rw [hi] at hv
  cases hv

theorem stronger_trans {p q r : Condition P} (hpq : Stronger p q) (hqr : Stronger q r) :
    Stronger p r := by
  refine ⟨hpq.1.trans hqr.1, fun i v hv => hpq.2.1 i v (hqr.2.1 i v hv),
    hqr.2.2.1.trans hpq.2.2.1, ?_⟩
  intro i hri v hpv F hFr
  cases hqi : q.stem i with
  | none => exact hpq.2.2.2 i hqi v hpv F (hqr.2.2.1 hFr)
  | some w =>
    have hpw := hpq.2.1 i w hqi
    have hwv : w = v := Option.some.inj (hpw.symm.trans hpv)
    rw [← hwv]
    exact boundedAt_mono (hqr.2.2.2 i hri w hqi F hFr) hpq.1

instance : Preorder (Condition P) where
  le := Stronger
  le_refl := stronger_refl
  le_trans := fun _ _ _ => stronger_trans

def emptyOver (p : P) : Condition P where
  base := p
  stem := fun _ => none
  stem_countable := by simp
  side := ∅
  side_countable := Set.countable_empty

instance [Inhabited P] : Inhabited (Condition P) := ⟨emptyOver default⟩

theorem base_le {p q : Condition P} (hqp : q ≤ p) : q.base ≤ p.base := hqp.1

def liftBase (p : Condition P) (q : P) : Condition P where
  base := q
  stem := p.stem
  stem_countable := p.stem_countable
  side := p.side
  side_countable := p.side_countable

theorem liftBase_le (p : Condition P) {q : P} (hqp : q ≤ p.base) : liftBase p q ≤ p := by
  refine ⟨hqp, fun _ _ h => h, Set.Subset.rfl, ?_⟩
  intro i hi v hv _ _
  change p.stem i = some v at hv
  rw [hi] at hv
  cases hv

theorem base_dense_of_dense {D : Set P} (hD : DenseBelow D) :
    DenseBelow {q : Condition P | q.base ∈ D} := by
  intro p
  obtain ⟨q, hqD, hqp⟩ := hD p.base
  exact ⟨liftBase p q, hqD, liftBase_le p hqp⟩

def liftFunction {I V : Type} (F : FunctionDecisions P I V) :
    FunctionDecisions (Condition P) I V where
  decides p i v := F.decides p.base i v
  dense := by
    intro p i
    obtain ⟨q, hqp, v, hv⟩ := F.dense p.base i
    exact ⟨liftBase p q, liftBase_le p hqp, v, hv⟩
  persistent hqp hv := F.persistent (base_le hqp) hv
  unique hv hw := F.unique hv hw

def track (p : Condition P) (F : NiceFunctionName P W1 W1) : Condition P where
  base := p.base
  stem := p.stem
  stem_countable := p.stem_countable
  side := insert F p.side
  side_countable := p.side_countable.insert F

theorem track_le (p : Condition P) (F : NiceFunctionName P W1 W1) : track p F ≤ p := by
  refine ⟨le_rfl, fun _ _ h => h, Set.subset_insert _ _, ?_⟩
  intro i hi v hv _ _
  change p.stem i = some v at hv
  rw [hi] at hv
  cases hv

theorem tracking_dense (F : NiceFunctionName P W1 W1) :
    DenseBelow {p : Condition P | F ∈ p.side} := by
  intro p
  exact ⟨track p F, Set.mem_insert _ _, track_le p F⟩

end Erdos1172Part3IteratedHechlerOrder
