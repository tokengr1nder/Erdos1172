/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ClosedDecisionSystem

@[expose] public section

/-!
# A concrete countably closed dominating-function order

Conditions have a countable partial function on omegaOne and a countable
family of functions to dominate at every newly decided coordinate.
This file constructs the order, its countable-chain lower bounds, and
the dense requirements. It does not assert existence of a ground-model
filter meeting all requirements, nor a domination principle under GCH.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3HechlerOrder

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed DenseBelow)

structure Condition where
  stem : W1 → Option W1
  stem_countable : {i | stem i ≠ none}.Countable
  side : Set (W1 → W1)
  side_countable : side.Countable

def Stronger (q p : Condition) : Prop :=
  (∀ i v, p.stem i = some v → q.stem i = some v) ∧ p.side ⊆ q.side ∧
    ∀ i, p.stem i = none → ∀ v, q.stem i = some v → ∀ f ∈ p.side, f i < v

theorem stronger_refl (p : Condition) : Stronger p p := by
  refine ⟨fun _ _ h => h, Set.Subset.rfl, ?_⟩
  intro i hi v hv _ _
  rw [hi] at hv
  cases hv

theorem stronger_trans {p q r : Condition} (hpq : Stronger p q) (hqr : Stronger q r) :
    Stronger p r := by
  refine ⟨fun i v hv => hpq.1 i v (hqr.1 i v hv), hqr.2.1.trans hpq.2.1, ?_⟩
  intro i hri v hpv f hfr
  cases hqi : q.stem i with
  | none => exact hpq.2.2 i hqi v hpv f (hqr.2.1 hfr)
  | some w =>
    have hpw := hpq.1 i w hqi
    have hwv : w = v := Option.some.inj (hpw.symm.trans hpv)
    rw [← hwv]
    exact hqr.2.2 i hri w hqi f hfr

instance : Preorder Condition where
  le := Stronger
  le_refl := stronger_refl
  le_trans := fun _ _ _ => stronger_trans

def emptyCondition : Condition where
  stem := fun _ => none
  stem_countable := by simp
  side := ∅
  side_countable := Set.countable_empty

instance : Inhabited Condition := ⟨emptyCondition⟩

theorem comparable_of_chain {C : Set Condition} (hc : IsChain (· ≤ ·) C)
    {p q : Condition} (hp : p ∈ C) (hq : q ∈ C) : p ≤ q ∨ q ≤ p := by
  by_cases heq : p = q
  · subst q
    exact Or.inl le_rfl
  · exact hc hp hq heq

theorem chain_stem_unique {C : Set Condition} (hc : IsChain (· ≤ ·) C)
    {p q : Condition} (hp : p ∈ C) (hq : q ∈ C) {i v w : W1}
    (hpv : p.stem i = some v) (hqw : q.stem i = some w) : v = w := by
  rcases comparable_of_chain hc hp hq with hpq | hqp
  · exact Option.some.inj (hpv.symm.trans (hpq.1 i w hqw))
  · exact Option.some.inj ((hqp.1 i v hpv).symm.trans hqw)

noncomputable def unionStem (C : Set Condition) (i : W1) : Option W1 := by
  classical
  exact if h : ∃ v : W1, ∃ p ∈ C, p.stem i = some v then some h.choose else none

theorem unionStem_some {C : Set Condition} {i v : W1}
    (h : unionStem C i = some v) : ∃ p ∈ C, p.stem i = some v := by
  classical
  dsimp only [unionStem] at h
  split_ifs at h with hex
  · have heq : hex.choose = v := Option.some.inj h
    simpa only [heq] using hex.choose_spec

theorem unionStem_extends {C : Set Condition} (hc : IsChain (· ≤ ·) C)
    {p : Condition} (hp : p ∈ C) {i v : W1} (hv : p.stem i = some v) :
    unionStem C i = some v := by
  classical
  have hex : ∃ w : W1, ∃ q ∈ C, q.stem i = some w := ⟨v, p, hp, hv⟩
  dsimp only [unionStem]
  rw [dif_pos hex]
  obtain ⟨q, hq, hqv⟩ := hex.choose_spec
  exact congrArg some (chain_stem_unique hc hq hp hqv hv)

noncomputable def unionCondition (C : Set Condition) (hC : C.Countable) : Condition where
  stem := unionStem C
  stem_countable := by
    have hcount : (⋃ p ∈ C, {i | p.stem i ≠ none}).Countable :=
      hC.biUnion (fun p _ => p.stem_countable)
    apply hcount.mono
    intro i hi
    cases hstem : unionStem C i with
    | none => exact (hi hstem).elim
    | some v =>
      obtain ⟨p, hp, hpv⟩ := unionStem_some hstem
      have hpn : p.stem i ≠ none := by
        rw [hpv]
        intro h
        cases h
      exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hpn⟩⟩
  side := ⋃ p ∈ C, p.side
  side_countable := hC.biUnion (fun p _ => p.side_countable)

theorem unionCondition_le {C : Set Condition} (hC : C.Countable)
    (hc : IsChain (· ≤ ·) C) {p : Condition} (hp : p ∈ C) : unionCondition C hC ≤ p := by
  refine ⟨fun _ _ hv => unionStem_extends hc hp hv, ?_, ?_⟩
  · intro f hf
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hf⟩⟩
  · intro i hpi v huv f hfp
    obtain ⟨q, hq, hqv⟩ := unionStem_some huv
    rcases comparable_of_chain hc hq hp with hqp | hpq
    · exact hqp.2.2 i hpi v hqv f hfp
    · have hpv := hpq.1 i v hqv
      rw [hpi] at hpv
      cases hpv

def track (p : Condition) (f : W1 → W1) : Condition where
  stem := p.stem
  stem_countable := p.stem_countable
  side := insert f p.side
  side_countable := p.side_countable.insert f

theorem cof_W1 : Order.cof W1 = ℵ_ 1 := by simp_all

theorem exists_bound_of_countable (s : Set W1) (hs : s.Countable) :
    ∃ b : W1, ∀ i ∈ s, i < b := by
  have hcard : #s < Order.cof W1 := by
    rw [cof_W1]
    exact (Cardinal.le_aleph0_iff_set_countable.mpr hs).trans_lt
      (Cardinal.aleph0_lt_aleph.mpr (by norm_num))
  exact not_isCofinal_iff.mp (fun h => hcard.not_ge (Order.cof_le h))

end Erdos1172Part3HechlerOrder
