/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularNeighborhoodCode
public import Erdos1172.Part3ClosedDenseRequirements

@[expose] public section

/-!
# Countably complete smallness for named neighborhoods

Smallness has dense local-code witnesses. Countable closure makes
countably many such witnesses hold at one condition, and local code
closure combines them. A source which holds at a reflecting cut cannot
be small. No possible-membership hypothesis is substituted for truth.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RegularNamedIdeal

open ErdosRadoCHAsym (W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)

variable {P : Type} [Preorder P]

/-- Countably many persistent, densely available witnesses have a common
strengthening. The lower bound is only for a countable collection. -/
theorem exists_common_countable_witnesses {J : Type} (hclosed : CountablyClosed P)
    (p0 : P) (R : P → J → Prop)
    (hpersistent : ∀ {p q j}, q ≤ p → R p j → R q j)
    (hdense : ∀ q : P, q ≤ p0 → ∀ j : J, ∃ r : P, r ≤ q ∧ R r j)
    (hJ : #J ≤ ℵ₀) : ∃ q : P, q ≤ p0 ∧ ∀ j : J, R q j := by
  let R0 (q : Set.Iic p0) (j : J) (_ : Unit) : Prop := R q.val j
  obtain ⟨F, hF⟩ := Erdos1172Part3DecisionSelection.exists_function_decisions_of_dense R0
    (fun hqp h => hpersistent hqp h) (by
      intro q j
      obtain ⟨r, hrq, hr⟩ := hdense q.val q.property j
      exact ⟨⟨r, hrq.trans q.property⟩, hrq, (), hr⟩)
  obtain ⟨q, _, hq⟩ := F.exists_simultaneous
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed p0)
    ⟨p0, le_rfl⟩ hJ
  refine ⟨q.val, q.property, ?_⟩
  intro j
  obtain ⟨v, hv⟩ := hq j
  exact hF q j v hv

variable {I : Type} [LinearOrder I] {G : SimpleGraph W2}

def WitnessSmall (r : Code P I G ↪ W2) (H : SimpleGraph W2) (a : W2)
    (p : P) (U : RegularName P W2) : Prop :=
  ∃ c : Code P I G, r c < a ∧ (neg (eval G H c)).holds p a ∧
    ∀ x < a, ∀ q : P, q ≤ p → U.holds q x → (eval G H c).holds q x

theorem witnessSmall_persistent {r : Code P I G ↪ W2} {H : SimpleGraph W2}
    {a : W2} {p q : P} {U : RegularName P W2} (hqp : q ≤ p)
    (h : WitnessSmall r H a p U) : WitnessSmall r H a q U := by
  obtain ⟨c, hc, hn, hsub⟩ := h
  exact ⟨c, hc, (neg (eval G H c)).persistent hqp hn, fun x hx s hsq => hsub x hx s (hsq.trans hqp)⟩

def smallName (r : Code P I G ↪ W2) (H : SimpleGraph W2) (a : W2) :
    RegularName P (RegularName P W2) := regularize (WitnessSmall r H a)

theorem smallName_of_witness {r : Code P I G ↪ W2} {H : SimpleGraph W2}
    {a : W2} {p : P} {U : RegularName P W2} (h : WitnessSmall r H a p U) :
    (smallName r H a).holds p U :=
  fun q hqp => ⟨q, le_rfl, witnessSmall_persistent hqp h⟩

theorem witnessSmall_mono_set {r : Code P I G ↪ W2} {H : SimpleGraph W2}
    {a : W2} {p : P} {U V : RegularName P W2}
    (hsub : ∀ x < a, (implication U V).holds p x)
    (h : WitnessSmall r H a p V) : WitnessSmall r H a p U := by
  obtain ⟨c, hc, hn, hcover⟩ := h
  exact ⟨c, hc, hn, fun x hx q hqp hU => hcover x hx q hqp (hsub x hx q hqp hU)⟩

theorem smallName_mono_set {r : Code P I G ↪ W2} {H : SimpleGraph W2}
    {a : W2} {p : P} {U V : RegularName P W2}
    (hsub : ∀ x < a, (implication U V).holds p x)
    (h : (smallName r H a).holds p V) : (smallName r H a).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, hs⟩ := h q hqp
  exact ⟨s, hsq, witnessSmall_mono_set
    (fun x hx => (implication U V).persistent (hsq.trans hqp) (hsub x hx)) hs⟩

theorem witnessSmall_join {r : Code P I G ↪ W2}
    {σ : NiceCliqueName P I W2 G ↪ W2} {H : SimpleGraph W2}
    {source : RegularName P W2} {a : W2} (ha : GoodCut r σ H source a)
    (p : P) (U : ℕ → RegularName P W2)
    (hU : ∀ n, WitnessSmall r H a p (U n)) : WitnessSmall r H a p (join U) := by
  choose c hc hn hsub using hU
  refine ⟨SmallUnionCode.union c, ha.union_lt c hc, ?_, ?_⟩
  · rw [eval_union, neg_join]
    exact hn
  · intro x hx q hqp hq
    rw [eval_union]
    intro t htq
    obtain ⟨s, hst, n, hs⟩ := hq t htq
    exact ⟨s, hst, n, hsub n x hx s ((hst.trans htq).trans hqp) hs⟩

/-- Dense smallness is countably complete, not only smallness with one
already chosen local witness for each member of the family. -/
theorem smallName_countable_join (hclosed : CountablyClosed P)
    {r : Code P I G ↪ W2} {σ : NiceCliqueName P I W2 G ↪ W2}
    {H : SimpleGraph W2} {source : RegularName P W2} {a : W2}
    (ha : GoodCut r σ H source a) (p : P) (U : ℕ → RegularName P W2)
    (hU : ∀ n, (smallName r H a).holds p (U n)) :
    (smallName r H a).holds p (join U) := by
  intro q hqp
  obtain ⟨s, hsq, hs⟩ := exists_common_countable_witnesses hclosed q
    (fun t n => WitnessSmall r H a t (U n)) (fun h hU => witnessSmall_persistent h hU)
    (fun t htq n => hU n t (htq.trans hqp)) Cardinal.mk_nat.le
  exact ⟨s, hsq, witnessSmall_join ha s U hs⟩

theorem smallName_empty {r : Code P I G ↪ W2}
    {σ : NiceCliqueName P I W2 G ↪ W2} {H : SimpleGraph W2}
    {source : RegularName P W2} {a : W2} (ha : GoodCut r σ H source a) (p : P) :
    (smallName r H a).holds p (ground ∅) := by
  apply smallName_of_witness
  refine ⟨SmallUnionCode.empty, ha.empty_lt, ?_, ?_⟩
  · intro q hqp hq
    exact hq
  · intro x hx q hqp hq
    exact hq.elim

/-- Truth of the source at the cut rules out smallness below every
strengthening. This is a conditional properness theorem with the source
membership stated explicitly. -/
theorem source_not_small {r : Code P I G ↪ W2}
    {σ : NiceCliqueName P I W2 G ↪ W2} {H : SimpleGraph W2}
    {source : RegularName P W2} {a : W2} (ha : GoodCut r σ H source a)
    (p : P) (hp : source.holds p a) :
    (neg (smallName r H a)).holds p source := by
  intro q hqp hq
  obtain ⟨s, hsq, c, hc, hn, hsub⟩ := hq q le_rfl
  exact hn s le_rfl (ha.reflects_source c hc s hsub a s le_rfl
    (source.persistent (hsq.trans hqp) hp))

end Erdos1172Part3RegularNamedIdeal
