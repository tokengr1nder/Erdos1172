/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FunctionDecisions

@[expose] public section

/-!
# Cofinality of an ordered cofinal decision name

Countable closure prevents a cofinal ordered decision name from having
countable ground-domain cofinality when its target has uncountable
cofinality. Only the values on a countable cofinal subset are decided
under one condition. Their ground image has a strict upper bound, and
orderedness propagates this bound to every future decided value.

Named cofinality is an explicit dense extension property. This file
does not infer it from possible membership or a ground-type cardinality.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedCofinality

open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)

variable {P I V : Type} [Preorder P] [LinearOrder I] [LinearOrder V]

/-- Decisions at a common condition respect the strict domain order. -/
def OrderedDecisions (E : FunctionDecisions P I V) : Prop :=
  ∀ {p i j x y}, i < j → E.decides p i x → E.decides p j y → x < y

/-- Above every ground cut, some value can be decided after strengthening
any condition. -/
def CofinalDecisions (E : FunctionDecisions P I V) : Prop :=
  ∀ p cut, ∃ q, q ≤ p ∧ ∃ i x, E.decides q i x ∧ cut ≤ x

/-- If the domain has countable cofinality, one strengthening bounds all
subsequent values of an ordered decision name. -/
theorem exists_uniform_bound_of_cof_le_alephZero
    (E : FunctionDecisions P I V) (hclosed : CountablyClosed P)
    (p0 : P) (hordered : OrderedDecisions E)
    (hI : Order.cof I ≤ ℵ₀) (hV : ℵ₀ < Order.cof V) :
    ∃ q : P, q ≤ p0 ∧ ∃ cut : V, ∀ r : P, r ≤ q → ∀ i x, E.decides r i x → x < cut := by
  classical
  obtain ⟨T, hTcof, hTcard⟩ := Order.exists_cof_eq I
  have hT : #T ≤ ℵ₀ := hTcard.trans_le hI
  let restricted : FunctionDecisions P T V :=
    ⟨fun p i v => E.decides p i.val v,
      fun p i => E.dense p i.val,
      fun {_ _ _ _} hqp hv => E.persistent hqp hv,
      fun {_ _ _ _} hv hw => E.unique hv hw⟩
  obtain ⟨q, hqp0, hvalues⟩ := restricted.exists_simultaneous hclosed p0 hT
  let chosen (j : T) : V := (hvalues j).choose
  have hchosen (j : T) : E.decides q j.val (chosen j) := (hvalues j).choose_spec
  have hcount : #(Set.range chosen) ≤ ℵ₀ := Cardinal.mk_range_le.trans hT
  have hnot : ¬IsCofinal (Set.range chosen) := by
    intro hcof
    exact hV.not_ge ((Order.cof_le hcof).trans hcount)
  obtain ⟨cut, hcut⟩ := not_isCofinal_iff.mp hnot
  refine ⟨q, hqp0, cut, ?_⟩
  intro r hrq i x hx
  obtain ⟨j, hj, hij⟩ := hTcof i
  let t : T := ⟨j, hj⟩
  have hjdec : E.decides r j (chosen t) := E.persistent hrq (hchosen t)
  have hle : x ≤ chosen t := by
    rcases eq_or_lt_of_le hij with heq | hlt
    · have hidec : E.decides r i (chosen t) := by
        simpa only [heq] using hjdec
      exact (E.unique hx hidec).le
    · exact (hordered hlt hx hjdec).le
  exact hle.trans_lt (hcut (chosen t) (Set.mem_range_self t))

/-- A cofinal ordered name into an order of uncountable cofinality has
uncountable domain cofinality. No omegaOne-stage lower bound is used. -/
theorem alephZero_lt_cof_domain
    (E : FunctionDecisions P I V) (hclosed : CountablyClosed P)
    (p0 : P) (hordered : OrderedDecisions E) (hcofinal : CofinalDecisions E)
    (hV : ℵ₀ < Order.cof V) : ℵ₀ < Order.cof I := by
  apply lt_of_not_ge
  intro hI
  obtain ⟨q, -, cut, hbound⟩ := exists_uniform_bound_of_cof_le_alephZero E hclosed p0 hordered hI hV
  obtain ⟨r, hrq, i, x, hx, hcutx⟩ := hcofinal q cut
  exact (hbound r hrq i x hx).not_ge hcutx

/-- For a domain of cardinality at most alephOne, the cofinality is
exactly alephOne when the target cofinality is alephOne. -/
theorem cof_domain_eq_alephOne
    (E : FunctionDecisions P I V) (hclosed : CountablyClosed P)
    (p0 : P) (hordered : OrderedDecisions E) (hcofinal : CofinalDecisions E)
    (hI : #I ≤ ℵ_ 1) (hV : Order.cof V = ℵ_ 1) :
    Order.cof I = ℵ_ 1 := by
  have hlarge : ℵ₀ < Order.cof I :=
    alephZero_lt_cof_domain E hclosed p0 hordered hcofinal
      (by simpa only [hV] using Cardinal.aleph0_lt_aleph_one)
  apply le_antisymm ((Order.cof_le_cardinalMk I).trans hI)
  apply le_of_not_gt
  intro hsmall
  exact hlarge.not_ge (Cardinal.lt_aleph_one_iff.mp hsmall)

/-- The ordinal order type of a well-ordered cofinal domain has
cofinality alephOne under the same explicit decision hypotheses. -/
theorem cof_typeLT_domain_eq_alephOne [WellFoundedLT I]
    (E : FunctionDecisions P I V) (hclosed : CountablyClosed P)
    (p0 : P) (hordered : OrderedDecisions E) (hcofinal : CofinalDecisions E)
    (hI : #I ≤ ℵ_ 1) (hV : Order.cof V = ℵ_ 1) :
    (typeLT I).cof = ℵ_ 1 := by
  rw [Ordinal.cof_type]
  exact cof_domain_eq_alephOne E hclosed p0 hordered hcofinal hI hV

end Erdos1172Part3NamedCofinality
