/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCofinality
public import Erdos1172.Part3RegularMembership

@[expose] public section

/-!
# Actual named final tails with a bounded discarded prefix

Reindex an ordered enumeration along a cofinal final-suborder embedding.
Its regularized range is an actual regular name contained in the original
source. One decided tail value bounds every source point not retained by
that name. Membership of a retained point is proved densely below the
original condition, not inferred from a single possible enumeration value.
Only individual decisions and persistence are used; no closure assumption
or completed transfinite lower bound is needed.
-/

open Set Order

namespace Erdos1172Part3NamedFinalTail

open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName regularize)
open Erdos1172Part3NamedCofinality (OrderedDecisions CofinalDecisions)

variable {P I J V : Type} [Preorder P]

/-- Every actual source member can be reached by an exact enumeration
decision. Persistence of the source makes these witnesses dense. -/
def DenseCoverage (E : FunctionDecisions P I V) (U : RegularName P V) : Prop :=
  ∀ p : P, ∀ x : V, U.holds p x →
    ∃ q : P, q ≤ p ∧ ∃ i : I, E.decides q i x

variable [LinearOrder I] [LinearOrder J]

def tailE (E : FunctionDecisions P I V) (e : J ↪o I) : FunctionDecisions P J V :=
  Erdos1172Part3DecisionSelection.reindex E e

def tailU (E : FunctionDecisions P I V) (e : J ↪o I) : RegularName P V :=
  regularize (fun p x => ∃ j : J, (tailE E e).decides p j x)

/-- A tail decision persists and hence gives actual regularized membership. -/
theorem tailU_holds_of_decision (E : FunctionDecisions P I V) (e : J ↪o I)
    {p : P} {j : J} {x : V} (hx : (tailE E e).decides p j x) :
    (tailU E e).holds p x :=
  fun q hqp => ⟨q, le_rfl, j, (tailE E e).persistent hqp hx⟩

theorem tailU_dense_coverage (E : FunctionDecisions P I V) (e : J ↪o I) :
    DenseCoverage (tailE E e) (tailU E e) :=
  fun p _ h => h p le_rfl

/-- Exact original decisions lie in the source, so dense tail certificates
recover actual source membership by regularity. -/
theorem tailU_sub (E : FunctionDecisions P I V) (U : RegularName P V) (e : J ↪o I)
    (hmem : ∀ p : P, ∀ i : I, ∀ x : V, E.decides p i x → U.holds p x) :
    ∀ p : P, ∀ x : V, (tailU E e).holds p x → U.holds p x := by
  intro p x hx
  apply U.of_dense p x
  intro q hqp
  obtain ⟨r, hrq, j, hj⟩ := hx q hqp
  exact ⟨r, hrq, hmem r (e j) x hj⟩

variable [LinearOrder V]

theorem tailE_ordered (E : FunctionDecisions P I V) (e : J ↪o I)
    (hordered : OrderedDecisions E) : OrderedDecisions (tailE E e) := by
  intro p i j x y hij hi hj
  exact hordered (e.strictMono hij) hi hj

/-- A later tail coordinate is decided at a strengthening of the original
cofinal witness, allowing comparison at one common condition. -/
theorem tailE_cofinal (E : FunctionDecisions P I V) (e : J ↪o I)
    (hordered : OrderedDecisions E) (hcofinal : CofinalDecisions E)
    (he : IsCofinal (Set.range e)) : CofinalDecisions (tailE E e) := by
  intro p cut
  obtain ⟨q, hqp, i, x, hx, hcutx⟩ := hcofinal p cut
  obtain ⟨k, hk, hik⟩ := he i
  rcases hk with ⟨j, rfl⟩
  obtain ⟨r, hrq, y, hy⟩ := E.dense q (e j)
  have hx' : E.decides r i x := E.persistent hrq hx
  have hxy : x ≤ y := by
    rcases eq_or_lt_of_le hik with hij | hij
    · have hx'' : E.decides r (e j) x := by simpa only [hij] using hx'
      exact (E.unique hx'' hy).le
    · exact (hordered hij hx' hy).le
  exact ⟨r, hrq.trans hqp, j, y, hy, hcutx.trans hxy⟩

/-- Once a tail value is decided, every actual source point outside its
bounded prefix has tail certificates densely below its own condition. -/
theorem bounded_prefix_of_tail_decision
    (E : FunctionDecisions P I V) (U : RegularName P V) (e : J ↪o I)
    (hordered : OrderedDecisions E) (hcover : DenseCoverage E U)
    (hsep : ∀ i : I, i ∉ Set.range e → ∀ j : J, i < e j)
    {q : P} {j0 : J} {cut : V} (hcut : (tailE E e).decides q j0 cut) :
    ∀ p : P, p ≤ q → ∀ x : V, U.holds p x → x < cut ∨ (tailU E e).holds p x := by
  classical
  intro p hpq x hx
  by_cases hxcut : x < cut
  · exact Or.inl hxcut
  · right
    intro r hrp
    obtain ⟨s, hsr, i, hi⟩ := hcover r x (U.persistent hrp hx)
    have hcut' : E.decides s (e j0) cut := E.persistent (hsr.trans (hrp.trans hpq)) hcut
    have hirange : i ∈ Set.range e := by
      by_contra hni
      exact hxcut (hordered (hsep i hni j0) hi hcut')
    obtain ⟨j, hj⟩ := hirange
    refine ⟨s, hsr, j, ?_⟩
    change E.decides s (e j) x
    simpa only [hj] using hi

/-- Decide one fixed nonempty tail coordinate. The resulting bound is
itself an actual tail member, and it bounds all discarded actual points. -/
theorem exists_bounded_prefix
    (E : FunctionDecisions P I V) (U : RegularName P V) (e : J ↪o I)
    (hJ : Nonempty J) (hordered : OrderedDecisions E) (hcover : DenseCoverage E U)
    (hsep : ∀ i : I, i ∉ Set.range e → ∀ j : J, i < e j) (p0 : P) :
    ∃ q : P, q ≤ p0 ∧ ∃ cut : V, (tailU E e).holds q cut ∧
      ∀ p : P, p ≤ q → ∀ x : V, U.holds p x → x < cut ∨ (tailU E e).holds p x := by
  obtain ⟨j0⟩ := hJ
  obtain ⟨q, hqp0, cut, hcut⟩ := E.dense p0 (e j0)
  exact ⟨q, hqp0, cut, tailU_holds_of_decision E e hcut,
    bounded_prefix_of_tail_decision E U e hordered hcover hsep hcut⟩

/-- The complete named-tail interface: ordered cofinal enumeration, exact
dense coverage, actual inclusion in the source, and a bounded complement. -/
theorem exists_cofinal_tail_with_bounded_prefix
    (E : FunctionDecisions P I V) (U : RegularName P V) (e : J ↪o I)
    (hJ : Nonempty J) (hordered : OrderedDecisions E) (hcover : DenseCoverage E U)
    (hmem : ∀ p : P, ∀ i : I, ∀ x : V, E.decides p i x → U.holds p x)
    (hcofinal : CofinalDecisions E) (he : IsCofinal (Set.range e))
    (hsep : ∀ i : I, i ∉ Set.range e → ∀ j : J, i < e j) (p0 : P) :
    OrderedDecisions (tailE E e) ∧ CofinalDecisions (tailE E e) ∧
      DenseCoverage (tailE E e) (tailU E e) ∧
      (∀ p : P, ∀ x : V, (tailU E e).holds p x → U.holds p x) ∧
      ∃ q : P, q ≤ p0 ∧ ∃ cut : V, (tailU E e).holds q cut ∧
        ∀ p : P, p ≤ q → ∀ x : V, U.holds p x → x < cut ∨ (tailU E e).holds p x :=
  ⟨tailE_ordered E e hordered, tailE_cofinal E e hordered hcofinal he,
    tailU_dense_coverage E e, tailU_sub E U e hmem,
    exists_bounded_prefix E U e hJ hordered hcover hsep p0⟩

end Erdos1172Part3NamedFinalTail
