/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCofinality

@[expose] public section

/-!
# Composing a named index selector with clique decisions

The intermediate index is decided at the same condition as its clique
value. Density follows by two successive decisions, retaining the first
decision by persistence. This keeps actual origins, strict order, and
adjacency; it does not replace actual membership by possible membership.
No closure or stationarity hypothesis is required.
-/

open Set

namespace Erdos1172Part3CliqueDecisionComposition

open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3NamedCofinality (OrderedDecisions)

variable {P I J X : Type} [Preorder P]
  [LinearOrder I] [LinearOrder J] [LinearOrder X] {G : SimpleGraph X}

/-- A named strictly ordered choice of indices selects a named subclique. -/
def compose (E : FunctionDecisions P J I) (core : CliqueDecisions P I X G)
    (hordered : OrderedDecisions E) : CliqueDecisions P J X G where
  decides p j x := ∃ i, E.decides p j i ∧ core.decides p i x
  dense := by
    intro p j
    obtain ⟨q, hqp, i, hi⟩ := E.dense p j
    obtain ⟨r, hrq, x, hx⟩ := core.dense q i
    exact ⟨r, hrq.trans hqp, x, i, E.persistent hrq hi, hx⟩
  persistent := by
    rintro p q j x hqp ⟨i, hi, hx⟩
    exact ⟨i, E.persistent hqp hi, core.persistent hqp hx⟩
  unique := by
    rintro p j x y ⟨i, hi, hx⟩ ⟨k, hk, hy⟩
    have hik : i = k := E.unique hi hk
    subst k
    exact core.unique hx hy
  ordered := by
    rintro p j k x y hjk ⟨i, hi, hx⟩ ⟨l, hl, hy⟩
    exact core.ordered (hordered hjk hi hl) hx hy
  adjacent := by
    rintro p j k x y hjk ⟨i, hi, hx⟩ ⟨l, hl, hy⟩
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · exact core.adjacent (ne_of_lt (hordered hjk hi hl)) hx hy
    · exact core.adjacent (ne_of_gt (hordered hkj hl hi)) hx hy

theorem compose_decides_iff (E : FunctionDecisions P J I)
    (core : CliqueDecisions P I X G) (hordered : OrderedDecisions E)
    (p : P) (j : J) (x : X) :
    (compose E core hordered).decides p j x ↔ ∃ i, E.decides p j i ∧ core.decides p i x := Iff.rfl

/-- Generic cone restriction. Existing iterated-Hechler base lifting
is supplied by `Erdos1172Part3IteratedHechlerPreservation.liftClique`. -/
def onCone (p0 : P) (core : CliqueDecisions P I X G) :
    CliqueDecisions (Set.Iic p0) I X G where
  decides p i x := core.decides p.val i x
  dense := by
    intro p i
    obtain ⟨q, hqp, x, hx⟩ := core.dense p.val i
    exact ⟨⟨q, hqp.trans p.property⟩, hqp, x, hx⟩
  persistent := core.persistent
  unique := core.unique
  ordered := core.ordered
  adjacent := core.adjacent

end Erdos1172Part3CliqueDecisionComposition
