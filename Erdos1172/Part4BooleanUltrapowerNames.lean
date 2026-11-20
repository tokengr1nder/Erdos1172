/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerValues
public import Flypitch4.Bvm
public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Order.WellFounded

@[expose] public section

/-! # The hereditary ultrapower of Boolean forcing names

Children of a family of names are selected on an ultrafilter-large set.
Countable completeness makes hereditary descent well-founded. The resulting
name can have children selected by nonconstant functions, even when the
parent name is constant.
-/

set_option autoImplicit false
noncomputable section
open Filter
universe u

namespace Erdos1172BooleanUltrapower

variable {I B : Type u} [NontrivialCompleteBooleanAlgebra B] (U : Ultrafilter I)

def immediate (x y : bSet B) : Prop := ∃ k : y.type, y.func k = x

private theorem immediate_wf : WellFounded (immediate (B := B)) := by
  constructor
  intro x
  induction x with
  | mk T f w ih =>
    constructor
    rintro y ⟨k, rfl⟩
    exact ih k

def familyChild (Y X : I → bSet B) : Prop := ∀ᶠ i in U, immediate (Y i) (X i)

theorem familyChild_wf [CountableInterFilter (U : Filter I)] :
    WellFounded (familyChild (B := B) U) := by
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  constructor
  rintro ⟨f, hf⟩
  obtain ⟨i, hi⟩ := (eventually_countable_forall.mpr hf).exists
  exact (wellFounded_iff_isEmpty_descending_chain.mp immediate_wf).false
    ⟨fun n => f n i, hi⟩

abbrev Children (X : I → bSet B) := LargeSelection U (fun i => (X i).type)

def child (X : I → bSet B) (a : Children U X) (i : I) : bSet B := by
  classical
  exact if hi : i ∈ a.carrier then (X i).func (a.pick ⟨i, hi⟩) else ∅

def weight (X : I → bSet B) (a : Children U X) : I → B :=
  selected (fun i => (X i).bval) a

theorem child_lt (X : I → bSet B) (a : Children U X) : familyChild U (child U X a) X := by
  apply Filter.mem_of_superset a.large
  intro i hi
  exact ⟨a.pick ⟨i, hi⟩, by simp [child, hi]⟩

variable [CountableInterFilter (U : Filter I)]

def liftName {C : Type u} [NontrivialCompleteBooleanAlgebra C] (V : (I → B) → C) :
    (I → bSet B) → bSet C :=
  (familyChild_wf U).fix fun X rec => .mk (Children U X)
    (fun a => rec (child U X a) (child_lt U X a)) (fun a => V (weight U X a))

theorem liftName_eq {C : Type u} [NontrivialCompleteBooleanAlgebra C] (V : (I → B) → C)
    (X : I → bSet B) :
    liftName U V X = .mk (Children U X) (fun a => liftName U V (child U X a))
      (fun a => V (weight U X a)) := WellFounded.fix_eq _ _ _

end Erdos1172BooleanUltrapower
