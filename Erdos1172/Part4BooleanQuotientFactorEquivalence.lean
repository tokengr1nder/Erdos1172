/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanQuotientName

@[expose] public section

/-! # The order of the two-stage quotient forcing

A condition of the name iteration chooses a positive target label and a
positive source value below its coefficient. Its Boolean order test is
reverse inclusion between two checked upper sets. This computes to the
order on the labels, giving a coordinate-preserving order isomorphism
with the factor poset.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172BooleanQuotient

open bSet Erdos1172PositiveBoolean Erdos1172BooleanFactor Erdos1172BooleanNameIteration

variable {B C : Type u}
variable [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

/-- Read the source value and the positive target label of an iteration condition. -/
def toFactor (e : CompleteLatticeHom B C) (p : Condition (quotientName e)) :
    FactorCondition e :=
  let i : Positive C := p.index
  ⟨p.value, i.val, p.nonzero, i.property, p.valid⟩

/-- Use the positive target value of a factor condition as its actual name index. -/
def ofFactor (e : CompleteLatticeHom B C) (p : FactorCondition e) :
    Condition (quotientName e) :=
  ⟨p.source, p.source_ne_bot, (⟨p.target, p.target_ne_bot⟩ : Positive C), p.compatible⟩

theorem ofFactor_toFactor (e : CompleteLatticeHom B C) (p : Condition (quotientName e)) :
    ofFactor e (toFactor e p) = p := rfl

theorem toFactor_ofFactor (e : CompleteLatticeHom B C) (p : FactorCondition e) :
    toFactor e (ofFactor e p) = p := rfl

theorem iteration_le_iff (e : CompleteLatticeHom B C) (p q : Condition (quotientName e)) :
    p ≤ q ↔ p.value ≤ q.value ∧
      (show Positive C from p.index) ≤ (show Positive C from q.index) := by
  change (p.value ≤ q.value ∧ p.value ≤
    (check (upperSetCode (show Positive C from q.index)) : bSet B) ⊆ᴮ
     check (upperSetCode (show Positive C from p.index))) ↔ _
  rw [check_upperSetCode_subset_iff p.nonzero]

def factorOrderIso (e : CompleteLatticeHom B C) :
    Condition (quotientName e) ≃o FactorCondition e where
  toFun := toFactor e
  invFun := ofFactor e
  left_inv := ofFactor_toFactor e
  right_inv := toFactor_ofFactor e
  map_rel_iff' := by
    intro p q
    exact (iteration_le_iff e p q).symm

end Erdos1172BooleanQuotient
