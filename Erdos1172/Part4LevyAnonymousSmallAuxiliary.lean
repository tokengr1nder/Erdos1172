/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanQuotientSmallPresentation
public import Mathlib.SetTheory.Ordinal.Family
public import Erdos1172.Part4InternalGCHCardinalTransport
public import Erdos1172.Part4LevyMatchingJointForcing

@[expose] public section

/-! # The internally small auxiliary forcing over the anonymous collapse -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u
open scoped Flypitch
open Cardinal bSet Erdos1172BooleanQuotient Erdos1172CompleteSubalgebra Erdos1172PosetGeneric
open Erdos1172PositiveBoolean Erdos1172PosetCompletion Erdos1172LevyCollapse.Matching

namespace Erdos1172LevyCohen

/-- A small named dense subset of the actual Boolean quotient, with its
checked enumeration and the identification of its forcing iteration. -/
structure SmallAuxiliary (κ : Cardinal.{u}) {A C : Type u}
    [NontrivialCompleteBooleanAlgebra A] [NontrivialCompleteBooleanAlgebra C]
    (e : CompleteLatticeHom A C) where
  forcing : bSet A
  size : Cardinal.mk forcing.type ≤ κ
  subset : (⊤ : A) ≤ forcing ⊆ᴮ quotientName e
  dense : (⊤ : A) ≤ denseValue (quotientName e) (fun y => y ∈ᴮ forcing)
  enumeration : bSet A
  enumerates : (⊤ : A) ≤ is_function (check (PSet.ordinalMk κ.ord)) forcing enumeration ⊓
    is_surj (check (PSet.ordinalMk κ.ord)) forcing enumeration
  completion : C ≃o Erdos1172BooleanNameIteration.Algebra forcing
  over_source : ∀ a, completion (e a) = Erdos1172BooleanNameIteration.sourceHom forcing a

def fromDense (κ : Cardinal.{u}) {A C K : Type u}
    [NontrivialCompleteBooleanAlgebra A] [NontrivialCompleteBooleanAlgebra C]
    (e : CompleteLatticeHom A C) (inj : Function.Injective e)
    (d : K → Positive C) (small : #K ≤ κ) (hd : ∀ c, ∃ k, d k ≤ c) : SmallAuxiliary κ e :=
  let f := SmallPresentation.exists_enumeration e d hd inj κ small
  ⟨SmallPresentation.labels e d,small,SmallPresentation.subset e d,
    SmallPresentation.internal_dense e d hd,f.choose,f.choose_spec,
    SmallPresentation.completion e d hd,SmallPresentation.completion_over_source e d hd⟩

abbrev LevyCohenConditions (κ : Cardinal.{u}) :=
  Erdos1172CohenIteration.Conditions (ErdosOmegaTwo.omegaOne : bSet (FirstAlgebra κ))

theorem conditions_dense (κ : Cardinal.{u}) {D : Set (LevyCohenConditions κ)}
    (hD : ∀ p, ∃ q ∈ D, q ≤ p) (c : Positive (Algebra κ)) :
    ∃ k : D, positiveCondition k.val ≤ c := by
  obtain ⟨p,hp⟩ := exists_condition_le c.property
  obtain ⟨q,h,hq⟩ := hD p
  exact ⟨⟨q,h⟩,(condition_mono hq).trans hp⟩

/-- Adjoin an independent Col(ω,κ) to the actual prepared extension. -/
abbrev AuxiliaryAmbient (κ : Cardinal.{u}) := JointForcing (Algebra κ) κ.ord.ToType

def auxiliaryInclusion (κ : Cardinal.{u}) : CompleteLatticeHom (anonymousAlgebra κ) (AuxiliaryAmbient κ) :=
  (jointSourceHom κ.ord.ToType).comp (inclusion (anonymousAlgebra κ))

theorem auxiliaryInclusion_injective (κ : Cardinal.{u}) : Function.Injective (auxiliaryInclusion κ) := by
  intro a b h
  apply inclusion_injective (anonymousAlgebra κ)
  apply joint_source_reflects (d := (⊤ : Erdos1172Collapse.Algebra κ.ord.ToType)) top_ne_bot
  exact congrArg (fun v => jointCollapseHom (Algebra κ) (⊤ : Erdos1172Collapse.Algebra κ.ord.ToType) ⊓ v) h

/-- The quotient with the independent collapse, computed in the same
anonymous algebra, is still enumerated by checked κ. Its iteration is the
completion of the independent product over the specified inclusion. -/
def anonymousSmallAuxiliaryWithCollapse (κ : Cardinal.{u}) (hκ : κ.IsInaccessible) :
    SmallAuxiliary κ (auxiliaryInclusion κ) := by
  let D := (exists_dense_presentation κ hκ).choose
  have data := (exists_dense_presentation κ hκ).choose_spec
  let K := D × Erdos1172Collapse.Condition κ.ord.ToType
  let d (k : K) : Positive (AuxiliaryAmbient κ) := positiveCondition (positiveCondition k.1.val,k.2)
  have bound : #(Erdos1172Collapse.Condition κ.ord.ToType) ≤ κ := Erdos1172Collapse.cardinal_le.trans
    (max_le hκ.aleph0_lt.le (Cardinal.mk_ord_toType κ).le)
  have small : #K ≤ κ := by
    simpa only [K,Cardinal.mk_prod,Cardinal.lift_id] using
      (mul_le_mul' data.1 bound).trans_eq (Cardinal.mul_eq_self hκ.aleph0_lt.le)
  apply fromDense κ _ (auxiliaryInclusion_injective κ) d small
  intro c
  obtain ⟨p,hp⟩ := exists_condition_le c.property
  obtain ⟨k,hk⟩ := conditions_dense κ data.2 p.1
  exact ⟨(k,p.2),(condition_mono (show (positiveCondition k.val,p.2) ≤ p from ⟨hk,le_rfl⟩)).trans hp⟩

end Erdos1172LevyCohen
