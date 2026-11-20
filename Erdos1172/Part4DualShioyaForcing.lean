/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4PartialProjectionHom
public import Erdos1172.Part4ShioyaStringTransport

@[expose] public section

/-! # The dual Shioya forcing on small presentations

We use an ordinal below θ to present the carrier of each small poset.
A condition stores its chosen point and the Boolean coefficients of a
binary function with ground ordinal domain. The order uses the two
forcing tests of Definition 23 of Eskew–Hayut, *Dense Ideals*.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
open scoped Flypitch
universe u

namespace Erdos1172Shioya

def Separative (P : Type u) [Preorder P] : Prop :=
  ∀ p q : P, ¬ p ≤ q → ∃ r ≤ p, ¬ ∃ t : P, t ≤ r ∧ t ≤ q

/-- The cardinal bound is encoded by an ordinal label for the carrier. -/
structure Presentation (θ : Cardinal.{u}) where
  index : θ.ord.ToType
  order : PartialOrder index.toOrd.val.ToType

namespace Presentation

variable {θ : Cardinal.{u}}

def Carrier (A : Presentation θ) : Type u := A.index.toOrd.val.ToType
instance (A : Presentation θ) : PartialOrder A.Carrier := A.order

theorem cardinal_lt (A : Presentation θ) : Cardinal.mk A.Carrier < θ := by
  change Cardinal.mk A.index.toOrd.val.ToType < θ
  rw [Cardinal.mk_toType]
  exact Cardinal.lt_ord.mp A.index.toOrd.property

end Presentation

structure Condition (κ θ : Cardinal.{u}) where
  presentation : Presentation θ
  separative : Separative presentation.Carrier
  complete : ShortInfima κ presentation.Carrier
  point : presentation.Carrier
  length : θ.ord.ToType
  bits : length.toOrd.val.ToType → Completion presentation.Carrier

namespace Condition

variable {κ θ : Cardinal.{u}}

abbrev Poset (p : Condition κ θ) := p.presentation.Carrier
abbrev Algebra (p : Condition κ θ) := Completion p.Poset
instance (p : Condition κ θ) : Nonempty p.Poset := ⟨p.point⟩
instance (p : Condition κ θ) : NontrivialCompleteBooleanAlgebra p.Algebra where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

def name (p : Condition κ θ) : StringName p.Algebra p.length.toOrd.val :=
  StringName.ofBits _ p.bits

/-- A projection induces membership of the weaker point in the projected
generic and translates its string to an initial segment of the stronger string. -/
def Refines (p q : Condition κ θ) : Prop :=
  ∃ π : PartialProjection κ p.Poset q.Poset,
    condition p.point ≤ π.booleanHom (condition q.point) ∧
    condition p.point ≤ extensionValue π.booleanHom q.name p.name

theorem refines_refl (p : Condition κ θ) : Refines p p := by
  refine ⟨PartialProjection.identity, ?_, ?_⟩
  · rw [PartialProjection.booleanHom_id]
    exact le_rfl
  · rw [PartialProjection.booleanHom_id]
    exact le_top.trans (extensionValue_refl p.name)

theorem refines_trans (hκ : Cardinal.aleph0 < κ) {p q r : Condition κ θ}
    (hpq : Refines p q) (hqr : Refines q r) : Refines p r := by
  obtain ⟨π, hp, hs⟩ := hpq
  obtain ⟨σ, hq, ht⟩ := hqr
  refine ⟨PartialProjection.comp π σ hκ p.complete, ?_, ?_⟩
  · rw [PartialProjection.booleanHom_comp]
    exact hp.trans (OrderHomClass.mono π.booleanHom hq)
  · rw [PartialProjection.booleanHom_comp]
    exact extensionValue_trans σ.booleanHom π.booleanHom r.name q.name p.name hp ht hs

instance [hκ : Fact (Cardinal.aleph0 < κ)] : Preorder (Condition κ θ) where
  le := Refines
  le_refl := refines_refl
  le_trans _ _ _ := refines_trans hκ.out

end Condition

/-- The regular completion of the preorder of dual Shioya conditions. -/
abbrev Algebra (κ θ : Cardinal.{u}) [Fact (Cardinal.aleph0 < κ)] :=
  Completion (Condition κ θ)

end Erdos1172Shioya
