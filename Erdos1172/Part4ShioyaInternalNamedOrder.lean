/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalConditions
public import Erdos1172.Part4ShioyaInternalProjection

@[expose] public section

/-! # The relation name for Shioya refinement in the preparing extension -/

set_option autoImplicit false
noncomputable section
universe u
open bSet ErdosRelationGraph Lattice
open scoped Flypitch
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def Fields.refines (K : N) (s t : Fields B) : B :=
  refinementValue K s.carrier s.order s.point s.length s.bits t.carrier t.order t.point t.length t.bits

def comparison (K x y : N) : B :=
  ⨆ s : Fields B, ⨆ t : Fields B, (x =ᴮ s.code ⊓ y =ᴮ t.code) ⊓ Fields.refines K s t

theorem comparison_ext_left (K y : N) : B_ext (fun x => comparison K x y) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_inf (B_ext_inf B_ext_bv_eq_left B_ext_const) B_ext_const))

theorem comparison_ext_right (K x : N) : B_ext (comparison K x) :=
  B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ => B_ext_inf (B_ext_inf B_ext_const B_ext_bv_eq_left) B_ext_const))

/-- The order is a set of pairs in the preparing universe. A refinement
witness can be a new partial projection there. -/
def orderSet (K : N) (θ : Cardinal.{u}) : N :=
  relationGraph (conditionSet K θ) (conditionSet K θ) (comparison K)

theorem mem_orderSet {K x y : N} {θ : Cardinal.{u}} {Γ : B} :
    Γ ≤ pair x y ∈ᴮ orderSet K θ ↔ Γ ≤ x ∈ᴮ conditionSet K θ ∧ Γ ≤ y ∈ᴮ conditionSet K θ ∧ Γ ≤ comparison K x y :=
  mem_relationGraph_iff (comparison_ext_left K) (comparison_ext_right K)

theorem orderSet_refl {K x : N} {θ : Cardinal.{u}} {Γ : B} (hx : Γ ≤ x ∈ᴮ conditionSet K θ) :
    Γ ≤ pair x x ∈ᴮ orderSet K θ := by
  refine mem_orderSet.mpr ⟨hx,hx,?_⟩
  rw [conditionSet,mem_namedCarrier] at hx
  apply hx.trans (iSup_le fun t => ?_)
  exact le_iSup_of_le t (le_iSup_of_le t (le_inf (le_inf inf_le_left inf_le_left)
    (refinementValue_refl _ _ _ _ _ _ (inf_le_right.trans (inf_le_right.trans inf_le_left)))))

end bSet.ErdosShioyaInternal
