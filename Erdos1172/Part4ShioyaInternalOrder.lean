/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationGraph
public import Erdos1172.Part4BooleanCheckedIndicatorAgreement

@[expose] public section

/-! # Partial orders, separativity, and regular-open columns on named carriers -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
universe u
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def allIn (P : N) (f : N → B) : B := ⨅ x : N, (x ∈ᴮ P) ⟹ f x
def someIn (P : N) (f : N → B) : B := ⨆ x : N, (x ∈ᴮ P) ⊓ f x
def edge (R p q : N) : B := pair p q ∈ᴮ R

theorem const_congr (p : N) : B_congr (fun _ : N => p) := fun _ => bv_refl
theorem id_congr : B_congr (fun x : N => x) := fun h => h

theorem allIn_ext {P : N → N} {f : N → N → B} (hp : B_congr P)
    (h : ∀ y, B_ext (fun x => f x y)) : B_ext (fun x => allIn (P x) (f x)) :=
  B_ext_iInf (h := fun y => B_ext_imp (h₁ := B_ext_term _ _ B_ext_mem_right hp) (h₂ := h y))

theorem someIn_ext {P : N → N} {f : N → N → B} (hp : B_congr P)
    (h : ∀ y, B_ext (fun x => f x y)) : B_ext (fun x => someIn (P x) (f x)) :=
  B_ext_iSup (h := fun y => B_ext_inf (B_ext_term _ _ B_ext_mem_right hp) (h y))

theorem edge_ext {R p q : N → N} (hr : B_congr R) (hp : B_congr p) (hq : B_congr q) :
    B_ext (fun x => edge (R x) (p x) (q x)) :=
  fun _ _ => mem_congr (pair_congr (hp inf_le_left) (hq inf_le_left)) (hr inf_le_left) inf_le_right

end bSet.ErdosShioyaInternal
