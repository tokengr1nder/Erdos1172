/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalOrder
public import Erdos1172.Part4InternalIndependentHomogeneous

@[expose] public section

/-! # Singleton internal orders and arbitrary mixed binary incidence -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

theorem allIn_intro {Γ : B} {P : N} {f : N → B}
    (h : ∀ {Δ : B}, Δ ≤ Γ → ∀ x, Δ ≤ x ∈ᴮ P → Δ ≤ f x) : Γ ≤ allIn P f :=
  le_iInf fun x => deduction.mp (h inf_le_left x inf_le_right)

theorem allIn_elim {Γ : B} {P x : N} {f : N → B}
    (h : Γ ≤ allIn P f) (hx : Γ ≤ x ∈ᴮ P) : Γ ≤ f x :=
  (le_inf (h.trans (iInf_le _ x)) hx).trans bv_imp_elim

end bSet.ErdosShioyaInternal
