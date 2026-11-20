/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-! # Named projection graphs, points, and regular-open word fibers -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal
open ErdosRelationGraph
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

abbrev inc (F x y : N) : B := pair x y ∈ᴮ F

/-- A subguard formulation of Boolean implication. -/
theorem projection_imp {Γ h k : B} :
    Γ ≤ h ⟹ k ↔ ∀ Δ ≤ Γ, Δ ≤ h → Δ ≤ k := by
  rw [← deduction]
  exact ⟨fun H _ a b => (le_inf a b).trans H,fun H => H _ inf_le_left inf_le_right⟩

end bSet.ErdosShioyaInternal
