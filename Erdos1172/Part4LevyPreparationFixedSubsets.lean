/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationNames

@[expose] public section

/-! # Agreement with initial-collapse transport for all mixed bounded subsets -/

set_option autoImplicit false
noncomputable section
open Filter bSet ErdosNameTransport ErdosCheckedIndicator Erdos1172GroundUltrapower
open Erdos1172BooleanUltrapower Erdos1172LevyCohen
open scoped Flypitch
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "A" => FirstAlgebra κ
local notation "B" => FirstAlgebra θ
local notation "j" => preparedName U a hk hf hn ht
local notation "inc" => initialCollapseHom hk
variable [CardinalInterFilter (U : Filter I) κ] (hκ : κ.IsRegular) (hu : Cardinal.aleph0 < κ)

theorem prepared_fixed_ordinal (β : Ordinal.{u}) (hβ : β < κ.ord) :
    (⊤ : B) ≤ j (check (PSet.ordinalMk β)) =ᴮ check (PSet.ordinalMk β) := by
  let φ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U A) B := collapseCompletionIso U a hk hf hn ht
  have h := OrderHomClass.mono φ (hereditary_fixed_checked_ordinal («B» := A) U κ β hβ)
  rwa [TopHomClass.map_top φ,map_bv_eq φ,map_check] at h

end Erdos1172LevyCollapse.Preparation
