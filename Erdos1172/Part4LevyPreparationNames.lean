/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationBooleanLift

@[expose] public section

/-! # The hereditary preparation lift into the actual larger Lévy collapse -/

set_option autoImplicit false
noncomputable section
open Filter bSet ErdosNameTransport ErdosOmegaTwo Erdos1172GroundUltrapower
open Erdos1172BooleanUltrapower Erdos1172LevyCohen
open scoped Flypitch
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]
variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "A" => FirstAlgebra κ
local notation "B" => FirstAlgebra θ
local notation "φ" => collapseCompletionIso U a hk hf hn ht
local notation "hφ" => ((φ) : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U A) B)
local notation "inc" => initialCollapseHom hk

def preparedName (X : bSet A) : bSet B := mapNames hφ (hereditary U (fun _ => X))
local notation "lift" => preparedName U a hk hf hn ht
variable [CardinalInterFilter (U : Filter I) κ] (hκ : κ.IsRegular) (hu : Cardinal.aleph0 < κ)
local notation "e₀" => firstCollapseConstantHom U κ hκ hu

include hκ hu in
theorem prepared_eq (X Y : bSet A) : (lift X =ᴮ lift Y) = inc (X =ᴮ Y) := by
  apply (map_bv_eq hφ _ _).symm.trans
  apply (congrArg (fun d => (φ) d) (value_name_eq U (fun _ => X) (fun _ => Y)).symm).trans
  exact collapseCompletionIso_constant U a hk hf hn ht hκ hu _

end Erdos1172LevyCollapse.Preparation
