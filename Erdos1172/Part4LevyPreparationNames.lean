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

include hκ hu in
theorem prepared_mem (X Y : bSet A) : (lift X ∈ᴮ lift Y) = inc (X ∈ᴮ Y) := by
  apply (map_mem hφ _ _).symm.trans
  apply (congrArg (fun d => (φ) d) (value_name_mem U (fun _ => X) (fun _ => Y)).symm).trans
  exact collapseCompletionIso_constant U a hk hf hn ht hκ hu _

include hκ hu in
theorem prepared_subset (X Y : bSet A) : (lift X ⊆ᴮ lift Y) = inc (X ⊆ᴮ Y) := by
  apply (map_subset hφ _ _).symm.trans
  apply (congrArg (fun d => (φ) d) (value_name_subset U (fun _ => X) (fun _ => Y)).symm).trans
  exact collapseCompletionIso_constant U a hk hf hn ht hκ hu _

include hκ hu in
/-- Prepared ω₁ in the smaller collapse has as its image precisely the checked
upper cardinal in the larger collapse. -/
theorem prepared_omegaOne : (⊤ : B) ≤ lift omegaOne =ᴮ check (PSet.ordinalMk θ.ord) := by
  have h := OrderHomClass.mono hφ (fine_firstCollapse_omegaOne_image U κ hκ hu θ a hf hn ht)
  rw [TopHomClass.map_top hφ,map_bv_eq hφ,map_check] at h
  exact h

include hκ hu in
theorem prepared_seed_mem (lt : κ < θ) : (⊤ : B) ≤ check (PSet.ordinalMk κ.ord) ∈ᴮ lift omegaOne :=
  mem_congr bv_refl (bv_symm (prepared_omegaOne U a hk hf hn ht hκ hu))
    (check_mem (PSet.mk_mem_mk_of_lt (Cardinal.ord_lt_ord.mpr lt)))

include hκ hu in
theorem prepared_seed_excludes_bound (b : bSet A) :
    inc (b ∈ᴮ omegaOne) ≤ (check (PSet.ordinalMk κ.ord) ∈ᴮ lift b)ᶜ := by
  have h := OrderHomClass.mono hφ (fine_firstCollapse_seed_excludes_bound U κ hκ hu b)
  rw [map_compl' hφ,map_mem hφ,map_check] at h
  exact (collapseCompletionIso_constant U a hk hf hn ht hκ hu _).symm.trans_le h

include hκ hu in
/-- Every mixed upper-collapse name below the seed locally equals the prepared
image of an ordinal of the lower-collapse extension. -/
theorem prepared_seed_covered (y : bSet B) :
    (y ∈ᴮ check (PSet.ordinalMk κ.ord)) ≤ ⨆ x : bSet A, inc (x ∈ᴮ omegaOne) ⊓ (y =ᴮ lift x) := by
  let inv : CompleteLatticeHom B (Erdos1172BooleanUltrapower.Algebra U A) := (φ).symm
  let z := mapNames inv y
  have comp : (hφ).comp inv = CompleteLatticeHom.id B := by ext b; exact (φ).apply_symm_apply b
  have eq : mapNames hφ z = y := by rw [show z = mapNames inv y from rfl,← mapNames_comp,comp,mapNames_id]
  have h := OrderHomClass.mono hφ (fine_firstCollapse_seed_covered U κ hκ hu z)
  rw [map_mem,map_check,eq,_root_.map_iSup] at h
  apply h.trans
  apply iSup_mono
  intro x
  apply le_inf ((OrderHomClass.mono hφ inf_le_left).trans_eq
    (collapseCompletionIso_constant U a hk hf hn ht hκ hu _))
  apply (OrderHomClass.mono hφ inf_le_right).trans
  rw [map_bv_eq hφ,eq]
  exact le_rfl

end Erdos1172LevyCollapse.Preparation
