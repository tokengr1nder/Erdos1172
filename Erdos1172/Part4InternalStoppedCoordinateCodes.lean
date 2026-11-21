/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalMixedProductInjection
public import Erdos1172.Part4InternalStoppedCoordinateTriangle
public import Erdos1172.Part4InternalCountableSubsetCodes

@[expose] public section

/-!
# A fixed small family of entire stopped coordinate histories

The fixed support is the omega-one cube of nested pairs. The family
contains all internally countable subsets of that support, including every
actual active triangle through a countable stopping stage. Mixed product
lifting proves the cube bound; no cardinal arithmetic is supplied as a
new premise. Congruence is unconditional for later bounded internal choice.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosStoppedCoordinateCodes

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph ErdosSimultaneousHistory ErdosSimultaneousRun
open ErdosSimultaneousEntry ErdosStoppedCoordinateTriangle ErdosCountableSubsetCodes

private theorem triangleDomain_subset_of_eq {ρ τ : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ ρ =ᴮ τ) : Γ ≤ triangleDomain ρ ⊆ᴮ triangleDomain τ := by
  rw [subset_unfold']
  apply le_iInf
  intro q
  rw [← deduction]
  let Δ := Γ ⊓ q ∈ᴮ triangleDomain ρ
  have Hprod : Δ ≤ q ∈ᴮ prod (succ ρ) (succ ρ) :=
    mem_of_mem_subset triangleDomain_subset_square inf_le_right
  obtain ⟨ξ, _, σ, _, Hq⟩ := mem_prod_iff₂.mp Hprod
  have Hold : Δ ≤ pair ξ σ ∈ᴮ triangleDomain ρ := mem_congr Hq bv_refl inf_le_right
  have Hparts := (mem_relationGraph_iff
    (fun _ => B_ext_mem_right) (fun _ => B_ext_mem_left)).mp Hold
  have Hsucc : Δ ≤ succ ρ =ᴮ succ τ := B_congr_succ (inf_le_left.trans H)
  have Hnew : Δ ≤ pair ξ σ ∈ᴮ triangleDomain τ :=
    (mem_relationGraph_iff (fun _ => B_ext_mem_right) (fun _ => B_ext_mem_left)).mpr
      ⟨mem_congr bv_refl Hsucc Hparts.1, mem_congr bv_refl Hsucc Hparts.2.1, Hparts.2.2⟩
  exact mem_congr (bv_symm Hq) bv_refl Hnew

theorem triangleDomain_congr : B_congr (triangleDomain (𝔹 := 𝔹)) := by
  intro ρ τ Γ H
  exact subset_ext (triangleDomain_subset_of_eq H) (triangleDomain_subset_of_eq (bv_symm H))

private theorem stoppedCoordinateTriangle_subset_of_eq {ρ τ P Q : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ =ᴮ τ) (HP : Γ ≤ P =ᴮ Q) :
    Γ ≤ stoppedCoordinateTriangle ρ P ⊆ᴮ stoppedCoordinateTriangle τ Q := by
  rw [subset_unfold']
  apply le_iInf
  intro e
  rw [← deduction]
  let Δ := Γ ⊓ e ∈ᴮ stoppedCoordinateTriangle ρ P
  have Hprod : Δ ≤ e ∈ᴮ prod (triangleDomain ρ) omegaOne :=
    mem_of_mem_subset stoppedCoordinateTriangle_subset_product inf_le_right
  obtain ⟨q, _, v, _, He⟩ := mem_prod_iff₂.mp Hprod
  have Hparts := mem_stoppedCoordinateTriangle_iff.mp (mem_congr He bv_refl
    (show Δ ≤ e ∈ᴮ stoppedCoordinateTriangle ρ P from inf_le_right))
  have Hnew : Δ ≤ pair q v ∈ᴮ stoppedCoordinateTriangle τ Q :=
    mem_stoppedCoordinateTriangle_iff.mpr
      ⟨mem_congr bv_refl (triangleDomain_congr (inf_le_left.trans Hρ)) Hparts.1,
        Hparts.2.1,
        mem_congr bv_refl (coordinateHistory_congr_graph (inf_le_left.trans HP)) Hparts.2.2⟩
  exact mem_congr (bv_symm He) bv_refl Hnew

theorem stoppedCoordinateTriangle_congr {ρ τ P Q : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ =ᴮ τ) (HP : Γ ≤ P =ᴮ Q) :
    Γ ≤ stoppedCoordinateTriangle ρ P =ᴮ stoppedCoordinateTriangle τ Q :=
  subset_ext (stoppedCoordinateTriangle_subset_of_eq Hρ HP)
    (stoppedCoordinateTriangle_subset_of_eq (bv_symm Hρ) (bv_symm HP))

theorem stoppedCoordinateTriangle_congr_graph (ρ : bSet 𝔹) :
    B_congr (stoppedCoordinateTriangle ρ) := by
  intro P Q Γ H
  exact stoppedCoordinateTriangle_congr bv_refl H

def coordinateSupport : bSet 𝔹 := prod (prod omegaOne omegaOne) omegaOne

theorem coordinateSupport_small {Γ : 𝔹} (HCH : Γ ≤ (CH : 𝔹)) :
    Γ ≤ injects_into (coordinateSupport : bSet 𝔹) omegaOne :=
  injects_into_trans
    (ErdosMixedProductInjection.injects_into_prod
      (ErdosCardinalSquare.omegaOne_square_injects HCH) injects_into_refl)
    (ErdosCardinalSquare.omegaOne_square_injects HCH)

theorem stoppedCoordinateTriangle_subset_cube {ρ P : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ ∈ᴮ omegaOne) :
    Γ ≤ stoppedCoordinateTriangle ρ P ⊆ᴮ coordinateSupport :=
  subset_trans' stoppedCoordinateTriangle_subset_product
    (ErdosPartialInjection.prod_domain_mono (triangleDomain_subset_omegaOne_square Hρ))

def coordinateHistoryCodes : bSet 𝔹 := countableSubsets coordinateSupport

theorem mem_coordinateHistoryCodes_iff {g : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ g ∈ᴮ coordinateHistoryCodes ↔ Γ ≤ g ⊆ᴮ coordinateSupport ∧ Γ ≤ injects_into g bSet.omega :=
  mem_countableSubsets_iff

theorem stoppedCoordinateTriangle_mem_codes_of_func {ρ P : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ ∈ᴮ omegaOne) (HX : Γ ≤ is_func (coordinateHistory P)) :
    Γ ≤ stoppedCoordinateTriangle ρ P ∈ᴮ coordinateHistoryCodes :=
  mem_coordinateHistoryCodes_iff.mpr
    ⟨stoppedCoordinateTriangle_subset_cube Hρ, stoppedCoordinateTriangle_countable Hρ HX⟩

theorem stoppedCoordinateTriangle_mem_codes
    {color : Bool} {R S top P ρ : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P) (Hρ : Γ ≤ ρ ∈ᴮ omegaOne) :
    Γ ≤ stoppedCoordinateTriangle ρ P ∈ᴮ coordinateHistoryCodes :=
  stoppedCoordinateTriangle_mem_codes_of_func Hρ
    ((coordinateHistory_is_function_of_run HP Hlaw).trans (inf_le_left.trans inf_le_left))

/-- All internally countable triple graphs lie in one omega-one-small
family under CH; there is no ground-countability restriction. -/
theorem coordinateHistoryCodes_small {Γ : 𝔹} (HCH : Γ ≤ (CH : 𝔹)) :
    Γ ≤ injects_into (coordinateHistoryCodes : bSet 𝔹) omegaOne :=
  countableSubsets_injects_omegaOne HCH (coordinateSupport_small HCH)

end bSet.ErdosStoppedCoordinateCodes
