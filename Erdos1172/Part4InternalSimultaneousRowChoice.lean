/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousCandidateBridge

@[expose] public section

/-!
# Coherent simultaneous least row choices

The actual graph is defined by the unique least point of each exact
candidate set. Different rows may use different ideals; existence of
these ideals is a guarded internal existential, not an external family
of chosen names. Ideal witnesses are used only to prove totality. No
successful simultaneous run or homogeneous block is assumed or asserted.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRowChoice

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosColargeIntersection ErdosOrdinalLeast
open ErdosRelationGraph ErdosSimultaneousCandidates

def rowIdealData (S σ J : bSet 𝔹) : 𝔹 :=
  properIdeal omegaOne J ⊓ (countableAbsorption omegaOne J ⊓
    (countableClosure J ⊓ (⨅ y, ⨅ A, _root_.imp
      (y ∈ᴮ omegaTwo ⊓ pair (pair σ y) A ∈ᴮ S) (colarge omegaOne J A))))

def simultaneousRowLaw (δ S Y X top Z : bSet 𝔹) : 𝔹 :=
  ⨅ σ, ⨅ v, _root_.imp (σ ∈ᴮ omegaOne ⊓ pair σ v ∈ᴮ Z)
    (leastIn (simultaneousCandidates δ S Y X top σ) v)

theorem simultaneousRowLaw_ext_graph (δ S Y X top : bSet 𝔹) :
    B_ext (simultaneousRowLaw δ S Y X top) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_const B_ext_mem_right) (h₂ := B_ext_const)))

def simultaneousChoices (δ S Y X top : bSet 𝔹) : bSet 𝔹 :=
  relationGraph omegaOne omegaOne
    (fun σ v => leastIn (simultaneousCandidates δ S Y X top σ) v)

theorem leastCandidate_ext_row (δ S Y X top v : bSet 𝔹) :
    B_ext (fun σ => leastIn (simultaneousCandidates δ S Y X top σ) v) :=
  B_ext_term (ϕ := fun C => leastIn C v)
    (t := simultaneousCandidates δ S Y X top) (leastIn_ext_set v)
    (simultaneousCandidates_congr_row δ S Y X top)

theorem mem_simultaneousChoices_iff {δ S Y X top σ v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair σ v ∈ᴮ simultaneousChoices δ S Y X top ↔
      Γ ≤ σ ∈ᴮ omegaOne ∧ Γ ≤ v ∈ᴮ omegaOne ∧
        Γ ≤ leastIn (simultaneousCandidates δ S Y X top σ) v :=
  mem_relationGraph_iff (leastCandidate_ext_row δ S Y X top)
    (fun σ => leastIn_ext_value (simultaneousCandidates δ S Y X top σ))

theorem simultaneousChoices_law {δ S Y X top : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ simultaneousRowLaw δ S Y X top (simultaneousChoices δ S Y X top) := by
  apply le_iInf
  intro σ
  apply le_iInf
  intro v
  rw [← deduction]
  exact (mem_simultaneousChoices_iff.mp
    (show Γ ⊓ (σ ∈ᴮ omegaOne ⊓ pair σ v ∈ᴮ simultaneousChoices δ S Y X top) ≤
      pair σ v ∈ᴮ simultaneousChoices δ S Y X top from
      inf_le_right.trans inf_le_right)).2.2

/-- The entire row-choice graph is total and supported. Per-row ideal
existence suffices; no coherent ideal selector is supplied or needed. -/
theorem simultaneousChoices_is_function {δ S Y X top : bSet 𝔹} {Γ : 𝔹}
    (Hδ : Γ ≤ δ ∈ᴮ omegaOne) (Htop : Γ ≤ top ∈ᴮ omegaTwo)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hrows : Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J)) :
    Γ ≤ is_function omegaOne omegaOne (simultaneousChoices δ S Y X top) := by
  apply relationGraph_is_function (leastCandidate_ext_row δ S Y X top)
    (fun σ => leastIn_ext_value (simultaneousCandidates δ S Y X top σ))
  · apply le_iInf
    intro σ
    rw [← deduction]
    let Δ := Γ ⊓ σ ∈ᴮ omegaOne
    have Hideals : Δ ≤ ⨆ J, rowIdealData S σ J :=
      (le_inf (inf_le_left.trans (Hrows.trans (iInf_le _ σ))) inf_le_right).trans bv_imp_elim
    apply (le_inf (le_refl Δ) Hideals).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro J
    let Λ := Δ ⊓ rowIdealData S σ J
    have HΛ : Λ ≤ Γ := inf_le_left.trans inf_le_left
    have Hdata : Λ ≤ rowIdealData S σ J := inf_le_right
    obtain ⟨v, Hv⟩ := exists_least_simultaneousCandidate
      (Hdata.trans inf_le_left)
      (Hdata.trans (inf_le_right.trans inf_le_left))
      (Hdata.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
      (HΛ.trans Hδ) (HΛ.trans Htop) (HΛ.trans HS) (HΛ.trans HY) (HΛ.trans HX)
      (show Λ ≤ σ ∈ᴮ omegaOne from inf_le_left.trans inf_le_right)
      (Hdata.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    exact le_iSup_of_le v (le_inf
      (mem_of_mem_subset simultaneousCandidates_subset (leastIn_mem (Hv.trans inf_le_right)))
      (Hv.trans inf_le_right))
  · intro σ τ v w Δ _ _ _ _ _ Hv Hw Hστ
    exact leastIn_unique_of_eq (simultaneousCandidates_congr_row δ S Y X top Hστ) Hv Hw

theorem exists_simultaneous_row_choices {δ S Y X top : bSet 𝔹} {Γ : 𝔹}
    (Hδ : Γ ≤ δ ∈ᴮ omegaOne) (Htop : Γ ≤ top ∈ᴮ omegaTwo)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hrows : Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J)) :
    ∃ Z : bSet 𝔹, Γ ≤ is_function omegaOne omegaOne Z ⊓ simultaneousRowLaw δ S Y X top Z :=
  ⟨simultaneousChoices δ S Y X top,
    le_inf (simultaneousChoices_is_function Hδ Htop HS HY HX Hrows) simultaneousChoices_law⟩

theorem simultaneousRowLaw_apply {δ S Y X top Z σ v : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ simultaneousRowLaw δ S Y X top Z)
    (Hσ : Γ ≤ σ ∈ᴮ omegaOne) (Hpair : Γ ≤ pair σ v ∈ᴮ Z) :
    Γ ≤ leastIn (simultaneousCandidates δ S Y X top σ) v :=
  (le_inf (Hlaw.trans ((iInf_le _ σ).trans (iInf_le _ v))) (le_inf Hσ Hpair)).trans bv_imp_elim

end bSet.ErdosSimultaneousRowChoice
