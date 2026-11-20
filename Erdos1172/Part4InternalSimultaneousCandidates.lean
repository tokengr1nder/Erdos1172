/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRowCandidates
public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-!
# Exact simultaneous row candidates

The constraints are read directly from the section and history graphs.
All earlier stages constrain every row, even before that row is active in
the vertex-selection triangle. No externally chosen family of names is used.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousCandidates

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph

def rowRequirements (δ S Y X top σ v : bSet 𝔹) : 𝔹 :=
  (⨅ A, _root_.imp (pair (pair σ top) A ∈ᴮ S) (v ∈ᴮ A)) ⊓
    ((⨅ j, ⨅ y, ⨅ A, _root_.imp
      (j ∈ᴮ δ ⊓ (pair j y ∈ᴮ Y ⊓ pair (pair σ y) A ∈ᴮ S)) (v ∈ᴮ A)) ⊓
    (⨅ j, ⨅ w, _root_.imp (j ∈ᴮ δ ⊓ pair (pair j σ) w ∈ᴮ X) (w ∈ᴮ v)))

theorem rowRequirements_ext_value (δ S Y X top σ : bSet 𝔹) :
    B_ext (rowRequirements δ S Y X top σ) :=
  B_ext_inf
    (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_mem_left)))
    (B_ext_inf
      (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf
        (h := fun _ => B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_mem_left)))))
      (B_ext_iInf (h := fun _ => B_ext_iInf
        (h := fun _ => B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_mem_right)))))

theorem rowRequirements_ext_row (δ S Y X top v : bSet 𝔹) :
    B_ext (fun σ => rowRequirements δ S Y X top σ v) :=
  B_ext_inf
    (B_ext_iInf (h := fun _ => B_ext_imp
      (h₁ := B_ext_pair_left B_ext_pair_mem_left) (h₂ := B_ext_const)))
    (B_ext_inf
      (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf
        (h := fun _ => B_ext_imp
          (h₁ := B_ext_inf B_ext_const (B_ext_inf B_ext_const
            (B_ext_pair_left B_ext_pair_mem_left))) (h₂ := B_ext_const)))))
      (B_ext_iInf (h := fun _ => B_ext_iInf
        (h := fun _ => B_ext_imp
          (h₁ := B_ext_inf B_ext_const (B_ext_pair_right B_ext_pair_mem_left))
          (h₂ := B_ext_const)))))

def simultaneousCandidates (δ S Y X top σ : bSet 𝔹) : bSet 𝔹 :=
  comprehend (rowRequirements δ S Y X top σ) omegaOne

theorem mem_simultaneousCandidates_iff {δ S Y X top σ v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ v ∈ᴮ simultaneousCandidates δ S Y X top σ ↔
      Γ ≤ v ∈ᴮ omegaOne ∧ Γ ≤ rowRequirements δ S Y X top σ v :=
  mem_comprehend_and (rowRequirements_ext_value δ S Y X top σ)

theorem simultaneousCandidates_subset {δ S Y X top σ : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ simultaneousCandidates δ S Y X top σ ⊆ᴮ omegaOne :=
  comprehend_subset (ϕ := rowRequirements δ S Y X top σ) omegaOne

theorem simultaneousCandidates_congr_row (δ S Y X top : bSet 𝔹) :
    B_congr (simultaneousCandidates δ S Y X top) := by
  intro σ τ Γ H
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_simultaneousCandidates_iff.mp
      (show Γ ⊓ v ∈ᴮ simultaneousCandidates δ S Y X top σ ≤
        v ∈ᴮ simultaneousCandidates δ S Y X top σ from inf_le_right)
    exact mem_simultaneousCandidates_iff.mpr ⟨Hv.1,
      bv_rw'' (ϕ := fun r => rowRequirements δ S Y X top r v)
        (inf_le_left.trans H) Hv.2 (rowRequirements_ext_row δ S Y X top v)⟩
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_simultaneousCandidates_iff.mp
      (show Γ ⊓ v ∈ᴮ simultaneousCandidates δ S Y X top τ ≤
        v ∈ᴮ simultaneousCandidates δ S Y X top τ from inf_le_right)
    exact mem_simultaneousCandidates_iff.mpr ⟨Hv.1,
      bv_rw' (ϕ := fun r => rowRequirements δ S Y X top r v)
        (inf_le_left.trans H) (h_congr := rowRequirements_ext_row δ S Y X top v)
        (H_new := Hv.2)⟩

theorem simultaneousCandidate_mem_seed {δ S Y X top σ v A : bSet 𝔹} {Γ : 𝔹}
    (Hv : Γ ≤ v ∈ᴮ simultaneousCandidates δ S Y X top σ)
    (HA : Γ ≤ pair (pair σ top) A ∈ᴮ S) : Γ ≤ v ∈ᴮ A :=
  (le_inf (((mem_simultaneousCandidates_iff.mp Hv).2.trans inf_le_left).trans
    (iInf_le _ A)) HA).trans bv_imp_elim

theorem simultaneousCandidate_mem_previous_section
    {δ S Y X top σ v j y A : bSet 𝔹} {Γ : 𝔹}
    (Hv : Γ ≤ v ∈ᴮ simultaneousCandidates δ S Y X top σ)
    (Hj : Γ ≤ j ∈ᴮ δ) (Hjy : Γ ≤ pair j y ∈ᴮ Y)
    (HA : Γ ≤ pair (pair σ y) A ∈ᴮ S) : Γ ≤ v ∈ᴮ A :=
  (le_inf (((mem_simultaneousCandidates_iff.mp Hv).2.trans
    (inf_le_right.trans inf_le_left)).trans
    ((iInf_le _ j).trans ((iInf_le _ y).trans (iInf_le _ A))))
    (le_inf Hj (le_inf Hjy HA))).trans bv_imp_elim

theorem simultaneousCandidate_above_previous
    {δ S Y X top σ v j w : bSet 𝔹} {Γ : 𝔹}
    (Hv : Γ ≤ v ∈ᴮ simultaneousCandidates δ S Y X top σ)
    (Hj : Γ ≤ j ∈ᴮ δ) (Hw : Γ ≤ pair (pair j σ) w ∈ᴮ X) : Γ ≤ w ∈ᴮ v :=
  (le_inf (((mem_simultaneousCandidates_iff.mp Hv).2.trans
    (inf_le_right.trans inf_le_right)).trans ((iInf_le _ j).trans (iInf_le _ w)))
    (le_inf Hj Hw)).trans bv_imp_elim

end bSet.ErdosSimultaneousCandidates
