/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaTwo

@[expose] public section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosHartogs

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- The exact semantic predicate realized by the first-order Hartogs formula. -/
def hartogsProperty (κ α : bSet 𝔹) : 𝔹 :=
  Ord α ⊓ ((injects_into α κ)ᶜ ⊓
    ⨅ γ, _root_.imp (γ ∈ᴮ α) (injects_into γ κ))

theorem B_ext_hartogsProperty_base {α : bSet 𝔹} :
    B_ext (fun κ => hartogsProperty κ α) :=
  B_ext_inf B_ext_const (B_ext_inf (B_ext_neg (h := B_ext_injects_into_right))
    (B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_injects_into_right))))

/-- The first-order specification determines the concrete name uniquely
under the same Boolean condition. No checked-ground-name premise is used. -/
theorem hartogsProperty_unique {κ α : bSet 𝔹} {Γ : 𝔹}
    (Hone : (⊤ : 𝔹) ≤ injects_into (1 : bSet 𝔹) κ)
    (H : Γ ≤ hartogsProperty κ α) : Γ ≤ α =ᴮ hartogs (κ := κ) := by
  have Hord : Γ ≤ Ord α := H.trans inf_le_left
  have Hnot : Γ ≤ (injects_into α κ)ᶜ := H.trans (inf_le_right.trans inf_le_left)
  have Hmin : Γ ≤ hartogs (κ := κ) ⊆ᴮ α := by
    have Hspec : Γ ≤ leastNoninjectingOrdinal κ (hartogs (κ := κ)) := hartogs_spec Hone
    have Hall := (Hspec.trans (inf_le_right.trans inf_le_right)).trans (iInf_le _ α)
    exact (le_inf ((le_inf Hall Hord).trans bv_imp_elim) Hnot).trans bv_imp_elim
  have Hsub : Γ ≤ α ⊆ᴮ hartogs (κ := κ) := by
    rw [subset_unfold']
    apply le_iInf
    intro γ
    rw [← deduction]
    have Hsmall : Γ ⊓ γ ∈ᴮ α ≤ injects_into γ κ := by
      have Hall := (H.trans (inf_le_right.trans inf_le_right)).trans (iInf_le _ γ)
      exact (le_inf (inf_le_left.trans Hall) inf_le_right).trans bv_imp_elim
    apply (mem_hartogs_iff Hone (Ord_of_mem_Ord inf_le_right (inf_le_left.trans Hord))).mpr
    exact injection_into_of_injects_into Hsmall
  exact (le_inf Hsub Hmin).trans (eq_of_subset_subset α (hartogs (κ := κ)))

end bSet.ErdosHartogs

namespace bSet.ErdosOmegaTwo

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem omegaOne_property {Γ : 𝔹} :
    Γ ≤ ErdosHartogs.hartogsProperty bSet.omega (omegaOne : bSet 𝔹) := by
  refine le_inf omegaOne_Ord (le_inf omegaOne_not_injects ?_)
  apply le_iInf
  intro γ
  rw [← deduction]
  exact omegaOne_member_injects inf_le_right

theorem omegaTwo_property {Γ : 𝔹} :
    Γ ≤ ErdosHartogs.hartogsProperty omegaOne (omegaTwo : bSet 𝔹) := by
  refine le_inf omegaTwo_Ord (le_inf omegaTwo_not_injects ?_)
  apply le_iInf
  intro γ
  rw [← deduction]
  exact omegaTwo_member_injects inf_le_right

theorem omegaOne_property_unique {α : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ ErdosHartogs.hartogsProperty bSet.omega α) : Γ ≤ α =ᴮ omegaOne :=
  ErdosHartogs.hartogsProperty_unique one_injects_omega H

theorem omegaTwo_property_unique {α δ : bSet 𝔹} {Γ : 𝔹}
    (Hα : Γ ≤ ErdosHartogs.hartogsProperty bSet.omega α)
    (Hδ : Γ ≤ ErdosHartogs.hartogsProperty α δ) : Γ ≤ δ =ᴮ omegaTwo := by
  have Hbase : Γ ≤ α =ᴮ omegaOne := omegaOne_property_unique Hα
  have Hnormalized : Γ ≤ ErdosHartogs.hartogsProperty omegaOne δ :=
    bv_rw'' (ϕ := fun κ => ErdosHartogs.hartogsProperty κ δ) Hbase Hδ
      ErdosHartogs.B_ext_hartogsProperty_base
  exact ErdosHartogs.hartogsProperty_unique one_injects_omegaOne Hnormalized

end bSet.ErdosOmegaTwo
