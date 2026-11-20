/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRowCandidates

@[expose] public section

/-!
Candidate sets depend on the guarded prefix of the history, not on later
graph support. A functional extension cannot change a prefix on which the
original history is already total. All equalities are local Boolean-valued
equalities, including congruence in the stage and history names.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosRowCandidates

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosCountablePast ErdosIndexedIntersection

/-- Any value of the larger graph at an old, already total coordinate was
already a value of the smaller graph. No support premise on the graphs is
needed outside the guarded domain. -/
theorem prefix_pair_of_extension {δ Y h k j v : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ h ⊆ᴮ k) (Hfunc : Γ ≤ is_func k)
    (Htotal : Γ ≤ is_func' δ Y h) (Hj : Γ ≤ j ∈ᴮ δ)
    (Hjv : Γ ≤ pair j v ∈ᴮ k) : Γ ≤ pair j v ∈ᴮ h := by
  have Hex : Γ ≤ ⨆ u, u ∈ᴮ Y ⊓ pair j u ∈ᴮ h :=
    (le_inf ((Htotal.trans inf_le_right).trans (iInf_le _ j)) Hj).trans bv_imp_elim
  obtain ⟨u, Hu⟩ := exists_convert Hex
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hju : Γ ≤ pair j u ∈ᴮ k :=
    mem_of_mem_subset Hsub (Hu.trans inf_le_right)
  have Hvu : Γ ≤ v =ᴮ u := eq_of_is_func_of_eq Hfunc bv_refl Hjv Hju
  exact bv_rw' (ϕ := fun z => pair j z ∈ᴮ h) Hvu
    (h_congr := B_ext_pair_mem_right) (H_new := Hu.trans inf_le_right)

/-- The actual bounded images of a total prefix agree under a functional
extension. In particular no values from later coordinates enter the image. -/
theorem prefix_image_eq_of_extension {δ Y h k : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ h ⊆ᴮ k) (Hfunc : Γ ≤ is_func k)
    (Htotal : Γ ≤ is_func' δ Y h) :
    Γ ≤ image δ Y h =ᴮ image δ Y k := by
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hmem := mem_image_iff.mp
      (show Γ ⊓ v ∈ᴮ image δ Y h ≤ v ∈ᴮ image δ Y h from inf_le_right)
    obtain ⟨j, Hj⟩ := exists_convert Hmem.2
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_image
      (mem_of_mem_subset (inf_le_left.trans Hsub) (Hj.trans inf_le_right))
      (Hj.trans inf_le_left) Hmem.1
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hmem := mem_image_iff.mp
      (show Γ ⊓ v ∈ᴮ image δ Y k ≤ v ∈ᴮ image δ Y k from inf_le_right)
    obtain ⟨j, Hj⟩ := exists_convert Hmem.2
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_image
      (prefix_pair_of_extension (inf_le_left.trans Hsub) (inf_le_left.trans Hfunc)
        (inf_le_left.trans Htotal) (Hj.trans inf_le_left) (Hj.trans inf_le_right))
      (Hj.trans inf_le_left) Hmem.1

private theorem binary_union_congr_both {A B C D : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A =ᴮ B) (HC : Γ ≤ C =ᴮ D) :
    Γ ≤ binary_union A C =ᴮ binary_union B D := by
  unfold binary_union
  apply B_congr_bv_union
  exact bv_trans (B_congr_insert1_left HA)
    (B_congr_insert1_right (B_congr_insert1_left HC))

private theorem past_congr {A B : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ A =ᴮ B) :
    Γ ≤ past A =ᴮ past B :=
  binary_union_congr_both H (B_congr_bv_union H)

private theorem difference_congr_both {A B C D : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A =ᴮ B) (HC : Γ ≤ C =ᴮ D) :
    Γ ≤ difference A C =ᴮ difference B D := by
  apply mem_ext
  · apply le_iInf
    intro z
    rw [← deduction, mem_difference, mem_difference]
    refine le_inf ?_ ?_
    · exact mem_congr bv_refl (inf_le_left.trans HA) (inf_le_right.trans inf_le_left)
    · exact bv_rw'' (ϕ := fun U => (z ∈ᴮ U)ᶜ) (inf_le_left.trans HC)
        (inf_le_right.trans inf_le_right) (B_ext_neg (h := B_ext_mem_right))
  · apply le_iInf
    intro z
    rw [← deduction, mem_difference, mem_difference]
    refine le_inf ?_ ?_
    · exact mem_congr bv_refl (inf_le_left.trans (bv_symm HA))
        (inf_le_right.trans inf_le_left)
    · exact bv_rw'' (ϕ := fun U => (z ∈ᴮ U)ᶜ) (inf_le_left.trans (bv_symm HC))
        (inf_le_right.trans inf_le_right) (B_ext_neg (h := B_ext_mem_right))

/-- Equality of the bounded prefix images is sufficient; no property of
the section family or seed is required for this congruence. -/
theorem rowCandidates_eq_of_image_eq {δ seed F h k : bSet 𝔹} {Γ : 𝔹}
    (Himage : Γ ≤ image δ omegaOne h =ᴮ image δ omegaOne k) :
    Γ ≤ rowCandidates δ seed F h =ᴮ rowCandidates δ seed F k :=
  difference_congr_both bv_refl
    (binary_union_congr_both bv_refl (past_congr Himage))

theorem rowCandidates_eq_of_extension {δ seed F h k : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ h ⊆ᴮ k) (Hfunc : Γ ≤ is_func k)
    (Htotal : Γ ≤ is_func' δ omegaOne h) :
    Γ ≤ rowCandidates δ seed F h =ᴮ rowCandidates δ seed F k :=
  rowCandidates_eq_of_image_eq (prefix_image_eq_of_extension Hsub Hfunc Htotal)

/-- Congruence under equality of arbitrary history names, without any
functionality or totality premise. -/
theorem rowCandidates_congr_graph (δ seed F : bSet 𝔹) :
    B_congr (rowCandidates δ seed F) := by
  intro h k Γ H
  exact rowCandidates_eq_of_image_eq (B_congr_image_right H)

private theorem indexedIntersection_congr_index (κ F : bSet 𝔹) :
    B_congr (indexedIntersection κ F) := by
  intro δ ε Γ H
  have Hext (z : bSet 𝔹) : B_ext (fun T => ⨅ j, ⨅ A,
      _root_.imp (j ∈ᴮ T ⊓ pair j A ∈ᴮ F) (z ∈ᴮ A)) :=
    B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_const) (h₂ := B_ext_const)))
  apply mem_ext
  · apply le_iInf
    intro z
    rw [← deduction]
    have Hmem := mem_indexedIntersection_iff.mp
      (show Γ ⊓ z ∈ᴮ indexedIntersection κ F δ ≤
        z ∈ᴮ indexedIntersection κ F δ from inf_le_right)
    exact mem_indexedIntersection_iff.mpr ⟨Hmem.1,
      bv_rw'' (ϕ := fun T => ⨅ j, ⨅ A,
        _root_.imp (j ∈ᴮ T ⊓ pair j A ∈ᴮ F) (z ∈ᴮ A))
        (inf_le_left.trans H) Hmem.2 (Hext z)⟩
  · apply le_iInf
    intro z
    rw [← deduction]
    have Hmem := mem_indexedIntersection_iff.mp
      (show Γ ⊓ z ∈ᴮ indexedIntersection κ F ε ≤
        z ∈ᴮ indexedIntersection κ F ε from inf_le_right)
    exact mem_indexedIntersection_iff.mpr ⟨Hmem.1,
      bv_rw'' (ϕ := fun T => ⨅ j, ⨅ A,
        _root_.imp (j ∈ᴮ T ⊓ pair j A ∈ᴮ F) (z ∈ᴮ A))
        (inf_le_left.trans (bv_symm H)) Hmem.2 (Hext z)⟩

/-- Congruence in the guarded stage, including the intersection index and
the bounded history image; it requires no ordinal or graph assumptions. -/
theorem rowCandidates_congr_stage (seed F h : bSet 𝔹) :
    B_congr (fun δ => rowCandidates δ seed F h) := by
  intro δ ε Γ H
  exact difference_congr_both (indexedIntersection_congr_index omegaOne F H)
    (binary_union_congr_both bv_refl (past_congr (B_congr_image_left H)))

end bSet.ErdosRowCandidates
