/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIdealSemantics

@[expose] public section

/-!
Internal pressing down from diagonal closure of an ideal name. All relations,
fibers, and existential witnesses are Boolean-valued names, not ground sets.
The diagonal-closure hypothesis is explicit; no ideal existence is asserted.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIdeal

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

private theorem mem_comprehend_value (ϕ : bSet 𝔹 → 𝔹) (Hϕ : B_ext ϕ)
    (A x : bSet 𝔹) : x ∈ᴮ comprehend ϕ A = (x ∈ᴮ A) ⊓ ϕ x := by
  apply le_antisymm
  · apply ((mem_comprehend_iff₂ ϕ A Hϕ).mp le_rfl).trans
    apply iSup_le
    intro y
    have Heq : y ∈ᴮ A ⊓ (x =ᴮ y ⊓ ϕ y) ≤ x =ᴮ y :=
      inf_le_right.trans inf_le_left
    exact le_inf
      (bv_rw' Heq (h_congr := B_ext_mem_left) (H_new := inf_le_left))
      (bv_rw' Heq (h_congr := Hϕ) (H_new := inf_le_right.trans inf_le_right))
  · apply (mem_comprehend_iff₂ ϕ A Hϕ).mpr
    apply le_iSup_of_le x
    exact le_inf inf_le_left (le_inf bv_refl inf_le_right)

/-- The inverse fiber at `i`, restricted to the underlying set. -/
def fiber (κ R i : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun x => pair x i ∈ᴮ R) κ

theorem mem_fiber (κ R i x : bSet 𝔹) :
    x ∈ᴮ fiber κ R i = (x ∈ᴮ κ) ⊓ (pair x i ∈ᴮ R) :=
  mem_comprehend_value _ B_ext_pair_mem_left _ _

theorem fiber_subset {κ R i : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ fiber κ R i ⊆ᴮ κ :=
  comprehend_subset (ϕ := fun x => pair x i ∈ᴮ R) (Γ := Γ) κ

/-- The diagonal union of the relation's inverse fibers. -/
def diagonalUnion (κ R : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun x => ⨆ i, (i ∈ᴮ κ ⊓ i ∈ᴮ x) ⊓ pair x i ∈ᴮ R) κ

theorem mem_diagonalUnion (κ R x : bSet 𝔹) :
    x ∈ᴮ diagonalUnion κ R =
      (x ∈ᴮ κ) ⊓ ⨆ i, (i ∈ᴮ κ ⊓ i ∈ᴮ x) ⊓ pair x i ∈ᴮ R :=
  mem_comprehend_value _ (B_ext_iSup (h := fun _ =>
    B_ext_inf (B_ext_inf B_ext_const B_ext_mem_right) B_ext_pair_mem_left)) _ _

/-- Every internally indexed family of small inverse fibers has small
diagonal union. The universal quantifier ranges over arbitrary relation names. -/
def diagonalClosure (κ I : bSet 𝔹) : 𝔹 :=
  ⨅ R, _root_.imp
    (⨅ i, _root_.imp (i ∈ᴮ κ) (fiber κ R i ∈ᴮ I))
    (diagonalUnion κ R ∈ᴮ I)

/-- Every point of `S` has a strictly regressive related value in `κ`.
Single-valuedness is unnecessary for the pressing-down implication. -/
def regressiveTotal (κ S R : bSet 𝔹) : 𝔹 :=
  ⨅ x, _root_.imp (x ∈ᴮ S)
    (⨆ i, (i ∈ᴮ κ ⊓ i ∈ᴮ x) ⊓ pair x i ∈ᴮ R)

theorem subset_diagonalUnion_of_regressiveTotal {κ S R : bSet 𝔹} {Γ : 𝔹}
    (HS : Γ ≤ S ⊆ᴮ κ) (HR : Γ ≤ regressiveTotal κ S R) :
    Γ ≤ S ⊆ᴮ diagonalUnion κ R := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, mem_diagonalUnion]
  exact le_inf (mem_of_mem_subset (inf_le_left.trans HS) inf_le_right)
    ((le_inf (inf_le_left.trans (HR.trans (iInf_le _ x))) inf_le_right).trans
      bv_imp_elim)

/-- Boolean-valued pressing down: a regressive relation on a positive set
has a positive inverse fiber. No external choice of a ground ordinal is made. -/
theorem positive_fiber_of_regressiveTotal {κ I S R : bSet 𝔹} {Γ : 𝔹}
    (Hdown : Γ ≤ downwardClosed I) (Hnormal : Γ ≤ diagonalClosure κ I)
    (HS : Γ ≤ positive κ I S) (HR : Γ ≤ regressiveTotal κ S R) :
    Γ ≤ ⨆ i, (i ∈ᴮ κ) ⊓ positive κ I (fiber κ R i) := by
  have Hraw : Γ ≤ ⨆ i, (i ∈ᴮ κ) ⊓ (fiber κ R i ∈ᴮ I)ᶜ := by
    rw [← compl_compl (⨆ i, (i ∈ᴮ κ) ⊓ (fiber κ R i ∈ᴮ I)ᶜ),
      ← imp_bot, ← deduction]
    let Δ := Γ ⊓ (⨆ i, (i ∈ᴮ κ) ⊓ (fiber κ R i ∈ᴮ I)ᶜ)ᶜ
    change Δ ≤ ⊥
    have HΔ : Δ ≤ Γ := inf_le_left
    have Hfibers : Δ ≤ ⨅ i, _root_.imp (i ∈ᴮ κ) (fiber κ R i ∈ᴮ I) := by
      apply le_iInf
      intro i
      have Hi : Δ ≤ ((i ∈ᴮ κ) ⊓ (fiber κ R i ∈ᴮ I)ᶜ)ᶜ :=
        inf_le_right.trans (compl_le_compl (le_iSup
          (fun j => (j ∈ᴮ κ) ⊓ (fiber κ R j ∈ᴮ I)ᶜ) i))
      simpa only [compl_inf, compl_compl, _root_.imp] using Hi
    have Hdiag : Δ ≤ diagonalUnion κ R ∈ᴮ I :=
      (le_inf (HΔ.trans (Hnormal.trans (iInf_le _ R))) Hfibers).trans bv_imp_elim
    have Hsmall : Δ ≤ S ∈ᴮ I :=
      small_of_subset (HΔ.trans Hdown) Hdiag
        (subset_diagonalUnion_of_regressiveTotal
          (HΔ.trans (HS.trans inf_le_left)) (HΔ.trans HR))
    exact bv_absurd _ Hsmall (HΔ.trans (HS.trans inf_le_right))
  apply Hraw.trans
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  exact le_inf inf_le_left (le_inf fiber_subset inf_le_right)

theorem fiber_subset_domain {κ S R i : bSet 𝔹} {Γ : 𝔹}
    (HR : Γ ≤ R ⊆ᴮ prod S κ) : Γ ≤ fiber κ R i ⊆ᴮ S := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  have Hpair : Γ ⊓ x ∈ᴮ fiber κ R i ≤ pair x i ∈ᴮ R := by
    rw [mem_fiber]
    exact inf_le_right.trans inf_le_right
  exact (mem_prod_iff.mp
    (mem_of_mem_subset (inf_le_left.trans HR) Hpair)).1

/-- For a relation supported on `S`, the positive constant fiber lies inside
`S` itself, not merely somewhere in the ambient ordinal. -/
theorem positive_subfiber_of_regressiveTotal {κ I S R : bSet 𝔹} {Γ : 𝔹}
    (Hdown : Γ ≤ downwardClosed I) (Hnormal : Γ ≤ diagonalClosure κ I)
    (HS : Γ ≤ positive κ I S) (HR : Γ ≤ regressiveTotal κ S R)
    (Hsupport : Γ ≤ R ⊆ᴮ prod S κ) :
    Γ ≤ ⨆ i, (i ∈ᴮ κ) ⊓
      (positive κ I (fiber κ R i) ⊓ (fiber κ R i ⊆ᴮ S)) := by
  have H := positive_fiber_of_regressiveTotal Hdown Hnormal HS HR
  apply (le_inf (le_refl Γ) H).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  exact le_inf (inf_le_right.trans inf_le_left)
    (le_inf (inf_le_right.trans inf_le_right)
      (fiber_subset_domain (inf_le_left.trans Hsupport)))

/-- The usual total regressive function supplies the relational hypothesis. -/
theorem regressiveTotal_of_is_function {κ S f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function S κ f)
    (Hreg : Γ ≤ ⨅ x, ⨅ i, _root_.imp (pair x i ∈ᴮ f) (i ∈ᴮ x)) :
    Γ ≤ regressiveTotal κ S f := by
  apply le_iInf
  intro x
  rw [← deduction]
  have Htotal : Γ ⊓ x ∈ᴮ S ≤ ⨆ i, (i ∈ᴮ κ) ⊓ pair x i ∈ᴮ f :=
    (le_inf (inf_le_left.trans
      ((Hf.trans (inf_le_left.trans inf_le_right)).trans (iInf_le _ x)))
      inf_le_right).trans bv_imp_elim
  obtain ⟨i, Hi⟩ := exists_convert Htotal
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  apply le_iSup_of_le i
  refine le_inf (le_inf (Hi.trans inf_le_left) ?_) (Hi.trans inf_le_right)
  exact (le_inf
    (inf_le_left.trans (Hreg.trans ((iInf_le _ x).trans (iInf_le _ i))))
    (Hi.trans inf_le_right)).trans bv_imp_elim

/-- An actual internal function which is regressive on a positive domain
has a positive constant fiber contained in that domain. -/
theorem positive_subfiber_of_regressiveFunction {κ I S f : bSet 𝔹} {Γ : 𝔹}
    (Hdown : Γ ≤ downwardClosed I) (Hnormal : Γ ≤ diagonalClosure κ I)
    (HS : Γ ≤ positive κ I S) (Hf : Γ ≤ is_function S κ f)
    (Hreg : Γ ≤ ⨅ x, ⨅ i, _root_.imp (pair x i ∈ᴮ f) (i ∈ᴮ x)) :
    Γ ≤ ⨆ i, (i ∈ᴮ κ) ⊓
      (positive κ I (fiber κ f i) ⊓ (fiber κ f i ⊆ᴮ S)) :=
  positive_subfiber_of_regressiveTotal Hdown Hnormal HS
    (regressiveTotal_of_is_function Hf Hreg) (Hf.trans inf_le_right)

end bSet.ErdosIdeal
