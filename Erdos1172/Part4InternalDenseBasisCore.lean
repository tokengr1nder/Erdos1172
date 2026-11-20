/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSmallFiberBound
public import Erdos1172.Part4InternalIdealLossFamily

@[expose] public section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosDenseBasis

open ErdosIdeal

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def positiveValues (κ J D F : bSet 𝔹) : 𝔹 :=
  ⨅ x, ⨅ A, _root_.imp ((x ∈ᴮ D) ⊓ pair x A ∈ᴮ F) (positive κ J A)

def denseValues (κ J I B : bSet 𝔹) : 𝔹 :=
  ⨅ A, _root_.imp (positive κ J A)
    (⨆ i, ⨆ A0, ((i ∈ᴮ I) ⊓ pair i A0 ∈ᴮ B) ⊓ difference A0 A ∈ᴮ J)

def commonLoss (J F U A0 : bSet 𝔹) : 𝔹 :=
  ⨅ x, ⨅ A, _root_.imp ((x ∈ᴮ U) ⊓ pair x A ∈ᴮ F) (difference A0 A ∈ᴮ J)

theorem positiveValues_apply {κ J D F x A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ positiveValues κ J D F)
    (Hx : Γ ≤ x ∈ᴮ D) (HA : Γ ≤ pair x A ∈ᴮ F) : Γ ≤ positive κ J A :=
  (le_inf (H.trans ((iInf_le _ x).trans (iInf_le _ A))) (le_inf Hx HA)).trans
    bv_imp_elim

theorem commonLoss_apply {J F U A0 x A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ commonLoss J F U A0)
    (Hx : Γ ≤ x ∈ᴮ U) (HA : Γ ≤ pair x A ∈ᴮ F) : Γ ≤ difference A0 A ∈ᴮ J :=
  (le_inf (H.trans ((iInf_le _ x).trans (iInf_le _ A))) (le_inf Hx HA)).trans
    bv_imp_elim

theorem difference_congr_left {A B C : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ A =ᴮ B) : Γ ≤ difference A C =ᴮ difference B C :=
  B_congr_comprehend (ϕ := fun z => (z ∈ᴮ C)ᶜ)
    (H_congr := B_ext_neg (h := B_ext_mem_left)) H

/-- A basis label works when its actual value has small loss from the
actual value at the original family index. -/
def basisChoice (J F B x i : bSet 𝔹) : 𝔹 :=
  ⨆ A, ⨆ A0, ((pair x A ∈ᴮ F) ⊓ pair i A0 ∈ᴮ B) ⊓ difference A0 A ∈ᴮ J

theorem basisChoice_ext_left (J F B i : bSet 𝔹) :
    B_ext (fun x => basisChoice J F B x i) := by
  unfold basisChoice
  exact B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_inf (B_ext_inf B_ext_pair_mem_left B_ext_const) B_ext_const))

theorem basisChoice_ext_right (J F B x : bSet 𝔹) :
    B_ext (basisChoice J F B x) := by
  unfold basisChoice
  exact B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
    B_ext_inf (B_ext_inf B_ext_const B_ext_pair_mem_left) B_ext_const))

/-- Function equality transports the selected loss to any actual pair of values. -/
theorem loss_of_basisChoice {κ J S I F B x i A A0 : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function S (bv_powerset κ) F)
    (HB : Γ ≤ is_function I (bv_powerset κ) B)
    (Hchoice : Γ ≤ basisChoice J F B x i)
    (HA : Γ ≤ pair x A ∈ᴮ F) (HA0 : Γ ≤ pair i A0 ∈ᴮ B) :
    Γ ≤ difference A0 A ∈ᴮ J := by
  apply (le_inf (le_refl Γ) Hchoice).trans
  unfold basisChoice
  rw [inf_iSup_eq]
  apply iSup_le; intro A'
  rw [inf_iSup_eq]
  apply iSup_le; intro A0'
  have HeqA : Γ ⊓ ((pair x A' ∈ᴮ F ⊓ pair i A0' ∈ᴮ B) ⊓
      difference A0' A' ∈ᴮ J) ≤ A' =ᴮ A :=
    eq_of_is_function_of_eq (inf_le_left.trans HF) bv_refl
      (inf_le_right.trans (inf_le_left.trans inf_le_left)) (inf_le_left.trans HA)
  have HeqA0 : Γ ⊓ ((pair x A' ∈ᴮ F ⊓ pair i A0' ∈ᴮ B) ⊓
      difference A0' A' ∈ᴮ J) ≤ A0' =ᴮ A0 :=
    eq_of_is_function_of_eq (inf_le_left.trans HB) bv_refl
      (inf_le_right.trans (inf_le_left.trans inf_le_right)) (inf_le_left.trans HA0)
  exact mem_congr
    (bv_trans (difference_congr_left HeqA0) (difference_congr_right HeqA))
    bv_refl (inf_le_right.trans inf_le_right)

/-- Density supplies pointwise basis labels; internal bounded choice constructs
one coherent selector on the original indexed domain. -/
theorem exists_basis_selector {κ J S I F B : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function S (bv_powerset κ) F)
    (HFpos : Γ ≤ positiveValues κ J S F)
    (Hdense : Γ ≤ denseValues κ J I B) :
    ∃ g : bSet 𝔹, Γ ≤ is_function S I g ⊓
      ⨅ x, ⨅ i, _root_.imp ((x ∈ᴮ S) ⊓ pair x i ∈ᴮ g)
        (basisChoice J F B x i) := by
  apply ErdosSmallFiberBound.exists_selector_of_pointwise
    (basisChoice_ext_left J F B) (basisChoice_ext_right J F B)
  apply le_iInf; intro x; rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ S
  have Hvalue : Δ ≤ ⨆ A, (A ∈ᴮ bv_powerset κ) ⊓ pair x A ∈ᴮ F :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function HF).trans (iInf_le _ x)))
      inf_le_right).trans bv_imp_elim
  obtain ⟨A, HA⟩ := exists_convert Hvalue
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hpositive : Δ ≤ positive κ J A :=
    positiveValues_apply (inf_le_left.trans HFpos) inf_le_right (HA.trans inf_le_right)
  have Hindex : Δ ≤ ⨆ i, ⨆ A0,
      ((i ∈ᴮ I) ⊓ pair i A0 ∈ᴮ B) ⊓ difference A0 A ∈ᴮ J :=
    (le_inf (inf_le_left.trans (Hdense.trans (iInf_le _ A))) Hpositive).trans bv_imp_elim
  apply (le_inf (le_refl Δ) Hindex).trans
  rw [inf_iSup_eq]
  apply iSup_le; intro i
  rw [inf_iSup_eq]
  apply iSup_le; intro A0
  apply le_iSup_of_le i
  refine le_inf (inf_le_right.trans (inf_le_left.trans inf_le_left)) ?_
  apply le_iSup_of_le A
  apply le_iSup_of_le A0
  exact le_inf
    (le_inf (inf_le_left.trans (HA.trans inf_le_right))
      (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    (inf_le_right.trans inf_le_right)

end bSet.ErdosDenseBasis
