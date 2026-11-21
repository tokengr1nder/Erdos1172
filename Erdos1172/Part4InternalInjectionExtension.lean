/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Flypitch4.BvmExtras

@[expose] public section

/-!
# One-pair extension of an internal injection

A fresh domain point may be sent to a codomain point outside the old image.
The resulting graph is an actual bounded internal injective function, not
merely a functional relation. All hypotheses hold in the same arbitrary
Boolean context and all points are arbitrary names.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosInjectionExtension

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

private theorem mem_insert1_value {x y z : bSet 𝔹} :
    x ∈ᴮ bSet.insert1 y z = x =ᴮ y ⊔ x ∈ᴮ z :=
  mem_insert1

private theorem insert_cases {p q f : bSet 𝔹} {Γ v : 𝔹}
    (Hp : Γ ≤ p ∈ᴮ bSet.insert1 q f)
    (Hnew : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ p =ᴮ q → Δ ≤ v)
    (Hold : ∀ {Δ : 𝔹}, Δ ≤ Γ → Δ ≤ p ∈ᴮ f → Δ ≤ v) : Γ ≤ v := by
  have Hsplit : Γ ≤ p =ᴮ q ⊔ p ∈ᴮ f := Hp.trans (mem_insert1_value (x := p) (y := q) (z := f)).le
  exact (le_inf le_rfl Hsplit).trans
    (bv_or_elim_right (Hnew inf_le_left inf_le_right) (Hold inf_le_left inf_le_right))

theorem subset_insertPair {a y f : bSet 𝔹} {Γ : 𝔹} : Γ ≤ f ⊆ᴮ bSet.insert1 (pair a y) f := by
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction, mem_insert1_value]
  exact inf_le_right.trans le_sup_right

theorem pair_mem_insertPair {a y f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair a y ∈ᴮ bSet.insert1 (pair a y) f := by
  rw [mem_insert1_value]
  exact bv_refl.trans le_sup_left

private theorem old_domain_conflict {A S f a x z : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function A S f) (Ha : Γ ≤ (a ∈ᴮ A)ᶜ)
    (Hxa : Γ ≤ x =ᴮ a) (Hp : Γ ≤ pair x z ∈ᴮ f) : Γ ≤ ⊥ :=
  bv_absurd _ (mem_congr Hxa bv_refl (mem_domain_of_is_function Hp Hf)) Ha

private theorem old_image_conflict {A S f y x z : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function A S f) (Hy : Γ ≤ (y ∈ᴮ image A S f)ᶜ)
    (Hzy : Γ ≤ z =ᴮ y) (Hp : Γ ≤ pair x z ∈ᴮ f) : Γ ≤ ⊥ :=
  bv_absurd _ (mem_congr Hzy bv_refl
    (mem_image Hp (mem_domain_of_is_function Hp Hf) (mem_codomain_of_is_function Hp Hf))) Hy

private theorem output_eq_of_insertPair {A S f a y x₁ x₂ z₁ z₂ : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function A S f) (Ha : Γ ≤ (a ∈ᴮ A)ᶜ)
    (H₁ : Γ ≤ pair x₁ z₁ ∈ᴮ bSet.insert1 (pair a y) f)
    (H₂ : Γ ≤ pair x₂ z₂ ∈ᴮ bSet.insert1 (pair a y) f)
    (Heq : Γ ≤ x₁ =ᴮ x₂) : Γ ≤ z₁ =ᴮ z₂ := by
  apply insert_cases H₁
  · intro Δ HΔ Hnew₁
    apply insert_cases (HΔ.trans H₂)
    · intro Θ HΘ Hnew₂
      exact bv_trans (HΘ.trans (eq_of_eq_pair_right' Hnew₁)) (bv_symm (eq_of_eq_pair_right' Hnew₂))
    · intro Θ HΘ Hold₂
      have Hxa : Θ ≤ x₂ =ᴮ a :=
        bv_trans (bv_symm ((HΘ.trans HΔ).trans Heq)) (HΘ.trans (eq_of_eq_pair_left' Hnew₁))
      exact (old_domain_conflict ((HΘ.trans HΔ).trans Hf)
        ((HΘ.trans HΔ).trans Ha) Hxa Hold₂).trans bot_le
  · intro Δ HΔ Hold₁
    apply insert_cases (HΔ.trans H₂)
    · intro Θ HΘ Hnew₂
      have Hxa : Θ ≤ x₁ =ᴮ a := bv_trans ((HΘ.trans HΔ).trans Heq) (eq_of_eq_pair_left' Hnew₂)
      exact (old_domain_conflict ((HΘ.trans HΔ).trans Hf)
        ((HΘ.trans HΔ).trans Ha) Hxa (HΘ.trans Hold₁)).trans bot_le
    · intro Θ HΘ Hold₂
      exact eq_of_is_function_of_eq ((HΘ.trans HΔ).trans Hf)
        ((HΘ.trans HΔ).trans Heq) (HΘ.trans Hold₁) Hold₂

theorem is_func_insertPair {A S f a y : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function A S f) (Ha : Γ ≤ (a ∈ᴮ A)ᶜ) :
    Γ ≤ is_func (bSet.insert1 (pair a y) f) := by
  apply le_iInf; intro x₁
  apply le_iInf; intro x₂
  apply le_iInf; intro z₁
  apply le_iInf; intro z₂
  rw [← deduction, ← deduction]
  exact output_eq_of_insertPair (inf_le_left.trans (inf_le_left.trans Hf))
    (inf_le_left.trans (inf_le_left.trans Ha))
    (inf_le_left.trans (inf_le_right.trans inf_le_left))
    (inf_le_left.trans (inf_le_right.trans inf_le_right)) inf_le_right

private theorem input_eq_of_insertPair {A S f a y x₁ x₂ z₁ z₂ : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function A S f) (Hinj : Γ ≤ is_inj f)
    (Hfresh : Γ ≤ (y ∈ᴮ image A S f)ᶜ)
    (H₁ : Γ ≤ pair x₁ z₁ ∈ᴮ bSet.insert1 (pair a y) f)
    (H₂ : Γ ≤ pair x₂ z₂ ∈ᴮ bSet.insert1 (pair a y) f)
    (Heq : Γ ≤ z₁ =ᴮ z₂) : Γ ≤ x₁ =ᴮ x₂ := by
  apply insert_cases H₁
  · intro Δ HΔ Hnew₁
    apply insert_cases (HΔ.trans H₂)
    · intro Θ HΘ Hnew₂
      exact bv_trans (HΘ.trans (eq_of_eq_pair_left' Hnew₁)) (bv_symm (eq_of_eq_pair_left' Hnew₂))
    · intro Θ HΘ Hold₂
      have Hzy : Θ ≤ z₂ =ᴮ y :=
        bv_trans (bv_symm ((HΘ.trans HΔ).trans Heq)) (HΘ.trans (eq_of_eq_pair_right' Hnew₁))
      exact (old_image_conflict ((HΘ.trans HΔ).trans Hf)
        ((HΘ.trans HΔ).trans Hfresh) Hzy Hold₂).trans bot_le
  · intro Δ HΔ Hold₁
    apply insert_cases (HΔ.trans H₂)
    · intro Θ HΘ Hnew₂
      have Hzy : Θ ≤ z₁ =ᴮ y := bv_trans ((HΘ.trans HΔ).trans Heq) (eq_of_eq_pair_right' Hnew₂)
      exact (old_image_conflict ((HΘ.trans HΔ).trans Hf)
        ((HΘ.trans HΔ).trans Hfresh) Hzy (HΘ.trans Hold₁)).trans bot_le
    · intro Θ HΘ Hold₂
      exact eq_of_is_inj_of_eq ((HΘ.trans HΔ).trans Hinj)
        ((HΘ.trans HΔ).trans Heq) (HΘ.trans Hold₁) Hold₂

theorem is_inj_insertPair {A S f a y : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function A S f) (Hinj : Γ ≤ is_inj f)
    (Hfresh : Γ ≤ (y ∈ᴮ image A S f)ᶜ) :
    Γ ≤ is_inj (bSet.insert1 (pair a y) f) := by
  apply le_iInf; intro x₁
  apply le_iInf; intro x₂
  apply le_iInf; intro z₁
  apply le_iInf; intro z₂
  rw [← deduction]
  exact input_eq_of_insertPair (inf_le_left.trans Hf) (inf_le_left.trans Hinj)
    (inf_le_left.trans Hfresh)
    (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_left.trans inf_le_right)) (inf_le_right.trans inf_le_right)

theorem is_total_insertPair {A S f a y : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function A S f) (Hy : Γ ≤ y ∈ᴮ S) :
    Γ ≤ is_total (bSet.insert1 a A) S (bSet.insert1 (pair a y) f) := by
  apply le_iInf
  intro x
  rw [← deduction, mem_insert1_value]
  apply bv_or_elim_right
  · apply le_iSup_of_le y
    refine le_inf (inf_le_left.trans Hy) ?_
    rw [mem_insert1_value]
    exact (pair_congr inf_le_right bv_refl).trans le_sup_left
  · have Htotal : Γ ⊓ x ∈ᴮ A ≤ ⨆ z, z ∈ᴮ S ⊓ pair x z ∈ᴮ f :=
      (le_inf (inf_le_left.trans ((is_total_of_is_function Hf).trans (iInf_le _ x)))
        inf_le_right).trans bv_imp_elim
    apply Htotal.trans
    apply iSup_le
    intro z
    apply le_iSup_of_le z
    refine le_inf inf_le_left ?_
    rw [mem_insert1_value]
    exact inf_le_right.trans le_sup_right

theorem insertPair_subset_prod {A S f a y : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function A S f) (Hy : Γ ≤ y ∈ᴮ S) :
    Γ ≤ bSet.insert1 (pair a y) f ⊆ᴮ prod (bSet.insert1 a A) S := by
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction, mem_insert1_value]
  apply bv_or_elim_right
  · have Ha : Γ ≤ a ∈ᴮ bSet.insert1 a A := by
      rw [mem_insert1_value]
      exact bv_refl.trans le_sup_left
    exact bv_rw' inf_le_right (ϕ := fun w => w ∈ᴮ prod (bSet.insert1 a A) S)
      (h_congr := B_ext_mem_left)
      (H_new := inf_le_left.trans (mem_prod Ha Hy))
  · have Hprod : Γ ⊓ z ∈ᴮ f ≤ z ∈ᴮ prod A S :=
      mem_of_mem_subset (inf_le_left.trans (subset_prod_of_is_function Hf)) inf_le_right
    obtain ⟨x, Hx, w, Hw, Heq⟩ := mem_prod_iff₂.mp Hprod
    have Hx' : Γ ⊓ z ∈ᴮ f ≤ x ∈ᴮ bSet.insert1 a A := by
      rw [mem_insert1_value]
      exact Hx.trans le_sup_right
    exact bv_rw' Heq (ϕ := fun w => w ∈ᴮ prod (bSet.insert1 a A) S)
      (h_congr := B_ext_mem_left) (H_new := mem_prod Hx' Hw)

/-- Adjoin one fresh domain/codomain pair to an actual internal injection. -/
theorem is_injective_function_insertPair {A S f a y : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_injective_function A S f)
    (Ha : Γ ≤ (a ∈ᴮ A)ᶜ) (Hy : Γ ≤ y ∈ᴮ S)
    (Hfresh : Γ ≤ (y ∈ᴮ image A S f)ᶜ) :
    Γ ≤ is_injective_function (bSet.insert1 a A) S (bSet.insert1 (pair a y) f) :=
  le_inf
    (le_inf (le_inf (is_func_insertPair (Hf.trans inf_le_left) Ha)
      (is_total_insertPair (Hf.trans inf_le_left) Hy))
      (insertPair_subset_prod (Hf.trans inf_le_left) Hy))
    (is_inj_insertPair (Hf.trans inf_le_left) (Hf.trans inf_le_right) Hfresh)

end bSet.ErdosInjectionExtension
