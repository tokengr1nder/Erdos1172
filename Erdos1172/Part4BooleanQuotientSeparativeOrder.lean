/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanQuotientName

@[expose] public section

/-! # Compatibility and separative order inside the quotient name

Compatibility asks for a common stronger condition in the named forcing.
A condition is below another in the separative order if it has no stronger
condition incompatible with the other. Both searches range over all names.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
universe u

namespace Erdos1172BooleanQuotient

open bSet Erdos1172BooleanFactor Erdos1172PositiveBoolean

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

def compatibleValue (Q x y : bSet B) : B :=
  ⨆ z : bSet B, z ∈ᴮ Q ⊓ ((x ⊆ᴮ z) ⊓ (y ⊆ᴮ z))

def separativeLeValue (Q x y : bSet B) : B :=
  (⨆ z : bSet B, z ∈ᴮ Q ⊓ ((x ⊆ᴮ z) ⊓ (compatibleValue Q z y)ᶜ))ᶜ

private theorem quotient_exists (e : CompleteLatticeHom B C) (F : bSet B → B) (h : B_ext F) :
    (⨆ x : bSet B, x ∈ᴮ quotientName e ⊓ F x) =
      ⨆ r : Positive C, lowerProjection e r.val ⊓ F (check (upperSetCode r)) :=
  (bounded_exists (v := quotientName e) (h_congr := h)).symm

private theorem projection_bot (e : CompleteLatticeHom B C) : lowerProjection e ⊥ = ⊥ :=
  bot_unique (lowerProjection_le e bot_le)

theorem compatibleValue_checked (e : CompleteLatticeHom B C) (p q : Positive C) :
    compatibleValue (quotientName e) (check (upperSetCode p)) (check (upperSetCode q)) =
      lowerProjection e (p.val ⊓ q.val) := by
  classical
  unfold compatibleValue
  rw [quotient_exists e _ (B_ext_inf B_ext_subset_right B_ext_subset_right)]
  apply le_antisymm
  · apply iSup_le
    intro r
    by_cases hp : r ≤ p
    · by_cases hq : r ≤ q
      · exact inf_le_left.trans (lowerProjection_mono e (le_inf hp hq))
      · rw [check_upperSetCode_subset_eq_bot hq]
        simp
    · rw [check_upperSetCode_subset_eq_bot hp]
      simp
  · by_cases hz : p.val ⊓ q.val = ⊥
    · rw [hz, projection_bot]
      exact bot_le
    · let r : Positive C := ⟨p.val ⊓ q.val, hz⟩
      apply le_iSup_of_le r
      rw [check_upperSetCode_subset_eq_top (show r ≤ p from inf_le_left),
        check_upperSetCode_subset_eq_top (show r ≤ q from inf_le_right)]
      simp [r]

private theorem compatible_ext (Q y : bSet B) : B_ext (fun z => compatibleValue Q z y) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const (B_ext_inf B_ext_subset_left B_ext_const))

/-- An incompatible strengthening exists precisely on the projection of
the Boolean difference. The relative order in the separative quotient is
therefore decided by the complement of that projection. -/
theorem separativeLeValue_checked (e : CompleteLatticeHom B C) (q p : Positive C) :
    separativeLeValue (quotientName e) (check (upperSetCode q)) (check (upperSetCode p)) =
      (lowerProjection e (q.val ⊓ p.valᶜ))ᶜ := by
  classical
  unfold separativeLeValue
  apply congrArg compl
  rw [quotient_exists e _ (B_ext_inf B_ext_subset_right (B_ext_neg (h := compatible_ext _ _)))]
  simp only [compatibleValue_checked]
  apply le_antisymm
  · apply iSup_le
    intro r
    by_cases hr : r ≤ q
    · rw [check_upperSetCode_subset_eq_top hr, top_inf_eq]
      let a := lowerProjection e (r.val ⊓ p.val)
      let b := lowerProjection e (q.val ⊓ p.valᶜ)
      have hr' : lowerProjection e r.val ≤ a ⊔ b := by
        apply lowerProjection_le e
        rw [map_sup]
        calc
          r.val = (r.val ⊓ p.val) ⊔ (r.val ⊓ p.valᶜ) := by
            rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
          _ ≤ e a ⊔ e b := sup_le_sup (le_image_lowerProjection e _)
            ((inf_le_inf_right _ (show r.val ≤ q.val from hr)).trans (le_image_lowerProjection e _))
      change lowerProjection e r.val ⊓ aᶜ ≤ b
      have h := inf_le_inf_right aᶜ hr'
      rw [inf_sup_right, inf_compl_eq_bot, bot_sup_eq] at h
      exact h.trans inf_le_left
    · rw [check_upperSetCode_subset_eq_bot hr]
      simp
  · by_cases hz : q.val ⊓ p.valᶜ = ⊥
    · rw [hz, projection_bot]
      exact bot_le
    · let r : Positive C := ⟨q.val ⊓ p.valᶜ, hz⟩
      have hzero : r.val ⊓ p.val = ⊥ := by
        change (q.val ⊓ p.valᶜ) ⊓ p.val = ⊥
        rw [inf_assoc, compl_inf_eq_bot, inf_bot_eq]
      apply le_iSup_of_le r
      rw [check_upperSetCode_subset_eq_top (show r ≤ q from inf_le_left), hzero, projection_bot]
      simp [r]

end Erdos1172BooleanQuotient
