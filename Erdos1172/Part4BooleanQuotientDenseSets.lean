/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanQuotientSeparativeOrder

@[expose] public section

/-! # Dense predicates on the quotient forcing

Density is evaluated below arbitrary members of the forcing name. For an
extensional predicate this Boolean value can be computed at checked labels.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
universe u

namespace Erdos1172BooleanQuotient

open bSet Erdos1172BooleanFactor Erdos1172PositiveBoolean

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

def denseValue (Q : bSet B) (W : bSet B → B) : B :=
  ⨅ x : bSet B, _root_.imp (x ∈ᴮ Q) (⨆ y : bSet B, y ∈ᴮ Q ⊓ ((x ⊆ᴮ y) ⊓ W y))

def separativelyOpen (Q U : bSet B) : B :=
  ⨅ x : bSet B, ⨅ y : bSet B,
    _root_.imp (((x ∈ᴮ Q ⊓ x ∈ᴮ U) ⊓ y ∈ᴮ Q) ⊓ separativeLeValue Q y x) (y ∈ᴮ U)

theorem checkedLabel_mem (e : CompleteLatticeHom B C) (p : Positive C) :
    (check (upperSetCode p) ∈ᴮ quotientName e) = lowerProjection e p.val := by
  apply le_antisymm _ (mem_mk' (quotientName e) p)
  have h : (check (upperSetCode p) ∈ᴮ quotientName e) ≤
      compatibleValue (quotientName e) (check (upperSetCode p)) (check (upperSetCode p)) :=
    le_iSup_of_le (check (upperSetCode p)) (le_inf le_rfl (le_inf subset_self subset_self))
  rw [compatibleValue_checked, inf_idem] at h
  exact h

private theorem below_label (e : CompleteLatticeHom B C) (W : bSet B → B) (hW : B_ext W)
    (p : Positive C) :
    (⨆ y : bSet B, y ∈ᴮ quotientName e ⊓ ((check (upperSetCode p) ⊆ᴮ y) ⊓ W y)) =
      ⨆ q : {q : Positive C // q ≤ p}, lowerProjection e q.val.val ⊓ W (check (upperSetCode q.val)) := by
  classical
  rw [← bounded_exists (h_congr := B_ext_inf B_ext_subset_right hW)]
  change (⨆ q : Positive C, lowerProjection e q.val ⊓
    (((check (upperSetCode p) : bSet B) ⊆ᴮ check (upperSetCode q)) ⊓ W (check (upperSetCode q)))) = _
  apply le_antisymm
  · apply iSup_le
    intro q
    by_cases h : q ≤ p
    · rw [check_upperSetCode_subset_eq_top h, top_inf_eq]
      exact le_iSup_of_le (⟨q, h⟩ : {q : Positive C // q ≤ p}) le_rfl
    · rw [check_upperSetCode_subset_eq_bot h]
      simp
  · apply iSup_le
    intro q
    apply le_iSup_of_le q.val
    rw [check_upperSetCode_subset_eq_top q.property, top_inf_eq]

theorem denseValue_iff (e : CompleteLatticeHom B C) (W : bSet B → B) (hW : B_ext W) (Γ : B) :
    Γ ≤ denseValue (quotientName e) W ↔ ∀ p : Positive C, Γ ⊓ lowerProjection e p.val ≤
      ⨆ q : {q : Positive C // q ≤ p}, lowerProjection e q.val.val ⊓ W (check (upperSetCode q.val)) := by
  unfold denseValue
  rw [← bounded_forall (h_congr := B_ext_iSup (h := fun _ =>
    B_ext_inf B_ext_const (B_ext_inf B_ext_subset_left B_ext_const)))]
  change (Γ ≤ ⨅ p : Positive C, _root_.imp (lowerProjection e p.val)
    (⨆ y : bSet B, y ∈ᴮ quotientName e ⊓ ((check (upperSetCode p) ⊆ᴮ y) ⊓ W y))) ↔ _
  rw [le_iInf_iff]
  apply forall_congr'
  intro p
  rw [← deduction, below_label e W hW p]

theorem open_checked (e : CompleteLatticeHom B C) (U : bSet B) (Γ : B)
    (hU : Γ ≤ separativelyOpen (quotientName e) U) (p q : Positive C) :
    Γ ⊓ (((lowerProjection e p.val ⊓ check (upperSetCode p) ∈ᴮ U) ⊓ lowerProjection e q.val) ⊓
      (lowerProjection e (q.val ⊓ p.valᶜ))ᶜ) ≤ check (upperSetCode q) ∈ᴮ U := by
  have h := hU.trans ((iInf_le _ (check (upperSetCode p))).trans (iInf_le _ (check (upperSetCode q))))
  rw [← deduction, checkedLabel_mem, checkedLabel_mem, separativeLeValue_checked] at h
  exact h

end Erdos1172BooleanQuotient
