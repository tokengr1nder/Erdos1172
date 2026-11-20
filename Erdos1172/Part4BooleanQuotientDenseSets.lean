/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanQuotientName

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

end Erdos1172BooleanQuotient
