/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanNameTransport
public import Erdos1172.Part4InternalSubsetRepresentation

@[expose] public section

/-!
# Local recovery of checked-ground subset indicators

The index family can have arbitrary ground cardinality and need not have
separated children. Agreement of the actual membership coefficients at one
Boolean context recovers the entire subset name at precisely that context.
No external enumeration, global branch, or distributivity is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCheckedIndicator

open ErdosNameTransport

variable {B C : Type u}
variable [NontrivialCompleteBooleanAlgebra B]
variable [NontrivialCompleteBooleanAlgebra C]

def checkedIndicator (A : PSet.{u}) (b : A.Type → B) : bSet B :=
  .mk A.Type (fun i => check (A.Func i)) b

theorem checkedIndicator_subset (A : PSet.{u}) (b : A.Type → B) :
    (⊤ : B) ≤ checkedIndicator A b ⊆ᴮ check A := by
  rw [subset_unfold]
  apply le_iInf
  intro i
  rw [← deduction]
  exact check_mem (PSet.func_mem A i)

theorem map_checkedIndicator (e : CompleteLatticeHom B C)
    (A : PSet.{u}) (b : A.Type → B) :
    mapNames e (checkedIndicator A b) = checkedIndicator A (fun i => e (b i)) := by
  simp only [checkedIndicator, mapNames_mk, map_check]

theorem checkedIndicator_membership_eq (A : PSet.{u}) (x : bSet B) :
    checkedIndicator A (fun i => check (A.Func i) ∈ᴮ x) =
      set_of_indicator (u := check A) (fun i => (check A : bSet B).func i ∈ᴮ x) := by
  cases A with
  | mk I a => rfl

theorem checkedIndicator_subset_of_coefficients (A : PSet.{u})
    {b c : A.Type → B} {Γ : B} (H : ∀ i, Γ ⊓ b i ≤ c i) :
    Γ ≤ checkedIndicator A b ⊆ᴮ checkedIndicator A c := by
  rw [subset_unfold]
  apply le_iInf
  intro i
  rw [← deduction, mem_unfold]
  exact le_iSup_of_le i (le_inf (H i) bv_refl)

private theorem agreement_forward {a b Γ : B}
    (H : Γ ≤ (a ⊓ b) ⊔ (aᶜ ⊓ bᶜ)) : Γ ⊓ a ≤ b := by
  rw [deduction]
  change Γ ≤ aᶜ ⊔ b
  exact H.trans (sup_le (inf_le_right.trans le_sup_right)
    (inf_le_left.trans le_sup_left))

private theorem agreement_reverse {a b Γ : B}
    (H : Γ ≤ (a ⊓ b) ⊔ (aᶜ ⊓ bᶜ)) : Γ ⊓ b ≤ a := by
  rw [deduction]
  change Γ ≤ bᶜ ⊔ a
  exact H.trans (sup_le (inf_le_left.trans le_sup_right)
    (inf_le_right.trans le_sup_left))

theorem checkedIndicator_eq_of_binary_agreement (A : PSet.{u})
    {b c : A.Type → B} {Γ : B}
    (H : ∀ i, Γ ≤ (b i ⊓ c i) ⊔ ((b i)ᶜ ⊓ (c i)ᶜ)) :
    Γ ≤ checkedIndicator A b =ᴮ checkedIndicator A c :=
  (le_inf
    (checkedIndicator_subset_of_coefficients A (fun i => agreement_forward (H i)))
    (checkedIndicator_subset_of_coefficients A (fun i => agreement_reverse (H i)))).trans
      (eq_of_subset_subset _ _)

/-- Actual mixed subsets are recovered without shrinking their context. -/
theorem eq_checkedIndicator_of_binary_agreement (A : PSet.{u})
    {x : bSet B} {b : A.Type → B} {Γ : B}
    (Hx : Γ ≤ x ⊆ᴮ check A)
    (H : ∀ i, Γ ≤ ((check (A.Func i) ∈ᴮ x) ⊓ b i) ⊔
      ((check (A.Func i) ∈ᴮ x)ᶜ ⊓ (b i)ᶜ)) :
    Γ ≤ x =ᴮ checkedIndicator A b := by
  have Hrep : Γ ≤ x =ᴮ checkedIndicator A (fun i => check (A.Func i) ∈ᴮ x) := by
    rw [checkedIndicator_membership_eq]
    exact eq_membership_indicator_of_subset Hx
  exact bv_trans Hrep (checkedIndicator_eq_of_binary_agreement A H)

end bSet.ErdosCheckedIndicator
