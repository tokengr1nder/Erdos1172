/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingPartitions

@[expose] public section

/-! # The Boolean completion of a single regular collapse stage -/

set_option autoImplicit false
noncomputable section
universe u
open bSet Lattice Cardinal Erdos1172PositiveBoolean Erdos1172PosetCompletion
open scoped Flypitch
namespace Erdos1172LevyCollapse.Matching

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- Extract a collapse matrix from an ordinary Boolean-valued surjection,
including all its mixed inputs and outputs. -/
def matrixOfSurjection (A : PSet.{u}) (sep : ∀ i j : A.Type, i ≠ j → ¬PSet.Equiv (A.Func i) (A.Func j))
    (f : bSet B) (hf : (⊤ : B) ≤ is_function omega (check A) f) (hs : (⊤ : B) ≤ is_surj omega (check A) f) :
    CollapseMatrix A.Type B where
  value n j := pair (of_nat n) (check (A.Func j)) ∈ᴮ f
  row n := by
    apply top_unique
    have ht := is_total_of_is_function hf
    have h : (⊤ : B) ≤ ⨆ y : bSet B, y ∈ᴮ check A ⊓ pair (of_nat n) y ∈ᴮ f :=
      (le_inf (ht.trans (iInf_le _ (of_nat n))) of_nat_mem_omega).trans bv_imp_elim
    rw [← @bounded_exists B _ (check A) (fun y => pair (of_nat n) y ∈ᴮ f) (h_congr := B_ext_pair_mem_right)] at h
    cases A
    exact h.trans (iSup_mono (fun _ => inf_le_right))
  disjoint n i j hij := bot_unique ((eq_of_is_function_of_eq (le_top.trans hf) bv_refl
    (show (pair (of_nat n) (check (A.Func i)) ∈ᴮ f) ⊓ (pair (of_nat n) (check (A.Func j)) ∈ᴮ f) ≤ _
      from inf_le_left) inf_le_right).trans_eq (check_bv_eq_bot_of_not_equiv (sep i j hij)))
  onto j := by
    apply top_unique
    have h : (⊤ : B) ≤ ⨆ x : bSet B, x ∈ᴮ omega ⊓ pair x (check (A.Func j)) ∈ᴮ f :=
      (le_inf (hs.trans (iInf_le _ (check (A.Func j)))) mem_check_of_mem).trans bv_imp_elim
    rw [← @bounded_exists B _ omega (fun x => pair x (check (A.Func j)) ∈ᴮ f) (h_congr := B_ext_pair_mem_left)] at h
    exact h.trans (iSup_le (fun n => inf_le_right.trans
      (le_iSup (fun k : ℕ => pair (of_nat k) (check (A.Func j)) ∈ᴮ f) n.down)))

end Erdos1172LevyCollapse.Matching
