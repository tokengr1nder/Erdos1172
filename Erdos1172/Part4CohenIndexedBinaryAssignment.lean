/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCohenFreshAssignment
public import Erdos1172.Part4CohenBinaryAssignment

@[expose] public section

/-!
# Whole checked-index binary assignments

A separated ground set supports a concrete function graph whose value at
each checked child is the binary mixed name for the supplied Boolean
coefficient. The graph is supported and total on the entire checked set,
including arbitrary mixed members. No enumeration or external countability
of its index type is assumed.

When that checked domain is internally countable and fresh for an existing
Cohen condition, the proved fresh-domain union construction gives one actual
extension realizing every coefficient at the original Boolean condition.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCohen

open ErdosPartialInjection ErdosIdeal

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

theorem indexedBinaryValues_congr (C : PSet.{u}) (b : C.Type → B)
    (Hsep : ∀ i j : C.Type, i ≠ j → ¬ PSet.Equiv (C.Func i) (C.Func j))
    (i j : (check C : bSet B).type) :
    (check C : bSet B).func i =ᴮ (check C : bSet B).func j ≤
      binaryAssignmentName (b (check_cast i)) =ᴮ
        binaryAssignmentName (b (check_cast j)) := by
  classical
  rw [check_func, check_func]
  by_cases hij : check_cast i = check_cast j
  · rw [hij]
    exact bv_refl
  · rw [check_bv_eq_bot_of_not_equiv (Hsep (check_cast i) (check_cast j) hij)]
    exact bot_le

/-- The complete graph of the binary mixed values, on the original whole
checked index set rather than on an enumeration of its members. -/
def indexedBinaryAssignment (C : PSet.{u}) (b : C.Type → B)
    (Hsep : ∀ i j : C.Type, i ≠ j → ¬ PSet.Equiv (C.Func i) (C.Func j)) :
    bSet B :=
  functionMk (u := check C) (fun i => binaryAssignmentName (b (check_cast i)))
    (indexedBinaryValues_congr C b Hsep)

theorem indexedBinaryAssignment_pair (C : PSet.{u}) (b : C.Type → B)
    (Hsep : ∀ i j : C.Type, i ≠ j → ¬ PSet.Equiv (C.Func i) (C.Func j))
    (i : C.Type) :
    (⊤ : B) ≤ pair (check (C.Func i)) (binaryAssignmentName (b i)) ∈ᴮ
      indexedBinaryAssignment C b Hsep := by
  unfold indexedBinaryAssignment
  simpa only [check_bval_top, check_func, check_cast, check_cast_symm,
    cast_cast, cast_eq] using
    (functionMk_self (u := (check C : bSet B))
      (F := fun j => binaryAssignmentName (b (check_cast j)))
      (h_congr := indexedBinaryValues_congr C b Hsep) (i := check_cast_symm i))

/-- Totality distributes the checked membership join, so it includes every
mixed member of the domain at top. -/
theorem indexedBinaryAssignment_is_function (C : PSet.{u}) (b : C.Type → B)
    (Hsep : ∀ i j : C.Type, i ≠ j → ¬ PSet.Equiv (C.Func i) (C.Func j)) :
    (⊤ : B) ≤ is_function (check C) two (indexedBinaryAssignment C b Hsep) := by
  unfold indexedBinaryAssignment
  refine le_inf (le_inf (functionMk_is_func _ _) ?_) ?_
  · apply le_iInf
    intro x
    rw [← deduction, mem_unfold]
    simp only [check_bval_top, top_inf_eq, check_func]
    apply iSup_le
    intro i
    apply le_iSup_of_le (binaryAssignmentName (b (check_cast i)))
    refine le_inf (le_top.trans (binaryAssignmentName_mem_two (b (check_cast i)))) ?_
    exact mem_congr (pair_congr (bv_symm le_rfl) bv_refl) bv_refl
      (le_top.trans (indexedBinaryAssignment_pair C b Hsep (check_cast i)))
  · rw [subset_unfold]
    apply le_iInf
    intro i
    change (check C : bSet B).type at i
    change (⊤ : B) ≤ _root_.imp ((check C : bSet B).bval i)
      (pair ((check C : bSet B).func i) (binaryAssignmentName (b (check_cast i))) ∈ᴮ
        prod (check C) two)
    rw [check_bval_top, top_imp, check_func]
    exact mem_prod (check_mem (PSet.func_mem C (check_cast i)))
      (binaryAssignmentName_mem_two (b (check_cast i)))

theorem indexedBinaryAssignment_one (C : PSet.{u}) (b : C.Type → B)
    (Hsep : ∀ i j : C.Type, i ≠ j → ¬ PSet.Equiv (C.Func i) (C.Func j))
    (i : C.Type) :
    b i ≤ pair (check (C.Func i)) (1 : bSet B) ∈ᴮ
      indexedBinaryAssignment C b Hsep :=
  mem_congr (pair_congr bv_refl (binaryAssignmentName_eq_one (b i))) bv_refl
    (le_top.trans (indexedBinaryAssignment_pair C b Hsep i))

theorem indexedBinaryAssignment_zero (C : PSet.{u}) (b : C.Type → B)
    (Hsep : ∀ i j : C.Type, i ≠ j → ¬ PSet.Equiv (C.Func i) (C.Func j))
    (i : C.Type) :
    (b i)ᶜ ≤ pair (check (C.Func i)) (0 : bSet B) ∈ᴮ
      indexedBinaryAssignment C b Hsep :=
  mem_congr (pair_congr bv_refl (binaryAssignmentName_eq_zero (b i))) bv_refl
    (le_top.trans (indexedBinaryAssignment_pair C b Hsep i))

/-- One same-condition extension realizes the entire checked-index binary
assignment. Internal countability is the only size assumption on check C. -/
theorem exists_indexed_binary_assignment (C : PSet.{u}) (b : C.Type → B)
    (Hsep : ∀ i j : C.Type, i ≠ j → ¬ PSet.Equiv (C.Func i) (C.Func j))
    {K p : bSet B} {Γ : B}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hp : Γ ≤ condition K p) (HC : Γ ≤ check C ⊆ᴮ K)
    (Hcount : Γ ≤ injects_into (check C) omega)
    (Hfresh : ∀ i : C.Type, Γ ≤ (check (C.Func i) ∈ᴮ graphDomain K two p)ᶜ) :
    ∃ q : bSet B, Γ ≤ condition K q ∧ Γ ≤ p ⊆ᴮ q ∧
      ∀ i : C.Type, (Γ ⊓ b i ≤ pair (check (C.Func i)) (1 : bSet B) ∈ᴮ q) ∧
        (Γ ⊓ (b i)ᶜ ≤ pair (check (C.Func i)) (0 : bSet B) ∈ᴮ q) := by
  let g : bSet B := indexedBinaryAssignment C b Hsep
  have Hextension := fresh_checked_assignment_extension C HK Hp
    (le_top.trans (indexedBinaryAssignment_is_function C b Hsep)) HC Hcount Hfresh
  refine ⟨binary_union p g, Hextension.trans inf_le_left,
    Hextension.trans (inf_le_right.trans inf_le_left), ?_⟩
  intro i
  constructor
  · exact mem_of_mem_subset
      (inf_le_left.trans (Hextension.trans (inf_le_right.trans inf_le_right)))
      (inf_le_right.trans (indexedBinaryAssignment_one C b Hsep i))
  · exact mem_of_mem_subset
      (inf_le_left.trans (Hextension.trans (inf_le_right.trans inf_le_right)))
      (inf_le_right.trans (indexedBinaryAssignment_zero C b Hsep i))

end bSet.ErdosCohen
