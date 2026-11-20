/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCohenSuccessorHartogs
public import Erdos1172.Part4BooleanOmegaSequenceTransport
public import Mathlib.SetTheory.Ordinal.Family

@[expose] public section

/-!
# Ground ordinal bounds for arbitrary internal ordinal-valued omega functions

An ordinal name injects into a checked cardinal obtained from its actual
index type. The proved noncollapse of that cardinal's checked successor
excludes inclusion of the successor in the name. Internal ordinal comparison
therefore puts the entire mixed name below one actual checked ground ordinal
at the unchanged Boolean condition.

The ground supremum of successor bounds on the numeral values bounds a
whole omega sequence. Supported graph equality with the actual numeral-value
sequence then transfers the new codomain to the SAME original function,
including mixed natural arguments. No prior ordinal bound, union-ordinal
closure shortcut, GCH, anonymous recovery, or ideal is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet ErdosBoundedFunctionValue ErdosOmegaSequence

/-- A possibly mixed ordinal name lies below one checked ground ordinal
at the original condition. The bound depends on its full host index type. -/
theorem exists_checked_ordinal_bound (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (a : bSet (Algebra κ)) {Γ : Algebra κ}
    (Ha : Γ ≤ Ord a) :
    ∃ η : Ordinal.{u}, Γ ≤ a ∈ᴮ check (PSet.ordinalMk η) := by
  let μ : Cardinal.{u} := max κ (Cardinal.mk a.type)
  have Hκμ : κ ≤ μ := le_max_left _ _
  have Hindex : (⊤ : Algebra κ) ≤
      injects_into a (check (PSet.ordinalMk μ.ord)) :=
    ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le
      μ a (le_max_right _ _)
  have Hnot : Γ ≤ (check (PSet.ordinalMk (Order.succ μ).ord) ⊆ᴮ a)ᶜ := by
    rw [← imp_bot, ← deduction]
    have Hinj : Γ ⊓ (check (PSet.ordinalMk (Order.succ μ).ord) ⊆ᴮ a) ≤
        injects_into (check (PSet.ordinalMk (Order.succ μ).ord))
          (check (PSet.ordinalMk μ.ord)) :=
      injects_into_trans (injects_into_of_subset inf_le_right) (le_top.trans Hindex)
    exact Hinj.trans_eq (checked_successor_injects_base_eq_bot κ Hκ μ Hκμ)
  exact ⟨(Order.succ μ).ord,
    Ord.lt_of_not_le (check_Ord (PSet.Ord_mk (Order.succ μ).ord)) Ha Hnot⟩

/-- A countable host family of arbitrary locally ordinal names admits a
single ground ordinal bound, without selecting ground representatives of
those names. The bound covers every member at exactly the same condition. -/
theorem exists_checked_ordinal_sequence_bound (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) (v : ℕ → bSet (Algebra κ)) {Γ : Algebra κ}
    (Hord : ∀ n : ℕ, Γ ≤ Ord (v n)) :
    ∃ η : Ordinal.{u}, ∀ n : ℕ, Γ ≤ v n ∈ᴮ check (PSet.ordinalMk η) := by
  classical
  choose α Hα using (fun n => exists_checked_ordinal_bound κ Hκ (v n) (Hord n))
  let η : Ordinal.{u} := ⨆ n : ℕ, α n + 1
  refine ⟨η, ?_⟩
  intro n
  have Hlt : α n < η := Ordinal.lt_iSup_add_one α n
  have Hmember : Γ ≤ check (PSet.ordinalMk (α n)) ∈ᴮ check (PSet.ordinalMk η) :=
    check_mem (PSet.mk_mem_mk_of_lt Hlt)
  exact mem_of_mem_Ord (Hα n) Hmember (check_Ord (PSet.Ord_mk η))

/-- Every supported internal omega function with ordinal values has an
actual checked-ordinal codomain at its original Boolean condition. The
function graph itself is not restricted, replaced, or merely enumerated
on external natural representatives. -/
theorem exists_checked_ordinal_function_bound (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) {S f : bSet (Algebra κ)} {Γ : Algebra κ}
    (Hf : Γ ≤ is_function omega S f)
    (HS : Γ ≤ ⨅ x : bSet (Algebra κ), _root_.imp (x ∈ᴮ S) (Ord x)) :
    ∃ η : Ordinal.{u}, Γ ≤ is_function omega (check (PSet.ordinalMk η)) f := by
  let v : ℕ → bSet (Algebra κ) := fun n => graphValue S f (of_nat n)
  have Hord (n : ℕ) : Γ ≤ Ord (v n) :=
    (le_inf (HS.trans (iInf_le _ (v n)))
      (graphValue_mem Hf of_nat_mem_omega)).trans bv_imp_elim
  obtain ⟨η, Hbound⟩ := exists_checked_ordinal_sequence_bound κ Hκ v Hord
  have Hsequence : Γ ≤ is_function omega (check (PSet.ordinalMk η)) (sequenceGraph v) :=
    sequenceGraph_is_function Hbound
  have Heq : Γ ≤ f =ᴮ sequenceGraph v := eq_sequenceGraph_graphValue Hf
  exact ⟨η, bv_rw'' (bv_symm Heq) Hsequence B_ext_is_function_right⟩

end Erdos1172LevyCohen
