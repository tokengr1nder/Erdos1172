/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4PosetBooleanCompletion
public import Erdos1172.Part4CollapseConditions
public import Mathlib.Order.CompleteBooleanAlgebra

@[expose] public section

/-!
# The Boolean matrix of the finite-sequence collapse

The entry at `(n, a)` is the supremum of the conditions that put `a` in
position `n`. Distinct entries of a row are disjoint; every row covers top
when the alphabet is nonempty, and every column covers top.

These are the Boolean laws of a countable enumeration of the ground alphabet.
In particular, using the old uncountable ordinal as the alphabet collapses
that ordinal. This is not a construction of the final GCH-preserving model,
nor of the normal ideal whose quotient may have this collapse algebra.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Erdos1172Collapse

open Erdos1172PosetCompletion

variable {α : Type u}

abbrev Algebra (α : Type u) := Completion (Condition α)

/-- The Boolean value that position `n` of the collapse sequence equals `a`. -/
def entry (n : ℕ) (a : α) : Algebra α :=
  ⨆ p : {p : Condition α // p.entries[n]? = some a}, condition p.val

/-- A strengthening preserves every already specified sequence entry. -/
theorem getElem?_eq_of_le {p q : Condition α} {n : ℕ} {a : α}
    (hpq : p ≤ q) (hq : q.entries[n]? = some a) :
    p.entries[n]? = some a := by
  obtain ⟨hn, ha⟩ := List.getElem?_eq_some_iff.mp hq
  exact (List.prefix_iff_getElem?.mp hpq n hn).trans (congrArg some ha)

theorem condition_le_entry {p : Condition α} {n : ℕ} {a : α}
    (hp : p.entries[n]? = some a) : condition p ≤ entry n a :=
  le_iSup (fun q : {q : Condition α // q.entries[n]? = some a} =>
    condition q.val) ⟨p, hp⟩

/-- Two conditions assigning different values to one position are incompatible. -/
theorem condition_inf_eq_bot_of_entries_ne {p q : Condition α} {n : ℕ} {a b : α}
    (hp : p.entries[n]? = some a) (hq : q.entries[n]? = some b)
    (hab : a ≠ b) : condition p ⊓ condition q = ⊥ := by
  classical
  by_contra h
  obtain ⟨r, hrp, hrq⟩ := (condition_inf_ne_bot_iff p q).mp h
  exact hab (Option.some.inj ((getElem?_eq_of_le hrp hp).symm.trans (getElem?_eq_of_le hrq hq)))

theorem entry_inf_eq_bot {n : ℕ} {a b : α} (hab : a ≠ b) : entry n a ⊓ entry n b = ⊥ := by
  unfold entry
  erw [iSup_inf_eq]
  apply le_antisymm ?_ bot_le
  apply iSup_le
  intro p
  erw [inf_iSup_eq]
  apply iSup_le
  intro q
  exact (condition_inf_eq_bot_of_entries_ne p.property q.property hab).le

theorem row_iSup_eq_top [Nonempty α] (n : ℕ) : (⨆ a : α, entry n a) = ⊤ := by
  have hD : (⨆ p : lengthDense (α := α) (n + 1), condition p.val) = ⊤ := by
    apply iSup_condition_eq_top_of_dense
    intro p
    obtain ⟨q, hqp, hq⟩ := lengthDense_dense (α := α) (n + 1) p
    exact ⟨q, hq, hqp⟩
  apply eq_top_iff.mpr
  rw [← hD]
  apply iSup_le
  intro p
  have hn : n < p.val.entries.length := (Nat.lt_succ_self n).trans_le p.property
  exact (condition_le_entry (List.getElem?_eq_getElem hn)).trans
    (le_iSup (fun a : α => entry n a) (p.val.entries[n]'hn))

theorem column_iSup_eq_top (a : α) : (⨆ n : ℕ, entry n a) = ⊤ := by
  have hD : (⨆ p : targetDense a, condition p.val) = ⊤ := by
    apply iSup_condition_eq_top_of_dense
    intro p
    obtain ⟨q, hqp, hq⟩ := targetDense_dense a p
    exact ⟨q, hq, hqp⟩
  apply eq_top_iff.mpr
  rw [← hD]
  apply iSup_le
  intro p
  obtain ⟨n, hn⟩ := List.getElem?_of_mem p.property
  exact (condition_le_entry hn).trans (le_iSup (fun n : ℕ => entry n a) n)

end Erdos1172Collapse
