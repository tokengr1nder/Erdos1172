/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Data.List.Infix
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

/-!
# Finite-sequence collapse conditions

A stronger condition extends the finite sequence, so the forcing order
is reverse prefix. Compatibility is exactly prefix comparability. The
length and target-occurrence requirements are dense below every condition.
The length assertion explicitly requires a nonempty alphabet; the poset
itself remains nonempty even when the alphabet is empty.

This file constructs only the concrete ordered conditions and dense sets.
It makes no assertion about a generic filter, Boolean completion, GCH,
ideal, forcing extension, or consistency.
-/

set_option autoImplicit false

universe u

namespace Erdos1172Collapse

structure Condition (α : Type u) where
  entries : List α

variable {α : Type u}

@[ext] theorem Condition.ext {p q : Condition α} (h : p.entries = q.entries) : p = q := by
  cases p
  cases q
  cases h
  rfl

instance conditionPartialOrder : PartialOrder (Condition α) where
  le p q := q.entries <+: p.entries
  le_refl _ := List.prefix_rfl
  le_trans _ _ _ hpq hqr := hqr.trans hpq
  le_antisymm _ _ hpq hqp := Condition.ext
    (hqp.eq_of_length (hqp.length_le.antisymm hpq.length_le))

instance conditionOrderTop : OrderTop (Condition α) where
  top := ⟨[]⟩
  le_top _ := List.nil_prefix

instance conditionInhabited : Inhabited (Condition α) := ⟨⊤⟩

@[simp] theorem le_iff_prefix {p q : Condition α} :
    p ≤ q ↔ q.entries <+: p.entries := Iff.rfl

@[simp] theorem top_entries : (⊤ : Condition α).entries = [] := rfl

theorem condition_nonempty : Nonempty (Condition α) := ⟨⊤⟩

def cone (p : Condition α) : Set (Condition α) := Set.Iic p

def Compatible (p q : Condition α) : Prop := ∃ r, r ≤ p ∧ r ≤ q

@[simp] theorem mem_cone {p q : Condition α} : q ∈ cone p ↔ q ≤ p := Iff.rfl

theorem cone_nonempty (p : Condition α) : (cone p).Nonempty :=
  ⟨p, mem_cone.mpr le_rfl⟩

theorem cone_mono {p q : Condition α} (hpq : p ≤ q) : cone p ⊆ cone q :=
  fun _ hr => hr.trans hpq

theorem cone_subset_iff {p q : Condition α} : cone p ⊆ cone q ↔ p ≤ q :=
  ⟨fun h => h (mem_cone.mpr le_rfl), cone_mono⟩

theorem compatible_iff_prefix_comparable {p q : Condition α} :
    Compatible p q ↔ p.entries <+: q.entries ∨ q.entries <+: p.entries := by
  constructor
  · rintro ⟨r, hrp, hrq⟩
    exact List.prefix_or_prefix_of_prefix hrp hrq
  · rintro (hpq | hqp)
    · exact ⟨q, hpq, le_rfl⟩
    · exact ⟨p, le_rfl, hqp⟩

theorem compatible_iff_comparable {p q : Condition α} :
    Compatible p q ↔ p ≤ q ∨ q ≤ p := by
  rw [compatible_iff_prefix_comparable]
  exact or_comm

theorem cones_inter_nonempty_iff {p q : Condition α} :
    (cone p ∩ cone q).Nonempty ↔
      p.entries <+: q.entries ∨ q.entries <+: p.entries :=
  compatible_iff_prefix_comparable

theorem compatible_iff_cones_inter_nonempty {p q : Condition α} :
    Compatible p q ↔ (cone p ∩ cone q).Nonempty := Iff.rfl

def extend (p : Condition α) (s : List α) : Condition α := ⟨p.entries ++ s⟩

@[simp] theorem extend_entries (p : Condition α) (s : List α) :
    (extend p s).entries = p.entries ++ s := rfl

theorem extend_le (p : Condition α) (s : List α) : extend p s ≤ p :=
  p.entries.prefix_append s

theorem le_iff_exists_extend {p q : Condition α} :
    p ≤ q ↔ ∃ s : List α, p = extend q s := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, Condition.ext hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact extend_le q s

theorem extend_append (p : Condition α) (s t : List α) :
    extend (extend p s) t = extend p (s ++ t) := by
  apply Condition.ext
  exact List.append_assoc _ _ _

def DenseBelow (D : Set (Condition α)) : Prop :=
  ∀ p : Condition α, ∃ q : Condition α, q ≤ p ∧ q ∈ D

def lengthDense (n : ℕ) : Set (Condition α) := {p | n ≤ p.entries.length}

def targetDense (a : α) : Set (Condition α) := {p | a ∈ p.entries}

theorem lengthDense_downward {n : ℕ} {p q : Condition α}
    (hpq : p ≤ q) (hq : q ∈ lengthDense n) : p ∈ lengthDense n :=
  hq.trans hpq.length_le

theorem targetDense_downward {a : α} {p q : Condition α}
    (hpq : p ≤ q) (hq : q ∈ targetDense a) : p ∈ targetDense a :=
  hpq.sublist.subset hq

theorem lengthDense_dense [Nonempty α] (n : ℕ) : DenseBelow (lengthDense (α := α) n) := by
  obtain ⟨a⟩ := ‹Nonempty α›
  intro p
  refine ⟨extend p (List.replicate n a), extend_le _ _, ?_⟩
  change n ≤ (p.entries ++ List.replicate n a).length
  simp only [List.length_append, List.length_replicate]
  exact Nat.le_add_left n p.entries.length

theorem targetDense_dense (a : α) : DenseBelow (targetDense a) := by
  intro p
  refine ⟨extend p [a], extend_le _ _, ?_⟩
  change a ∈ p.entries ++ [a]
  exact List.mem_append_right _ (List.mem_singleton_self _)

def conditionEquivList : Condition α ≃ List α where
  toFun := Condition.entries
  invFun := Condition.mk
  left_inv p := by cases p; rfl
  right_inv _ := rfl

theorem cardinal_eq_list : Cardinal.mk (Condition α) = Cardinal.mk (List α) :=
  Cardinal.mk_congr conditionEquivList

theorem cardinal_le : Cardinal.mk (Condition α) ≤ max Cardinal.aleph0 (Cardinal.mk α) :=
  cardinal_eq_list.trans_le (Cardinal.mk_list_le_max α)

theorem cardinal_eq_of_nonempty [Nonempty α] :
    Cardinal.mk (Condition α) = max Cardinal.aleph0 (Cardinal.mk α) :=
  cardinal_eq_list.trans (Cardinal.mk_list_eq_max α)

theorem cardinal_eq_of_infinite [Infinite α] :
    Cardinal.mk (Condition α) = Cardinal.mk α :=
  cardinal_eq_list.trans (Cardinal.mk_list_eq_mk α)

end Erdos1172Collapse
