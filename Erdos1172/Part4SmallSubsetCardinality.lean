/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.Set.Image

@[expose] public section

/-!
# Small subsets and countable sequences below an inaccessible cardinal

These are host-cardinality bounds. A set of cardinality at most κ has at
most κ subsets of size strictly below κ when κ is inaccessible. Countable
sequences are then encoded by their actual graphs, retaining the coordinate
labels rather than just their ranges. No GCH or forcing statement is assumed.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Erdos1172SmallSubsetCardinality

/-- Mathlib's cofinality-indexed small-subset theorem, specialized to the
canonical type of an inaccessible cardinal. -/
theorem small_subsets_ord_cardinal_eq (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) :
    Cardinal.mk {A : Set κ.ord.ToType // Cardinal.mk A < κ} = κ := by
  have Hstrong : Cardinal.IsStrongPrelimit (Cardinal.mk κ.ord.ToType) := by
    simpa only [Cardinal.mk_ord_toType] using Hκ.isStrongPrelimit
  simpa only [Cardinal.mk_ord_toType, Hκ.isRegular.cof_ord] using
    Cardinal.mk_subset_mk_lt_cof Hstrong

/-- Moving a small subset along an embedding into κ proves the same bound
for any type of size at most κ, including an empty type. -/
theorem small_subsets_cardinal_le (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) {P : Type u} (HP : Cardinal.mk P ≤ κ) :
    Cardinal.mk {A : Set P // Cardinal.mk A < κ} ≤ κ := by
  classical
  obtain ⟨e⟩ : Nonempty (P ↪ κ.ord.ToType) :=
    (Cardinal.le_def P κ.ord.ToType).mp (by simpa only [Cardinal.mk_ord_toType] using HP)
  let F : {A : Set P // Cardinal.mk A < κ} →
      {A : Set κ.ord.ToType // Cardinal.mk A < κ} :=
    fun A => ⟨e '' A.val, Cardinal.mk_image_le.trans_lt A.property⟩
  have HF : Function.Injective F := by
    intro A B h
    apply Subtype.ext
    apply e.injective.image_injective
    exact congrArg Subtype.val h
  calc
    Cardinal.mk {A : Set P // Cardinal.mk A < κ} ≤
        Cardinal.mk {A : Set κ.ord.ToType // Cardinal.mk A < κ} :=
      Cardinal.mk_le_of_injective HF
    _ = κ := small_subsets_ord_cardinal_eq κ Hκ

/-- The lifted natural coordinate keeps all types in the same universe. -/
def sequenceGraph {P : Type u} (f : ℕ → P) : Set (ULift.{u} ℕ × P) :=
  Set.range (fun n : ULift.{u} ℕ => (n, f n.down))

theorem sequenceGraph_cardinal_le {P : Type u} (f : ℕ → P) :
    Cardinal.mk (sequenceGraph f) ≤ Cardinal.aleph0 := by
  have H : Cardinal.mk (sequenceGraph f) ≤ Cardinal.mk (ULift.{u} ℕ) :=
    Cardinal.mk_range_le
  simpa using H

theorem sequenceGraph_injective {P : Type u} :
    Function.Injective (sequenceGraph (P := P)) := by
  intro f g h
  funext n
  have Hmem : (ULift.up n, f n) ∈ sequenceGraph f := ⟨ULift.up n, rfl⟩
  rw [h] at Hmem
  obtain ⟨m, Hm⟩ := Hmem
  have Hmn : m.down = n := congrArg (fun z : ULift.{u} ℕ × P => z.1.down) Hm
  have Hvalue : g m.down = f n := congrArg Prod.snd Hm
  rw [Hmn] at Hvalue
  exact Hvalue.symm

/-- Inaccessibility also bounds all countable sequences in any κ-sized type.
The graph proof does not confuse sequences with their unordered ranges. -/
theorem nat_function_cardinal_le (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) {P : Type u} (HP : Cardinal.mk P ≤ κ) :
    Cardinal.mk (ℕ → P) ≤ κ := by
  have Hprod : Cardinal.mk (ULift.{u} ℕ × P) ≤ κ := by
    calc
      Cardinal.mk (ULift.{u} ℕ × P) = Cardinal.aleph0 * Cardinal.mk P := by simp
      _ ≤ κ * κ := mul_le_mul' Hκ.aleph0_lt.le HP
      _ = κ := Cardinal.mul_eq_self Hκ.aleph0_lt.le
  let F : (ℕ → P) →
      {A : Set (ULift.{u} ℕ × P) // Cardinal.mk A < κ} :=
    fun f => ⟨sequenceGraph f, (sequenceGraph_cardinal_le f).trans_lt Hκ.aleph0_lt⟩
  have HF : Function.Injective F := by
    intro f g h
    exact sequenceGraph_injective (congrArg Subtype.val h)
  exact (Cardinal.mk_le_of_injective HF).trans
    (small_subsets_cardinal_le κ Hκ Hprod)

theorem nat_ord_function_cardinal_le (κ : Cardinal.{u})
    (Hκ : κ.IsInaccessible) : Cardinal.mk (ℕ → κ.ord.ToType) ≤ κ :=
  nat_function_cardinal_le κ Hκ (by rw [Cardinal.mk_ord_toType])

end Erdos1172SmallSubsetCardinality
