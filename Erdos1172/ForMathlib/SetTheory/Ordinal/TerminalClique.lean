/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueExtension

@[expose] public section

open Ordinal Set

universe u

namespace Ordinal

/-- A set of successor order type `β + 1` has a canonical terminal point;
the elements before it form a subset of exact order type `β`. -/
theorem exists_core_terminal_of_typeLT_eq_add_one
    {V : Type u} [LinearOrder V] [WellFoundedLT V]
    (base : Set V) {β : Ordinal.{u}} (hbaseType : typeLT base = β + 1) :
    ∃ (core : Set V) (x : V), core ⊆ base ∧ x ∈ base ∧
      base = insert x core ∧ typeLT core = β ∧ ∀ y ∈ core, y < x := by
  have hβlt : β < typeLT base := by
    rw [hbaseType]
    exact lt_add_one β
  let xsub : base := Ordinal.enum (α := base) (· < ·) ⟨β, hβlt⟩
  let core : Set V := {y | y ∈ base ∧ y < (xsub : V)}
  let e : Set.Iio xsub ≃o core :=
    { toEquiv :=
        { toFun := fun y ↦ ⟨(y.1.1 : V), y.1.2, y.2⟩
          invFun := fun y ↦ ⟨⟨y.1, y.2.1⟩, y.2.2⟩
          left_inv := fun y ↦ Subtype.ext rfl
          right_inv := fun y ↦ Subtype.ext rfl }
      map_rel_iff' := by
        intro a b
        rfl }
  have hxtype : typeLT core = β := by
    have he := e.ordinalType_congr
    have hIio : typeLT (Set.Iio xsub) = β := by
      rw [Ordinal.type_Iio_lt, Ordinal.typein_enum]
    exact he.symm.trans hIio
  have hbaseEq : base = insert (xsub : V) core := by
    ext y
    constructor
    · intro hy
      let ysub : base := ⟨y, hy⟩
      have hyidx : Ordinal.typein (α := base) (· < ·) ysub ≤ β := by
        rw [← Order.lt_add_one_iff, ← hbaseType]
        exact Ordinal.typein_lt_type (α := base) (· < ·) ysub
      have hyle : ysub ≤ xsub := by
        apply le_of_not_gt
        exact (Ordinal.typein_le_typein (α := base) (· < ·)).mp <| by
          rw [Ordinal.typein_enum]
          exact hyidx
      rw [Set.mem_insert_iff]
      rcases hyle.eq_or_lt with heq | hlt
      · exact Or.inl (congrArg Subtype.val heq)
      · exact Or.inr ⟨hy, hlt⟩
    · intro hy
      rcases hy with rfl | hycore
      · exact xsub.property
      · exact hycore.1
  exact ⟨core, xsub, fun _ h ↦ h.1, xsub.property, hbaseEq, hxtype,
    fun _ h ↦ h.2⟩

end Ordinal

namespace SimpleGraph

/-- Clique version of terminal decomposition.  The terminal point is a
common later neighbor of the exact predecessor-type core. -/
theorem exists_clique_core_with_terminal_common_later
    {V : Type u} [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) {base : Set V} {β : Ordinal.{u}}
    (hbase : G.IsClique base) (hbaseType : typeLT base = β + 1) :
    ∃ (core : Set V) (x : V), core ⊆ base ∧ G.IsClique core ∧
      typeLT core = β ∧ (∀ y ∈ core, y < x) ∧
      ∀ y ∈ core, G.Adj y x := by
  obtain ⟨core, x, hsub, hxbase, -, hcoreType, hlater⟩ :=
    Ordinal.exists_core_terminal_of_typeLT_eq_add_one base hbaseType
  refine ⟨core, x, hsub, hbase.subset hsub, hcoreType, hlater, ?_⟩
  intro y hy
  exact hbase (hsub hy) hxbase (hlater y hy).ne

end SimpleGraph
