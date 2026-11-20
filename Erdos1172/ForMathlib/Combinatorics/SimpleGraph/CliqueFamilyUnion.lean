/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueBlockExtension

@[expose] public section

open Ordinal Set

universe u v

namespace Ordinal

/-- The range of a strictly monotone map has exactly the order type of its
domain.  This packages the `StrictMonoOn.orderIso` argument used repeatedly
when a transfinite clique is assembled by choosing one point at each stage. -/
theorem typeLT_range_of_strictMono
    {I V : Type u}
    [LinearOrder I] [WellFoundedLT I]
    [LinearOrder V] [WellFoundedLT V]
    (f : I → V) (hf : StrictMono f) :
    typeLT (Set.range f) = typeLT I := by
  have heq : typeLT (Set.univ : Set I) =
      typeLT (f '' (Set.univ : Set I)) :=
    ((hf.strictMonoOn (Set.univ : Set I)).orderIso
      f (Set.univ : Set I)).ordinalType_congr
  rw [Set.image_univ] at heq
  calc
    typeLT (Set.range f) = typeLT (Set.univ : Set I) := heq.symm
    _ = typeLT I := OrderIso.Set.univ.ordinalType_congr

end Ordinal

namespace SimpleGraph

/-- A union of clique blocks is a clique when every two differently indexed
blocks are completely joined.  Unlike `SimpleGraph.isClique_iUnion`, this
does not require the blocks to form a directed family under inclusion. -/
theorem IsClique.iUnion_of_cross
    {V : Type u} {ι : Type v} (G : SimpleGraph V) (blocks : ι → Set V)
    (hblocks : ∀ i, G.IsClique (blocks i))
    (hcross : ∀ i j, i ≠ j →
      ∀ x ∈ blocks i, ∀ y ∈ blocks j, G.Adj x y) :
    G.IsClique (⋃ i, blocks i) := by
  intro x hx y hy hxy
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
  by_cases hij : i = j
  · subst j
    exact hblocks i hxi hyj hxy
  · exact hcross i j hij x hxi y hyj

/-- Ordered formulation of `IsClique.iUnion_of_cross`: it is enough to prove
complete joining only from every earlier block to every later block. -/
theorem IsClique.iUnion_of_lt_cross
    {V : Type u} {ι : Type v} [LinearOrder ι]
    (G : SimpleGraph V) (blocks : ι → Set V)
    (hblocks : ∀ i, G.IsClique (blocks i))
    (hcross : ∀ i j, i < j →
      ∀ x ∈ blocks i, ∀ y ∈ blocks j, G.Adj x y) :
    G.IsClique (⋃ i, blocks i) := by
  apply SimpleGraph.IsClique.iUnion_of_cross G blocks hblocks
  intro i j hij x hxi y hyj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hcross i j hij x hxi y hyj
  · rw [G.adj_comm]
    exact hcross j i hji y hyj x hxi

/-- A clique of type `β` followed by any well-ordered family of nonempty
clique reservoirs can be extended by one chosen point from each reservoir.
Strict ordering of the blocks gives the exact tail order type, while complete
joining gives the clique edges.  Thus the resulting clique has type
`β + typeLT I` and lies in the union of the supplied blocks.

This is the family analogue of `exists_clique_type_add_of_later_block`, but it
needs only nonemptiness (rather than an internal clique) from each later block. -/
theorem exists_clique_type_add_of_later_family
    {V I : Type u}
    [LinearOrder V] [WellFoundedLT V]
    [LinearOrder I] [WellFoundedLT I]
    (G : SimpleGraph V) {base : Set V} (blocks : I → Set V)
    {β : Ordinal.{u}}
    (hbaseClique : G.IsClique base)
    (hbaseType : typeLT base = β)
    (hblocksNonempty : ∀ i, (blocks i).Nonempty)
    (hbaseBefore : ∀ x ∈ base, ∀ i, ∀ y ∈ blocks i, x < y)
    (hblocksBefore : ∀ i j, i < j →
      ∀ x ∈ blocks i, ∀ y ∈ blocks j, x < y)
    (hbaseCross : ∀ x ∈ base, ∀ i, ∀ y ∈ blocks i, G.Adj x y)
    (hblocksCross : ∀ i j, i < j →
      ∀ x ∈ blocks i, ∀ y ∈ blocks j, G.Adj x y) :
    ∃ u : Set V,
      u ⊆ (base ∪ ⋃ i, blocks i) ∧
      G.IsClique u ∧ typeLT u = β + typeLT I := by
  classical
  let pick : I → V := fun i ↦ Classical.choose (hblocksNonempty i)
  have hpick (i : I) : pick i ∈ blocks i :=
    Classical.choose_spec (hblocksNonempty i)
  have hpickStrict : StrictMono pick := by
    intro i j hij
    exact hblocksBefore i j hij (pick i) (hpick i) (pick j) (hpick j)
  let tail : Set V := Set.range pick
  have htailClique : G.IsClique tail := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun hij ↦ hne (congrArg pick hij)
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hblocksCross i j hij (pick i) (hpick i) (pick j) (hpick j)
    · exact (hblocksCross j i hji (pick j) (hpick j)
        (pick i) (hpick i)).symm
  have htailType : typeLT tail = typeLT I :=
    Ordinal.typeLT_range_of_strictMono pick hpickStrict
  have hbaseTailBefore : ∀ x ∈ base, ∀ y ∈ tail, x < y := by
    rintro x hx _ ⟨i, rfl⟩
    exact hbaseBefore x hx i (pick i) (hpick i)
  have hbaseTailCross : ∀ x ∈ base, ∀ y ∈ tail, G.Adj x y := by
    rintro x hx _ ⟨i, rfl⟩
    exact hbaseCross x hx i (pick i) (hpick i)
  refine ⟨base ∪ tail, ?_,
    SimpleGraph.IsClique.union_of_cross G hbaseClique htailClique
      hbaseTailCross, ?_⟩
  · rintro x (hx | hx)
    · exact Or.inl hx
    · right
      obtain ⟨i, rfl⟩ := hx
      exact Set.mem_iUnion.mpr ⟨i, hpick i⟩
  · rw [Ordinal.typeLT_union_of_forall_lt hbaseTailBefore,
      hbaseType, htailType]

end SimpleGraph
