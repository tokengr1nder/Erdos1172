/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Regular
public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelationAPI

@[expose] public section

open Cardinal Ordinal Set Function

/-!
# The Erdős–Dushnik–Miller theorem for regular cardinals

This file proves the regular-cardinal half of the Erdős–Dushnik–Miller graph dichotomy.
For an infinite regular cardinal `κ`, every graph on the initial ordinal of `κ` has either
a clique of cardinality `κ` or a countably infinite independent set.

The proof uses the standard two-case argument.  If every `κ`-sized reservoir contains a
vertex with `κ` many neighbors, nested reservoirs yield a countable clique.  Otherwise, in
a `κ`-sized set all relevant neighborhoods are small; regularity then permits a transfinite
recursion avoiding the union of all earlier neighborhoods.
-/

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {k : Cardinal.{u}}

/-- Removing a set of cardinality below an infinite cardinal does not change the cardinality
of a set having exactly that cardinality. -/
private theorem mk_sdiff_eq_of_mk_eq_of_mk_lt {s t : Set V}
    (hk : ℵ₀ ≤ k) (hs : #s = k) (ht : #t < k) : #(s \ t : Set V) = k := by
  apply le_antisymm
  · simpa [hs] using Cardinal.mk_le_mk_of_subset (Set.sdiff_subset : s \ t ⊆ s)
  · by_contra h
    have hdiff : #(s \ t : Set V) < k := lt_of_not_ge h
    have hcover : k ≤ #(s \ t : Set V) + #t := by
      simpa [hs] using Cardinal.le_mk_sdiff_add_mk s t
    exact (not_lt_of_ge hcover) (Cardinal.add_lt_of_lt hk hdiff ht)

/-- If every large reservoir has a vertex with a large neighborhood, iterating this choice
produces a countably infinite clique. -/
private theorem exists_countable_clique_of_large_neighborhoods
    (k : Cardinal.{u}) (hk : ℵ₀ ≤ k) (G : SimpleGraph k.ord.ToType)
    (hlarge : ∀ X : Set k.ord.ToType, #X = k →
      ∃ x ∈ X, #(X ∩ G.neighborSet x : Set k.ord.ToType) = k) :
    ∃ A : Set k.ord.ToType, G.IsClique A ∧ #A = ℵ₀ := by
  classical
  let LargeSet := {X : Set k.ord.ToType // #X = k}
  let initial : LargeSet := ⟨Set.univ, by simp⟩
  let pick : ∀ X : LargeSet,
      {x : k.ord.ToType // x ∈ X.1 ∧ #(X.1 ∩ G.neighborSet x : Set k.ord.ToType) = k} :=
    fun X ↦ ⟨Classical.choose (hlarge X.1 X.2), Classical.choose_spec (hlarge X.1 X.2)⟩
  let next : LargeSet → LargeSet := fun X ↦
    ⟨(X.1 ∩ G.neighborSet (pick X).1) \ Set.Iic (pick X).1,
      mk_sdiff_eq_of_mk_eq_of_mk_lt hk (pick X).2.2 (by
        simpa using Cardinal.mk_Iic_lt (pick X).1 (by simp) (by simpa using hk))⟩
  let reservoir : ℕ → LargeSet := fun n ↦ next^[n] initial
  let vertex : ℕ → k.ord.ToType := fun n ↦ (pick (reservoir n)).1
  have reservoir_succ (n : ℕ) : reservoir (n + 1) = next (reservoir n) := by
    simp only [reservoir, Function.iterate_succ_apply']
  have reservoir_antitone : Antitone fun n ↦ (reservoir n).1 := by
    apply antitone_nat_of_succ_le
    intro n
    rw [reservoir_succ]
    exact Set.sdiff_subset.trans Set.inter_subset_left
  have vertex_mem (n : ℕ) : vertex n ∈ (reservoir n).1 := (pick (reservoir n)).2.1
  have vertex_adj {i j : ℕ} (hij : i < j) : G.Adj (vertex i) (vertex j) := by
    have hj : vertex j ∈ (reservoir (i + 1)).1 :=
      reservoir_antitone (Nat.succ_le_iff.2 hij) (vertex_mem j)
    rw [reservoir_succ] at hj
    exact hj.1.2
  have vertex_injective : Injective vertex := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (vertex_adj hlt).ne hij
    · exact (vertex_adj hgt).ne hij.symm
  refine ⟨Set.range vertex, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun h ↦ hne (congrArg vertex h)
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact vertex_adj hlt
    · exact (vertex_adj hgt).symm
  · simpa [Cardinal.mk_nat] using Cardinal.mk_range_eq_of_injective vertex_injective

/-- On a large set whose complementary neighborhoods are all small, regularity permits a
transfinite recursion producing a large clique. -/
private theorem exists_large_clique_of_small_compl_neighborhoods
    (k : Cardinal.{u}) (hk : k.IsRegular) (G : SimpleGraph k.ord.ToType)
    (S : Set k.ord.ToType) (hS : #S = k)
    (hsmall : ∀ x ∈ S, #(S ∩ Gᶜ.neighborSet x : Set k.ord.ToType) < k) :
    ∃ A : Set k.ord.ToType, G.IsClique A ∧ #A = k := by
  classical
  let bad (x : S) : Set k.ord.ToType := insert x.1 (S ∩ Gᶜ.neighborSet x.1)
  have bad_small (x : S) : #(bad x) < k := by
    apply Cardinal.mk_insert_le.trans_lt
    exact Cardinal.add_one_lt_of_lt hk.aleph0_le (hsmall x.1 x.2)
  have available (i : k.ord.ToType) (previous : ∀ j, j < i → S) :
      (S \ ⋃ j : Set.Iio i, bad (previous j.1 j.2)).Nonempty := by
    have hi : #(Set.Iio i) < k := by
      simpa using Cardinal.mk_Iio_lt i (by simp)
    have hunion : #(⋃ j : Set.Iio i, bad (previous j.1 j.2)) < k :=
      (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hk hi).2 fun j ↦
        bad_small (previous j.1 j.2)
    apply Cardinal.sdiff_nonempty_of_mk_lt_mk
    simpa [hS] using hunion
  let chooseNext (i : k.ord.ToType) (previous : ∀ j, j < i → S) : S :=
    ⟨Classical.choose (available i previous), (Classical.choose_spec (available i previous)).1⟩
  have chooseNext_spec (i : k.ord.ToType) (previous : ∀ j, j < i → S) :
      (chooseNext i previous).1 ∈ S \ ⋃ j : Set.Iio i, bad (previous j.1 j.2) :=
    Classical.choose_spec (available i previous)
  let chosen : k.ord.ToType → S := WellFoundedLT.fix chooseNext
  have chosen_spec (i : k.ord.ToType) :
      (chosen i).1 ∈ S \ ⋃ j : Set.Iio i, bad (chosen j.1) := by
    change (WellFoundedLT.fix chooseNext i).1 ∈
      S \ ⋃ j : Set.Iio i, bad (WellFoundedLT.fix chooseNext j.1)
    rw [WellFoundedLT.fix_eq chooseNext i]
    exact chooseNext_spec i fun j _ ↦ WellFoundedLT.fix chooseNext j
  have chosen_ne_of_lt {i j : k.ord.ToType} (hij : i < j) :
      (chosen i).1 ≠ (chosen j).1 := by
    intro heq
    have hmem : (chosen j).1 ∈ bad (chosen i) := by
      simp only [bad, Set.mem_insert_iff]
      exact Or.inl heq.symm
    exact (chosen_spec j).2 (Set.mem_iUnion.2 ⟨⟨i, hij⟩, hmem⟩)
  have chosen_adj_of_lt {i j : k.ord.ToType} (hij : i < j) :
      G.Adj (chosen i).1 (chosen j).1 := by
    have hnotmem : (chosen j).1 ∉ bad (chosen i) := by
      intro hmem
      exact (chosen_spec j).2 (Set.mem_iUnion.2 ⟨⟨i, hij⟩, hmem⟩)
    have hncompl : ¬ Gᶜ.Adj (chosen i).1 (chosen j).1 := by
      intro hadj
      apply hnotmem
      simp only [bad, Set.mem_insert_iff, Set.mem_inter_iff,
        SimpleGraph.mem_neighborSet]
      exact Or.inr ⟨(chosen j).2, hadj⟩
    by_contra hadj
    exact hncompl (by simp [SimpleGraph.compl_adj, chosen_ne_of_lt hij, hadj])
  let vertex : k.ord.ToType → k.ord.ToType := fun i ↦ (chosen i).1
  have vertex_injective : Injective vertex := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact chosen_ne_of_lt hlt hij
    · exact chosen_ne_of_lt hgt hij.symm
  refine ⟨Set.range vertex, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun h ↦ hne (congrArg vertex h)
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact chosen_adj_of_lt hlt
    · exact (chosen_adj_of_lt hgt).symm
  · simpa [vertex] using Cardinal.mk_range_eq_of_injective vertex_injective

/-- **Erdős–Dushnik–Miller for regular cardinals (graph form).**

Every graph on the initial ordinal of an infinite regular cardinal `k` has either a clique of
cardinality `k`, or an independent set of cardinality `ℵ₀`. -/
theorem erdosDushnikMiller_of_isRegular (k : Cardinal.{u}) (hk : k.IsRegular)
    (G : SimpleGraph k.ord.ToType) :
    (∃ A : Set k.ord.ToType, G.IsClique A ∧ #A = k) ∨
      ∃ B : Set k.ord.ToType, Gᶜ.IsClique B ∧ #B = ℵ₀ := by
  classical
  by_cases hlarge : ∀ X : Set k.ord.ToType, #X = k →
      ∃ x ∈ X, #(X ∩ Gᶜ.neighborSet x : Set k.ord.ToType) = k
  · obtain ⟨B, hB, hBcard⟩ :=
      exists_countable_clique_of_large_neighborhoods k hk.aleph0_le Gᶜ hlarge
    exact Or.inr ⟨B, hB, hBcard⟩
  · push Not at hlarge
    obtain ⟨S, hS, hsmall_ne⟩ := hlarge
    apply Or.inl
    apply exists_large_clique_of_small_compl_neighborhoods k hk G S hS
    intro x hx
    have hle : #(S ∩ Gᶜ.neighborSet x : Set k.ord.ToType) ≤ k :=
      (Cardinal.mk_le_mk_of_subset Set.inter_subset_left).trans_eq hS
    exact lt_of_le_of_ne hle (hsmall_ne x hx)

/-- **Erdős–Dushnik–Miller for regular cardinals (ordinal partition form).**

For every infinite regular cardinal `k`, its initial ordinal satisfies
`k.ord → (k.ord, ω)²`. -/
theorem ordinalRamsey_ord_ord_omega_of_isRegular (k : Cardinal.{u}) (hk : k.IsRegular) :
    OrdinalRamsey k.ord k.ord ω := by
  classical
  intro red blue hcompl
  obtain ⟨A, hA, hAcard⟩ | ⟨B, hB, hBcard⟩ :=
    erdosDushnikMiller_of_isRegular k hk red
  · refine Or.inl ⟨A, hA, le_antisymm ?_ ?_⟩
    · simpa using Ordinal.type_set_le A
    · simpa only [hAcard] using
        (Cardinal.ord_le_type ((· < ·) : A → A → Prop))
  · have homega : ω ≤ typeLT B := by
      simpa only [hBcard, Cardinal.ord_aleph0] using
        (Cardinal.ord_le_type ((· < ·) : B → B → Prop))
    obtain ⟨T, hTB, hTtype⟩ := Ordinal.exists_subset_typeLT_eq B homega
    refine Or.inr ⟨T, ?_, hTtype⟩
    rw [← hcompl.compl_eq]
    exact hB.subset hTB

end SimpleGraph
