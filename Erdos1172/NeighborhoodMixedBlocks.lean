/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.NeighborhoodDerivedIdeal

@[expose] public section

/-!
# Ordered mixed-color blocks from the constructed derived ideals

The small block recursion retains the common outer-color endpoint. Thus
every union of previous blocks has ideal-small outer-color failure sets,
allowing the recursion to continue through `omegaOne` stages.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172NeighborhoodMixedBlocks

open Erdos1172NeighborhoodCode Erdos1172NeighborhoodIdeal Erdos1172NeighborhoodIdealCore Erdos1172NeighborhoodDerivedIdeal

variable {r : Code ↪ W3} {G H : SimpleGraph W3} {a : W3}

theorem exists_extension_core (ha : GoodCut r G H a) (outer : Bool)
    (word : List Bool) (inner : Bool) (hinner : inner ∈ word)
    (s : Set W3) (hs : ¬DerivedSmall r G H (outer :: word) a s)
    (_hsBelow : s ⊆ Set.Iio a) (selected : Set W3)
    (hselected : selected ⊆ Set.Iio a) (hcard : #selected < ℵ_ 2)
    (hselectedColor : ∀ x ∈ selected, (colorGraph G H outer).Adj x a)
    (cutoff : W3) (hcutoff : cutoff < a) :
    ∃ core : Set W3, core ⊆ s ∧ (colorGraph G H inner).IsClique core ∧
      typeLT core = ω_ 2 ∧ (∀ y ∈ core, (colorGraph G H outer).Adj y a) ∧
      (∀ y ∈ core, cutoff < y) ∧
      ∀ x ∈ selected, ∀ y ∈ core, (colorGraph G H outer).Adj x y := by
  classical
  let bad : Set W3 := ⋃ x : selected, {y | ¬(colorGraph G H outer).Adj x.val y}
  have hbad : Small r G H a bad := iUnion_small ha _ hcard (fun x =>
    nonneighbors_small ha outer (hselected x.property)
      (hselectedColor x.val x.property))
  have hdeleted : DerivedSmall r G H (outer :: word) a (bad ∪ Set.Iic cutoff) :=
    base_le_derived _ ha (union_small ha hbad (bounded_interval_small ha hcutoff))
  let remaining : Set W3 :=
    (s ∩ {x | (colorGraph G H outer).Adj x a}) \ (bad ∪ Set.Iic cutoff)
  have hremaining : ¬DerivedSmall r G H (outer :: word) a remaining :=
    (derivedSmallness (outer :: word) ha).positive_sdiff
      ((derivedSmall_cons_inter outer word a s).not.mpr hs) hdeleted
  let support : Set W3 := {β | β < a ∧ GoodCut r G H β ∧
    ¬DerivedSmall r G H word β (sectionAt G H outer a β remaining)}
  have hnonempty : support.Nonempty := by
    by_contra h
    apply hremaining
    change Small r G H a support
    rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact empty_small ha
  obtain ⟨β, hβ⟩ := hnonempty
  obtain ⟨core, hcore, hclique, htype⟩ := exists_core_of_derived_positive word hβ.2.1
    (sectionAt G H outer a β remaining) (fun _ hx => hx.2) hβ.2.2 inner hinner
  have hr : core ⊆ remaining := fun _ hx => (hcore hx).1.1
  refine ⟨core, fun y hy => (hr hy).1.1, hclique, htype,
    fun y hy => (hr hy).1.2, ?_, ?_⟩
  · exact fun y hy => lt_of_not_ge (fun h => (hr hy).2 (Or.inr h))
  · intro x hx y hy
    by_contra hxy
    exact (hr hy).2 (Or.inl (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxy⟩))

/-- A block keeps its common outer-color endpoint as part of its data. -/
structure SmallBlock (G H : SimpleGraph W3) (outer inner : Bool)
    (a : W3) (s : Set W3) where
  points : Set W3
  subset : points ⊆ s
  clique : (colorGraph G H inner).IsClique points
  type_eq : typeLT points = ω_ 1
  outer_adj : ∀ x ∈ points, (colorGraph G H outer).Adj x a

theorem SmallBlock.card {outer inner : Bool} {s : Set W3}
    (block : SmallBlock G H outer inner a s) : #block.points = ℵ_ 1 := by
  have h := congrArg Ordinal.card block.type_eq
  simpa only [Ordinal.card_type, Ordinal.card_omega] using h

theorem exists_next_block (ha : GoodCut r G H a) (outer inner : Bool)
    (s : Set W3) (hs : ¬DerivedSmall r G H [outer, inner] a s)
    (hsBelow : s ⊆ Set.Iio a) (i : W1)
    (previous : ∀ j, j < i → SmallBlock G H outer inner a s)
    (floor : W3) (hfloor : floor < a) :
    ∃ block : SmallBlock G H outer inner a s,
      (∀ y ∈ block.points, floor < y) ∧
      ∀ j (hj : j < i), ∀ x ∈ (previous j hj).points, ∀ y ∈ block.points,
        x < y ∧ (colorGraph G H outer).Adj x y := by
  let selected : Set W3 := ⋃ j : Set.Iio i, (previous j.val j.property).points
  have hselected : selected ⊆ Set.Iio a := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    exact hsBelow ((previous j.val j.property).subset hj)
  have hindex : #(Set.Iio i) < ℵ_ 2 := by
    have h := Cardinal.mk_Iio_lt i (by simp [W1])
    have h12 : (ℵ_ 1 : Cardinal.{0}) < ℵ_ 2 :=
      Cardinal.aleph_lt_aleph.mpr (by norm_num)
    have h1 : #(Set.Iio i) < ℵ_ 1 := by
      simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using h
    exact h1.trans h12
  have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
    convert Cardinal.isRegular_aleph_add_one 1 using 1 <;> norm_num
  have hcard : #selected < ℵ_ 2 := by
    apply (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hreg hindex).2
    intro j
    rw [(previous j.val j.property).card]
    exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  have hcolor : ∀ x ∈ selected, (colorGraph G H outer).Adj x a := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    exact (previous j.val j.property).outer_adj x hj
  obtain ⟨bound, hbound, hb⟩ :=
    ErdosRadoGCHAsym.exists_strict_bound_of_small_of_IsOmegaTwoSup ha.isOmegaTwoSup
      (mk_le_alephOne_of_lt_alephTwo hcard) (fun x hx => hselected hx)
  obtain ⟨core, hcore, hclique, htype, htop, hlater, hcross⟩ :=
    exists_extension_core ha outer [inner] inner (by simp) s hs hsBelow selected
      hselected hcard hcolor (max floor bound) (max_lt hfloor hbound)
  obtain ⟨points, hp, hptype⟩ := Ordinal.exists_subset_typeLT_eq core
    (show (ω_ 1 : Ordinal.{0}) ≤ typeLT core by
      rw [htype]
      exact Ordinal.omega_le_omega.mpr (by norm_num))
  let block : SmallBlock G H outer inner a s :=
    ⟨points, hp.trans hcore, hclique.subset hp, hptype, fun y hy => htop y (hp hy)⟩
  refine ⟨block, fun y hy => (le_max_left floor bound).trans_lt (hlater y (hp hy)), ?_⟩
  intro j hj x hx y hy
  have hxsel : x ∈ selected := Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩
  exact ⟨(hb x hxsel).trans ((le_max_right floor bound).trans_lt
    (hlater y (hp hy))), hcross x hxsel y (hp hy)⟩

/-- A positive two-color word supplies an `omegaOne` family of ordered
inner-color blocks with complete outer-color cross edges. -/
theorem exists_mixed_blocks (ha : GoodCut r G H a) (outer inner : Bool)
    (s : Set W3) (hs : ¬DerivedSmall r G H [outer, inner] a s)
    (hsBelow : s ⊆ Set.Iio a) (floor : W3) (hfloor : floor < a) :
    ∃ blocks : W1 → SmallBlock G H outer inner a s,
      (∀ i, ∀ y ∈ (blocks i).points, floor < y) ∧
      ∀ i j, i < j → ∀ x ∈ (blocks i).points, ∀ y ∈ (blocks j).points,
        x < y ∧ (colorGraph G H outer).Adj x y := by
  classical
  let chooseNext (i : W1)
      (previous : ∀ j, j < i → SmallBlock G H outer inner a s) :
      SmallBlock G H outer inner a s :=
    (exists_next_block ha outer inner s hs hsBelow i previous floor hfloor).choose
  let blocks : W1 → SmallBlock G H outer inner a s := WellFoundedLT.fix chooseNext
  have heq (i : W1) : blocks i = chooseNext i (fun j _ => blocks j) := by
    exact WellFoundedLT.fix_eq chooseNext i
  have hspec (i : W1) :
      (∀ y ∈ (blocks i).points, floor < y) ∧
      ∀ j, j < i → ∀ x ∈ (blocks j).points, ∀ y ∈ (blocks i).points,
        x < y ∧ (colorGraph G H outer).Adj x y := by
    have h := (exists_next_block ha outer inner s hs hsBelow i
      (fun j _ => blocks j) floor hfloor).choose_spec
    change (∀ y ∈ (chooseNext i (fun j _ => blocks j)).points, floor < y) ∧
      (∀ j, j < i → ∀ x ∈ (blocks j).points,
        ∀ y ∈ (chooseNext i (fun j _ => blocks j)).points,
          x < y ∧ (colorGraph G H outer).Adj x y) at h
    rwa [← heq i] at h
  exact ⟨blocks, fun i => (hspec i).1, fun i j hij => (hspec j).2 i hij⟩

end Erdos1172NeighborhoodMixedBlocks
