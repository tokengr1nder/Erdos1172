/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CoverProfileTools

@[expose] public section

/-!
# Assembly of monotone higher-power covers

Given the strictly lower-dimensional cofinal covers, the construction
selects endpoints by a line cover and uses one common function per row.
Every row has genuinely smaller order type; the entire assembled cover
has exactly the prescribed finite-power type and remains cofinal.
The lower-dimensional families are supplied by induction in the final
cofinal-cover theorem, not assumed there as an additional principle.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CofinalPowerCoverAssembly

open ErdosRadoCHAsym (W1)
open Erdos1172Part3CofinalLineCover (LineCoverData)
open Erdos1172Part3CofinalPowerEndpoints (below)
open Erdos1172Part3CofinalFiniteCuts (rowSection cofinal_row_type_lt typeLT_le_finite_power_of_rows_small)
open Erdos1172Part3CoverProfileTools
open Erdos1172Part3CofinalCoverSupport (FinitelySupported)

structure LowerCovers (n : ℕ) (V : Type) [LinearOrder V] [WellFoundedLT V] where
  into : V → Fin n → (W1 → W1) → Set V
  inside : ∀ y k f, into y k f ⊆ Set.Iio y
  mono : ∀ y k, Monotone (into y k)
  supported : ∀ y k, FinitelySupported (into y k)
  type_le : ∀ y k f, typeLT (into y k f) ≤
    (ω_ 1 : Ordinal.{0}) ^ ((k.val + 1 : ℕ) : Ordinal)
  covers : ∀ y k (B : Set V), B ⊆ Set.Iio y → IsCofinal (below B y) →
    typeLT (below B y) = (ω_ 1 : Ordinal.{0}) ^ ((k.val + 1 : ℕ) : Ordinal) →
      ∃ f : W1 → W1, B ⊆ into y k f

variable {V : Type} [LinearOrder V] [WellFoundedLT V] {n : ℕ}

noncomputable def addedRow (data : LineCoverData V) (L : LowerCovers n V)
    (f : Profile) (i : W1) : Set V :=
  ⋃ y ∈ (data.cover (head f) ∩ Set.Iic (data.cut i)),
    ⋃ k : Fin n, {x | data.row x = i} ∩ L.into y k (row f i)

theorem addedRow_mem_row (data : LineCoverData V) (L : LowerCovers n V)
    (f : Profile) (i : W1) {x : V} (hx : x ∈ addedRow data L f i) : data.row x = i := by
  obtain ⟨y, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hx
  exact hx.1

theorem addedRow_mono (data : LineCoverData V) (L : LowerCovers n V) (i : W1) :
    Monotone (fun f => addedRow data L f i) := by
  intro f g hfg x hx
  obtain ⟨y, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hy, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨k, hx⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr
    ⟨⟨data.cover_mono (fun j => hfg (Sum.inl j)) hy.1, hy.2⟩,
      Set.mem_iUnion.mpr ⟨k, hx.1, L.mono y k (fun j => hfg (Sum.inr (i, j))) hx.2⟩⟩⟩

theorem addedRow_type_lt (data : LineCoverData V) (L : LowerCovers n V)
    (f : Profile) (i : W1) :
    typeLT (addedRow data L f i) < (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
  apply Erdos1172Part3FiniteOrderTypeIdeal.countable_biUnion_type_lt_finite_power n
    (data.cover (head f) ∩ Set.Iic (data.cut i))
    (line_closed_prefix_countable data (head f) (data.cut i))
  intro y _
  apply countable_iUnion_type_lt n
  intro k
  exact ((Ordinal.type_mono (Set.inter_subset_right :
    ({x : V | data.row x = i} ∩ L.into y k (row f i) : Set V) ⊆ L.into y k (row f i))).trans
      (L.type_le y k (row f i))).trans_lt (lower_power_lt n k.val k.isLt)

theorem addedRow_supported (data : LineCoverData V) (L : LowerCovers n V) (i : W1) :
    FinitelySupported (fun f => addedRow data L f i) := by
  classical
  intro f x hx
  obtain ⟨y, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hy, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨k, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨s, hs⟩ := Erdos1172Part3CofinalCoverSupport.line_supported data (head f) y hy.1
  obtain ⟨t, ht⟩ := L.supported y k (row f i) x hx.2
  refine ⟨s.image Sum.inl ∪ t.image (fun j => Sum.inr (i, j)), fun g hg => ?_⟩
  have hhead : y ∈ data.cover (head g) := hs (head g) (fun j hj =>
    hg (Sum.inl j) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)))
  have hlocal : x ∈ L.into y k (row g i) := ht (row g i) (fun j hj =>
    hg (Sum.inr (i, j)) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)))
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨⟨hhead, hy.2⟩,
    Set.mem_iUnion.mpr ⟨k, hx.1, hlocal⟩⟩⟩

noncomputable def cover (data : LineCoverData V) (L : LowerCovers n V)
    (seed : Set V) (f : Profile) : Set V :=
  seed ∪ (data.cover (head f) ∪ ⋃ i : W1, addedRow data L f i)

theorem cover_mono (data : LineCoverData V) (L : LowerCovers n V) (seed : Set V) :
    Monotone (cover data L seed) := by
  intro f g hfg x hx
  rcases hx with hx | hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inl (data.cover_mono (fun j => hfg (Sum.inl j)) hx))
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨i, addedRow_mono data L i hfg hi⟩))

theorem cover_cofinal (data : LineCoverData V) (L : LowerCovers n V) (seed : Set V)
    (hseed : IsCofinal seed) (f : Profile) : IsCofinal (cover data L seed f) :=
  hseed.mono Set.subset_union_left

theorem cover_supported (data : LineCoverData V) (L : LowerCovers n V) (seed : Set V) :
    FinitelySupported (cover data L seed) := by
  apply Erdos1172Part3CofinalCoverSupport.union_supported
  · exact Erdos1172Part3CofinalCoverSupport.constant_supported seed
  · apply Erdos1172Part3CofinalCoverSupport.union_supported
    · exact Erdos1172Part3CofinalCoverSupport.precompose_supported Sum.inl data.cover
        (Erdos1172Part3CofinalCoverSupport.line_supported data)
    · exact Erdos1172Part3CofinalCoverSupport.iUnion_supported
        (fun i f => addedRow data L f i) (addedRow_supported data L)

theorem cover_type (data : LineCoverData V) (L : LowerCovers n V) (seed : Set V)
    (hseed : IsCofinal seed)
    (htype : typeLT seed = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) (f : Profile) :
    typeLT (cover data L seed f) = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
  apply le_antisymm
  · apply typeLT_le_finite_power_of_rows_small data n
    intro i
    have hseedRow : typeLT (rowSection data seed i) <
        (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) :=
      (cofinal_row_type_lt data seed hseed i).trans_eq htype
    have hlineCount : (rowSection data (data.cover (head f)) i).Countable := by
      apply (data.cover_prefix_countable (head f) (data.cut i)).mono
      intro x hx
      exact ⟨hx.1, hx.2 ▸ data.lt_cut_row x⟩
    have hlineRow := (countable_type_lt_omegaOne _ hlineCount).trans_le (omegaOne_le_power n)
    have hsmall := union_type_lt n hseedRow (union_type_lt n hlineRow (addedRow_type_lt data L f i))
    apply (Ordinal.type_mono (show rowSection data (cover data L seed f) i ⊆
      rowSection data seed i ∪ (rowSection data (data.cover (head f)) i ∪ addedRow data L f i)
      from ?_)).trans_lt hsmall
    intro x hx
    rcases hx.1 with hseedx | hlinex | hadded
    · exact Or.inl ⟨hseedx, hx.2⟩
    · exact Or.inr (Or.inl ⟨hlinex, hx.2⟩)
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hadded
      have heq : j = i := (addedRow_mem_row data L f j hj).symm.trans hx.2
      exact Or.inr (Or.inr (heq ▸ hj))
  · rw [← htype]
    exact Ordinal.type_mono (Set.subset_union_left : seed ⊆ cover data L seed f)

end Erdos1172Part3CofinalPowerCoverAssembly
