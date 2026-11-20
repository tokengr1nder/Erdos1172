/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanSeedKernelName
public import Erdos1172.Part4InternalOmegaOneCountablyBounded
public import Erdos1172.Part4InternalIdealNormality

@[expose] public section

/-! # Countable and diagonal closure for a seed-derived kernel

The lifting laws here concern the action on names. A countable family in
the source has its image covered by images of source members. Elements of
the seed are locally images of source ordinals below the carrier. These
two distinct covering properties account for the two closure operations.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u v

namespace bSet.ErdosSeedKernel

open ErdosIdeal ErdosOmegaTwo

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable (e : CompleteLatticeHom B C) (j : bSet B → bSet C) (s : bSet C)
variable (hEq : ∀ X Y, e (X =ᴮ Y) ≤ (j X =ᴮ j Y))

private theorem split_cover {I : Type v} {D t : C} {f : I → C}
    (h : D ≤ ⨆ i, f i) (hpiece : ∀ i, D ⊓ f i ≤ t) : D ≤ t := by
  apply (le_inf (le_refl D) h).trans
  rw [inf_iSup_eq]
  exact iSup_le hpiece

include hEq in
private theorem seed_piece_vanishes {K X : bSet B} {Δ : B} {d : C}
    (hsmall : Δ ≤ X ∈ᴮ seedKernelName e j s K)
    (hΔ : d ≤ e Δ) (hs : d ≤ s ∈ᴮ j X) : d ≤ ⊥ :=
  (le_inf hΔ hs).trans_eq ((mem_seedKernelName_iff e j s hEq).mp hsmall).2

include hEq in
/-- Every countable subset of omega-one is bounded at the same condition.
Being above the images of its proper initial segments suffices for absorption. -/
theorem seedKernelName_countableAbsorption {Γ : B}
    (hSub : ∀ X Y, e (X ⊆ᴮ Y) ≤ (j X ⊆ᴮ j Y))
    (hBound : ∀ b : bSet B, e (Γ ⊓ b ∈ᴮ omegaOne) ≤ (s ∈ᴮ j b)ᶜ) :
    Γ ≤ countableAbsorption omegaOne (seedKernelName e j s omegaOne) := by
  apply le_iInf; intro A
  rw [← deduction]
  let Δ := Γ ⊓ (A ⊆ᴮ omegaOne ⊓ injects_into A omega)
  have hA : Δ ≤ A ⊆ᴮ omegaOne := inf_le_right.trans inf_le_left
  obtain ⟨b, hb⟩ := ErdosOmegaOneCountablyBounded.exists_bound_of_countable hA
    (inf_le_right.trans inf_le_right)
  apply (mem_seedKernelName_iff e j s hEq).mpr
  refine ⟨hA, bot_unique ?_⟩
  have hmem : e Δ ⊓ (s ∈ᴮ j A) ≤ s ∈ᴮ j b := mem_of_mem_subset
    (inf_le_left.trans ((OrderHomClass.mono e (hb.trans inf_le_right)).trans (hSub A b))) inf_le_right
  exact bv_absurd _ hmem (inf_le_left.trans ((OrderHomClass.mono e
    (le_inf (show Δ ≤ Γ from inf_le_left) (hb.trans inf_le_left))).trans (hBound b)))

include hEq in
/-- Union preservation and the pointwise-image property for countable
families imply closure under unions of all internally countable families. -/
theorem seedKernelName_countableClosure (K : bSet B) {Γ : B}
    (hUnion : ∀ F : bSet B, e Γ ≤ j (bv_union F) ⊆ᴮ bv_union (j F))
    (hCount : ∀ (F : bSet B) (y : bSet C), e (Γ ⊓ injects_into F omega) ⊓ (y ∈ᴮ j F) ≤
      ⨆ x : bSet B, e (x ∈ᴮ F) ⊓ (y =ᴮ j x)) :
    Γ ≤ countableClosure (seedKernelName e j s K) := by
  let J := seedKernelName e j s K
  apply le_iInf; intro F
  rw [← deduction]
  let Δ := Γ ⊓ (injects_into F omega ⊓ F ⊆ᴮ J)
  have hsmall (x : bSet B) : Δ ⊓ (x ∈ᴮ F) ≤ x ∈ᴮ J :=
    mem_of_mem_subset (inf_le_left.trans (inf_le_right.trans inf_le_right)) inf_le_right
  apply (mem_seedKernelName_iff e j s hEq).mpr
  refine ⟨ErdosInitialSegments.union_subset_of_members_subset ?_, bot_unique ?_⟩
  · apply le_iInf; intro x; rw [← deduction]
    exact ((mem_seedKernelName_iff e j s hEq).mp (hsmall x)).1
  · let d := e Δ ⊓ (s ∈ᴮ j (bv_union F))
    have hd : d ≤ s ∈ᴮ bv_union (j F) := mem_of_mem_subset
      (inf_le_left.trans ((OrderHomClass.mono e (show Δ ≤ Γ from inf_le_left)).trans (hUnion F)))
      inf_le_right
    apply split_cover ((bv_union_spec_split (j F) s).mp hd)
    intro y
    let a := d ⊓ (y ∈ᴮ j F ⊓ s ∈ᴮ y)
    have hΓ : a ≤ e (Γ ⊓ injects_into F omega) :=
      (show a ≤ e Δ from inf_le_left.trans inf_le_left).trans (OrderHomClass.mono e
        (le_inf (show Δ ≤ Γ from inf_le_left) (inf_le_right.trans inf_le_left)))
    apply split_cover ((le_inf hΓ (show a ≤ y ∈ᴮ j F from inf_le_right.trans inf_le_left)).trans (hCount F y))
    intro x
    apply seed_piece_vanishes e j s hEq (hsmall x)
    · rw [map_inf]
      exact le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) (inf_le_right.trans inf_le_left)
    · exact bv_rw'' (inf_le_right.trans inf_le_right)
        (inf_le_left.trans (inf_le_right.trans inf_le_right)) B_ext_mem_right

include hEq in
/-- Every target member of the seed is locally the image of a source
index. Applying this to the index witnessing membership in a diagonal
union supplies a single source fiber on each target Boolean piece. -/
theorem seedKernelName_diagonalClosure (K : bSet B) {Γ : B}
    (hSeed : ∀ y : bSet C, e Γ ⊓ (y ∈ᴮ s) ≤ ⨆ i : bSet B, e (i ∈ᴮ K) ⊓ (y =ᴮ j i))
    (hDiag : ∀ R, e Γ ≤ j (diagonalUnion K R) ⊆ᴮ diagonalUnion (j K) (j R))
    (hFiber : ∀ R i, e Γ ≤ fiber (j K) (j R) (j i) ⊆ᴮ j (fiber K R i)) :
    Γ ≤ diagonalClosure K (seedKernelName e j s K) := by
  let J := seedKernelName e j s K
  apply le_iInf; intro R
  rw [← deduction]
  let Δ := Γ ⊓ ⨅ i : bSet B, _root_.imp (i ∈ᴮ K) (fiber K R i ∈ᴮ J)
  have hsmall (i : bSet B) : Δ ⊓ (i ∈ᴮ K) ≤ fiber K R i ∈ᴮ J :=
    (le_inf (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) inf_le_right).trans bv_imp_elim
  apply (mem_seedKernelName_iff e j s hEq).mpr
  refine ⟨?_, bot_unique ?_⟩
  · unfold diagonalUnion
    apply comprehend_subset
  let d := e Δ ⊓ (s ∈ᴮ j (diagonalUnion K R))
  have hg : d ≤ e Γ := inf_le_left.trans (OrderHomClass.mono e (show Δ ≤ Γ from inf_le_left))
  have hd : d ≤ s ∈ᴮ diagonalUnion (j K) (j R) := mem_of_mem_subset (hg.trans (hDiag R)) inf_le_right
  rw [mem_diagonalUnion] at hd
  apply split_cover (hd.trans inf_le_right)
  intro y
  let a := d ⊓ ((y ∈ᴮ j K ⊓ y ∈ᴮ s) ⊓ pair s y ∈ᴮ j R)
  have ha : a ≤ y ∈ᴮ s := inf_le_right.trans (inf_le_left.trans inf_le_right)
  apply split_cover ((le_inf (show a ≤ e Γ from inf_le_left.trans hg) ha).trans (hSeed y))
  intro i
  let z := a ⊓ (e (i ∈ᴮ K) ⊓ y =ᴮ j i)
  apply seed_piece_vanishes e j s hEq (hsmall i)
  · rw [map_inf]
    exact le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) (inf_le_right.trans inf_le_left)
  · have hp : z ≤ pair s (j i) ∈ᴮ j R := bv_rw'' (ϕ := fun t => pair s t ∈ᴮ j R)
        (inf_le_right.trans inf_le_right)
        (inf_le_left.trans (inf_le_right.trans inf_le_right)) B_ext_pair_mem_right
    have hf : z ≤ s ∈ᴮ fiber (j K) (j R) (j i) := by
      rw [mem_fiber]
      exact le_inf (inf_le_left.trans (inf_le_left.trans (hd.trans inf_le_left))) hp
    exact mem_of_mem_subset (inf_le_left.trans (inf_le_left.trans (hg.trans (hFiber R i)))) hf

end bSet.ErdosSeedKernel
