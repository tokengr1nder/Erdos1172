/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousCheckedSequenceReading

@[expose] public section

/-! # Reading countable subsets through the anonymous collapse

A supported enumeration of a nonempty countable subset has a reading through
the anonymous algebra. Bounded images commute with the complete inclusion,
so its range gives an anonymous name for the original subset on each piece.
-/

set_option autoImplicit false

noncomputable section
open scoped Flypitch
open Lattice
universe u

namespace bSet.ErdosNameTransport

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B]
  [NontrivialCompleteBooleanAlgebra C]

private theorem image_mk_bounded {I J : Type u} (x : I → bSet B)
    (b : I → B) (y : J → bSet B) (c : J → B) (f : bSet B) :
    image (.mk I x b) (.mk J y c) f =
      .mk J y (fun j => (⨆ i, b i ⊓ (pair (x i) (y j) ∈ᴮ f)) ⊓ c j) := by
  unfold image subset.mk set_of_indicator
  congr 1
  funext j
  exact congrArg (· ⊓ c j)
    (@bounded_exists B _ (.mk I x b) (fun z => pair z (y j) ∈ᴮ f)
      (h_congr := B_ext_pair_mem_left)).symm

theorem map_bounded_image (e : CompleteLatticeHom B C) (x y f : bSet B) :
    mapNames e (image x y f) = image (mapNames e x) (mapNames e y) (mapNames e f) := by
  cases x
  cases y
  simp only [image_mk_bounded, mapNames_mk, map_iSup, map_inf, map_mem, map_pair]

end bSet.ErdosNameTransport

namespace Erdos1172LevyCohen
open bSet ErdosNameTransport Erdos1172CompleteSubalgebra

theorem ordinalRect_separated (δ α : Ordinal.{u}) :
    let A := PSet.pSet_prod (PSet.ordinalMk δ) (PSet.ordinalMk α)
    ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j) := by
  intro A i j hne he
  obtain ⟨h₁,h₂⟩ := PSet.equiv_iff_eq_pSet_pair.mpr he
  apply hne
  apply Prod.ext
  · by_contra h
    exact PSet.ordinalMk_inj δ _ _ h h₁
  · by_contra h
    exact PSet.ordinalMk_inj α _ _ h h₂

private theorem eq_image_of_surjection {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {P X A f : bSet B} {Γ : B} (hX : Γ ≤ X ⊆ᴮ A)
    (hf : Γ ≤ is_function P X f) (hs : Γ ≤ is_surj P X f) :
    Γ ≤ X =ᴮ image P A f := by
  apply mem_ext
  · apply le_iInf
    intro z
    rw [← deduction]
    exact mem_image_iff.mpr ⟨mem_of_mem_subset (inf_le_left.trans hX) inf_le_right,
      (le_inf (inf_le_left.trans (hs.trans (iInf_le _ z))) inf_le_right).trans bv_imp_elim⟩
  · apply le_iInf
    intro z
    rw [← deduction]
    have h := (mem_image_iff.mp (show Γ ⊓ (z ∈ᴮ image P A f) ≤ z ∈ᴮ image P A f
      from inf_le_right)).2
    obtain ⟨w, hw⟩ := exists_convert h (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_right_of_prod_mem (mem_of_mem_subset
      (inf_le_left.trans (subset_prod_of_is_function hf)) (hw.trans inf_le_right))

theorem anonymous_countable_subset_reading_cover (κ : Cardinal.{u})
    (hκ : κ.IsRegular) (hunc : Cardinal.aleph0 < κ) (A : PSet.{u})
    (hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    {X : bSet (Algebra κ)} {Γ : Algebra κ} (hX : Γ ≤ X ⊆ᴮ check A)
    (hc : Γ ≤ injects_into X omega) :
    Γ ≤ ⨆ Y : bSet (anonymousAlgebra κ), X =ᴮ mapNames (inclusion (anonymousAlgebra κ)) Y := by
  let empty := X =ᴮ ∅
  have split : Γ = (Γ ⊓ empty) ⊔ (Γ ⊓ emptyᶜ) := by
    exact (inf_top_eq Γ).symm.trans ((congrArg (Γ ⊓ ·) (sup_compl_eq_top (x := empty)).symm).trans
      (inf_sup_left Γ empty emptyᶜ))
  apply split.le.trans
  apply sup_le
  · apply le_iSup_of_le ∅
    rw [map_empty]
    exact inf_le_right
  · let Δ := Γ ⊓ emptyᶜ
    have honto := surjects_onto_of_injects_into' (inf_le_left.trans hc : Δ ≤ injects_into X omega)
      (exists_mem_of_nonempty X inf_le_right)
    apply (le_inf le_rfl honto).trans
    erw [inf_iSup_eq]
    apply iSup_le
    intro f
    let Ψ := Δ ⊓ (is_func' omega X f ⊓ is_surj omega X f)
    have hsub : Ψ ≤ X ⊆ᴮ check A := inf_le_left.trans (inf_le_left.trans hX)
    have hweak : Ψ ≤ is_func' omega X f := inf_le_right.trans inf_le_left
    have hfun := function_of_func'_is_function hweak
    have hrange := eq_image_of_surjection hsub hfun
      (function_of_func'_surj_of_surj hweak (inf_le_right.trans inf_le_right))
    have hread := anonymous_checked_sequence_reading_cover κ hκ hunc A hsep
      (ErdosIndependentHomogeneous.is_function_codomain_mono hsub hfun)
    apply (le_inf le_rfl hread).trans
    erw [inf_iSup_eq]
    apply iSup_le
    intro g
    apply le_iSup_of_le (image omega (check A) g)
    rw [map_bounded_image]
    simp only [omega, map_check]
    exact bv_trans (inf_le_left.trans hrange)
      (B_congr_image_right (inf_le_right.trans inf_le_right))

end Erdos1172LevyCohen
