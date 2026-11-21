/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaTwo

@[expose] public section

/-!
Internal CH in terms of the concrete Hartogs omega-one name.  The comparison
`larger_than X Y` in Flypitch means a partial surjection from X onto Y, so its
orientation is opposite to `injects_into`.  For ordinal X the converse is
proved below by constructing the graph which selects the least preimage.
No use is made of the upstream `Card` predicate.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCHHartogs

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

private theorem mem_comprehend_and {P : bSet 𝔹 → 𝔹} (hP : B_ext P)
    {S z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ comprehend P S ↔ Γ ≤ z ∈ᴮ S ∧ Γ ≤ P z := by
  rw [mem_comprehend_iff₂ P S hP]
  constructor
  · intro H
    constructor
    · apply H.trans
      apply iSup_le; intro w
      exact bv_rw' (x := z) (y := w) (ϕ := fun z => z ∈ᴮ S)
        (inf_le_right.trans inf_le_left)
        (h_congr := B_ext_mem_left) (H_new := inf_le_left)
    · apply H.trans
      apply iSup_le; intro w
      exact bv_rw' (inf_le_right.trans inf_le_left)
        (h_congr := hP) (H_new := inf_le_right.trans inf_le_right)
  · rintro ⟨Hz, HP⟩
    exact le_iSup_of_le z (le_inf Hz (le_inf bv_refl HP))

/-- Separation inside a product realizes any extensional binary predicate. -/
noncomputable def relationGraph (A B : bSet 𝔹)
    (P : bSet 𝔹 → bSet 𝔹 → 𝔹) : bSet 𝔹 :=
  comprehend (fun z => ⨆ a, ⨆ b, z =ᴮ pair a b ⊓ P a b) (prod A B)

private theorem mem_relationGraph_iff {A B : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹}
    (hL : ∀ b, B_ext (fun a => P a b)) (hR : ∀ a, B_ext (P a))
    {a b : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair a b ∈ᴮ relationGraph A B P ↔ Γ ≤ a ∈ᴮ A ∧ Γ ≤ b ∈ᴮ B ∧ Γ ≤ P a b := by
  have hExt : B_ext (fun z : bSet 𝔹 =>
      ⨆ a', ⨆ b', z =ᴮ pair a' b' ⊓ P a' b') :=
    B_ext_iSup (h := fun _ => B_ext_iSup (h := fun _ =>
      B_ext_inf B_ext_bv_eq_left B_ext_const))
  unfold relationGraph
  rw [mem_comprehend_and hExt]
  constructor
  · rintro ⟨Hprod, HP⟩
    refine ⟨(mem_prod_iff.mp Hprod).1, (mem_prod_iff.mp Hprod).2, ?_⟩
    apply HP.trans
    apply iSup_le; intro a'
    apply iSup_le; intro b'
    exact bv_rw' (x := a) (y := a') (ϕ := fun z => P z b)
      (eq_of_eq_pair_left' inf_le_left) (h_congr := hL b)
      (H_new := bv_rw' (x := b) (y := b') (ϕ := fun z => P a' z)
        (eq_of_eq_pair_right' inf_le_left)
        (h_congr := hR a') (H_new := inf_le_right))
  · rintro ⟨Ha, Hb, HP⟩
    exact ⟨mem_prod_iff.mpr ⟨Ha, Hb⟩, le_iSup_of_le a (le_iSup_of_le b (le_inf bv_refl HP))⟩

/-- Being the least member of the indicated fiber of a relation. -/
def leastPreimage (S f y x : bSet 𝔹) : 𝔹 :=
  (x ∈ᴮ S ⊓ pair x y ∈ᴮ f) ⊓
    ⨅ z, (z ∈ᴮ S ⊓ pair z y ∈ᴮ f) ⟹ (z ∈ᴮ x)ᶜ

private theorem leastPreimage_ext_left (S f x : bSet 𝔹) :
    B_ext (fun y => leastPreimage S f y x) := by
  unfold leastPreimage
  exact B_ext_inf (B_ext_inf B_ext_const B_ext_pair_mem_right)
    (B_ext_iInf (h := fun _ => B_ext_imp
      (h₁ := B_ext_inf B_ext_const B_ext_pair_mem_right) (h₂ := B_ext_const)))

private theorem leastPreimage_ext_right (S f y : bSet 𝔹) : B_ext (leastPreimage S f y) := by
  unfold leastPreimage
  exact B_ext_inf (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    (B_ext_iInf (h := fun _ => B_ext_imp
      (h₁ := B_ext_const) (h₂ := B_ext_neg (h := B_ext_mem_right))))

private theorem leastPreimage_unique {X S f y x₁ x₂ : bSet 𝔹} {Γ : 𝔹}
    (HOrd : Γ ≤ Ord X) (H₁ : Γ ≤ x₁ ∈ᴮ X) (H₂ : Γ ≤ x₂ ∈ᴮ X)
    (HP₁ : Γ ≤ leastPreimage S f y x₁)
    (HP₂ : Γ ≤ leastPreimage S f y x₂) : Γ ≤ x₁ =ᴮ x₂ := by
  apply Ord.eq_of_not_mem (Ord_of_mem_Ord H₁ HOrd) (Ord_of_mem_Ord H₂ HOrd)
  · exact (le_inf (HP₂.trans (inf_le_right.trans (iInf_le _ x₁)))
      (HP₁.trans inf_le_left)).trans bv_imp_elim
  · exact (le_inf (HP₁.trans (inf_le_right.trans (iInf_le _ x₂)))
      (HP₂.trans inf_le_left)).trans bv_imp_elim

/-- Every nonempty fiber inside an ordinal has a least member, internally. -/
private theorem exists_leastPreimage {X S Y f y : bSet 𝔹} {Γ : 𝔹}
    (HOrd : Γ ≤ Ord X) (Hsub : Γ ≤ S ⊆ᴮ X)
    (Hsurj : Γ ≤ is_surj S Y f) (Hy : Γ ≤ y ∈ᴮ Y) :
    Γ ≤ ⨆ x, x ∈ᴮ X ⊓ leastPreimage S f y x := by
  let U := comprehend (fun x => pair x y ∈ᴮ f) S
  have hU {z : bSet 𝔹} {Δ : 𝔹} :
      Δ ≤ z ∈ᴮ U ↔ Δ ≤ z ∈ᴮ S ∧ Δ ≤ pair z y ∈ᴮ f :=
    mem_comprehend_and B_ext_pair_mem_left
  have HUsub : Γ ≤ U ⊆ᴮ X := subset_trans' (comprehend_subset S) Hsub
  have Hex : Γ ≤ ⨆ x, x ∈ᴮ S ⊓ pair x y ∈ᴮ f :=
    (le_inf (Hsurj.trans (iInf_le _ y)) Hy).trans bv_imp_elim
  have HUne : Γ ≤ (U =ᴮ ∅)ᶜ := by
    apply nonempty_of_exists_mem
    apply Hex.trans
    apply iSup_le; intro x
    exact le_iSup_of_le x (hU.mpr ⟨inf_le_left, inf_le_right⟩)
  have Hwf : Γ ≤ epsilon_well_founded X := HOrd.trans (inf_le_left.trans inf_le_right)
  have Hmin : Γ ≤ ⨆ x, x ∈ᴮ U ⊓
      ⨅ z, z ∈ᴮ U ⟹ (z ∈ᴮ x)ᶜ :=
    (le_inf ((le_inf (Hwf.trans (iInf_le _ U)) HUsub).trans bv_imp_elim) HUne).trans bv_imp_elim
  apply le_trans (le_inf Hmin le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro x
  have HxU : (x ∈ᴮ U ⊓ (⨅ z, z ∈ᴮ U ⟹ (z ∈ᴮ x)ᶜ)) ⊓ Γ ≤ x ∈ᴮ U := inf_le_left.trans inf_le_left
  apply le_iSup_of_le x
  refine le_inf (mem_of_mem_subset (inf_le_right.trans HUsub) HxU) ?_
  refine le_inf (le_inf (hU.mp HxU).1 (hU.mp HxU).2) ?_
  apply le_iInf; intro z; rw [← deduction]
  exact (le_inf
    (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans (iInf_le _ z))))
    (hU.mpr ⟨inf_le_right.trans inf_le_left, inf_le_right.trans inf_le_right⟩)).trans bv_imp_elim

/-- The least-preimage graph is an actual internal injection into the ordinal. -/
theorem injects_into_of_partial_surjection_ordinal {X S Y f : bSet 𝔹} {Γ : 𝔹}
    (HOrd : Γ ≤ Ord X) (Hsub : Γ ≤ S ⊆ᴮ X)
    (Hfunc : Γ ≤ is_func' S Y f) (Hsurj : Γ ≤ is_surj S Y f) :
    Γ ≤ injects_into Y X := by
  let g := relationGraph Y X (leastPreimage S f)
  have hg {y x : bSet 𝔹} {Δ : 𝔹} :
      Δ ≤ pair y x ∈ᴮ g ↔ Δ ≤ y ∈ᴮ Y ∧ Δ ≤ x ∈ᴮ X ∧ Δ ≤ leastPreimage S f y x :=
    mem_relationGraph_iff (leastPreimage_ext_left S f) (leastPreimage_ext_right S f)
  apply le_iSup_of_le g
  refine le_inf (le_inf ?_ ?_) ?_
  · -- Least preimages of equal outputs coincide.
    apply le_iInf; intro y₁; apply le_iInf; intro y₂
    apply le_iInf; intro x₁; apply le_iInf; intro x₂
    rw [← deduction, ← deduction]
    let Δ := (Γ ⊓ (pair y₁ x₁ ∈ᴮ g ⊓ pair y₂ x₂ ∈ᴮ g)) ⊓ y₁ =ᴮ y₂
    have H₁ : Δ ≤ pair y₁ x₁ ∈ᴮ g := inf_le_left.trans (inf_le_right.trans inf_le_left)
    have H₂ : Δ ≤ pair y₂ x₂ ∈ᴮ g := inf_le_left.trans (inf_le_right.trans inf_le_right)
    exact leastPreimage_unique (inf_le_left.trans (inf_le_left.trans HOrd))
      (hg.mp H₁).2.1 (hg.mp H₂).2.1 (hg.mp H₁).2.2
      (bv_rw' (x := y₁) (y := y₂) (ϕ := fun y => leastPreimage S f y x₂)
        inf_le_right (h_congr := leastPreimage_ext_left S f x₂)
        (H_new := (hg.mp H₂).2.2))
  · -- Each point of Y has a least preimage.
    apply le_iInf; intro y; rw [← deduction]
    have Hmin := exists_leastPreimage (inf_le_left.trans HOrd)
      (inf_le_left.trans Hsub) (inf_le_left.trans Hsurj)
      (show Γ ⊓ y ∈ᴮ Y ≤ y ∈ᴮ Y from inf_le_right)
    apply le_trans (le_inf Hmin le_rfl)
    rw [iSup_inf_eq']; apply iSup_le; intro x
    apply le_iSup_of_le x
    exact le_inf (inf_le_left.trans inf_le_left)
      (hg.mpr ⟨inf_le_right.trans inf_le_right,
        inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right⟩)
  · -- Functionality of the original surjection makes the selection injective.
    apply le_iInf; intro y₁; apply le_iInf; intro y₂
    apply le_iInf; intro x₁; apply le_iInf; intro x₂
    rw [← deduction]
    let Δ := Γ ⊓ (pair y₁ x₁ ∈ᴮ g ⊓ pair y₂ x₂ ∈ᴮ g ⊓ x₁ =ᴮ x₂)
    have H₁ : Δ ≤ pair y₁ x₁ ∈ᴮ g := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have H₂ : Δ ≤ pair y₂ x₂ ∈ᴮ g := inf_le_right.trans (inf_le_left.trans inf_le_right)
    exact eq_of_is_func'_of_eq (inf_le_left.trans Hfunc)
      (inf_le_right.trans inf_le_right)
      ((hg.mp H₁).2.2.trans (inf_le_left.trans inf_le_right))
      ((hg.mp H₂).2.2.trans (inf_le_left.trans inf_le_right))

/-- Partial surjections out of an ordinal have injective right inverses. -/
theorem injects_into_of_larger_than_ordinal {X Y : bSet 𝔹} {Γ : 𝔹}
    (HOrd : Γ ≤ Ord X) (Hlarge : Γ ≤ larger_than X Y) :
    Γ ≤ injects_into Y X := by
  unfold larger_than at Hlarge
  apply le_trans (le_inf Hlarge le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro S
  rw [iSup_inf_eq']; apply iSup_le; intro f
  exact injects_into_of_partial_surjection_ordinal (inf_le_right.trans HOrd)
    (inf_le_left.trans (inf_le_left.trans inf_le_left))
    (inf_le_left.trans (inf_le_left.trans inf_le_right))
    (inf_le_left.trans inf_le_right)

/-- An injection always yields a partial surjection in the reverse direction. -/
theorem larger_than_of_injects_into {X Y : bSet 𝔹} {Γ : 𝔹}
    (Hinj : Γ ≤ injects_into X Y) : Γ ≤ larger_than Y X := by
  simp only [larger_than, injects_into] at *
  apply le_trans (le_inf Hinj le_rfl)
  rw [iSup_inf_eq']; apply iSup_le; intro f
  apply le_iSup_of_le (image X Y f)
  apply le_iSup_of_le (inj_inverse
    (inf_le_left.trans inf_le_left : _ ≤ is_func' X Y f)
    (inf_le_left.trans inf_le_right : _ ≤ is_inj f))
  refine le_inf (le_inf image_subset (le_inf ?_ ?_)) ?_
  · exact inj_inverse_is_func (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
  · exact inj_inverse_is_total (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
  · exact inj_inverse_is_surj (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)

open ErdosOmegaTwo

theorem omegaOne_not_countable {Γ : 𝔹} : Γ ≤ (larger_than bSet.omega (omegaOne : bSet 𝔹))ᶜ := by
  rw [← imp_bot, ← deduction]
  exact bv_absurd _ (injects_into_of_larger_than_ordinal Ord_omega inf_le_right)
    omegaOne_not_injects

/-- CH's cardinal upper bound uses the actual internal Hartogs omega-one. -/
theorem CH₂_iff_powerset_omega_injects_omegaOne {Γ : 𝔹} :
    Γ ≤ CH₂ ↔ Γ ≤ injects_into (bv_powerset bSet.omega) (omegaOne : bSet 𝔹) := by
  constructor
  · intro HCH
    apply injects_into_of_larger_than_ordinal omegaOne_Ord
    rw [← compl_compl (larger_than (omegaOne : bSet 𝔹) (bv_powerset bSet.omega))]
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    apply bv_absurd _ ?_ (inf_le_left.trans HCH)
    apply le_iSup_of_le (omegaOne : bSet 𝔹)
    exact le_inf (le_inf omegaOne_Ord omegaOne_not_countable) inf_le_right
  · intro Hinj
    change Γ ≤ (⨆ x : bSet 𝔹, Ord x ⊓ (larger_than bSet.omega x)ᶜ ⊓
      (larger_than x (bv_powerset bSet.omega))ᶜ)ᶜ
    rw [← imp_bot, ← deduction, inf_iSup_eq']
    apply iSup_le; intro x
    let Δ := Γ ⊓ (Ord x ⊓ (larger_than bSet.omega x)ᶜ ⊓ (larger_than x (bv_powerset bSet.omega))ᶜ)
    have HOrd : Δ ≤ Ord x := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have Hnotinj : Δ ≤ (injects_into x bSet.omega)ᶜ := by
      rw [← imp_bot, ← deduction]
      exact bv_absurd _ (larger_than_of_injects_into inf_le_right)
        (inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    have Hleast : Δ ≤ omegaOne ⊆ᴮ x := by
      have Hspec : Δ ≤ ErdosHartogs.leastNoninjectingOrdinal bSet.omega omegaOne := omegaOne_spec
      exact (le_inf ((le_inf
        (Hspec.trans (inf_le_right.trans (inf_le_right.trans (iInf_le _ x))))
        HOrd).trans bv_imp_elim) Hnotinj).trans bv_imp_elim
    have Hlarge : Δ ≤ larger_than x (bv_powerset bSet.omega) :=
      larger_than_of_injects_into
        (injects_into_trans (inf_le_left.trans Hinj) (injects_into_of_subset Hleast))
    exact bv_absurd _ Hlarge (inf_le_right.trans inf_le_right)

theorem CH_iff_powerset_omega_injects_omegaOne {Γ : 𝔹} :
    Γ ≤ CH ↔ Γ ≤ injects_into (bv_powerset bSet.omega) (omegaOne : bSet 𝔹) :=
  CH_iff_CH₂.trans CH₂_iff_powerset_omega_injects_omegaOne

end bSet.ErdosCHHartogs
