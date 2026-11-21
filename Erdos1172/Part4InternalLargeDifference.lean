/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaTwoPigeonhole
public import Erdos1172.Part4InternalIdealSemantics

@[expose] public section

/-!
Removing an internally omega-one-small set preserves omega-two-largeness
under internal CH. All sets and selector graphs are arbitrary Boolean names.
No containment, nonemptiness, or checked-ground-name restriction is imposed.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosLargeDifference

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosFiberInjection ErdosIdeal ErdosRelationGraph

theorem zero_mem_omegaOne {Γ : 𝔹} : Γ ≤ (0 : bSet 𝔹) ∈ᴮ omegaOne :=
  mem_of_mem_subset
    (subset_of_mem_transitive (omegaOne_Ord.trans inf_le_right)
      (le_top.trans one_mem_omegaOne)) zero_mem_one

/-- Label zero records membership; a nonzero label records nonmembership. -/
def membershipCode (L x i : bSet 𝔹) : 𝔹 :=
  _root_.imp (i =ᴮ 0) (x ∈ᴮ L) ⊓ _root_.imp (x ∈ᴮ L) (i =ᴮ 0)

def codesMembership (S L f : bSet 𝔹) : 𝔹 :=
  ⨅ x, ⨅ i, _root_.imp (x ∈ᴮ S ⊓ pair x i ∈ᴮ f) (membershipCode L x i)

theorem membershipCode_ext_left (L i : bSet 𝔹) :
    B_ext (fun x => membershipCode L x i) :=
  B_ext_inf (B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_mem_left))
    (B_ext_imp (h₁ := B_ext_mem_left) (h₂ := B_ext_const))

theorem membershipCode_ext_right (L x : bSet 𝔹) :
    B_ext (membershipCode L x) :=
  B_ext_inf (B_ext_imp (h₁ := B_ext_bv_eq_left) (h₂ := B_ext_const))
    (B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_bv_eq_left))

theorem membershipCode_zero {L x : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ L) : Γ ≤ membershipCode L x 0 := by
  refine le_inf ?_ ?_
  · rw [← deduction]
    exact inf_le_left.trans Hx
  · rw [← deduction]
    exact bv_refl

theorem membershipCode_one {L x : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ (x ∈ᴮ L)ᶜ) : Γ ≤ membershipCode L x 1 := by
  refine le_inf ?_ ?_
  · rw [← deduction]
    exact (bot_of_zero_eq_one (bv_symm inf_le_right)).trans bot_le
  · rw [← deduction]
    exact (bv_absurd _ inf_le_right (inf_le_left.trans Hx)).trans bot_le

theorem codesMembership_apply {S L f x i : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ codesMembership S L f) (Hx : Γ ≤ x ∈ᴮ S)
    (Hxi : Γ ≤ pair x i ∈ᴮ f) : Γ ≤ membershipCode L x i :=
  (le_inf (H.trans ((iInf_le _ x).trans (iInf_le _ i))) (le_inf Hx Hxi)).trans bv_imp_elim

/-- Bounded internal choice constructs one actual membership selector. -/
theorem exists_membership_selector (S L : bSet 𝔹) {Γ : 𝔹} :
    ∃ f : bSet 𝔹, Γ ≤ is_function S omegaOne f ⊓ codesMembership S L f := by
  apply ErdosSmallFiberBound.exists_selector_of_pointwise
    (membershipCode_ext_left L) (membershipCode_ext_right L)
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ S
  calc
    Δ = (Δ ⊓ x ∈ᴮ L) ⊔ (Δ ⊓ (x ∈ᴮ L)ᶜ) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
    _ ≤ ⨆ i, i ∈ᴮ omegaOne ⊓ membershipCode L x i := by
      apply sup_le
      · exact le_iSup_of_le 0 (le_inf zero_mem_omegaOne (membershipCode_zero inf_le_right))
      · exact le_iSup_of_le 1
          (le_inf (le_top.trans one_mem_omegaOne) (membershipCode_one inf_le_right))

theorem fiber_subset_of_zero {S L f i : bSet 𝔹} {Γ : 𝔹}
    (Hcode : Γ ≤ codesMembership S L f) (Hi : Γ ≤ i =ᴮ 0) :
    Γ ≤ fiber S f i ⊆ᴮ L := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  have Hx := mem_fiber_iff.mp (show Γ ⊓ x ∈ᴮ fiber S f i ≤ x ∈ᴮ fiber S f i from inf_le_right)
  have Hc := codesMembership_apply (inf_le_left.trans Hcode) Hx.1 Hx.2
  exact (le_inf (Hc.trans inf_le_left) (inf_le_left.trans Hi)).trans bv_imp_elim

theorem fiber_subset_difference_of_not_zero {S L f i : bSet 𝔹} {Γ : 𝔹}
    (Hcode : Γ ≤ codesMembership S L f) (Hi : Γ ≤ (i =ᴮ 0)ᶜ) :
    Γ ≤ fiber S f i ⊆ᴮ difference S L := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction, mem_difference]
  have Hx := mem_fiber_iff.mp (show Γ ⊓ x ∈ᴮ fiber S f i ≤ x ∈ᴮ fiber S f i from inf_le_right)
  have Hc := codesMembership_apply (inf_le_left.trans Hcode) Hx.1 Hx.2
  refine le_inf Hx.1 ?_
  rw [← imp_bot, ← deduction]
  have Hz : (Γ ⊓ x ∈ᴮ fiber S f i) ⊓ x ∈ᴮ L ≤ i =ᴮ 0 :=
    (le_inf (inf_le_left.trans (Hc.trans inf_le_right)) inf_le_right).trans bv_imp_elim
  exact bv_absurd _ Hz (inf_le_left.trans (inf_le_left.trans Hi))

/-- Removing an omega-one-small name preserves full omega-two-largeness. -/
theorem omegaTwo_injects_difference {S L : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ injects_into omegaTwo S)
    (HL : Γ ≤ injects_into L omegaOne) :
    Γ ≤ injects_into omegaTwo (difference S L) := by
  obtain ⟨f, Hf⟩ := exists_membership_selector S L (Γ := Γ)
  have Hfound := ErdosOmegaTwoPigeonhole.omegaTwo_pigeonhole_of_large_domain
    HCH (Hf.trans inf_le_left) HS
  apply (le_inf (le_refl Γ) Hfound).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  let Δ := Γ ⊓ (i ∈ᴮ omegaOne ⊓ injects_into omegaTwo (fiber S f i))
  have Hlarge : Δ ≤ injects_into omegaTwo (fiber S f i) := inf_le_right.trans inf_le_right
  have Hcode : Δ ≤ codesMembership S L f := inf_le_left.trans (Hf.trans inf_le_right)
  have Hnonzero : Δ ≤ (i =ᴮ 0)ᶜ := by
    rw [← imp_bot, ← deduction]
    have Hsub : Δ ⊓ (i =ᴮ 0) ≤ fiber S f i ⊆ᴮ L :=
      fiber_subset_of_zero (inf_le_left.trans Hcode) inf_le_right
    have Hbad : Δ ⊓ (i =ᴮ 0) ≤ injects_into omegaTwo omegaOne :=
      injects_into_trans (inf_le_left.trans Hlarge)
        (injects_into_trans (injects_into_of_subset Hsub)
          (inf_le_left.trans (inf_le_left.trans HL)))
    exact bv_absurd _ Hbad omegaTwo_not_injects
  exact injects_into_trans Hlarge
    (injects_into_of_subset (fiber_subset_difference_of_not_zero Hcode Hnonzero))

/-- A singleton injects into every inhabited internal set, by an actual
constant graph whose singleton domain makes it injective. -/
theorem singleton_injects_of_mem {a b B : bSet 𝔹} {Γ : 𝔹}
    (Hb : Γ ≤ b ∈ᴮ B) : Γ ≤ injects_into ({a} : bSet 𝔹) B := by
  let g := relationGraph ({a} : bSet 𝔹) B (fun _ y => y =ᴮ b)
  have Hfunc : Γ ≤ is_function ({a} : bSet 𝔹) B g := by
    apply relationGraph_is_function (P := fun _ y => y =ᴮ b) (fun _ => B_ext_const)
      (fun _ => B_ext_bv_eq_left)
    · apply le_iInf
      intro x
      rw [← deduction]
      exact le_iSup_of_le b (le_inf (inf_le_left.trans Hb) bv_refl)
    · intro x₁ x₂ y₁ y₂ Δ _ _ _ _ _ Hy₁ Hy₂ _
      exact bv_trans Hy₁ (bv_symm Hy₂)
  have Hinj : Γ ≤ is_inj g := by
    apply le_iInf
    intro x₁
    apply le_iInf
    intro x₂
    apply le_iInf
    intro y₁
    apply le_iInf
    intro y₂
    rw [← deduction]
    let Δ := Γ ⊓ (pair x₁ y₁ ∈ᴮ g ⊓ pair x₂ y₂ ∈ᴮ g ⊓ y₁ =ᴮ y₂)
    have Hx₁ : Δ ≤ x₁ ∈ᴮ ({a} : bSet 𝔹) :=
      mem_domain_of_is_function
        (inf_le_right.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans Hfunc)
    have Hx₂ : Δ ≤ x₂ ∈ᴮ ({a} : bSet 𝔹) :=
      mem_domain_of_is_function
        (inf_le_right.trans (inf_le_left.trans inf_le_right))
        (inf_le_left.trans Hfunc)
    exact bv_trans (eq_mem_singleton Hx₁) (bv_symm (eq_mem_singleton Hx₂))
  exact injects_into_of_injection_into (le_iSup_of_le g (le_inf Hfunc Hinj))

theorem singleton_injects_omegaOne (a : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ injects_into ({a} : bSet 𝔹) omegaOne :=
  singleton_injects_of_mem zero_mem_omegaOne

/-- Removing an ordinal and then its singleton removes its successor. -/
theorem double_difference_singleton_subset {S a : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ difference (difference S a) ({a} : bSet 𝔹) ⊆ᴮ difference S (succ a) := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ difference (difference S a) ({a} : bSet 𝔹)
  have Hx : Δ ≤ x ∈ᴮ difference (difference S a) ({a} : bSet 𝔹) := inf_le_right
  rw [mem_difference, mem_difference] at Hx
  have HS : Δ ≤ x ∈ᴮ S := Hx.trans (inf_le_left.trans inf_le_left)
  have Ha : Δ ≤ (x ∈ᴮ a)ᶜ := Hx.trans (inf_le_left.trans inf_le_right)
  have Hsingle : x ∈ᴮ ({a} : bSet 𝔹) = x =ᴮ a := by
    rw [mem_singleton_bSet]
    have Hempty : x ∈ᴮ (∅ : bSet 𝔹) = ⊥ := bot_unique (bot_of_mem_empty le_rfl)
    rw [Hempty, sup_bot_eq]
  have Hneq : Δ ≤ (x =ᴮ a)ᶜ := by
    rw [← Hsingle]
    exact Hx.trans inf_le_right
  change Δ ≤ x ∈ᴮ difference S (succ a)
  rw [mem_difference, show x ∈ᴮ succ a = x =ᴮ a ⊔ x ∈ᴮ a from mem_insert1,
    compl_sup]
  exact le_inf HS (le_inf Hneq Ha)

/-- Every bounded ordinal segment can be removed from an omega-two-large
set. In particular, when S is a subset of omega-two this is its strict
tail above a. Containment of S is unnecessary for the largeness conclusion. -/
theorem omegaTwo_injects_difference_succ {S a : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ injects_into omegaTwo S)
    (Ha : Γ ≤ a ∈ᴮ omegaTwo) :
    Γ ≤ injects_into omegaTwo (difference S (succ a)) := by
  have Hfirst : Γ ≤ injects_into omegaTwo (difference S a) :=
    omegaTwo_injects_difference HCH HS (omegaTwo_member_injects Ha)
  have Hsecond : Γ ≤ injects_into omegaTwo
      (difference (difference S a) ({a} : bSet 𝔹)) :=
    omegaTwo_injects_difference HCH Hfirst (singleton_injects_omegaOne a)
  exact injects_into_trans Hsecond (injects_into_of_subset double_difference_singleton_subset)

end bSet.ErdosLargeDifference
