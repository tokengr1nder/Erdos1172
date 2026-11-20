/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalGraphNeighborhood
public import Erdos1172.Part4InternalInjectionChain

@[expose] public section

/-!
# Maximal internal color-independent subsets

The family is separated inside the powerset of the given arbitrary name X.
An internally inclusion-ordered union is independent because any two of
its elements occur together in one member of the chain. Zorn's lemma then
produces an actual maximal independent member. This module does not assert
that this member is large, covers X by neighborhoods, or has any particular
order type.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIndependentMaximal

open ErdosPartition ErdosRelationGraph ErdosInjectionChain

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- No two members have the specified graph color. Diagonal pairs need
no exception because the Boolean graph color has no loops. -/
def independent (color : Bool) (R A : bSet 𝔹) : 𝔹 :=
  ⨅ x : bSet 𝔹, ⨅ y : bSet 𝔹,
    _root_.imp (x ∈ᴮ A ⊓ y ∈ᴮ A) (graphColor color R x y)ᶜ

theorem independent_ext (color : Bool) (R : bSet 𝔹) :
    B_ext (independent color R) := by
  unfold independent
  exact B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_mem_right)
      (h₂ := B_ext_const)))

theorem independent_apply {color : Bool} {R A x y : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ independent color R A) (Hx : Γ ≤ x ∈ᴮ A)
    (Hy : Γ ≤ y ∈ᴮ A) : Γ ≤ (graphColor color R x y)ᶜ :=
  (le_inf (HA.trans ((iInf_le _ x).trans (iInf_le _ y)))
    (le_inf Hx Hy)).trans bv_imp_elim

/-- The actual set-sized family used in the maximality construction. -/
def independentFamily (color : Bool) (R X : bSet 𝔹) : bSet 𝔹 :=
  comprehend (independent color R) (bv_powerset X)

theorem mem_independentFamily_iff {color : Bool} {R X A : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ A ∈ᴮ independentFamily color R X ↔
      Γ ≤ A ⊆ᴮ X ⊓ independent color R A := by
  unfold independentFamily
  rw [mem_comprehend_and (independent_ext color R)]
  constructor
  · rintro ⟨Hsub, Hind⟩
    exact le_inf (mem_powerset_iff.mp Hsub) Hind
  · intro H
    exact ⟨mem_powerset_iff.mpr (H.trans inf_le_left), H.trans inf_le_right⟩

/-- Exact Boolean membership, valid under every condition. -/
theorem mem_independentFamily (color : Bool) (R X A : bSet 𝔹) :
    A ∈ᴮ independentFamily color R X = A ⊆ᴮ X ⊓ independent color R A :=
  le_antisymm (mem_independentFamily_iff.mp le_rfl)
    (mem_independentFamily_iff.mpr le_rfl)

theorem empty_independent {color : Bool} {R : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ independent color R ∅ := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  exact (bot_of_mem_empty (inf_le_right.trans inf_le_left)).trans bot_le

theorem empty_mem_independentFamily {color : Bool} {R X : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (∅ : bSet 𝔹) ∈ᴮ independentFamily color R X :=
  mem_independentFamily_iff.mpr (le_inf empty_subset empty_independent)

theorem independentFamily_nonempty {color : Bool} {R X : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (independentFamily color R X =ᴮ ∅)ᶜ :=
  nonempty_of_exists_mem (independentFamily color R X)
    (le_iSup_of_le (∅ : bSet 𝔹) empty_mem_independentFamily)

/-- Both vertices occur together in a chain member, where the selected
color is absent. No external chain enumeration is used. -/
theorem independent_union_of_chain {color : Bool} {R C : bSet 𝔹} {Γ : 𝔹}
    (Hchain : Γ ≤ inclusionChain C)
    (Hfamily : Γ ≤ ⨅ A : bSet 𝔹,
      _root_.imp (A ∈ᴮ C) (independent color R A)) :
    Γ ≤ independent color R (bv_union C) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ (x ∈ᴮ bv_union C ⊓ y ∈ᴮ bv_union C)
  have Hcommon : Δ ≤ ⨆ A : bSet 𝔹, A ∈ᴮ C ⊓ x ∈ᴮ A ⊓ y ∈ᴮ A :=
    exists_common_member_of_mem_union (inf_le_left.trans Hchain)
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
  obtain ⟨A, HA⟩ := exists_convert Hcommon
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_mem_right) B_ext_mem_right)
  have Hind : Δ ≤ independent color R A :=
    (le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ A)))
      (HA.trans (inf_le_left.trans inf_le_left))).trans bv_imp_elim
  exact independent_apply Hind
    (HA.trans (inf_le_left.trans inf_le_right)) (HA.trans inf_le_right)

theorem independentFamily_chain_union {color : Bool} {R X C : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ C ⊆ᴮ independentFamily color R X)
    (Hchain : Γ ≤ inclusionChain C) :
    Γ ≤ bv_union C ∈ᴮ independentFamily color R X := by
  apply mem_independentFamily_iff.mpr
  refine le_inf (union_subset_of_forall_subset ?_)
    (independent_union_of_chain Hchain ?_)
  · apply le_iInf
    intro A
    rw [← deduction]
    exact (mem_independentFamily_iff.mp
      (mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right)).trans inf_le_left
  · apply le_iInf
    intro A
    rw [← deduction]
    exact (mem_independentFamily_iff.mp
      (mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right)).trans inf_le_right

theorem exists_maximal_independent_member {color : Bool} {R X : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨆ A : bSet 𝔹, A ∈ᴮ independentFamily color R X ⊓
      ⨅ B : bSet 𝔹, _root_.imp (B ∈ᴮ independentFamily color R X)
        (_root_.imp (A ⊆ᴮ B) (A =ᴮ B)) := by
  have Hclosure : Γ ≤ ⨅ C : bSet 𝔹,
      _root_.imp (C ⊆ᴮ independentFamily color R X ⊓ inclusionChain C)
        (bv_union C ∈ᴮ independentFamily color R X) := by
    apply le_iInf
    intro C
    rw [← deduction]
    exact independentFamily_chain_union (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right)
  have Hzorn : Γ ≤ _root_.imp (independentFamily color R X =ᴮ ∅)ᶜ
      (_root_.imp
        (⨅ C : bSet 𝔹,
          _root_.imp (C ⊆ᴮ independentFamily color R X ⊓ inclusionChain C)
            (bv_union C ∈ᴮ independentFamily color R X))
        (⨆ A : bSet 𝔹, A ∈ᴮ independentFamily color R X ⊓
          ⨅ B : bSet 𝔹, _root_.imp (B ∈ᴮ independentFamily color R X)
            (_root_.imp (A ⊆ᴮ B) (A =ᴮ B)))) :=
    (bSet_zorns_lemma' (Γ := Γ)).trans (iInf_le _ (independentFamily color R X))
  exact (le_inf ((le_inf Hzorn independentFamily_nonempty).trans bv_imp_elim)
    Hclosure).trans bv_imp_elim

/-- An actual internally maximal independent subset of any arbitrary X.
No cardinal size, ordinal structure, or CH hypothesis is required. -/
theorem exists_maximal_independent {color : Bool} {R X : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨆ A : bSet 𝔹, (A ⊆ᴮ X ⊓ independent color R A) ⊓
      ⨅ B : bSet 𝔹, _root_.imp (B ⊆ᴮ X ⊓ independent color R B)
        (_root_.imp (A ⊆ᴮ B) (A =ᴮ B)) := by
  simpa only [mem_independentFamily] using
    (exists_maximal_independent_member (color := color) (R := R) (X := X) (Γ := Γ))

end bSet.ErdosIndependentMaximal
