/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaTwo
public import Erdos1172.Part4InternalSubsetRepresentation

@[expose] public section

/-!
# Arbitrary-name semantics of the two-block partition target

The domains are internal set names and every quantifier ranges over arbitrary
names. `is_func'` means a relation contains a total single-valued map; domain
guards ensure that extraneous graph entries do not affect its used range.
The two colors are joined inside the Boolean algebra, not chosen externally.
No partition theorem, model of GCH, or dense ideal is asserted here.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPartition

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def rangeMem (A f x : bSet 𝔹) : 𝔹 :=
  ⨆ i, (i ∈ᴮ A) ⊓ (pair i x ∈ᴮ f)

def increasingOn (A f : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ j, ⨅ x, ⨅ y,
    _root_.imp (((i ∈ᴮ A ⊓ j ∈ᴮ A) ⊓ i ∈ᴮ j) ⊓
      (pair i x ∈ᴮ f ⊓ pair j y ∈ᴮ f)) (x ∈ᴮ y)

def separatedRanges (A B f g : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ j, ⨅ x, ⨅ y,
    _root_.imp ((i ∈ᴮ A ⊓ j ∈ᴮ B) ⊓
      (pair i x ∈ᴮ f ⊓ pair j y ∈ᴮ g)) (x ∈ᴮ y)

def homogeneousUnion (color : Bool) (R A B f g : bSet 𝔹) : 𝔹 :=
  ⨅ x, ⨅ y,
    _root_.imp (((rangeMem A f x ⊔ rangeMem B g x) ⊓
      (rangeMem A f y ⊔ rangeMem B g y)) ⊓ x ∈ᴮ y)
      (if color then pair x y ∈ᴮ R else (pair x y ∈ᴮ R)ᶜ)

def twoBlockWitness (color : Bool) (R A B κ f g : bSet 𝔹) : 𝔹 :=
  (is_func' A κ f ⊓ is_func' B κ g) ⊓
    ((increasingOn A f ⊓ increasingOn B g) ⊓
      (separatedRanges A B f g ⊓ homogeneousUnion color R A B f g))

def hasTwoBlock (color : Bool) (R A B κ : bSet 𝔹) : 𝔹 :=
  ⨆ f, ⨆ g, twoBlockWitness color R A B κ f g

def partitionValue (κ A B : bSet 𝔹) : 𝔹 :=
  ⨅ R, hasTwoBlock false R A B κ ⊔ hasTwoBlock true R A B κ

/-- The intended internal balanced target, not an assertion that it holds. -/
noncomputable def part4Value : 𝔹 :=
  partitionValue ErdosOmegaTwo.omegaTwo ErdosOmegaTwo.omegaOne bSet.omega

/-- Even the weaker total-functional relation predicate bounds every value
whose argument belongs to the stated domain. -/
theorem value_mem_codomain {A κ f i x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' A κ f) (Hi : Γ ≤ i ∈ᴮ A)
    (Hx : Γ ≤ pair i x ∈ᴮ f) : Γ ≤ x ∈ᴮ κ := by
  have Htotal : Γ ≤ ⨆ y, y ∈ᴮ κ ⊓ pair i y ∈ᴮ f :=
    (le_inf ((Hf.trans inf_le_right).trans (iInf_le _ i)) Hi).trans bv_imp_elim
  obtain ⟨y, Hy⟩ := exists_convert Htotal
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hxy : Γ ≤ x =ᴮ y :=
    eq_of_is_func'_of_eq Hf bv_refl Hx (Hy.trans inf_le_right)
  exact mem_congr (bv_symm Hxy) bv_refl (Hy.trans inf_le_left)

theorem rangeMem_le_codomain {A κ f x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' A κ f) (Hx : Γ ≤ rangeMem A f x) : Γ ≤ x ∈ᴮ κ := by
  obtain ⟨i, Hi⟩ := exists_convert Hx
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact value_mem_codomain Hf (Hi.trans inf_le_left) (Hi.trans inf_le_right)

/-- The domain-guarded range is the actual internal bounded image under
the same Boolean condition; it is not a host-language range. -/
theorem rangeMem_eq_image {A κ f x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' A κ f) :
    Γ ⊓ rangeMem A f x = Γ ⊓ (x ∈ᴮ image A κ f) := by
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    exact mem_image_iff.mpr
      ⟨rangeMem_le_codomain (inf_le_left.trans Hf) inf_le_right, inf_le_right⟩
  · exact le_inf inf_le_left ((mem_image_iff.mp inf_le_right).2)

theorem unionRange_le_codomain {A B κ f g x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' A κ f) (Hg : Γ ≤ is_func' B κ g) :
    Γ ⊓ (rangeMem A f x ⊔ rangeMem B g x) ≤ x ∈ᴮ κ := by
  rw [inf_sup_left]
  exact sup_le (rangeMem_le_codomain (inf_le_left.trans Hf) inf_le_right)
    (rangeMem_le_codomain (inf_le_left.trans Hg) inf_le_right)

theorem separatedRanges_apply {A B f g x y : bSet 𝔹} {Γ : 𝔹}
    (Hsep : Γ ≤ separatedRanges A B f g)
    (Hx : Γ ≤ rangeMem A f x) (Hy : Γ ≤ rangeMem B g y) : Γ ≤ x ∈ᴮ y := by
  obtain ⟨i, Hi⟩ := exists_convert Hx
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  obtain ⟨j, Hj⟩ := exists_convert Hy
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hspec := Hsep.trans ((iInf_le _ i).trans
    ((iInf_le _ j).trans ((iInf_le _ x).trans (iInf_le _ y))))
  exact (le_inf Hspec (le_inf (le_inf (Hi.trans inf_le_left) (Hj.trans inf_le_left))
    (le_inf (Hi.trans inf_le_right) (Hj.trans inf_le_right)))).trans bv_imp_elim

theorem homogeneousUnion_apply {color : Bool} {R A B f g x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ homogeneousUnion color R A B f g)
    (Hx : Γ ≤ rangeMem A f x ⊔ rangeMem B g x)
    (Hy : Γ ≤ rangeMem A f y ⊔ rangeMem B g y) (Hxy : Γ ≤ x ∈ᴮ y) :
    Γ ≤ (if color then pair x y ∈ᴮ R else (pair x y ∈ᴮ R)ᶜ) := by
  exact (le_inf (H.trans ((iInf_le _ x).trans (iInf_le _ y)))
    (le_inf (le_inf Hx Hy) Hxy)).trans bv_imp_elim

end bSet.ErdosPartition
