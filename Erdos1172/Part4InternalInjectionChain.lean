/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Flypitch4.BvmExtras

@[expose] public section

/-!
Unions of internally inclusion-ordered families of injective relation names.
The chain, its members, and all membership witnesses are arbitrary Boolean-
valued names. No external chain enumeration or global truth assumption is used.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosInjectionChain

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Inclusion comparability for every two internal members of a family. -/
def inclusionChain (C : bSet 𝔹) : 𝔹 :=
  ⨅ f : bSet 𝔹, ⨅ g : bSet 𝔹,
    (f ∈ᴮ C ⊓ g ∈ᴮ C) ⟹ (f ⊆ᴮ g ⊔ g ⊆ᴮ f)

theorem inclusionChain_apply {C f g : bSet 𝔹} {Γ : 𝔹}
    (Hchain : Γ ≤ inclusionChain C) (Hf : Γ ≤ f ∈ᴮ C) (Hg : Γ ≤ g ∈ᴮ C) :
    Γ ≤ f ⊆ᴮ g ⊔ g ⊆ᴮ f :=
  (le_inf (Hchain.trans ((iInf_le _ f).trans (iInf_le _ g))) (le_inf Hf Hg)).trans bv_imp_elim

/-- Any two elements of the union occur together in one member of the chain. -/
theorem exists_common_member_of_mem_union {C a b : bSet 𝔹} {Γ : 𝔹}
    (Hchain : Γ ≤ inclusionChain C)
    (Ha : Γ ≤ a ∈ᴮ bv_union C) (Hb : Γ ≤ b ∈ᴮ bv_union C) :
    Γ ≤ ⨆ f : bSet 𝔹, f ∈ᴮ C ⊓ a ∈ᴮ f ⊓ b ∈ᴮ f := by
  obtain ⟨f, Hf⟩ := exists_convert ((bv_union_spec_split C a).mp Ha)
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  obtain ⟨g, Hg⟩ := exists_convert ((bv_union_spec_split C b).mp Hb)
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have Hcomp := inclusionChain_apply Hchain (Hf.trans inf_le_left) (Hg.trans inf_le_left)
  apply le_trans (le_inf Hcomp le_rfl)
  apply bv_or_elim_left
  · apply le_iSup_of_le g
    exact le_inf (le_inf (inf_le_right.trans (Hg.trans inf_le_left))
      (mem_of_mem_subset inf_le_left (inf_le_right.trans (Hf.trans inf_le_right))))
      (inf_le_right.trans (Hg.trans inf_le_right))
  · apply le_iSup_of_le f
    exact le_inf (le_inf (inf_le_right.trans (Hf.trans inf_le_left))
      (inf_le_right.trans (Hf.trans inf_le_right)))
      (mem_of_mem_subset inf_le_left (inf_le_right.trans (Hg.trans inf_le_right)))

/-- Functionality passes to the union of an internal inclusion chain. -/
theorem is_func_union_of_chain {C : bSet 𝔹} {Γ : 𝔹}
    (Hchain : Γ ≤ inclusionChain C)
    (Hfunc : Γ ≤ ⨅ f : bSet 𝔹, f ∈ᴮ C ⟹ is_func f) :
    Γ ≤ is_func (bv_union C) := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]
  let Δ := (Γ ⊓ (pair w₁ v₁ ∈ᴮ bv_union C ⊓ pair w₂ v₂ ∈ᴮ bv_union C)) ⊓ w₁ =ᴮ w₂
  have Hbase : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have H₁ : Δ ≤ pair w₁ v₁ ∈ᴮ bv_union C := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have H₂ : Δ ≤ pair w₂ v₂ ∈ᴮ bv_union C := inf_le_left.trans (inf_le_right.trans inf_le_right)
  obtain ⟨f, Hf⟩ := exists_convert
    (exists_common_member_of_mem_union (Hbase.trans Hchain) H₁ H₂)
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_mem_right) B_ext_mem_right)
  have Hffunc : Δ ≤ is_func f :=
    (le_inf (Hbase.trans (Hfunc.trans (iInf_le _ f)))
      (Hf.trans (inf_le_left.trans inf_le_left))).trans bv_imp_elim
  exact eq_of_is_func_of_eq Hffunc inf_le_right
    (Hf.trans (inf_le_left.trans inf_le_right)) (Hf.trans inf_le_right)

/-- Injectivity passes to the union of an internal inclusion chain. -/
theorem is_inj_union_of_chain {C : bSet 𝔹} {Γ : 𝔹}
    (Hchain : Γ ≤ inclusionChain C)
    (Hinj : Γ ≤ ⨅ f : bSet 𝔹, f ∈ᴮ C ⟹ is_inj f) :
    Γ ≤ is_inj (bv_union C) := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]
  let Δ := Γ ⊓ (pair w₁ v₁ ∈ᴮ bv_union C ⊓ pair w₂ v₂ ∈ᴮ bv_union C ⊓ v₁ =ᴮ v₂)
  have Hbase : Δ ≤ Γ := inf_le_left
  have H₁ : Δ ≤ pair w₁ v₁ ∈ᴮ bv_union C := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have H₂ : Δ ≤ pair w₂ v₂ ∈ᴮ bv_union C := inf_le_right.trans (inf_le_left.trans inf_le_right)
  obtain ⟨f, Hf⟩ := exists_convert
    (exists_common_member_of_mem_union (Hbase.trans Hchain) H₁ H₂)
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_mem_right) B_ext_mem_right)
  have Hfinj : Δ ≤ is_inj f :=
    (le_inf (Hbase.trans (Hinj.trans (iInf_le _ f)))
      (Hf.trans (inf_le_left.trans inf_le_left))).trans bv_imp_elim
  exact eq_of_is_inj_of_eq Hfinj (inf_le_right.trans inf_le_right)
    (Hf.trans (inf_le_left.trans inf_le_right)) (Hf.trans inf_le_right)

/-- A common upper bound contains the union; no chain hypothesis is needed. -/
theorem union_subset_of_forall_subset {C X : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ ⨅ f : bSet 𝔹, f ∈ᴮ C ⟹ f ⊆ᴮ X) :
    Γ ≤ bv_union C ⊆ᴮ X := by
  rw [subset_unfold']
  apply le_iInf; intro z; rw [← deduction]
  obtain ⟨f, Hf⟩ := exists_convert
    ((bv_union_spec_split C z).mp (show Γ ⊓ z ∈ᴮ bv_union C ≤ z ∈ᴮ bv_union C from inf_le_right))
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  exact mem_of_mem_subset
    ((le_inf (inf_le_left.trans (Hsub.trans (iInf_le _ f)))
      (Hf.trans inf_le_left)).trans bv_imp_elim)
    (Hf.trans inf_le_right)

theorem subset_prod_union {C X Y : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ ⨅ f : bSet 𝔹, f ∈ᴮ C ⟹ f ⊆ᴮ prod X Y) :
    Γ ≤ bv_union C ⊆ᴮ prod X Y :=
  union_subset_of_forall_subset Hsub

end bSet.ErdosInjectionChain
