/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartialInjection
public import Erdos1172.Part4InternalInjectionChain

@[expose] public section

/-!
An actual internally maximal partial injective graph with a prefix-closed
domain. The family is the separated powerset `partialMaps κ S`, and Zorn's
lemma is applied to internal inclusion chains. The construction does not
require κ to be an ordinal and is valid in arbitrary Boolean contexts.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPartialInjection

open ErdosInjectionChain

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

theorem empty_partialGraph {κ S : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ partialGraph κ S ∅ := by
  refine le_inf empty_subset (le_inf ?_ (le_inf ?_ ?_))
  · exact (is_func'_empty (x := S)).trans inf_le_left
  · apply le_iInf; intro x₁; apply le_iInf; intro x₂
    apply le_iInf; intro y₁; apply le_iInf; intro y₂
    rw [← deduction]
    exact (bot_of_mem_empty
      (inf_le_right.trans (inf_le_left.trans inf_le_left))).trans bot_le
  · apply le_iInf; intro x; apply le_iInf; intro y; apply le_iInf; intro z
    rw [← deduction]
    exact (bot_of_mem_empty (inf_le_right.trans inf_le_left)).trans bot_le

theorem empty_mem_partialMaps {κ S : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (∅ : bSet 𝔹) ∈ᴮ partialMaps κ S :=
  mem_partialMaps_iff.mpr empty_partialGraph

theorem partialMaps_nonempty {κ S : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (partialMaps κ S =ᴮ ∅)ᶜ :=
  nonempty_of_exists_mem (partialMaps κ S)
    (le_iSup_of_le (∅ : bSet 𝔹) empty_mem_partialMaps)

private theorem forall_mem_mono {C : bSet 𝔹} {P Q : bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (H : Γ ≤ ⨅ f, f ∈ᴮ C ⟹ P f) (HPQ : ∀ f, P f ≤ Q f) :
    Γ ≤ ⨅ f, f ∈ᴮ C ⟹ Q f := by
  apply le_iInf; intro f; rw [← deduction]
  exact ((le_inf (inf_le_left.trans (H.trans (iInf_le _ f))) inf_le_right).trans
    bv_imp_elim).trans (HPQ f)

/-- All four actual partial-graph conditions survive a chain union. -/
theorem partialGraph_union_of_chain {κ S C : bSet 𝔹} {Γ : 𝔹}
    (Hchain : Γ ≤ inclusionChain C)
    (Hfamily : Γ ≤ ⨅ f, f ∈ᴮ C ⟹ partialGraph κ S f) :
    Γ ≤ partialGraph κ S (bv_union C) := by
  refine le_inf (subset_prod_union (forall_mem_mono Hfamily (fun _ => inf_le_left)))
    (le_inf ?_ (le_inf ?_ ?_))
  · exact is_func_union_of_chain Hchain
      (forall_mem_mono Hfamily (fun _ => inf_le_right.trans inf_le_left))
  · exact is_inj_union_of_chain Hchain
      (forall_mem_mono Hfamily (fun _ => inf_le_right.trans (inf_le_right.trans inf_le_left)))
  · exact prefixClosed_union
      (forall_mem_mono Hfamily (fun _ => inf_le_right.trans (inf_le_right.trans inf_le_right)))

theorem partialMaps_chain_union {κ S C : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ C ⊆ᴮ partialMaps κ S) (Hchain : Γ ≤ inclusionChain C) :
    Γ ≤ bv_union C ∈ᴮ partialMaps κ S := by
  apply mem_partialMaps_iff.mpr
  apply partialGraph_union_of_chain Hchain
  apply le_iInf; intro f; rw [← deduction]
  exact mem_partialMaps_iff.mp (mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right)

/-- Zorn's lemma produces a genuinely maximal member of the concrete family. -/
theorem exists_maximal_partialMap {κ S : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨆ f : bSet 𝔹, f ∈ᴮ partialMaps κ S ⊓
      ⨅ g : bSet 𝔹, g ∈ᴮ partialMaps κ S ⟹ (f ⊆ᴮ g ⟹ f =ᴮ g) := by
  have Hclosure : Γ ≤ ⨅ C : bSet 𝔹,
      (C ⊆ᴮ partialMaps κ S ⊓ inclusionChain C) ⟹ bv_union C ∈ᴮ partialMaps κ S := by
    apply le_iInf; intro C; rw [← deduction]
    exact partialMaps_chain_union (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right)
  have Hzorn : Γ ≤ (partialMaps κ S =ᴮ ∅)ᶜ ⟹
      ((⨅ C : bSet 𝔹, (C ⊆ᴮ partialMaps κ S ⊓ inclusionChain C) ⟹
        bv_union C ∈ᴮ partialMaps κ S) ⟹
        ⨆ f : bSet 𝔹, f ∈ᴮ partialMaps κ S ⊓
          ⨅ g : bSet 𝔹, g ∈ᴮ partialMaps κ S ⟹ (f ⊆ᴮ g ⟹ f =ᴮ g)) :=
    (bSet_zorns_lemma' (Γ := Γ)).trans (iInf_le _ (partialMaps κ S))
  exact (le_inf ((le_inf Hzorn partialMaps_nonempty).trans bv_imp_elim) Hclosure).trans
    bv_imp_elim

/-- The same maximal graph stated directly in terms of its graph properties. -/
theorem exists_maximal_partialGraph {κ S : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨆ f : bSet 𝔹, partialGraph κ S f ⊓
      ⨅ g : bSet 𝔹, partialGraph κ S g ⟹ (f ⊆ᴮ g ⟹ f =ᴮ g) := by
  apply (exists_maximal_partialMap (κ := κ) (S := S) (Γ := Γ)).trans
  apply iSup_le; intro f
  apply le_iSup_of_le f
  refine le_inf (mem_partialMaps_iff.mp inf_le_left) ?_
  apply le_iInf; intro g; rw [← deduction, ← deduction]
  have Hg := mem_partialMaps_iff.mpr
    (show ((f ∈ᴮ partialMaps κ S ⊓
      (⨅ g : bSet 𝔹, g ∈ᴮ partialMaps κ S ⟹ (f ⊆ᴮ g ⟹ f =ᴮ g))) ⊓
      partialGraph κ S g) ⊓ f ⊆ᴮ g ≤ partialGraph κ S g from
      inf_le_left.trans inf_le_right)
  exact (le_inf ((le_inf
    (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans (iInf_le _ g))))
    Hg).trans bv_imp_elim) inf_le_right).trans bv_imp_elim

end bSet.ErdosPartialInjection
