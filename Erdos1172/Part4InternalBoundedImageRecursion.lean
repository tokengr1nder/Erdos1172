/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPrefixFunction
public import Erdos1172.Part4InternalRowCandidateCongruence

@[expose] public section

/-!
# Lawful prefixes for bounded recursion from the image of the past

Each value is prescribed by its stage and the actual set of earlier
values. Functional extension preserves that strict-prefix image, and
therefore every old recursion equation. The resulting separated family
of bounded prefix graphs contains the empty graph and is closed under
arbitrary internal inclusion-chain unions.

This core does not assume or assert that a full recursion exists. No
external stage enumeration, supplied chain, or successful run is used.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosBoundedImageRecursion

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPrefixFunction ErdosPartialInjection ErdosInjectionChain ErdosRelationGraph

def imageRecLaw (V : bSet 𝔹) (Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹) (P : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ y, _root_.imp (pair i y ∈ᴮ P) (y =ᴮ Φ i (image i V P))

def imageRecPartial (θ V : bSet 𝔹) (Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹)
    (P : bSet 𝔹) : 𝔹 :=
  prefixGraph θ V P ⊓ imageRecLaw V Φ P

def imageRecMaps (θ V : bSet 𝔹) (Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹) : bSet 𝔹 :=
  comprehend (imageRecPartial θ V Φ) (bv_powerset (prod θ V))

theorem imageRecLaw_apply {V P i y : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ imageRecLaw V Φ P) (Hpair : Γ ≤ pair i y ∈ᴮ P) :
    Γ ≤ y =ᴮ Φ i (image i V P) :=
  (le_inf (Hlaw.trans ((iInf_le _ i).trans (iInf_le _ y))) Hpair).trans bv_imp_elim

private theorem imageRecValue_congr_graph (V i : bSet 𝔹)
    (Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹) (Hpast : ∀ j, B_congr (Φ j)) :
    B_congr (fun P => Φ i (image i V P)) := by
  intro P Q Γ H
  exact Hpast i (B_congr_image_right H)

theorem imageRecLaw_ext_graph (V : bSet 𝔹) (Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹)
    (Hpast : ∀ i, B_congr (Φ i)) : B_ext (imageRecLaw V Φ) :=
  B_ext_iInf (h := fun i => B_ext_iInf (h := fun y =>
    B_ext_imp (h₁ := B_ext_mem_right)
      (h₂ := B_ext_term (ϕ := fun z => y =ᴮ z) (t := fun P => Φ i (image i V P))
        B_ext_bv_eq_right (imageRecValue_congr_graph V i Φ Hpast))))

theorem imageRecPartial_ext_graph (θ V : bSet 𝔹)
    (Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹) (Hpast : ∀ i, B_congr (Φ i)) :
    B_ext (imageRecPartial θ V Φ) :=
  B_ext_inf (prefixGraph_ext_graph θ V) (imageRecLaw_ext_graph V Φ Hpast)

theorem mem_imageRecMaps_iff {θ V P : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hpast : ∀ i, B_congr (Φ i)) :
    Γ ≤ P ∈ᴮ imageRecMaps θ V Φ ↔ Γ ≤ imageRecPartial θ V Φ P := by
  unfold imageRecMaps
  rw [mem_comprehend_and (imageRecPartial_ext_graph θ V Φ Hpast)]
  constructor
  · rintro ⟨_, HP⟩
    exact HP
  · intro HP
    exact ⟨mem_powerset_iff.mpr (HP.trans (inf_le_left.trans inf_le_left)), HP⟩

theorem mem_imageRecMaps {θ V P : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} (Hpast : ∀ i, B_congr (Φ i)) :
    P ∈ᴮ imageRecMaps θ V Φ = imageRecPartial θ V Φ P :=
  le_antisymm ((mem_imageRecMaps_iff Hpast).mp le_rfl)
    ((mem_imageRecMaps_iff Hpast).mpr le_rfl)

theorem imageRecPartial_function {θ V P : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ imageRecPartial θ V Φ P) :
    Γ ≤ is_function (graphDomain θ V P) V P :=
  prefixGraph_function (HP.trans inf_le_left)

theorem imageRecPartial_is_func'_prefix {θ V P i y : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ imageRecPartial θ V Φ P) (Hpair : Γ ≤ pair i y ∈ᴮ P) :
    Γ ≤ is_func' i V P :=
  prefixGraph_is_func'_prefix (HP.trans inf_le_left) Hpair

theorem empty_imageRecLaw {V : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ imageRecLaw V Φ (∅ : bSet 𝔹) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro y
  rw [← deduction]
  exact (bot_of_mem_empty inf_le_right).trans bot_le

theorem empty_imageRecPartial {θ V : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ imageRecPartial θ V Φ (∅ : bSet 𝔹) :=
  le_inf empty_prefixGraph empty_imageRecLaw

theorem imageRecMaps_nonempty {θ V : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hpast : ∀ i, B_congr (Φ i)) : Γ ≤ (imageRecMaps θ V Φ =ᴮ ∅)ᶜ :=
  nonempty_of_exists_mem _ (le_iSup_of_le (∅ : bSet 𝔹)
    ((mem_imageRecMaps_iff Hpast).mpr empty_imageRecPartial))

/-- The old graph is already total below its stored stage. Functionality
of the extension therefore fixes the actual strict-prefix image exactly. -/
theorem imageRecLaw_entry_of_extension {θ V P Q i y : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hpast : ∀ j, B_congr (Φ j)) (Hsub : Γ ≤ P ⊆ᴮ Q) (HfuncQ : Γ ≤ is_func Q)
    (HP : Γ ≤ imageRecPartial θ V Φ P) (Hpair : Γ ≤ pair i y ∈ᴮ P) :
    Γ ≤ y =ᴮ Φ i (image i V Q) :=
  bv_trans (imageRecLaw_apply (HP.trans inf_le_right) Hpair)
    (Hpast i (ErdosRowCandidates.prefix_image_eq_of_extension Hsub HfuncQ
      (imageRecPartial_is_func'_prefix HP Hpair)))

/-- Once the union is functional, every old entry equation transfers.
This lemma itself does not require a chain or a nonempty family. -/
theorem imageRecLaw_union {θ V C : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hpast : ∀ i, B_congr (Φ i)) (HfuncUnion : Γ ≤ is_func (bv_union C))
    (Hfamily : Γ ≤ ⨅ P, _root_.imp (P ∈ᴮ C) (imageRecPartial θ V Φ P)) :
    Γ ≤ imageRecLaw V Φ (bv_union C) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro y
  rw [← deduction]
  let Δ := Γ ⊓ pair i y ∈ᴮ bv_union C
  obtain ⟨P, HP⟩ := exists_convert (mem_bv_union_iff.mp
    (show Δ ≤ pair i y ∈ᴮ bv_union C from inf_le_right))
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have Hpartial : Δ ≤ imageRecPartial θ V Φ P :=
    (le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ P)))
      (HP.trans inf_le_left)).trans bv_imp_elim
  exact imageRecLaw_entry_of_extension Hpast
    (ErdosIdeal.loss_subset_union (HP.trans inf_le_left))
    (inf_le_left.trans HfuncUnion) Hpartial (HP.trans inf_le_right)

/-- Arbitrary internal inclusion chains have a lawful bounded union.
Only congruence in the set of past values is needed for this closure. -/
theorem imageRecPartial_union_of_chain {θ V C : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hpast : ∀ i, B_congr (Φ i)) (Hchain : Γ ≤ inclusionChain C)
    (Hfamily : Γ ≤ ⨅ P, _root_.imp (P ∈ᴮ C) (imageRecPartial θ V Φ P)) :
    Γ ≤ imageRecPartial θ V Φ (bv_union C) := by
  have HprefixFamily : Γ ≤ ⨅ P, _root_.imp (P ∈ᴮ C) (prefixGraph θ V P) := by
    apply le_iInf
    intro P
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ P))) inf_le_right).trans
      bv_imp_elim).trans inf_le_left
  have Hprefix : Γ ≤ prefixGraph θ V (bv_union C) :=
    prefixGraph_union_of_chain Hchain HprefixFamily
  exact le_inf Hprefix (imageRecLaw_union Hpast
    (Hprefix.trans (inf_le_right.trans inf_le_left)) Hfamily)

theorem imageRecMaps_chain_union {θ V C : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (Hpast : ∀ i, B_congr (Φ i))
    (Hsub : Γ ≤ C ⊆ᴮ imageRecMaps θ V Φ) (Hchain : Γ ≤ inclusionChain C) :
    Γ ≤ bv_union C ∈ᴮ imageRecMaps θ V Φ := by
  apply (mem_imageRecMaps_iff Hpast).mpr
  apply imageRecPartial_union_of_chain Hpast Hchain
  apply le_iInf
  intro P
  rw [← deduction]
  exact (mem_imageRecMaps_iff Hpast).mp
    (mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right)

end bSet.ErdosBoundedImageRecursion
