/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaTwo
public import Erdos1172.Part4InternalInitialSegments
public import Erdos1172.Part4InternalInjectionChain

@[expose] public section

/-!
The set-sized family of injective graphs with initial-segment domains. Its
chain unions are actual unions of internal graph names. No cardinal
preservation or ground-model graph representation is assumed.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPartialInjection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

private theorem mem_comprehend_value (ϕ : bSet 𝔹 → 𝔹) (Hϕ : B_ext ϕ)
    (A x : bSet 𝔹) : x ∈ᴮ comprehend ϕ A = (x ∈ᴮ A) ⊓ ϕ x := by
  apply le_antisymm
  · apply ((mem_comprehend_iff₂ ϕ A Hϕ).mp le_rfl).trans
    apply iSup_le
    intro y
    have Heq : y ∈ᴮ A ⊓ (x =ᴮ y ⊓ ϕ y) ≤ x =ᴮ y :=
      inf_le_right.trans inf_le_left
    exact le_inf
      (bv_rw' (ϕ := fun z => z ∈ᴮ A) Heq
        (h_congr := B_ext_mem_left) (H_new := inf_le_left))
      (bv_rw' Heq (h_congr := Hϕ) (H_new := inf_le_right.trans inf_le_right))
  · apply (mem_comprehend_iff₂ ϕ A Hϕ).mpr
    exact le_iSup_of_le x (le_inf inf_le_left (le_inf bv_refl inf_le_right))

def graphDomain (κ S f : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun x => ⨆ y, (y ∈ᴮ S) ⊓ pair x y ∈ᴮ f) κ

theorem mem_graphDomain (κ S f x : bSet 𝔹) :
    x ∈ᴮ graphDomain κ S f =
      (x ∈ᴮ κ) ⊓ ⨆ y, (y ∈ᴮ S) ⊓ pair x y ∈ᴮ f :=
  mem_comprehend_value _ (B_ext_iSup (h := fun _ =>
    B_ext_inf B_ext_const B_ext_pair_mem_left)) _ _

theorem graphDomain_subset {κ S f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ graphDomain κ S f ⊆ᴮ κ :=
  comprehend_subset (ϕ := fun x => ⨆ y, (y ∈ᴮ S) ⊓ pair x y ∈ᴮ f)
    (Γ := Γ) κ

theorem mem_graphDomain_of_pair {κ S f x y : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ f ⊆ᴮ prod κ S) (Hpair : Γ ≤ pair x y ∈ᴮ f) :
    Γ ≤ x ∈ᴮ graphDomain κ S f := by
  have Hxy := mem_prod_iff.mp (mem_of_mem_subset Hsub Hpair)
  rw [mem_graphDomain]
  exact le_inf Hxy.1 (le_iSup_of_le y (le_inf Hxy.2 Hpair))

theorem function_on_graphDomain {κ S f : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ f ⊆ᴮ prod κ S) (Hfunc : Γ ≤ is_func f) :
    Γ ≤ is_function (graphDomain κ S f) S f := by
  refine le_inf (le_inf Hfunc ?_) ?_
  · apply le_iInf
    intro x
    rw [← deduction, mem_graphDomain]
    exact inf_le_right.trans inf_le_right
  · rw [subset_unfold']
    apply le_iInf
    intro z
    rw [← deduction]
    have Hprod := mem_of_mem_subset (inf_le_left.trans Hsub)
      (show Γ ⊓ z ∈ᴮ f ≤ z ∈ᴮ f from inf_le_right)
    obtain ⟨x, _, y, Hy, Hz⟩ := mem_prod_iff₂.mp Hprod
    have Hpair : Γ ⊓ z ∈ᴮ f ≤ pair x y ∈ᴮ f :=
      mem_congr Hz bv_refl inf_le_right
    exact mem_prod_iff₂.mpr ⟨x,
      mem_graphDomain_of_pair (inf_le_left.trans Hsub) Hpair, y, Hy, Hz⟩

def prefixClosed (S f : bSet 𝔹) : 𝔹 :=
  ⨅ x, ⨅ y, ⨅ z, _root_.imp ((pair x y ∈ᴮ f) ⊓ z ∈ᴮ x)
    (⨆ w, (w ∈ᴮ S) ⊓ pair z w ∈ᴮ f)

theorem prefixClosed_apply {S f x y z : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ prefixClosed S f) (Hpair : Γ ≤ pair x y ∈ᴮ f)
    (Hz : Γ ≤ z ∈ᴮ x) : Γ ≤ ⨆ w, (w ∈ᴮ S) ⊓ pair z w ∈ᴮ f :=
  (le_inf (H.trans ((iInf_le _ x).trans ((iInf_le _ y).trans (iInf_le _ z))))
    (le_inf Hpair Hz)).trans bv_imp_elim

theorem B_ext_prefixClosed (S : bSet 𝔹) : B_ext (prefixClosed S) := by
  unfold prefixClosed
  exact B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_imp
      (h₁ := B_ext_inf B_ext_mem_right B_ext_const)
      (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))))

theorem graphDomain_transitive {κ S f : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (Hprefix : Γ ≤ prefixClosed S f) :
    Γ ≤ is_transitive (graphDomain κ S f) := by
  apply le_iInf
  intro x
  rw [← deduction, subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction]
  let Δ := (Γ ⊓ x ∈ᴮ graphDomain κ S f) ⊓ z ∈ᴮ x
  have Hdom : Δ ≤ x ∈ᴮ graphDomain κ S f := inf_le_left.trans inf_le_right
  rw [mem_graphDomain] at Hdom
  obtain ⟨y, Hy⟩ := exists_convert (Hdom.trans inf_le_right)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  rw [mem_graphDomain κ S f z]
  exact le_inf
    (mem_of_mem_subset
      (subset_of_mem_Ord (Hdom.trans inf_le_left)
        (inf_le_left.trans (inf_le_left.trans Hκ))) inf_le_right)
    (prefixClosed_apply (inf_le_left.trans (inf_le_left.trans Hprefix))
      (Hy.trans inf_le_right) inf_le_right)

def partialGraph (κ S f : bSet 𝔹) : 𝔹 :=
  (f ⊆ᴮ prod κ S) ⊓ (is_func f ⊓ (is_inj f ⊓ prefixClosed S f))

private theorem B_ext_func : B_ext (is_func : bSet 𝔹 → 𝔹) := by
  unfold is_func
  exact B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_mem_right)
        (h₂ := B_ext_const)))))

private theorem B_ext_inj : B_ext (is_inj : bSet 𝔹 → 𝔹) := by
  unfold is_inj
  exact B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf (B_ext_inf B_ext_mem_right B_ext_mem_right)
        B_ext_const) (h₂ := B_ext_const)))))

def partialMaps (κ S : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun f => is_func f ⊓ (is_inj f ⊓ prefixClosed S f))
    (bv_powerset (prod κ S))

theorem mem_partialMaps_iff {κ S f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ f ∈ᴮ partialMaps κ S ↔ Γ ≤ partialGraph κ S f := by
  unfold partialMaps
  rw [mem_comprehend_value _
    (B_ext_inf B_ext_func (B_ext_inf B_ext_inj (B_ext_prefixClosed S)))]
  constructor
  · intro H
    exact le_inf (mem_powerset_iff.mp (H.trans inf_le_left)) (H.trans inf_le_right)
  · intro H
    exact le_inf (mem_powerset_iff.mpr (H.trans inf_le_left)) (H.trans inf_le_right)

theorem partialGraph_function {κ S f : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ partialGraph κ S f) :
    Γ ≤ is_injective_function (graphDomain κ S f) S f :=
  le_inf (function_on_graphDomain (H.trans inf_le_left)
    (H.trans (inf_le_right.trans inf_le_left)))
    (H.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))

theorem partialGraph_domain_Ord {κ S f : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (H : Γ ≤ partialGraph κ S f) :
    Γ ≤ Ord (graphDomain κ S f) :=
  ErdosInitialSegments.Ord_of_transitive_subset Hκ graphDomain_subset
    (graphDomain_transitive Hκ
      (H.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))))

theorem prefixClosed_union {S C : bSet 𝔹} {Γ : 𝔹}
    (Hfamily : Γ ≤ ⨅ f, _root_.imp (f ∈ᴮ C) (prefixClosed S f)) :
    Γ ≤ prefixClosed S (bv_union C) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro z
  rw [← deduction]
  let Δ := Γ ⊓ (pair x y ∈ᴮ bv_union C ⊓ z ∈ᴮ x)
  have Hmem : Δ ≤ pair x y ∈ᴮ bv_union C := inf_le_right.trans inf_le_left
  obtain ⟨f, Hf⟩ := exists_convert (mem_bv_union_iff.mp Hmem)
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have Hprefix : Δ ≤ prefixClosed S f :=
    (le_inf (inf_le_left.trans (Hfamily.trans (iInf_le _ f)))
      (Hf.trans inf_le_left)).trans bv_imp_elim
  have Hstep := prefixClosed_apply Hprefix (Hf.trans inf_le_right)
    (show Δ ≤ z ∈ᴮ x from inf_le_right.trans inf_le_right)
  obtain ⟨w, Hw⟩ := exists_convert Hstep
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  apply le_iSup_of_le w
  refine le_inf (Hw.trans inf_le_left) ?_
  exact mem_bv_union_iff.mpr
    (le_iSup_of_le f (le_inf (Hf.trans inf_le_left) (Hw.trans inf_le_right)))

end bSet.ErdosPartialInjection
