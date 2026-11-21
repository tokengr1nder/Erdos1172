/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPartialInjection
public import Erdos1172.Part4InternalInjectionExtension

@[expose] public section

/-!
# Bounded internal choice from a total relation

Zorn's lemma supplies a maximal functional subrelation inside the concrete
set `R ∩ᴮ prod D C`. Its domain is all of `D`: a missing domain point could
be assigned any permitted value of the total relation and adjoined to the
graph. No freshness of the output, injectivity, or coherent external
selection of representatives is assumed.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosRelationChoice

open ErdosInjectionChain ErdosPartialInjection ErdosInjectionExtension

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

private theorem B_ext_func : B_ext (is_func : bSet 𝔹 → 𝔹) := by
  unfold is_func
  exact B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_mem_right) (h₂ := B_ext_const)))))

private theorem mem_comprehend_value (ϕ : bSet 𝔹 → 𝔹) (Hϕ : B_ext ϕ)
    (A x : bSet 𝔹) : x ∈ᴮ comprehend ϕ A = (x ∈ᴮ A) ⊓ ϕ x := by
  apply le_antisymm
  · apply ((mem_comprehend_iff₂ ϕ A Hϕ).mp le_rfl).trans
    apply iSup_le
    intro y
    have Heq : y ∈ᴮ A ⊓ (x =ᴮ y ⊓ ϕ y) ≤ x =ᴮ y := inf_le_right.trans inf_le_left
    exact le_inf
      (bv_rw' (ϕ := fun z => z ∈ᴮ A) Heq
        (h_congr := B_ext_mem_left) (H_new := inf_le_left))
      (bv_rw' Heq (h_congr := Hϕ) (H_new := inf_le_right.trans inf_le_right))
  · apply (mem_comprehend_iff₂ ϕ A Hϕ).mpr
    exact le_iSup_of_le x (le_inf inf_le_left (le_inf bv_refl inf_le_right))

/-- The actual set of partial functional choices from a bounded relation. -/
def partialChoices (D C R : bSet 𝔹) : bSet 𝔹 :=
  comprehend is_func (bv_powerset (R ∩ᴮ prod D C))

theorem mem_partialChoices_iff {D C R f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ f ∈ᴮ partialChoices D C R ↔ Γ ≤ (f ⊆ᴮ R ∩ᴮ prod D C) ⊓ is_func f := by
  unfold partialChoices
  rw [mem_comprehend_value _ B_ext_func]
  constructor
  · intro H
    exact le_inf (mem_powerset_iff.mp (H.trans inf_le_left)) (H.trans inf_le_right)
  · intro H
    exact le_inf (mem_powerset_iff.mpr (H.trans inf_le_left)) (H.trans inf_le_right)

theorem empty_mem_partialChoices {D C R : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (∅ : bSet 𝔹) ∈ᴮ partialChoices D C R :=
  mem_partialChoices_iff.mpr (le_inf empty_subset ((is_func'_empty (x := C)).trans inf_le_left))

theorem partialChoices_nonempty {D C R : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (partialChoices D C R =ᴮ ∅)ᶜ :=
  nonempty_of_exists_mem (partialChoices D C R)
    (le_iSup_of_le (∅ : bSet 𝔹) empty_mem_partialChoices)

theorem partialChoices_chain_union {D C R T : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ T ⊆ᴮ partialChoices D C R)
    (Hchain : Γ ≤ inclusionChain T) :
    Γ ≤ bv_union T ∈ᴮ partialChoices D C R := by
  apply mem_partialChoices_iff.mpr
  refine le_inf (union_subset_of_forall_subset ?_) (is_func_union_of_chain Hchain ?_)
  · apply le_iInf
    intro f
    rw [← deduction]
    exact (mem_partialChoices_iff.mp
      (mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right)).trans inf_le_left
  · apply le_iInf
    intro f
    rw [← deduction]
    exact (mem_partialChoices_iff.mp
      (mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right)).trans inf_le_right

/-- Zorn is applied to this particular separated powerset, not assumed as
a selection theorem for the relation. -/
theorem exists_maximal_partialChoice {D C R : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨆ f : bSet 𝔹, f ∈ᴮ partialChoices D C R ⊓
      ⨅ g : bSet 𝔹, _root_.imp (g ∈ᴮ partialChoices D C R) (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)) := by
  have Hclosure : Γ ≤ ⨅ T : bSet 𝔹,
      _root_.imp (T ⊆ᴮ partialChoices D C R ⊓ inclusionChain T)
        (bv_union T ∈ᴮ partialChoices D C R) := by
    apply le_iInf
    intro T
    rw [← deduction]
    exact partialChoices_chain_union (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right)
  have Hzorn : Γ ≤ _root_.imp (partialChoices D C R =ᴮ ∅)ᶜ
      (_root_.imp
        (⨅ T : bSet 𝔹,
          _root_.imp (T ⊆ᴮ partialChoices D C R ⊓ inclusionChain T)
            (bv_union T ∈ᴮ partialChoices D C R))
        (⨆ f : bSet 𝔹, f ∈ᴮ partialChoices D C R ⊓
          ⨅ g : bSet 𝔹, _root_.imp (g ∈ᴮ partialChoices D C R) (_root_.imp (f ⊆ᴮ g) (f =ᴮ g)))) :=
    (bSet_zorns_lemma' (Γ := Γ)).trans (iInf_le _ (partialChoices D C R))
  exact (le_inf ((le_inf Hzorn partialChoices_nonempty).trans bv_imp_elim)
    Hclosure).trans bv_imp_elim

theorem insert_subset_of_mem {f X z : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ f ⊆ᴮ X) (Hz : Γ ≤ z ∈ᴮ X) :
    Γ ≤ bSet.insert1 z f ⊆ᴮ X := by
  rw [subset_unfold']
  apply le_iInf
  intro w
  have Hinsert : w ∈ᴮ bSet.insert1 z f = w =ᴮ z ⊔ w ∈ᴮ f := mem_insert1
  rw [← deduction, Hinsert]
  apply bv_or_elim_right
  · exact bv_rw' (ϕ := fun a => a ∈ᴮ X) inf_le_right
      (h_congr := B_ext_mem_left) (H_new := inf_le_left.trans Hz)
  · exact mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right

/-- A maximal functional choice has no missing point in the domain of a
total relation. The permitted output need not be fresh. -/
theorem maximal_partialChoice_covers {D C R f : bSet 𝔹} {Γ : 𝔹}
    (Htotal : Γ ≤ is_total D C R)
    (Hmem : Γ ≤ f ∈ᴮ partialChoices D C R)
    (Hmax : Γ ≤ ⨅ g : bSet 𝔹, _root_.imp (g ∈ᴮ partialChoices D C R)
      (_root_.imp (f ⊆ᴮ g) (f =ᴮ g))) :
    Γ ≤ D ⊆ᴮ graphDomain D C f := by
  have Hf := mem_partialChoices_iff.mp Hmem
  have Hsub : Γ ≤ f ⊆ᴮ R ∩ᴮ prod D C := Hf.trans inf_le_left
  have Hprod : Γ ≤ f ⊆ᴮ prod D C := (subset_binary_inter_iff.mp Hsub).2
  have Hfunc : Γ ≤ is_function (graphDomain D C f) C f :=
    function_on_graphDomain Hprod (Hf.trans inf_le_right)
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  rw [← compl_compl (x ∈ᴮ graphDomain D C f), ← imp_bot, ← deduction]
  let Δ := (Γ ⊓ x ∈ᴮ D) ⊓ (x ∈ᴮ graphDomain D C f)ᶜ
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Hx : Δ ≤ x ∈ᴮ D := inf_le_left.trans inf_le_right
  have Hex : Δ ≤ ⨆ y : bSet 𝔹, y ∈ᴮ C ⊓ pair x y ∈ᴮ R :=
    (le_inf (HΔ.trans (Htotal.trans (iInf_le _ x))) Hx).trans bv_imp_elim
  obtain ⟨y, Hy⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hpair : Δ ≤ pair x y ∈ᴮ R ∩ᴮ prod D C :=
    mem_binary_inter_iff.mpr ⟨Hy.trans inf_le_right, mem_prod Hx (Hy.trans inf_le_left)⟩
  have Hnew : Δ ≤ bSet.insert1 (pair x y) f ∈ᴮ partialChoices D C R :=
    mem_partialChoices_iff.mpr
      (le_inf (insert_subset_of_mem (HΔ.trans Hsub) Hpair)
        (is_func_insertPair (HΔ.trans Hfunc) inf_le_right))
  have Heq : Δ ≤ f =ᴮ bSet.insert1 (pair x y) f :=
    (le_inf ((le_inf
      (HΔ.trans (Hmax.trans (iInf_le _ (bSet.insert1 (pair x y) f))))
      Hnew).trans bv_imp_elim) subset_insertPair).trans bv_imp_elim
  have Hold : Δ ≤ pair x y ∈ᴮ f := mem_congr bv_refl (bv_symm Heq) pair_mem_insertPair
  exact bv_absurd _ (mem_graphDomain_of_pair (HΔ.trans Hprod) Hold) inf_le_right

theorem maximal_partialChoice_function {D C R f : bSet 𝔹} {Γ : 𝔹}
    (Htotal : Γ ≤ is_total D C R)
    (Hmem : Γ ≤ f ∈ᴮ partialChoices D C R)
    (Hmax : Γ ≤ ⨅ g : bSet 𝔹, _root_.imp (g ∈ᴮ partialChoices D C R)
      (_root_.imp (f ⊆ᴮ g) (f =ᴮ g))) :
    Γ ≤ is_function D C f ⊓ f ⊆ᴮ R := by
  have Hf := mem_partialChoices_iff.mp Hmem
  have Hsupport := subset_binary_inter_iff.mp (Hf.trans inf_le_left)
  have Hcover := maximal_partialChoice_covers Htotal Hmem Hmax
  refine le_inf (le_inf (le_inf (Hf.trans inf_le_right) ?_) Hsupport.2) Hsupport.1
  apply le_iInf
  intro x
  rw [← deduction]
  have Hdom : Γ ⊓ x ∈ᴮ D ≤ x ∈ᴮ graphDomain D C f :=
    mem_of_mem_subset (inf_le_left.trans Hcover) inf_le_right
  rw [mem_graphDomain] at Hdom
  exact Hdom.trans inf_le_right

/-- Every internally total bounded relation has an actual internal choice
function contained in it, in the same arbitrary Boolean context. -/
theorem bounded_choice {D C R : bSet 𝔹} {Γ : 𝔹}
    (Htotal : Γ ≤ is_total D C R) :
    Γ ≤ ⨆ f : bSet 𝔹, is_function D C f ⊓ f ⊆ᴮ R := by
  have Hmax := exists_maximal_partialChoice (D := D) (C := C) (R := R) (Γ := Γ)
  apply (le_inf (le_refl Γ) Hmax).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro f
  apply le_iSup_of_le f
  exact maximal_partialChoice_function (inf_le_left.trans Htotal)
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)

/-- Fullness extracts a single name for the constructed choice function;
the selected name still satisfies both properties under precisely Γ. -/
theorem exists_function_subrelation {D C R : bSet 𝔹} {Γ : 𝔹}
    (Htotal : Γ ≤ is_total D C R) :
    ∃ f : bSet 𝔹, Γ ≤ is_function D C f ⊓ f ⊆ᴮ R :=
  exists_convert (bounded_choice Htotal) (B_ext_inf B_ext_is_function_right B_ext_subset_left)

end bSet.ErdosRelationChoice
