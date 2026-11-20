/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalUnorderedCollapseProjection

@[expose] public section

/-! # Order, separativity, and short infima of the mixed countable collapse -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosPartialInjection ErdosOmegaTwo ErdosInjectionExtension ErdosCountableSuccessor
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

theorem extension_order_laws (C : N) {Γ : B} : Γ ≤ partialOrderValue C (extensionOrder C) := by
  refine le_inf ErdosRelationGraph.relationGraph_subset (le_inf (allIn_intro ?_) (le_inf (allIn_intro ?_) (allIn_intro ?_)))
  · intro _ _ p hp
    exact extensionOrder_iff.mpr ⟨hp,hp,subset_self⟩
  · intro _ _ p _
    refine allIn_intro fun _ q _ => projection_imp.mpr fun _ _ h => ?_
    exact subset_ext (extensionOrder_iff.mp (h.trans inf_le_right)).2.2 (extensionOrder_iff.mp (h.trans inf_le_left)).2.2
  · intro _ _ p _
    refine allIn_intro fun _ q _ => allIn_intro fun _ r _ => projection_imp.mpr fun _ _ h => ?_
    obtain ⟨hp,_,qp⟩ := extensionOrder_iff.mp (h.trans inf_le_left)
    obtain ⟨_,hr,rq⟩ := extensionOrder_iff.mp (h.trans inf_le_right)
    exact extensionOrder_iff.mpr ⟨hp,hr,subset_trans' rq qp⟩

theorem collapse_union {Γ : B} {H X U : N} (sub : Γ ≤ U ⊆ᴮ countableCollapse H X)
    (count : Γ ≤ injects_into U omega) (chain : Γ ≤ ErdosInjectionChain.inclusionChain U) :
    Γ ≤ bv_union U ∈ᴮ countableCollapse H X := by
  have members {d : B} (hd : d ≤ Γ) {g : N} (hg : d ≤ g ∈ᴮ U) :=
    countableCollapse_mem.mp (mem_of_mem_subset (hd.trans sub) hg)
  exact countableCollapse_mem.mpr ⟨ErdosInjectionChain.subset_prod_union
    (le_iInf fun _ => projection_imp.mpr fun _ hd hg => (members hd hg).1),
    ErdosInjectionChain.is_func_union_of_chain chain
      (le_iInf fun _ => projection_imp.mpr fun _ hd hg => (members hd hg).2.1),
    ErdosCountableFamilyUnion.union_countable count
      (le_iInf fun _ => projection_imp.mpr fun _ hd hg => (members hd hg).2.2)⟩

theorem collapse_shortInfima (H X : N) {Γ : B} :
    Γ ≤ shortInfimaValue omegaOne (countableCollapse H X) (extensionOrder (countableCollapse H X)) := by
  apply shortInfimaValue_iff.mpr
  intro D s d _ hD hs desc
  exact ⟨_,graphUnion_glb hs (collapse_union image_subset
    (ErdosCountableImage.image_countable_of_function hs (omegaOne_member_injects hD))
    (descending_image_chain (Ord_of_mem_Ord hD omegaOne_Ord) hs desc))⟩

private theorem negate {d a b : B} (h : d ≤ aᶜ) (f : ∀ e ≤ d, e ≤ b → e ≤ a) : d ≤ bᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  exact disjoint_iff_inf_le.mpr ((le_inf (f _ inf_le_left inf_le_right) (inf_le_left.trans h)).trans (by simp))

private theorem separate_rows {Γ : B} {H X p q t i v y : N}
    (ht : Γ ≤ t ∈ᴮ countableCollapse H X) (hp : Γ ≤ p ∈ᴮ countableCollapse H X)
    (pt : Γ ≤ p ⊆ᴮ t) (tv : Γ ≤ edge t i v) (qy : Γ ≤ edge q i y) (ne : Γ ≤ (v =ᴮ y)ᶜ) :
    Γ ≤ separatesValue (countableCollapse H X) (extensionOrder (countableCollapse H X)) p q := by
  refine le_iSup_of_le t (le_inf ht (le_inf (extensionOrder_iff.mpr ⟨ht,hp,pt⟩) ?_))
  apply negate ne
  intro d hd h
  obtain ⟨a,ha⟩ := exists_convert h (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_left B_ext_pair_mem_left))
  have func := (countableCollapse_mem.mp (ha.trans inf_le_left)).2.1
  exact eq_of_is_func_of_eq func bv_refl
    (mem_of_mem_subset (extensionOrder_iff.mp (ha.trans (inf_le_right.trans inf_le_left))).2.2 (hd.trans tv))
    (mem_of_mem_subset (extensionOrder_iff.mp (ha.trans (inf_le_right.trans inf_le_right))).2.2 (hd.trans qy))

theorem collapse_insert {Γ : B} {H X p i v : N} (hp : Γ ≤ p ∈ᴮ countableCollapse H X)
    (hi : Γ ≤ i ∈ᴮ H) (hv : Γ ≤ v ∈ᴮ X) (fresh : Γ ≤ (i ∈ᴮ graphDomain H X p)ᶜ) :
    Γ ≤ bSet.insert1 (pair i v) p ∈ᴮ countableCollapse H X := by
  obtain ⟨sub,func,count⟩ := countableCollapse_mem.mp hp
  exact countableCollapse_mem.mpr ⟨ErdosRelationChoice.insert_subset_of_mem sub (mem_prod hi hv),
    is_func_insertPair (function_on_graphDomain sub func) fresh,
    insert_countable_of_fresh count (negate fresh fun _ hd h => mem_graphDomain_of_pair (hd.trans sub) h)⟩

/-- With two distinct available values, each failed inclusion can be forced
to disagree at one coordinate. Neither the missing pair nor its coordinate
has to be decided in the ground model. -/
theorem collapse_separative {Γ : B} {H X v₀ v₁ : N} (h₀ : Γ ≤ v₀ ∈ᴮ X) (h₁ : Γ ≤ v₁ ∈ᴮ X)
    (apart : Γ ≤ (v₀ =ᴮ v₁)ᶜ) : Γ ≤ separativeValue (countableCollapse H X) (extensionOrder (countableCollapse H X)) := by
  apply allIn_intro
  intro d hd p hp
  refine allIn_intro fun {c} cd q hq => projection_imp.mpr ?_
  intro b bc missed
  have pq := (bc.trans cd).trans hp
  have qq := bc.trans hq
  have missing := negate missed (fun _ h sub => extensionOrder_iff.mpr ⟨h.trans pq,h.trans qq,sub⟩)
  rw [subset_unfold'] at missing
  simp only [compl_iInf,_root_.imp,compl_sup,compl_compl] at missing
  obtain ⟨z,hz⟩ := exists_convert missing (B_ext_inf B_ext_mem_left (B_ext_neg (h := B_ext_mem_left)))
  obtain ⟨i,hi,y,_,eq⟩ := mem_prod_iff₂.mp (mem_of_mem_subset (countableCollapse_mem.mp qq).1 (hz.trans inf_le_left))
  have qy := mem_congr eq bv_refl (hz.trans inf_le_left)
  have absent := negate (hz.trans inf_le_right) (fun _ h e => mem_congr (bv_symm (h.trans eq)) bv_refl e)
  let D := graphDomain H X p
  apply (le_inf (a := b) le_rfl (show b ≤ (i ∈ᴮ D) ⊔ (i ∈ᴮ D)ᶜ by simp)).trans
  apply bv_or_elim_right
  · have inD : b ⊓ i ∈ᴮ D ≤ i ∈ᴮ graphDomain H X p := inf_le_right
    obtain ⟨v,hv⟩ := exists_convert ((inD.trans (mem_graphDomain H X p i).le).trans inf_le_right)
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    exact separate_rows (inf_le_left.trans pq) (inf_le_left.trans pq) subset_self (hv.trans inf_le_right)
      (inf_le_left.trans qy) (negate (inf_le_left.trans absent) fun _ h e => mem_congr (pair_congr bv_refl e) bv_refl (h.trans (hv.trans inf_le_right)))
  · let e := b ⊓ (i ∈ᴮ D)ᶜ
    have add {a : B} (ae : a ≤ e) {v : N} (hv : a ≤ v ∈ᴮ X) (ne : a ≤ (v =ᴮ y)ᶜ) :=
      separate_rows (collapse_insert ((ae.trans inf_le_left).trans pq) ((ae.trans inf_le_left).trans hi) hv (ae.trans inf_le_right))
        ((ae.trans inf_le_left).trans pq) subset_insertPair pair_mem_insertPair ((ae.trans inf_le_left).trans qy) ne
    have base : e ≤ Γ := inf_le_left.trans (bc.trans (cd.trans hd))
    apply (le_inf (a := e) le_rfl (show e ≤ (v₀ =ᴮ y) ⊔ (v₀ =ᴮ y)ᶜ by simp)).trans
    apply bv_or_elim_right
    · apply add inf_le_left ((inf_le_left.trans base).trans h₁)
      apply negate ((inf_le_left.trans base).trans apart)
      exact fun _ h e' => bv_trans (h.trans inf_le_right) (bv_symm e')
    · exact add inf_le_left ((inf_le_left.trans base).trans h₀) inf_le_right

end bSet.ErdosShioyaInternal.CollapsePath
