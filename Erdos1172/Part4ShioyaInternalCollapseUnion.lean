/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCollapseGraph

@[expose] public section

/-! # Unions and preservation of existing infima by native collapse evaluation -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosBoundedFunctionValue ErdosPrefixFunction ErdosPartialInjection ErdosInjectionChain
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

private theorem member_sub_union {Γ : B} {g U : N} (hg : Γ ≤ g ∈ᴮ U) : Γ ≤ g ⊆ᴮ bv_union U := by
  rw [subset_unfold']
  exact le_iInf fun x => projection_imp.mpr fun _ hd hx => mem_bv_union_iff.mpr (le_iSup_of_le g (le_inf (hd.trans hg) hx))

theorem value_union {Γ : B} {P R K f U p x : N} (ok : Γ ≤ Ord K) (po : Γ ≤ partialOrderValue P R)
    (cl : Γ ≤ shortInfimaValue K P R) (pathsU : Γ ≤ U ⊆ᴮ paths K P) (eq : Γ ≤ f =ᴮ bv_union U)
    (endp : Γ ≤ value K P R f p) (hx : Γ ≤ x ∈ᴮ P)
    (older : ∀ {d : B}, d ≤ Γ → ∀ {g y : N}, d ≤ g ∈ᴮ U → d ≤ edge (graph K P R) g y → d ≤ edge R x y) :
    Γ ≤ edge R x p := by
  apply value_cases endp
  intro d hd l h _ hf hh law out
  apply (out.2 le_rfl (hd.trans hx)).mp
  apply allIn_intro
  intro c cd C hc
  have base := cd.trans hd
  obtain ⟨j,hj⟩ := exists_convert (mem_image_iff.mp hc).2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have label := graphValue_pair_mem (cd.trans hf) (hj.trans inf_le_left)
  have inU := mem_congr bv_refl (base.trans eq) label
  obtain ⟨g,hg⟩ := exists_convert (mem_bv_union_iff.mp inU) (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have pg := mem_of_mem_subset (base.trans pathsU) (hg.trans inf_le_left)
  obtain ⟨a,ha,gf⟩ := (paths_mem (base.trans ok)).mp pg
  obtain ⟨k,y,hk,klaw,hy,rep⟩ := exists_evaluation (base.trans po) (base.trans cl) (base.trans ok) ha gf
  have gy := graph_pair.mpr ⟨pg,hy,value_of_trace ha gf hk klaw ⟨hy,rep⟩⟩
  have survive := (rep le_rfl (base.trans hx)).mpr (older base (hg.trans inf_le_left) gy)
  have gfsub := subset_trans' (member_sub_union (hg.trans inf_le_left)) (subset_of_eq (bv_symm (base.trans eq)))
  have ja := mem_domain_of_is_function (hg.trans inf_le_right) gf
  have row := graphValue_spec hk ja
  have seen := allIn_elim survive (mem_image (row.trans inf_le_right) ja (row.trans inf_le_left))
  have rowEq := prefix_rows (Ord_of_mem_Ord ha (base.trans ok)) gf (cd.trans hf) gfsub hk (cd.trans hh)
    klaw (cd.trans law) le_rfl ja
  exact mem_congr bv_refl (bv_trans rowEq (graphValue_eq_of_pair (cd.trans hh) (hj.trans inf_le_right))) seen

private theorem paths_prefix {Γ : B} {K P g : N} (ok : Γ ≤ Ord K) (hg : Γ ≤ g ∈ᴮ paths K P) :
    Γ ≤ prefixGraph K P g := by
  obtain ⟨a,ha,hf⟩ := (paths_mem ok).mp hg
  exact le_inf (subset_trans' (subset_prod_of_is_function hf) (prod_domain_mono (subset_of_mem_transitive
    (ok.trans inf_le_right) ha))) (le_inf (hf.trans (inf_le_left.trans inf_le_left))
      (prefixClosed_of_ordinal_function (Ord_of_mem_Ord ha ok) hf))

theorem glb_is_union {Γ : B} {K P A s f : N} (ok : Γ ≤ Ord K) (oa : Γ ≤ Ord A)
    (hs : Γ ≤ is_function A (paths K P) s) (desc : Γ ≤ descendingValue A s (extensionOrder (paths K P)))
    (hg : Γ ≤ glbValue A s (paths K P) (extensionOrder (paths K P)) f) :
    Γ ≤ f =ᴮ bv_union (image A (paths K P) s) := by
  let U := image A (paths K P) s
  let m := bv_union U
  have ispath := hg.trans (inf_le_left.trans inf_le_left)
  obtain ⟨l,hl,hf⟩ := (paths_mem ok).mp ispath
  have cmp : ∀ {d : B}, d ≤ Γ → ∀ {g : N}, d ≤ g ∈ᴮ U → d ≤ g ⊆ᴮ f := by
    intro d hd g h
    obtain ⟨j,hj⟩ := exists_convert (mem_image_iff.mp h).2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact (extensionOrder_iff.mp (rowForall_iff.mp (hg.trans (inf_le_left.trans inf_le_right))
      j g d hd (hj.trans inf_le_left) (hj.trans inf_le_right))).2.2
  have upper : Γ ≤ m ⊆ᴮ f := by
    rw [subset_unfold']
    refine le_iInf fun z => projection_imp.mpr ?_
    intro d hd hz
    obtain ⟨g,hg'⟩ := exists_convert (mem_bv_union_iff.mp hz) (B_ext_inf B_ext_mem_left B_ext_mem_right)
    exact mem_of_mem_subset (cmp hd (hg'.trans inf_le_left)) (hg'.trans inf_le_right)
  have pfx : Γ ≤ prefixGraph K P m := prefixGraph_union_of_chain (descending_image_chain oa hs desc)
    (le_iInf fun g => projection_imp.mpr fun _ hd hin => paths_prefix (hd.trans ok) (mem_of_mem_subset image_subset hin))
  have dom := prefixGraph_function pfx
  have domOrd := prefixGraph_domain_Ord ok pfx
  have domBound := length_mono dom hf upper
  have alt := ErdosInitialSegments.eq_or_mem_of_ordinal_subset domOrd (Ord_of_mem_Ord hl ok) domBound
  have short : Γ ≤ graphDomain K P m ∈ᴮ K := by
    apply (le_inf le_rfl alt).trans
    rw [inf_sup_left]
    exact sup_le (mem_congr (bv_symm inf_le_right) bv_refl (inf_le_left.trans hl))
      (mem_of_mem_Ord inf_le_right (inf_le_left.trans hl) (inf_le_left.trans ok))
  have member := (paths_mem ok).mpr ⟨_,short,dom⟩
  have low : Γ ≤ lowerBoundValue A s (extensionOrder (paths K P)) m := by
    apply rowForall_iff.mpr
    intro j g d hd hj hjg
    have gp := (projection_function_bounds (hd.trans hs) hjg).2
    exact extensionOrder_iff.mpr ⟨hd.trans member,gp,member_sub_union (mem_image hjg hj gp)⟩
  have strongest := projection_imp.mp ((hg.trans inf_le_right).trans (iInf_le _ m)) Γ le_rfl (le_inf member low)
  exact subset_ext (extensionOrder_iff.mp strongest).2.2 upper

end bSet.ErdosShioyaInternal.CollapsePath
