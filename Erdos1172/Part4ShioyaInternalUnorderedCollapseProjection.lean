/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCollapseTreeDensity

@[expose] public section

/-! # The native projection from arbitrary countable partial assignments -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosPartialInjection ErdosOmegaTwo ErdosPrefixFunction
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

theorem descending_on_subcarrier {Γ : B} {C D A s : N} (hs : Γ ≤ is_function A D s)
    (desc : Γ ≤ descendingValue A s (extensionOrder C)) :
    Γ ≤ descendingValue A s (extensionOrder D) := by
  refine le_iInf fun i => le_iInf fun j => le_iInf fun x => le_iInf fun y => projection_imp.mpr ?_
  intro d hd h
  have orig := projection_imp.mp (desc.trans (iInf_le _ i) |>.trans (iInf_le _ j) |>.trans
    (iInf_le _ x) |>.trans (iInf_le _ y)) d hd h
  exact extensionOrder_iff.mpr ⟨(projection_function_bounds (hd.trans hs) (h.trans (inf_le_right.trans inf_le_right))).2,
    (projection_function_bounds (hd.trans hs) (h.trans (inf_le_right.trans inf_le_left))).2,
    (extensionOrder_iff.mp orig).2.2⟩

/-- Short infima in the full collapse of a sequence of paths are still paths
and are infima for the restricted order. The ambient infimum itself bounds
the size of the union, including the empty sequence. -/
theorem unordered_glb_path {Γ : B} {P A s f : N} (oa : Γ ≤ Ord A)
    (hs : Γ ≤ is_function A (paths omegaOne P) s)
    (desc : Γ ≤ descendingValue A s (extensionOrder (countableCollapse omegaOne P)))
    (hg : Γ ≤ glbValue A s (countableCollapse omegaOne P) (extensionOrder (countableCollapse omegaOne P)) f) :
    Γ ≤ glbValue A s (paths omegaOne P) (extensionOrder (paths omegaOne P)) f := by
  let U := image A (paths omegaOne P) s
  let m := bv_union U
  have ambient := hg.trans (inf_le_left.trans inf_le_left)
  have inc : Γ ≤ m ⊆ᴮ f := by
    rw [subset_unfold']
    refine le_iInf fun z => projection_imp.mpr ?_
    intro d hd hz
    obtain ⟨g,gu⟩ := exists_convert (mem_bv_union_iff.mp hz) (B_ext_inf B_ext_mem_left B_ext_mem_right)
    obtain ⟨i,hi⟩ := exists_convert (mem_image_iff.mp (gu.trans inf_le_left)).2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    have cmp := rowForall_iff.mp (hg.trans (inf_le_left.trans inf_le_right))
      i g d hd (hi.trans inf_le_left) (hi.trans inf_le_right)
    exact mem_of_mem_subset (extensionOrder_iff.mp cmp).2.2 (gu.trans inf_le_right)
  have pfx : Γ ≤ prefixGraph omegaOne P m := by
    apply prefixGraph_union_of_chain (descending_image_chain oa hs (descending_on_subcarrier hs desc))
    refine le_iInf fun g => projection_imp.mpr ?_
    intro d _ h
    obtain ⟨a,ha,hf⟩ := (paths_mem omegaOne_Ord).mp (mem_of_mem_subset image_subset h)
    exact le_inf (subset_trans' (subset_prod_of_is_function hf) (prod_domain_mono (subset_of_mem_Ord ha omegaOne_Ord)))
      (le_inf (hf.trans (inf_le_left.trans inf_le_left)) (prefixClosed_of_ordinal_function (Ord_of_mem_Ord ha omegaOne_Ord) hf))
  have count := injects_into_trans (injects_into_of_subset inc) (countableCollapse_mem.mp ambient).2.2
  have mem := (paths_mem omegaOne_Ord).mpr ⟨_,ErdosOmegaOneCountablyBounded.countable_ordinal_mem_omegaOne
    (prefixGraph_domain_Ord omegaOne_Ord pfx) (domain_countable (pfx.trans inf_le_left) count),prefixGraph_function pfx⟩
  have actual := graphUnion_glb hs mem
  have low : Γ ≤ lowerBoundValue A s (extensionOrder (countableCollapse omegaOne P)) m := by
    apply rowForall_iff.mpr
    intro i g d hd hi edge
    have r := extensionOrder_iff.mp (rowForall_iff.mp (actual.trans (inf_le_left.trans inf_le_right)) i g d hd hi edge)
    exact extensionOrder_iff.mpr ⟨path_mem_countableCollapse r.1,path_mem_countableCollapse r.2.1,r.2.2⟩
  have strongest := projection_imp.mp ((hg.trans inf_le_right).trans (iInf_le _ m)) Γ le_rfl
    (le_inf (path_mem_countableCollapse mem) low)
  have eq := subset_ext (extensionOrder_iff.mp strongest).2.2 inc
  exact bv_rw' eq (h_congr := glbValue_ext_point _ _ _ _) (H_new := actual)

/-- The actual arbitrary-domain countable collapse projects onto any internally
short-complete order. Its closed dense domain consists of the ordinal-length
strings and its projection graph is the native recursive evaluation. -/
theorem unordered_collapse_projection {Γ : B} {P R : N} (po : Γ ≤ partialOrderValue P R)
    (cl : Γ ≤ shortInfimaValue omegaOne P R) :
    Γ ≤ partialProjectionValue omegaOne (countableCollapse omegaOne P) (extensionOrder (countableCollapse omegaOne P))
      P R (paths omegaOne P) (graph omegaOne P R) := by
  have zero : Γ ≤ (∅ : N) ∈ᴮ omegaOne := mem_congr zero_eq_empty bv_refl
    (mem_of_mem_Ord zero_mem_one (le_top.trans one_mem_omegaOne) omegaOne_Ord)
  have law := projectionLaws_iff.mp (tree_projection omegaOne_Ord zero (by
    intro d _ a h
    exact ErdosOmegaOneCountablyBounded.countable_ordinal_mem_omegaOne (Ord_succ (Ord_of_mem_Ord h omegaOne_Ord))
      (ErdosCountableSuccessor.succ_countable (omegaOne_member_injects h))) po cl)
  have empty : Γ ≤ is_function (∅ : N) P ∅ := le_inf is_func'_empty empty_subset
  obtain ⟨_,p,_,_,hp,_⟩ := exists_evaluation po cl omegaOne_Ord zero empty
  apply projectionLaws_iff.mpr
  refine ⟨?_,law.func,projectionDense_iff.mp (tree_dense_countableCollapse hp),?_,law.reaches,?_,?_,?_⟩
  · rw [subset_unfold']
    exact le_iInf fun _ => projection_imp.mpr fun _ _ h => path_mem_countableCollapse h
  · intro d hd x y a b hx hy comp
    exact law.mono hd hx hy (extensionOrder_iff.mpr ⟨(graph_pair.mp hx).1,(graph_pair.mp hy).1,
      (extensionOrder_iff.mp comp).2.2⟩)
  · intro d hd x a q hx hq cmp
    obtain ⟨y,b,hy,hxy,hb⟩ := law.lifts hd hx hq cmp
    obtain ⟨yD,xD,xy⟩ := extensionOrder_iff.mp hxy
    exact ⟨y,b,hy,extensionOrder_iff.mpr ⟨path_mem_countableCollapse yD,path_mem_countableCollapse xD,xy⟩,hb⟩
  · intro d _ A s f hA hs desc glb
    exact (unordered_glb_path (Ord_of_mem_Ord hA omegaOne_Ord) hs desc glb).trans (inf_le_left.trans inf_le_left)
  · intro d hd A s f q hA hs desc glb hf
    exact law.continuous hd hA hs (descending_on_subcarrier hs desc)
      (unordered_glb_path (Ord_of_mem_Ord hA omegaOne_Ord) hs desc glb) hf

end bSet.ErdosShioyaInternal.CollapsePath
