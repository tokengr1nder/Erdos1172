/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCollapseUnion
public import Erdos1172.Part4InternalIncreasingComposition

@[expose] public section

/-! # The continuous native projection from the tree of short ordinal strings -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosIncreasingComposition
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

theorem graph_continuity {Γ : B} {K P R A s f q : N} (ok : Γ ≤ Ord K) (po : Γ ≤ partialOrderValue P R)
    (cl : Γ ≤ shortInfimaValue K P R) (ha : Γ ≤ A ∈ᴮ K) (hs : Γ ≤ is_function A (paths K P) s)
    (desc : Γ ≤ descendingValue A s (extensionOrder (paths K P)))
    (glb : Γ ≤ glbValue A s (paths K P) (extensionOrder (paths K P)) f)
    (hq : Γ ≤ edge (graph K P R) f q) :
    ∃ g : N, Γ ≤ is_function A P g ∧ Γ ≤ projectionSequence (graph K P R) s g ∧ Γ ≤ glbValue A g P R q := by
  have funG := graph_function ok po cl
  let g := function_comp hs funG
  have gf : Γ ≤ is_function A P g := function_comp_is_function
  have mid {d : B} {i y : N} (h : d ≤ edge g i y) :
      ∃ u : N, d ≤ u ∈ᴮ paths K P ∧ d ≤ edge s i u ∧ d ≤ edge (graph K P R) u y := by
    obtain ⟨u,hu⟩ := comp_pair_witness (is_func'_of_is_function hs) (is_func'_of_is_function funG) h
    exact ⟨u,hu.trans inf_le_left,hu.trans (inf_le_right.trans inf_le_left),hu.trans (inf_le_right.trans inf_le_right)⟩
  have out {d : B} (hd : d ≤ Γ) {i u y : N} (hi : d ≤ edge s i u) (hy : d ≤ edge (graph K P R) u y) :
      d ≤ edge g i y := (mem_is_func'_comp_iff (is_func'_of_is_function hs) (is_func'_of_is_function funG)).mpr
    ⟨(projection_function_bounds (hd.trans hs) hi).1,(graph_pair.mp hy).2.1,
      le_iSup_of_le u (le_inf (graph_pair.mp hy).1 (le_inf hi hy))⟩
  refine ⟨g,gf,?_,le_inf (le_inf (graph_pair.mp hq).2.1 ?_) ?_⟩
  · refine le_iInf fun i => le_iInf fun x => le_iInf fun y => projection_imp.mpr ?_
    intro d hd h
    obtain ⟨u,_,hi,hy⟩ := mid (h.trans inf_le_right)
    have eq := eq_of_is_function_of_eq (hd.trans hs) bv_refl hi (h.trans inf_le_left)
    exact mem_congr (pair_congr eq bv_refl) bv_refl hy
  · apply rowForall_iff.mpr
    intro i y d hd hi hy
    obtain ⟨u,_,iu,uy⟩ := mid hy
    have below := rowForall_iff.mp (glb.trans (inf_le_left.trans inf_le_right)) i u d hd hi iu
    exact value_monotone (hd.trans ok) (hd.trans po) (extensionOrder_iff.mp below).2.2
      (graph_pair.mp uy).2.2 (hd.trans (graph_pair.mp hq).2.2)
  · refine le_iInf fun x => projection_imp.mpr ?_
    intro d hd hp
    have eq := glb_is_union ok (Ord_of_mem_Ord ha ok) hs desc glb
    apply value_union (hd.trans ok) (hd.trans po) (hd.trans cl) image_subset (hd.trans eq)
      (hd.trans (graph_pair.mp hq).2.2) (hp.trans inf_le_left)
    intro c cd u y hu uy
    obtain ⟨i,hi⟩ := exists_convert (mem_image_iff.mp hu).2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact rowForall_iff.mp (hp.trans inf_le_right) i y c cd (hi.trans inf_le_left)
      (out (cd.trans hd) (hi.trans inf_le_right) uy)

/-- Every named short-complete order is a projection of its full ordinal
string tree. Its genuine evaluation graph lifts refinements and preserves
all existing short descending infima on every Boolean subcondition. -/
theorem tree_projection {Γ : B} {K P R : N} (ok : Γ ≤ Ord K) (zero : Γ ≤ (∅ : N) ∈ᴮ K)
    (lim : ∀ {Δ : B}, Δ ≤ Γ → ∀ {a : N}, Δ ≤ a ∈ᴮ K → Δ ≤ succ a ∈ᴮ K)
    (po : Γ ≤ partialOrderValue P R) (cl : Γ ≤ shortInfimaValue K P R) :
    Γ ≤ partialProjectionValue K (paths K P) (extensionOrder (paths K P)) P R (paths K P) (graph K P R) := by
  refine le_inf (le_inf (le_inf subset_self (graph_function ok po cl)) (le_inf (le_inf (le_inf
    (projectionDense_iff.mpr (fun _ _ hp => ⟨_,hp,extensionOrder_iff.mpr ⟨hp,hp,subset_self⟩⟩))
    (graph_monotone ok po)) (graph_reaches ok po cl zero (lim le_rfl zero))) (graph_lifts ok po lim))) (le_inf ?_ ?_)
  · refine le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => projection_imp.mpr fun _ _ h => ?_
    exact h.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
  · refine le_iInf fun A => le_iInf fun s => le_iInf fun f => le_iInf fun p => projection_imp.mpr ?_
    intro d hd h
    have first := h.trans inf_le_left
    have left := first.trans inf_le_left
    obtain ⟨g,hg,hseq,hglb⟩ := graph_continuity (hd.trans ok) (hd.trans po) (hd.trans cl)
      (left.trans (inf_le_left.trans inf_le_left)) (left.trans (inf_le_left.trans inf_le_right))
      (left.trans inf_le_right) (first.trans inf_le_right) (h.trans inf_le_right)
    exact le_iSup_of_le g (le_inf (le_inf hg hseq) hglb)

end bSet.ErdosShioyaInternal.CollapsePath
