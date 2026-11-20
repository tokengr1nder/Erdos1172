/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCollapseGraph
public import Erdos1172.Part4ShioyaAnonymousOrdinalPresentation

@[expose] public section

/-! # The ordinal-string tree is dense in the arbitrary-domain countable collapse -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosRelationGraph ErdosPartialInjection ErdosCountableImage ErdosOmegaTwo
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

/-- Projecting the graph onto its first coordinates preserves internal countability. -/
theorem domain_countable {Γ : B} {K P f : N} (hs : Γ ≤ f ⊆ᴮ prod K P)
    (hc : Γ ≤ injects_into f omega) : Γ ≤ injects_into (graphDomain K P f) omega := by
  let pred (z i : N) : B := ⨆ y : N, z =ᴮ pair i y
  have left (i : N) : B_ext (fun z => pred z i) := B_ext_iSup (h := fun _ => B_ext_bv_eq_left)
  have right (z : N) : B_ext (pred z) := B_ext_iSup (h := fun _ => B_ext_pair_left B_ext_bv_eq_right)
  let π := relationGraph f K pred
  have law : Γ ≤ is_function f K π := by
    apply relationGraph_is_function left right
    · refine le_iInf fun z => projection_imp.mpr ?_
      intro d hd hz
      obtain ⟨i,hi,y,_,eq⟩ := mem_prod_iff₂.mp (mem_of_mem_subset (hd.trans hs) hz)
      exact le_iSup_of_le i (le_inf hi (le_iSup_of_le y eq))
    · intro z z' i i' d _ _ _ _ _ old new eq
      obtain ⟨y,hy⟩ := exists_convert old (B_ext_pair_right B_ext_bv_eq_right)
      obtain ⟨y',hy'⟩ := exists_convert new (B_ext_pair_right B_ext_bv_eq_right)
      exact eq_of_eq_pair_left' (bv_trans (bv_symm hy) (bv_trans eq hy'))
  apply injects_into_trans _ (image_countable_of_function law hc)
  apply injects_into_of_subset
  rw [subset_unfold']
  refine le_iInf fun i => projection_imp.mpr ?_
  intro d _ hi
  rw [mem_graphDomain] at hi
  obtain ⟨y,hy⟩ := exists_convert (hi.trans inf_le_right) (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  apply mem_image_iff.mpr
  exact ⟨hi.trans inf_le_left,le_iSup_of_le (pair i y) (le_inf (hy.trans inf_le_right)
    ((mem_relationGraph_iff left right).mpr ⟨hy.trans inf_le_right,hi.trans inf_le_left,le_iSup_of_le y bv_refl⟩))⟩

end bSet.ErdosShioyaInternal.CollapsePath
