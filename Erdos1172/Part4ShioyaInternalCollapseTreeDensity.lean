/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalTreeProjection
public import Erdos1172.Part4ShioyaAnonymousOrdinalPresentation
public import Erdos1172.Part4InternalOmegaOneCountablyBounded
public import Erdos1172.Part4InternalStoppedCoordinateTriangle
public import Erdos1172.Part4InternalRelationChoice

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

/-- Complete a supported partial function on a larger specified domain. Its old
values are preserved on their whole Boolean support, including mixed inputs. -/
theorem exists_total_extension {Γ : B} {K P f b p₀ : N} (hs : Γ ≤ f ⊆ᴮ prod K P)
    (hf : Γ ≤ is_func f) (hb : Γ ≤ graphDomain K P f ⊆ᴮ b) (hp : Γ ≤ p₀ ∈ᴮ P) :
    ∃ g : N, Γ ≤ is_function b P g ∧ Γ ≤ f ⊆ᴮ g := by
  let D := graphDomain K P f
  let pred (i y : N) := _root_.imp (i ∈ᴮ D) (edge f i y)
  have left (y : N) : B_ext (fun i => pred i y) := B_ext_imp (h₁ := B_ext_mem_left) (h₂ := B_ext_pair_mem_left)
  have right (i : N) : B_ext (pred i) := B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_pair_mem_right)
  let Q := relationGraph b P pred
  have total : Γ ≤ is_total b P Q := by
    refine le_iInf fun i => projection_imp.mpr ?_
    intro d hd hi
    have help {c : B} (cd : c ≤ d) {y : N} (hy : c ≤ y ∈ᴮ P) (pr : c ≤ pred i y) :
        c ≤ ⨆ y : N, (y ∈ᴮ P) ⊓ pair i y ∈ᴮ Q :=
      le_iSup_of_le y (le_inf hy ((mem_relationGraph_iff left right).mpr ⟨cd.trans hi,hy,pr⟩))
    apply (le_inf (a := d) le_rfl (show d ≤ (i ∈ᴮ D) ⊔ (i ∈ᴮ D)ᶜ by simp)).trans
    apply bv_or_elim_right
    · have h : d ⊓ i ∈ᴮ D ≤ i ∈ᴮ graphDomain K P f := inf_le_right
      have row := h.trans (mem_graphDomain K P f i).le
      obtain ⟨y,hy⟩ := exists_convert (row.trans inf_le_right) (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
      exact help inf_le_left (hy.trans inf_le_left) (projection_imp.mpr fun _ hc _ => hc.trans (hy.trans inf_le_right))
    · apply help inf_le_left ((inf_le_left.trans hd).trans hp)
      apply projection_imp.mpr
      intro c h hc
      exact (le_inf hc (h.trans inf_le_right)).trans (by simp)
  obtain ⟨g,hg⟩ := ErdosRelationChoice.exists_function_subrelation total
  refine ⟨g,hg.trans inf_le_left,?_⟩
  rw [subset_unfold']
  refine le_iInf fun z => projection_imp.mpr ?_
  intro d hd hz
  obtain ⟨i,_,y,_,eq⟩ := mem_prod_iff₂.mp (mem_of_mem_subset (hd.trans hs) hz)
  have old := mem_congr eq bv_refl hz
  have hi := mem_graphDomain_of_pair (hd.trans hs) old
  have hib := mem_of_mem_subset (hd.trans hb) hi
  have htotal : d ≤ is_total b P g := hd.trans (hg.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  obtain ⟨v,hv⟩ := exists_convert (projection_imp.mp (htotal.trans (iInf_le _ i)) d le_rfl hib)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have vrow := hv.trans inf_le_right
  have pr := (mem_relationGraph_iff left right).mp (mem_of_mem_subset (hd.trans (hg.trans inf_le_right)) vrow)
  have vy := eq_of_is_func_of_eq (hd.trans hf) bv_refl (projection_imp.mp pr.2.2 d le_rfl hi) old
  exact mem_congr (bv_trans (pair_congr bv_refl vy) (bv_symm eq)) bv_refl vrow

theorem path_mem_countableCollapse {Γ : B} {P f : N} (h : Γ ≤ f ∈ᴮ paths omegaOne P) :
    Γ ≤ f ∈ᴮ countableCollapse omegaOne P := by
  obtain ⟨l,hl,hf⟩ := (paths_mem omegaOne_Ord).mp h
  have func := hf.trans (inf_le_left.trans inf_le_left)
  exact countableCollapse_mem.mpr ⟨subset_trans' (subset_prod_of_is_function hf)
    (prod_domain_mono (subset_of_mem_Ord hl omegaOne_Ord)),func,
    ErdosStoppedCoordinateTriangle.graph_countable_of_domain func (subset_prod_of_is_function hf)
      (omegaOne_member_injects hl)⟩

/-- Every countable partial assignment into an inhabited alphabet extends to
a total string on one internally countable ordinal. -/
theorem tree_dense_countableCollapse {Γ : B} {P p₀ : N} (hp : Γ ≤ p₀ ∈ᴮ P) :
    Γ ≤ projectionDense (countableCollapse omegaOne P) (extensionOrder (countableCollapse omegaOne P))
      (paths omegaOne P) := by
  apply projectionDense_iff.mpr
  intro d hd f h
  obtain ⟨sub,func,count⟩ := countableCollapse_mem.mp h
  obtain ⟨b,hb⟩ := ErdosOmegaOneCountablyBounded.exists_bound_of_countable graphDomain_subset
    (domain_countable sub count)
  obtain ⟨g,hg,fg⟩ := exists_total_extension sub func (hb.trans inf_le_right) (hd.trans hp)
  have path := (paths_mem omegaOne_Ord).mpr ⟨b,hb.trans inf_le_left,hg⟩
  exact ⟨g,path,extensionOrder_iff.mpr ⟨path_mem_countableCollapse path,h,fg⟩⟩

end bSet.ErdosShioyaInternal.CollapsePath
