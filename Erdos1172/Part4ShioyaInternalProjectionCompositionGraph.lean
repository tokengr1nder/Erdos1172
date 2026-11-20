/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalProjectionLaws

@[expose] public section

/-! # The composite graph on the named pullback of two domains -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosRelationGraph ErdosBoundedFunctionValue
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def through (F G x z : N) : B := ⨆ y : N, edge F x y ⊓ edge G y z

private theorem through_left (F G z : N) : B_ext (fun x => through F G x z) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const)

private theorem through_right (F G x : N) : B_ext (through F G x) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_pair_mem_right)

private theorem through_witness {Γ : B} {F G x z : N} (h : Γ ≤ through F G x z) :
    ∃ y : N, Γ ≤ edge F x y ∧ Γ ≤ edge G y z := by
  obtain ⟨y,hy⟩ := exists_convert h (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left)
  exact ⟨y,hy.trans inf_le_left,hy.trans inf_le_right⟩

def projectionComposite (D F E G T : N) : N :=
  relationGraph (projectionPullback D F E) T (through F G)

variable {Γ : B}

theorem projectionComposite_pair {D F E G Q T x z : N} (hf : Γ ≤ is_function D Q F) (hg : Γ ≤ is_function E T G) :
    Γ ≤ edge (projectionComposite D F E G T) x z ↔ ∃ y : N, Γ ≤ edge F x y ∧ Γ ≤ edge G y z := by
  constructor
  · intro h
    exact through_witness ((mem_relationGraph_iff (through_left F G) (through_right F G)).mp h).2.2
  · rintro ⟨y,hxy,hyz⟩
    have ab := projection_function_bounds hf hxy
    have bc := projection_function_bounds hg hyz
    exact (mem_relationGraph_iff (through_left F G) (through_right F G)).mpr
      ⟨projectionPullback_mem.mpr ⟨ab.1,y,hxy,bc.1⟩,bc.2,le_iSup_of_le y (le_inf hxy hyz)⟩

theorem projectionComposite_function {D F E G Q T : N} (hf : Γ ≤ is_function D Q F) (hg : Γ ≤ is_function E T G) :
    Γ ≤ is_function (projectionPullback D F E) T (projectionComposite D F E G T) := by
  apply relationGraph_is_function (through_left F G) (through_right F G)
  · apply le_iInf
    intro x
    apply projection_imp.mpr
    intro Δ hd hx
    obtain ⟨_,y,hxy,hy⟩ := projectionPullback_mem.mp hx
    have hz := graphValue_spec (hd.trans hg) hy
    exact le_iSup_of_le _ (le_inf (hz.trans inf_le_left) (le_iSup_of_le y (le_inf hxy (hz.trans inf_le_right))))
  · intro _ _ _ _ _ hd _ _ _ _ h₁ h₂ hx
    obtain ⟨y₁,a₁,b₁⟩ := through_witness h₁
    obtain ⟨y₂,a₂,b₂⟩ := through_witness h₂
    exact eq_of_is_function_of_eq (hd.trans hg) (eq_of_is_function_of_eq (hd.trans hf) hx a₁ a₂) b₁ b₂

/-- A graph remains the same function when every one of its outputs belongs
to another prescribed codomain. This also permits shrinking a codomain. -/
theorem function_recodomain {A P C f : N} (hf : Γ ≤ is_function A P f)
    (hc : ∀ {Δ : B}, Δ ≤ Γ → ∀ {i x : N}, Δ ≤ edge f i x → Δ ≤ x ∈ᴮ C) :
    Γ ≤ is_function A C f := by
  refine le_inf (le_inf (hf.trans (inf_le_left.trans inf_le_left)) ?_) ?_
  · apply le_iInf
    intro i
    apply projection_imp.mpr
    intro Δ hd hi
    have hpair := graphValue_pair_mem (hd.trans hf) hi
    exact le_iSup_of_le _ (le_inf (hc hd hpair) hpair)
  · rw [subset_unfold']
    apply le_iInf
    intro z
    apply projection_imp.mpr
    intro Δ hd hz
    obtain ⟨i,hi,x,_,he⟩ := mem_prod_iff₂.mp (mem_of_mem_subset (hd.trans (subset_prod_of_is_function hf)) hz)
    exact mem_prod_iff₂.mpr ⟨i,hi,x,hc hd (mem_congr he bv_refl hz),he⟩

theorem projectionSequence_descending {K P R Q S D F A f g : N} (π : ProjectionLaws Γ K P R Q S D F)
    (hf : Γ ≤ is_function A D f) (hd : Γ ≤ descendingValue A f R)
    (mapped : Γ ≤ projectionSequence F f g) : Γ ≤ descendingValue A g S := by
  refine le_iInf fun i => le_iInf fun j => le_iInf fun a => le_iInf fun b => projection_imp.mpr ?_
  intro Δ h context
  have hi := context.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hj := context.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have x := graphValue_pair_mem (h.trans hf) hi
  have y := graphValue_pair_mem (h.trans hf) hj
  have descending := projection_imp.mp (hd.trans (iInf_le _ i) |>.trans (iInf_le _ j) |>.trans
    (iInf_le _ (graphValue D f i)) |>.trans (iInf_le _ (graphValue D f j))) Δ h
    (le_inf (context.trans inf_le_left) (le_inf x y))
  exact π.mono h (projectionSequence_apply (h.trans mapped) y (context.trans (inf_le_right.trans inf_le_right)))
    (projectionSequence_apply (h.trans mapped) x (context.trans (inf_le_right.trans inf_le_left))) descending

end bSet.ErdosShioyaInternal
