/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalShortInfima
public import Erdos1172.Part4InternalCohenCountableUnion
public import Erdos1172.Part4InternalCountableImage

@[expose] public section

/-! # Short infima of the internally presented countable partial-function Cohen order -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosCohen ErdosRelationGraph
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def extensionOrder (P : N) : N := relationGraph P P (fun p q => q ⊆ᴮ p)

theorem extensionOrder_iff {P p q : N} {Γ : B} : Γ ≤ pair p q ∈ᴮ extensionOrder P ↔
    Γ ≤ p ∈ᴮ P ∧ Γ ≤ q ∈ᴮ P ∧ Γ ≤ q ⊆ᴮ p :=
  mem_relationGraph_iff (fun _ => B_ext_subset_right) (fun _ => B_ext_subset_left)

private theorem atDescending {D F R i j x y : N} {Γ : B} (h : Γ ≤ descendingValue D F R)
    (hi : Γ ≤ i ∈ᴮ D) (hj : Γ ≤ j ∈ᴮ D) (hij : Γ ≤ i ∈ᴮ j)
    (hix : Γ ≤ pair i x ∈ᴮ F) (hjy : Γ ≤ pair j y ∈ᴮ F) : Γ ≤ pair y x ∈ᴮ R :=
  (le_inf (h.trans (iInf_le _ i) |>.trans (iInf_le _ j) |>.trans (iInf_le _ x) |>.trans (iInf_le _ y))
    (le_inf (le_inf (le_inf hi hj) hij) (le_inf hix hjy))).trans bv_imp_elim

private theorem comparable_values {D P F i j x y : N} {Γ : B} (ho : Γ ≤ Ord D)
    (hf : Γ ≤ is_function D P F) (desc : Γ ≤ descendingValue D F (extensionOrder P))
    (hi : Γ ≤ i ∈ᴮ D) (hj : Γ ≤ j ∈ᴮ D) (hx : Γ ≤ pair i x ∈ᴮ F) (hy : Γ ≤ pair j y ∈ᴮ F) :
    Γ ≤ (x ⊆ᴮ y) ⊔ (y ⊆ᴮ x) := by
  apply (le_inf (le_refl Γ) (epsilon_trichotomy_of_Ord hi hj ho)).trans
  rw [inf_sup_left,inf_sup_left]
  apply sup_le
  · apply sup_le
    · exact (subset_of_eq (eq_of_is_function_of_eq (inf_le_left.trans hf) inf_le_right
        (inf_le_left.trans hx) (inf_le_left.trans hy))).trans le_sup_left
    · exact (extensionOrder_iff.mp (atDescending (inf_le_left.trans desc) (inf_le_left.trans hi)
        (inf_le_left.trans hj) inf_le_right (inf_le_left.trans hx) (inf_le_left.trans hy))).2.2.trans le_sup_left
  · exact (extensionOrder_iff.mp (atDescending (inf_le_left.trans desc) (inf_le_left.trans hj)
      (inf_le_left.trans hi) inf_le_right (inf_le_left.trans hy) (inf_le_left.trans hx))).2.2.trans le_sup_right

theorem descending_image_chain {D P F : N} {Γ : B} (ho : Γ ≤ Ord D) (hf : Γ ≤ is_function D P F)
    (desc : Γ ≤ descendingValue D F (extensionOrder P)) :
    Γ ≤ ErdosInjectionChain.inclusionChain (image D P F) := by
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  rw [← deduction]
  obtain ⟨i,hi⟩ := exists_convert (mem_image_iff.mp (show Γ ⊓ ((x ∈ᴮ image D P F) ⊓ y ∈ᴮ image D P F)
    ≤ x ∈ᴮ image D P F from inf_le_right.trans inf_le_left)).2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  obtain ⟨j,hj⟩ := exists_convert (mem_image_iff.mp (show Γ ⊓ ((x ∈ᴮ image D P F) ⊓ y ∈ᴮ image D P F)
    ≤ y ∈ᴮ image D P F from inf_le_right.trans inf_le_right)).2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact comparable_values (inf_le_left.trans ho) (inf_le_left.trans hf) (inf_le_left.trans desc)
    (hi.trans inf_le_left) (hj.trans inf_le_left) (hi.trans inf_le_right) (hj.trans inf_le_right)

/-- The union of the full internal image is the greatest lower bound in reverse-inclusion order
whenever it belongs to the carrier. The graph and its values may all be mixed. -/
theorem graphUnion_glb {D P F : N} {Γ : B} (hf : Γ ≤ is_function D P F)
    (member : Γ ≤ bv_union (image D P F) ∈ᴮ P) :
    Γ ≤ glbValue D F P (extensionOrder P) (bv_union (image D P F)) := by
  let C := image D P F
  refine le_inf (le_inf member (rowForall_iff.mpr ?_)) ?_
  · intro i x Δ hd hi hx
    have xp := (mem_prod_iff.mp (mem_of_mem_subset (hd.trans (subset_prod_of_is_function hf)) hx)).2
    have xc : Δ ≤ x ∈ᴮ C := mem_image_iff.mpr ⟨xp,le_iSup_of_le i (le_inf hi hx)⟩
    apply extensionOrder_iff.mpr ⟨hd.trans member,xp,?_⟩
    exact (le_inf (le_top.trans ((bv_union_spec'' C).trans (iInf_le _ x))) xc).trans bv_imp_elim
  · apply le_iInf
    intro t
    rw [← deduction]
    have ht := inf_le_right (a := Γ) (b := (t ∈ᴮ P) ⊓ lowerBoundValue D F (extensionOrder P) t)
    apply extensionOrder_iff.mpr ⟨ht.trans inf_le_left,inf_le_left.trans member,?_⟩
    rw [subset_unfold']
    apply le_iInf
    intro z
    rw [← deduction]
    obtain ⟨x,hx⟩ := exists_convert (mem_bv_union_iff.mp (show (Γ ⊓ _) ⊓ z ∈ᴮ bv_union C ≤
      z ∈ᴮ bv_union C from inf_le_right)) (B_ext_inf B_ext_mem_left B_ext_mem_right)
    obtain ⟨i,hi⟩ := exists_convert (mem_image_iff.mp (hx.trans inf_le_left)).2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    have h := rowForall_iff.mp (ht.trans inf_le_right) i x _ inf_le_left (hi.trans inf_le_left) (hi.trans inf_le_right)
    exact mem_of_mem_subset (extensionOrder_iff.mp h).2.2 (hx.trans inf_le_right)

theorem cohen_shortInfima {K : N} {Γ : B} (hK : Γ ≤ ErdosHartogs.hartogsProperty omega K) :
    Γ ≤ shortInfimaValue K (conditions K) (extensionOrder (conditions K)) := by
  apply shortInfimaValue_iff.mpr
  intro D F Δ hd hD hf hdesc
  have hk := hd.trans hK
  have ord := Ord_of_mem_Ord hD (hk.trans inf_le_left)
  have cnt := ErdosCountableImage.image_countable_of_function hf (ErdosFullGCH.hartogs_predecessor_injects hk hD)
  have member := mem_conditions_iff.mpr (condition_union_of_countable_chain hk image_subset
    (descending_image_chain ord hf hdesc) cnt)
  exact ⟨_,graphUnion_glb hf member⟩

theorem cohen_omegaOne_shortInfima :
    shortInfimaValue ErdosOmegaTwo.omegaOne (conditions (ErdosOmegaTwo.omegaOne : N))
      (extensionOrder (conditions ErdosOmegaTwo.omegaOne)) = ⊤ := top_unique (cohen_shortInfima ErdosOmegaTwo.omegaOne_property)

end bSet.ErdosShioyaInternal
