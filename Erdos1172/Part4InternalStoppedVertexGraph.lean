/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalStoppedCoordinateTriangle
public import Erdos1172.Part4InternalCountableSubsetCodes
public import Erdos1172.Part4InternalLeastStoppedHistory
public import Erdos1172.Part4InternalIndependentHomogeneous

@[expose] public section

/-!
# Countable codes for whole ordered prior vertex histories

The canonical prior graph keeps the assignment from every strict prior
stage to its decoded vertex. A supplied bound of the prior vertex image
bounds this same graph in `omegaOne × b`. Under CH, for `b < omegaTwo`,
all internally countable subsets of this fixed support form an omega-one-
small family. No reconstruction of an ordered history from its range, and
no equality of independently selected histories, is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosStoppedVertexGraph

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph ErdosSimultaneousHistory ErdosSimultaneousRun
open ErdosSimultaneousEntry ErdosOrdinalLeast ErdosStoppedCoordinateTriangle
open ErdosCountableSubsetCodes

/-- The graph is independent of the proposed cutoff and retains stage
labels. Its domain is the strict stopping prefix, including the empty case. -/
def priorVertexGraph (ρ P : bSet 𝔹) : bSet 𝔹 :=
  relationGraph ρ omegaTwo (fun i y => pair i y ∈ᴮ vertexHistory P)

theorem mem_priorVertexGraph_iff {ρ P i y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair i y ∈ᴮ priorVertexGraph ρ P ↔
      Γ ≤ i ∈ᴮ ρ ∧ Γ ≤ pair i y ∈ᴮ vertexHistory P := by
  unfold priorVertexGraph
  rw [mem_relationGraph_iff (fun _ => B_ext_pair_mem_left) (fun _ => B_ext_pair_mem_right)]
  constructor
  · rintro ⟨Hi, _, Hpair⟩
    exact ⟨Hi, Hpair⟩
  · rintro ⟨Hi, Hpair⟩
    exact ⟨Hi, (mem_vertexHistory_iff.mp Hpair).2.1, Hpair⟩

theorem priorVertexGraph_subset_product {ρ P : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ priorVertexGraph ρ P ⊆ᴮ prod ρ omegaTwo := relationGraph_subset

theorem priorVertexGraph_subset_history {ρ P : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ priorVertexGraph ρ P ⊆ᴮ vertexHistory P := by
  rw [subset_unfold']
  apply le_iInf
  intro e
  rw [← deduction]
  let Δ := Γ ⊓ e ∈ᴮ priorVertexGraph ρ P
  have Hprod : Δ ≤ e ∈ᴮ prod ρ omegaTwo :=
    mem_of_mem_subset priorVertexGraph_subset_product inf_le_right
  obtain ⟨i, _, y, _, He⟩ := mem_prod_iff₂.mp Hprod
  have Hpair := mem_priorVertexGraph_iff.mp (mem_congr He bv_refl
    (show Δ ≤ e ∈ᴮ priorVertexGraph ρ P from inf_le_right))
  exact mem_congr (bv_symm He) bv_refl Hpair.2

private theorem priorVertexGraph_subset_of_eq {ρ τ P Q : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ =ᴮ τ) (HP : Γ ≤ P =ᴮ Q) :
    Γ ≤ priorVertexGraph ρ P ⊆ᴮ priorVertexGraph τ Q := by
  rw [subset_unfold']
  apply le_iInf
  intro e
  rw [← deduction]
  let Δ := Γ ⊓ e ∈ᴮ priorVertexGraph ρ P
  have Hprod : Δ ≤ e ∈ᴮ prod ρ omegaTwo :=
    mem_of_mem_subset priorVertexGraph_subset_product inf_le_right
  obtain ⟨i, _, y, _, He⟩ := mem_prod_iff₂.mp Hprod
  have Hpair := mem_priorVertexGraph_iff.mp (mem_congr He bv_refl
    (show Δ ≤ e ∈ᴮ priorVertexGraph ρ P from inf_le_right))
  have Hnew : Δ ≤ pair i y ∈ᴮ priorVertexGraph τ Q :=
    mem_priorVertexGraph_iff.mpr
      ⟨mem_congr bv_refl (inf_le_left.trans Hρ) Hpair.1,
        mem_congr bv_refl (vertexHistory_congr (inf_le_left.trans HP)) Hpair.2⟩
  exact mem_congr (bv_symm He) bv_refl Hnew

theorem priorVertexGraph_congr {ρ τ P Q : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ =ᴮ τ) (HP : Γ ≤ P =ᴮ Q) :
    Γ ≤ priorVertexGraph ρ P =ᴮ priorVertexGraph τ Q :=
  subset_ext (priorVertexGraph_subset_of_eq Hρ HP)
    (priorVertexGraph_subset_of_eq (bv_symm Hρ) (bv_symm HP))

theorem priorVertexGraph_congr_graph (ρ : bSet 𝔹) : B_congr (priorVertexGraph ρ) := by
  intro P Q Γ H
  exact priorVertexGraph_congr bv_refl H

theorem priorVertexGraph_is_func {ρ P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_func P) : Γ ≤ is_func (priorVertexGraph ρ P) :=
  is_func_subset_of_is_func (vertexHistory_is_func HP) priorVertexGraph_subset_history

/-- The whole graph, not just its range, is internally countable. -/
theorem priorVertexGraph_countable {ρ P : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ ∈ᴮ omegaOne) (HP : Γ ≤ is_func P) :
    Γ ≤ injects_into (priorVertexGraph ρ P) bSet.omega :=
  graph_countable_of_domain (priorVertexGraph_is_func HP) priorVertexGraph_subset_product
    (omegaOne_member_injects Hρ)

theorem priorVertexGraph_value_in_priorVertices {ρ P i y : bSet 𝔹} {Γ : 𝔹}
    (Hpair : Γ ≤ pair i y ∈ᴮ priorVertexGraph ρ P) :
    Γ ≤ y ∈ᴮ priorVertices ρ P := by
  have H := mem_priorVertexGraph_iff.mp Hpair
  exact mem_image_iff.mpr ⟨(mem_vertexHistory_iff.mp H.2).2.1,
    le_iSup_of_le i (le_inf H.1 H.2)⟩

theorem priorVertexGraph_subset_bound {ρ P b : bSet 𝔹} {Γ : 𝔹}
    (Hbound : Γ ≤ priorVertices ρ P ⊆ᴮ b) :
    Γ ≤ priorVertexGraph ρ P ⊆ᴮ prod ρ b := by
  rw [subset_unfold']
  apply le_iInf
  intro e
  rw [← deduction]
  let Δ := Γ ⊓ e ∈ᴮ priorVertexGraph ρ P
  have Hprod : Δ ≤ e ∈ᴮ prod ρ omegaTwo :=
    mem_of_mem_subset priorVertexGraph_subset_product inf_le_right
  obtain ⟨i, _, y, _, He⟩ := mem_prod_iff₂.mp Hprod
  have Hpair : Δ ≤ pair i y ∈ᴮ priorVertexGraph ρ P := mem_congr He bv_refl inf_le_right
  exact mem_congr (bv_symm He) bv_refl
    (mem_prod (mem_priorVertexGraph_iff.mp Hpair).1
      (mem_of_mem_subset (inf_le_left.trans Hbound) (priorVertexGraph_value_in_priorVertices Hpair)))

theorem priorVertexGraph_subset_fixed_bound {ρ P b : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ ∈ᴮ omegaOne) (Hbound : Γ ≤ priorVertices ρ P ⊆ᴮ b) :
    Γ ≤ priorVertexGraph ρ P ⊆ᴮ prod omegaOne b :=
  subset_trans' (priorVertexGraph_subset_bound Hbound)
    (ErdosPartialInjection.prod_domain_mono (subset_of_mem_Ord Hρ omegaOne_Ord))

/-- Mixed products of these ordinal bounds reduce locally to a square:
either `b` is contained in omega-one or omega-one is contained in `b`. -/
theorem vertexGraph_support_injects_omegaOne {b : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (Hb : Γ ≤ b ∈ᴮ omegaTwo) :
    Γ ≤ injects_into (prod omegaOne b) omegaOne := by
  calc
    Γ = (Γ ⊓ b ⊆ᴮ omegaOne) ⊔ (Γ ⊓ (b ⊆ᴮ omegaOne)ᶜ) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
    _ ≤ injects_into (prod omegaOne b) omegaOne := by
      apply sup_le
      · exact injects_into_trans
          (injects_into_of_subset (ErdosIndependentHomogeneous.prod_codomain_mono inf_le_right))
          (ErdosCardinalSquare.omegaOne_square_injects (inf_le_left.trans HCH))
      · let Δ := Γ ⊓ (b ⊆ᴮ omegaOne)ᶜ
        have HbOrd : Δ ≤ Ord b := Ord_of_mem_Ord (inf_le_left.trans Hb) omegaTwo_Ord
        have Hsub : Δ ≤ omegaOne ⊆ᴮ b :=
          subset_of_mem_Ord (Ord.lt_of_not_le HbOrd omegaOne_Ord inf_le_right) HbOrd
        exact injects_into_trans
          (injects_into_of_subset (ErdosPartialInjection.prod_domain_mono Hsub))
          (injects_into_trans
            (ErdosProductInjection.injects_into_prod_self (omegaTwo_member_injects (inf_le_left.trans Hb)))
            (ErdosCardinalSquare.omegaOne_square_injects (inf_le_left.trans HCH)))

/-- This fixed family contains every countable graph with the stated
support, not only histories of the currently selected run. -/
def vertexHistoryCodes (b : bSet 𝔹) : bSet 𝔹 :=
  countableSubsets (prod omegaOne b)

theorem mem_vertexHistoryCodes_iff {b g : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ g ∈ᴮ vertexHistoryCodes b ↔
      Γ ≤ g ⊆ᴮ prod omegaOne b ∧ Γ ≤ injects_into g bSet.omega :=
  mem_countableSubsets_iff

theorem priorVertexGraph_mem_codes {ρ P b : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_func P) (Hρ : Γ ≤ ρ ∈ᴮ omegaOne)
    (Hbound : Γ ≤ priorVertices ρ P ⊆ᴮ b) :
    Γ ≤ priorVertexGraph ρ P ∈ᴮ vertexHistoryCodes b :=
  mem_vertexHistoryCodes_iff.mpr
    ⟨priorVertexGraph_subset_fixed_bound Hρ Hbound, priorVertexGraph_countable Hρ HP⟩

theorem vertexHistoryCodes_small {b : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (Hb : Γ ≤ b ∈ᴮ omegaTwo) :
    Γ ≤ injects_into (vertexHistoryCodes b) omegaOne :=
  countableSubsets_injects_omegaOne HCH (vertexGraph_support_injects_omegaOne HCH Hb)

end bSet.ErdosStoppedVertexGraph
