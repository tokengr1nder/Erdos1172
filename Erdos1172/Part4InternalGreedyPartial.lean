/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRowCandidateCongruence
public import Erdos1172.Part4InternalPartialInjectionMaximal

@[expose] public section

/-!
The actual set of partial greedy graphs on internal omega-one. Each used
coordinate is assigned the least member of its exact row-candidate set,
computed from the same graph. Separation inside the existing partial-map
family retains support, injectivity and an initial-segment domain.
No successful run, ideal assumptions, or totality on omega-one is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosGreedyPartial

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartialInjection ErdosRowCandidates ErdosOrdinalLeast

def greedyLaw (seed F f : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ x, _root_.imp (pair i x ∈ᴮ f) (leastIn (rowCandidates i seed F f) x)

def greedyPartial (seed F f : bSet 𝔹) : 𝔹 :=
  partialGraph omegaOne omegaOne f ⊓ greedyLaw seed F f

theorem greedyLaw_apply {seed F f i x : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ greedyLaw seed F f) (Hpair : Γ ≤ pair i x ∈ᴮ f) :
    Γ ≤ leastIn (rowCandidates i seed F f) x :=
  (le_inf (H.trans ((iInf_le _ i).trans (iInf_le _ x))) Hpair).trans bv_imp_elim

theorem greedyLaw_ext_graph (seed F : bSet 𝔹) : B_ext (greedyLaw seed F) :=
  B_ext_iInf (h := fun i => B_ext_iInf (h := fun x =>
    B_ext_imp (h₁ := B_ext_mem_right)
      (h₂ := B_ext_term (ϕ := fun C => leastIn C x) (t := rowCandidates i seed F)
        (leastIn_ext_set x) (rowCandidates_congr_graph i seed F))))

def greedyMaps (seed F : bSet 𝔹) : bSet 𝔹 :=
  comprehend (greedyLaw seed F) (partialMaps omegaOne omegaOne)

theorem mem_greedyMaps_iff {seed F f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ f ∈ᴮ greedyMaps seed F ↔ Γ ≤ greedyPartial seed F f := by
  unfold greedyMaps
  rw [ErdosRelationGraph.mem_comprehend_and (greedyLaw_ext_graph seed F)]
  constructor
  · rintro ⟨Hf, Hlaw⟩
    exact le_inf (mem_partialMaps_iff.mp Hf) Hlaw
  · intro H
    exact ⟨mem_partialMaps_iff.mpr (H.trans inf_le_left), H.trans inf_le_right⟩

theorem mem_greedyMaps (seed F f : bSet 𝔹) :
    f ∈ᴮ greedyMaps seed F = greedyPartial seed F f :=
  le_antisymm (mem_greedyMaps_iff.mp le_rfl) (mem_greedyMaps_iff.mpr le_rfl)

theorem greedyPartial_ext_graph (seed F : bSet 𝔹) : B_ext (greedyPartial seed F) := by
  intro f g
  rw [← mem_greedyMaps seed F f, ← mem_greedyMaps seed F g]
  exact B_ext_mem_left f g

theorem greedyPartial_function {seed F f : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ greedyPartial seed F f) :
    Γ ≤ is_injective_function (graphDomain omegaOne omegaOne f) omegaOne f :=
  partialGraph_function (H.trans inf_le_left)

/-- Prefix closure already supplies totality on every used coordinate's
strict predecessors. No external domain presentation is involved. -/
theorem prefix_is_func'_of_partial_pair {f i x : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ partialGraph omegaOne omegaOne f) (Hpair : Γ ≤ pair i x ∈ᴮ f) :
    Γ ≤ is_func' i omegaOne f := by
  refine le_inf (H.trans (inf_le_right.trans inf_le_left)) ?_
  apply le_iInf
  intro j
  rw [← deduction]
  exact prefixClosed_apply
    (inf_le_left.trans (H.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))))
    (inf_le_left.trans Hpair) inf_le_right

theorem greedyPartial_is_func'_prefix {seed F f i x : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ greedyPartial seed F f) (Hpair : Γ ≤ pair i x ∈ᴮ f) :
    Γ ≤ is_func' i omegaOne f :=
  prefix_is_func'_of_partial_pair (H.trans inf_le_left) Hpair

theorem empty_greedyLaw {seed F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ greedyLaw seed F (∅ : bSet 𝔹) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro x
  rw [← deduction]
  exact (bot_of_mem_empty inf_le_right).trans bot_le

theorem empty_greedyPartial {seed F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ greedyPartial seed F (∅ : bSet 𝔹) :=
  le_inf empty_partialGraph empty_greedyLaw

theorem empty_mem_greedyMaps {seed F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (∅ : bSet 𝔹) ∈ᴮ greedyMaps seed F :=
  mem_greedyMaps_iff.mpr empty_greedyPartial

theorem greedyMaps_nonempty {seed F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ (greedyMaps seed F =ᴮ ∅)ᶜ :=
  nonempty_of_exists_mem (greedyMaps seed F)
    (le_iSup_of_le (∅ : bSet 𝔹) empty_mem_greedyMaps)

end bSet.ErdosGreedyPartial
