/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousRunPartial

@[expose] public section

/-!
# Extending a lawful simultaneous prefix

The entire next row graph is chosen before its vertex. Raw prefix
functionality and validity of the stored row functions are established
first; they then justify exact history transfer for all old and new
entry laws. No successful vertex or freshness of the output is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartialInjection ErdosPrefixFunction ErdosInjectionExtension
open ErdosSimultaneousEntry ErdosSimultaneousHistory

/-- Appending a complete next entry preserves the exact laws of every
entry, including on Boolean pieces where its vertex is the stop marker. -/
theorem runPartial_insert_next {color : Bool} {R S top P y Z : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ runPartial color R S top P)
    (HD : Γ ≤ graphDomain omegaOne entrySpace P ∈ᴮ omegaOne)
    (Hnew : Γ ≤ pair y Z ∈ᴮ (entrySpace : bSet 𝔹) ⊓
      entryValid color (graphDomain omegaOne entrySpace P) R S
        (vertexHistory P) (coordinateHistory P) top y Z) :
    Γ ≤ runPartial color R S top
      (bSet.insert1 (pair (graphDomain omegaOne entrySpace P) (pair y Z)) P) := by
  let D := graphDomain omegaOne entrySpace P
  let Q := bSet.insert1 (pair D (pair y Z)) P
  have HprefixQ : Γ ≤ prefixGraph omegaOne entrySpace Q :=
    prefixGraph_insert_next (HP.trans inf_le_left) HD (Hnew.trans inf_le_left)
  have HfuncQ : Γ ≤ is_func Q := HprefixQ.trans (inf_le_right.trans inf_le_left)
  have HrowsQ : Γ ≤ rowFunctions Q :=
    rowFunctions_insert (runPartial_rowFunctions HP) (Hnew.trans (inf_le_right.trans inf_le_left))
  have HfunctionP : Γ ≤ is_function D entrySpace P := runPartial_function HP
  have HY : Γ ≤ is_func' D omegaTwo (vertexHistory P) :=
    vertexHistory_is_func' graphDomain_subset (is_func'_of_is_function HfunctionP)
  have HX : Γ ≤ is_func' (prod D omegaOne) omegaOne (coordinateHistory P) :=
    coordinateHistory_is_func'_prefix graphDomain_subset
      (is_func'_of_is_function HfunctionP) (runPartial_rowFunctions HP)
  have HnewQ : Γ ≤ entryValid color D R S (vertexHistory Q) (coordinateHistory Q) top y Z :=
    entryValid_of_history_extension
      (vertexHistory_mono (show Γ ≤ P ⊆ᴮ Q from subset_insertPair))
      (coordinateHistory_mono (show Γ ≤ P ⊆ᴮ Q from subset_insertPair))
      (vertexHistory_is_func HfuncQ) (coordinateHistory_is_func HfuncQ HrowsQ)
      HY HX graphDomain_subset (Hnew.trans inf_le_right)
  refine le_inf HprefixQ ?_
  apply le_iInf
  intro i
  apply le_iInf
  intro v
  apply le_iInf
  intro W
  rw [← deduction]
  let Δ := Γ ⊓ pair i (pair v W) ∈ᴮ Q
  have Hcases : Δ ≤ pair i (pair v W) =ᴮ pair D (pair y Z) ⊔ pair i (pair v W) ∈ᴮ P := by
    rw [← mem_insert1]
    exact inf_le_right
  apply (le_inf (le_refl Δ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · let Λ := Δ ⊓ pair i (pair v W) =ᴮ pair D (pair y Z)
    have HΛ : Λ ≤ Γ := inf_le_left.trans inf_le_left
    have HiD : Λ ≤ i =ᴮ D := eq_of_eq_pair_left' inf_le_right
    have Hvw : Λ ≤ pair v W =ᴮ pair y Z := eq_of_eq_pair_right' inf_le_right
    have Hvy : Λ ≤ v =ᴮ y := eq_of_eq_pair_left' Hvw
    have HWZ : Λ ≤ W =ᴮ Z := eq_of_eq_pair_right' Hvw
    have Hrows : Λ ≤ entryValid color D R S (vertexHistory Q) (coordinateHistory Q) top y W :=
      bv_rw' (ϕ := fun U => entryValid color D R S (vertexHistory Q) (coordinateHistory Q) top y U)
        HWZ (h_congr := entryValid_ext_rows color D R S (vertexHistory Q) (coordinateHistory Q) top y)
        (H_new := HΛ.trans HnewQ)
    have Hvalue : Λ ≤ entryValid color D R S (vertexHistory Q) (coordinateHistory Q) top v W :=
      bv_rw' (ϕ := fun z => entryValid color D R S (vertexHistory Q) (coordinateHistory Q) top z W)
        Hvy (h_congr := entryValid_ext_value color D R S (vertexHistory Q) (coordinateHistory Q) top W)
        (H_new := Hrows)
    exact bv_rw' (ϕ := fun d => entryValid color d R S (vertexHistory Q) (coordinateHistory Q) top v W)
      HiD (h_congr := entryValid_ext_stage color R S (vertexHistory Q) (coordinateHistory Q) top v W)
      (H_new := Hvalue)
  · exact runEntry_of_extension subset_insertPair
      (inf_le_left.trans (inf_le_left.trans HfuncQ))
      (inf_le_left.trans (inf_le_left.trans HrowsQ))
      (inf_le_left.trans (inf_le_left.trans HP)) inf_le_right

end bSet.ErdosSimultaneousRun
