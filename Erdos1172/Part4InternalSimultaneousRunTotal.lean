/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousRunMaximal
public import Erdos1172.Part4InternalSimultaneousRunExtension

@[expose] public section

/-!
# Totality of an actual simultaneous run

A maximal lawful prefix cannot end at a proper internal omega-one
ordinal. Its actual decoded histories are total on that prefix, so the
proved next-entry theorem constructs another bounded entry. Maximality
would put this new domain point into its own strict predecessors.
The resulting run is a genuine full supported function. It may choose
the endpoint sentinel: neither success nor a homogeneous block follows
from totality alone, and neither is assumed here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartialInjection ErdosPrefixFunction
open ErdosSimultaneousEntry ErdosSimultaneousHistory ErdosSimultaneousRowChoice

/-- A maximal lawful prefix has full domain, including when its vertex
choices eventually equal the fixed endpoint. The row ideals can vary
internally; no external family of ideal witnesses is supplied. -/
theorem maximal_run_domain_eq
    {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (Htop : Γ ≤ top ∈ᴮ omegaTwo)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J))
    (HP : Γ ≤ runPartial color R S top P)
    (Hmax : Γ ≤ ⨅ Q, _root_.imp (runPartial color R S top Q)
      (_root_.imp (P ⊆ᴮ Q) (P =ᴮ Q))) :
    Γ ≤ graphDomain omegaOne entrySpace P =ᴮ omegaOne := by
  let D := graphDomain omegaOne entrySpace P
  have Hprefix : Γ ≤ prefixGraph omegaOne entrySpace P := HP.trans inf_le_left
  have Hfunction : Γ ≤ is_function D entrySpace P := runPartial_function HP
  have Hcases := ErdosInitialSegments.eq_or_mem_of_ordinal_subset
    (prefixGraph_domain_Ord omegaOne_Ord Hprefix) omegaOne_Ord
    (graphDomain_subset (κ := omegaOne) (S := entrySpace) (f := P) (Γ := Γ))
  apply (le_inf (le_refl Γ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact inf_le_right
  · let Δ := Γ ⊓ D ∈ᴮ omegaOne
    have HΔ : Δ ≤ Γ := inf_le_left
    have HweakP : Δ ≤ is_func' D entrySpace P :=
      is_func'_of_is_function (HΔ.trans Hfunction)
    have HDsub : Δ ≤ D ⊆ᴮ omegaOne := graphDomain_subset
    have HY : Δ ≤ is_func' D omegaTwo (vertexHistory P) :=
      vertexHistory_is_func' HDsub HweakP
    have HX : Δ ≤ is_func' (prod D omegaOne) omegaOne (coordinateHistory P) :=
      coordinateHistory_is_func'_prefix HDsub HweakP
        (runPartial_rowFunctions (HΔ.trans HP))
    obtain ⟨y, Z, Hnew⟩ := exists_next_entry (color := color) (R := R)
      (show Δ ≤ D ∈ᴮ omegaOne from inf_le_right)
      (HΔ.trans Htop) (HΔ.trans HS) HY HX (HΔ.trans Hrows)
    have Hextended : Δ ≤ runPartial color R S top
        (bSet.insert1 (pair D (pair y Z)) P) :=
      runPartial_insert_next (HΔ.trans HP)
        (show Δ ≤ D ∈ᴮ omegaOne from inf_le_right) Hnew
    have Heq : Δ ≤ P =ᴮ bSet.insert1 (pair D (pair y Z)) P :=
      (le_inf ((le_inf (HΔ.trans (Hmax.trans
        (iInf_le _ (bSet.insert1 (pair D (pair y Z)) P)))) Hextended).trans bv_imp_elim)
        ErdosInjectionExtension.subset_insertPair).trans bv_imp_elim
    have Hpair : Δ ≤ pair D (pair y Z) ∈ᴮ P :=
      mem_congr bv_refl (bv_symm Heq) ErdosInjectionExtension.pair_mem_insertPair
    exact (bot_of_mem_self' (mem_domain_of_is_function Hpair (HΔ.trans Hfunction))).trans
      bot_le

/-- Construct one full supported simultaneous run at the original Boolean
condition. The theorem asserts its exact entry law, not successful vertex
choices, injectivity of the run, or a partition relation. -/
theorem exists_simultaneous_run
    {color : Bool} {R S top : bSet 𝔹} {Γ : 𝔹}
    (Htop : Γ ≤ top ∈ᴮ omegaTwo)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J)) :
    ∃ P : bSet 𝔹, Γ ≤ is_function omegaOne entrySpace P ⊓ runLaw color R S top P := by
  obtain ⟨P, HP⟩ := exists_convert
    (exists_maximal_runPartial (color := color) (R := R) (S := S) (top := top) (Γ := Γ))
    (maximal_runPartial_ext color R S top)
  have Hpartial : Γ ≤ runPartial color R S top P := HP.trans inf_le_left
  have Hdomain := maximal_run_domain_eq Htop HS Hrows Hpartial (HP.trans inf_le_right)
  exact ⟨P, le_inf
    (bv_rw'' (ϕ := fun D => is_function D entrySpace P) Hdomain
      (runPartial_function Hpartial) B_ext_is_function_left)
    (Hpartial.trans inf_le_right)⟩

end bSet.ErdosSimultaneousRun
