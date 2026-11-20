/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalGreedyMaximal
public import Erdos1172.Part4InternalGreedyExtension

@[expose] public section

/-!
An actual full omega-one least-choice graph. A maximal coherent initial
graph cannot stop at a countable domain: the proved least-candidate theorem
constructs its next pair. Thus totality is derived, not assumed as a field
or supplied as an externally enumerated successful run.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosGreedyPartial

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartialInjection ErdosPartition
open ErdosColargeIntersection ErdosOrdinalLeast ErdosRowCandidates

theorem colarge_values_on_prefix {J T F : bSet 𝔹} {Γ : 𝔹}
    (HT : Γ ≤ T ⊆ᴮ omegaOne)
    (Hvalues : Γ ≤ ⨅ j, ⨅ A, _root_.imp (j ∈ᴮ omegaOne ⊓ pair j A ∈ᴮ F)
      (difference omegaOne A ∈ᴮ J)) :
    Γ ≤ ⨅ j, ⨅ A, _root_.imp (j ∈ᴮ T ⊓ pair j A ∈ᴮ F)
      (difference omegaOne A ∈ᴮ J) := by
  apply le_iInf
  intro j
  apply le_iInf
  intro A
  rw [← deduction]
  exact (le_inf (inf_le_left.trans (Hvalues.trans
    ((iInf_le _ j).trans (iInf_le _ A))))
    (le_inf (mem_of_mem_subset (inf_le_left.trans HT) (inf_le_right.trans inf_le_left))
      (inf_le_right.trans inf_le_right))).trans bv_imp_elim

theorem maximal_greedy_domain_eq {J seed F f : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hseed : Γ ≤ colarge omegaOne J seed)
    (HF : Γ ≤ is_func' omegaOne (bv_powerset omegaOne) F)
    (Hvalues : Γ ≤ ⨅ j, ⨅ A, _root_.imp (j ∈ᴮ omegaOne ⊓ pair j A ∈ᴮ F)
      (difference omegaOne A ∈ᴮ J))
    (Hf : Γ ≤ greedyPartial seed F f)
    (Hmax : Γ ≤ ⨅ g, _root_.imp (greedyPartial seed F g)
      (_root_.imp (f ⊆ᴮ g) (f =ᴮ g))) :
    Γ ≤ graphDomain omegaOne omegaOne f =ᴮ omegaOne := by
  let D := graphDomain omegaOne omegaOne f
  have Hp : Γ ≤ partialGraph omegaOne omegaOne f := Hf.trans inf_le_left
  have Hfunction : Γ ≤ is_function D omegaOne f :=
    (partialGraph_function Hp).trans inf_le_left
  have Hcases := ErdosInitialSegments.eq_or_mem_of_ordinal_subset
    (partialGraph_domain_Ord omegaOne_Ord Hp) omegaOne_Ord
    (graphDomain_subset (κ := omegaOne) (S := omegaOne) (f := f) (Γ := Γ))
  apply (le_inf (le_refl Γ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact inf_le_right
  · let Δ := Γ ⊓ D ∈ᴮ omegaOne
    have HΔ : Δ ≤ Γ := inf_le_left
    obtain ⟨y, Hy⟩ := exists_least_row_candidate
      (HΔ.trans HJ) (HΔ.trans Habsorb) (HΔ.trans Hclosure)
      (show Δ ≤ D ∈ᴮ omegaOne from inf_le_right) (HΔ.trans Hseed)
      (is_func'_subset_of_is_func' (HΔ.trans HF) graphDomain_subset)
      (colarge_values_on_prefix graphDomain_subset (HΔ.trans Hvalues))
      (is_func'_of_is_function (HΔ.trans Hfunction))
    have Hnew : Δ ≤ greedyPartial seed F (bSet.insert1 (pair D y) f) :=
      greedyPartial_insert_next (HΔ.trans Hf)
        (show Δ ≤ D ∈ᴮ omegaOne from inf_le_right) (Hy.trans inf_le_right)
    have Heq : Δ ≤ f =ᴮ bSet.insert1 (pair D y) f :=
      (le_inf ((le_inf (HΔ.trans (Hmax.trans
        (iInf_le _ (bSet.insert1 (pair D y) f)))) Hnew).trans bv_imp_elim)
        ErdosInjectionExtension.subset_insertPair).trans bv_imp_elim
    have Hpair : Δ ≤ pair D y ∈ᴮ f :=
      mem_congr bv_refl (bv_symm Heq) ErdosInjectionExtension.pair_mem_insertPair
    exact (bot_of_mem_self' (mem_domain_of_is_function Hpair (HΔ.trans Hfunction))).trans
      bot_le

/-- Properness and countable closure produce an actual supported full
least-choice graph. This is independent of CH and ideal normality. -/
theorem exists_greedy_function {J seed F : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hseed : Γ ≤ colarge omegaOne J seed)
    (HF : Γ ≤ is_func' omegaOne (bv_powerset omegaOne) F)
    (Hvalues : Γ ≤ ⨅ j, ⨅ A, _root_.imp (j ∈ᴮ omegaOne ⊓ pair j A ∈ᴮ F)
      (difference omegaOne A ∈ᴮ J)) :
    ∃ f : bSet 𝔹, Γ ≤ is_injective_function omegaOne omegaOne f ⊓
      greedyLaw seed F f := by
  obtain ⟨f, Hf⟩ := exists_convert
    (exists_maximal_greedyPartial (seed := seed) (F := F) (Γ := Γ))
    (maximal_greedyPartial_ext seed F)
  have Hp : Γ ≤ greedyPartial seed F f := Hf.trans inf_le_left
  have Hdomain := maximal_greedy_domain_eq HJ Habsorb Hclosure Hseed HF Hvalues Hp
    (Hf.trans inf_le_right)
  have Hinj := partialGraph_function (Hp.trans inf_le_left)
  exact ⟨f, le_inf
    (bv_rw'' (ϕ := fun D => is_injective_function D omegaOne f) Hdomain Hinj
      B_ext_is_injective_function_left)
    (Hp.trans inf_le_right)⟩

end bSet.ErdosGreedyPartial
