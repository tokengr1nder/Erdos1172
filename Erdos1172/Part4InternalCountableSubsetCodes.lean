/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountableRealEnumeration
public import Erdos1172.Part4InternalSmallFiberBound
public import Erdos1172.Part4InternalCantor

@[expose] public section

/-!
All internally countable subsets of an omega-one-small name have an
omega-one-sized code family under internal CH. The construction uses one
actual partial enumeration per subset, its complete marker-and-bit real
code, and bounded internal choice. Empty subsets and arbitrary mixed names
are included. This is not just a finite-product or ground-countability bound.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableSubsetCodes

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph ErdosCountableRealEnumeration
open ErdosCountableRealMatrix ErdosSmallFiberBound

local notation "Pω" => bv_powerset (bSet.omega : bSet 𝔹)

def countableSubsets (A : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun T => injects_into T bSet.omega) (bv_powerset A)

theorem mem_countableSubsets_iff {A T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ T ∈ᴮ countableSubsets A ↔ Γ ≤ T ⊆ᴮ A ∧ Γ ≤ injects_into T bSet.omega := by
  unfold countableSubsets
  rw [mem_comprehend_and B_ext_injects_into_left]
  exact and_congr mem_powerset_iff Iff.rfl

private theorem enumCode_congr_set (j e : bSet 𝔹) :
    B_congr (fun T => realGraphCode (enumGraph T j e)) := by
  intro T U Γ H
  exact realGraphCode_congr (enumGraph_congr_set j e H)

private theorem enumCode_congr_index (T e : bSet 𝔹) :
    B_congr (fun j => realGraphCode (enumGraph T j e)) := by
  intro j k Γ H
  exact realGraphCode_congr (enumGraph_congr_index T e H)

def subsetCodeSpec (e T c : bSet 𝔹) : 𝔹 :=
  ⨆ j, is_injective_function T bSet.omega j ⊓ c =ᴮ realGraphCode (enumGraph T j e)

theorem subsetCodeSpec_ext_set (e c : bSet 𝔹) :
    B_ext (fun T => subsetCodeSpec e T c) :=
  B_ext_iSup (h := fun j => B_ext_inf
    (B_ext_inf B_ext_is_function_left B_ext_const)
    (B_ext_term (ϕ := fun d => c =ᴮ d) (t := fun T => realGraphCode (enumGraph T j e))
      B_ext_bv_eq_right (enumCode_congr_set j e)))

theorem subsetCodeSpec_ext_code (e T : bSet 𝔹) : B_ext (subsetCodeSpec e T) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_bv_eq_left)

theorem subsetCodeSpec_witness {e T c : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ subsetCodeSpec e T c) :
    ∃ j : bSet 𝔹, Γ ≤ is_injective_function T bSet.omega j ⊓
      c =ᴮ realGraphCode (enumGraph T j e) :=
  exists_convert H (B_ext_inf B_ext_injective_code
    (B_ext_term (ϕ := fun d => c =ᴮ d) (t := fun j => realGraphCode (enumGraph T j e))
      B_ext_bv_eq_right (enumCode_congr_index T e)))

theorem exists_subset_real_code (e : bSet 𝔹) {T : bSet 𝔹} {Γ : 𝔹}
    (HT : Γ ≤ injects_into T bSet.omega) :
    ∃ c : bSet 𝔹, Γ ≤ c ∈ᴮ Pω ⊓ subsetCodeSpec e T c := by
  obtain ⟨j, Hj⟩ := exists_convert (injection_into_of_injects_into HT) B_ext_injective_code
  exact ⟨realGraphCode (enumGraph T j e), le_inf (realGraphCode_mem _)
    (le_iSup_of_le j (le_inf Hj bv_refl))⟩

/-- Equality of chosen codes reflects equality of whole subsets, even
when their partial enumerations were chosen independently. -/
theorem subsetCodeSpec_reflects_equality {A e T U c d : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_injective_function A Pω e)
    (HT : Γ ≤ T ⊆ᴮ A) (HU : Γ ≤ U ⊆ᴮ A)
    (HTc : Γ ≤ subsetCodeSpec e T c) (HUd : Γ ≤ subsetCodeSpec e U d)
    (Hcd : Γ ≤ c =ᴮ d) : Γ ≤ T =ᴮ U := by
  obtain ⟨j, Hj⟩ := subsetCodeSpec_witness HTc
  obtain ⟨k, Hk⟩ := subsetCodeSpec_witness HUd
  have Hcodes : Γ ≤ realGraphCode (enumGraph T j e) =ᴮ realGraphCode (enumGraph U k e) :=
    bv_trans (bv_symm (Hj.trans inf_le_right)) (bv_trans Hcd (Hk.trans inf_le_right))
  have Hgraphs := (realGraphCode_eq_iff
    (enumGraph_is_func_of_injections He (Hj.trans inf_le_left)) enumGraph_subset
    (enumGraph_is_func_of_injections He (Hk.trans inf_le_left)) enumGraph_subset).mp Hcodes
  exact eq_of_enumGraph_eq He HT HU (Hj.trans inf_le_left) (Hk.trans inf_le_left) Hgraphs

def subsetCodeFamilyLaw (A e F : bSet 𝔹) : 𝔹 :=
  ⨅ T, ⨅ c, _root_.imp (T ∈ᴮ countableSubsets A ⊓ pair T c ∈ᴮ F)
    (subsetCodeSpec e T c)

theorem subsetCodeFamilyLaw_apply {A e F T c : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ subsetCodeFamilyLaw A e F)
    (HT : Γ ≤ T ∈ᴮ countableSubsets A) (Hpair : Γ ≤ pair T c ∈ᴮ F) :
    Γ ≤ subsetCodeSpec e T c :=
  (le_inf (Hlaw.trans ((iInf_le _ T).trans (iInf_le _ c)))
    (le_inf HT Hpair)).trans bv_imp_elim

theorem subsetCodeFamily_is_inj {A e F : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_injective_function A Pω e)
    (HF : Γ ≤ is_function (countableSubsets A) Pω F)
    (Hlaw : Γ ≤ subsetCodeFamilyLaw A e F) : Γ ≤ is_inj F := by
  apply le_iInf
  intro T
  apply le_iInf
  intro U
  apply le_iInf
  intro c
  apply le_iInf
  intro d
  rw [← deduction]
  let Δ := Γ ⊓ ((pair T c ∈ᴮ F ⊓ pair U d ∈ᴮ F) ⊓ c =ᴮ d)
  have HTc : Δ ≤ pair T c ∈ᴮ F := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have HUd : Δ ≤ pair U d ∈ᴮ F := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have HT : Δ ≤ T ∈ᴮ countableSubsets A :=
    mem_domain_of_is_function HTc (inf_le_left.trans HF)
  have HU : Δ ≤ U ∈ᴮ countableSubsets A :=
    mem_domain_of_is_function HUd (inf_le_left.trans HF)
  exact subsetCodeSpec_reflects_equality (inf_le_left.trans He)
    (mem_countableSubsets_iff.mp HT).1 (mem_countableSubsets_iff.mp HU).1
    (subsetCodeFamilyLaw_apply (inf_le_left.trans Hlaw) HT HTc)
    (subsetCodeFamilyLaw_apply (inf_le_left.trans Hlaw) HU HUd)
    (show Δ ≤ c =ᴮ d from inf_le_right.trans inf_le_right)

/-- The code assignment is one actual supported internal injection, not
an external selection of one enumeration for each displayed subset. -/
theorem exists_countable_subset_real_coding {A e : bSet 𝔹} {Γ : 𝔹}
    (He : Γ ≤ is_injective_function A Pω e) :
    ∃ F : bSet 𝔹, Γ ≤ is_injective_function (countableSubsets A) Pω F ⊓
      subsetCodeFamilyLaw A e F := by
  have Hpoint : Γ ≤ ⨅ T, _root_.imp (T ∈ᴮ countableSubsets A)
      (⨆ c, c ∈ᴮ Pω ⊓ subsetCodeSpec e T c) := by
    apply le_iInf
    intro T
    rw [← deduction]
    obtain ⟨c, Hc⟩ := exists_subset_real_code e
      ((mem_countableSubsets_iff.mp
        (show Γ ⊓ T ∈ᴮ countableSubsets A ≤ T ∈ᴮ countableSubsets A from inf_le_right)).2)
    exact le_iSup_of_le c Hc
  obtain ⟨F, HF⟩ := exists_selector_of_pointwise
    (subsetCodeSpec_ext_set e) (subsetCodeSpec_ext_code e) Hpoint
  exact ⟨F, le_inf
    (le_inf (HF.trans inf_le_left)
      (subsetCodeFamily_is_inj He (HF.trans inf_le_left) (HF.trans inf_le_right)))
    (HF.trans inf_le_right)⟩

theorem countableSubsets_injects_reals {A : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ injects_into A Pω) : Γ ≤ injects_into (countableSubsets A) Pω := by
  obtain ⟨e, He⟩ := exists_convert (injection_into_of_injects_into HA) B_ext_injective_code
  obtain ⟨F, HF⟩ := exists_countable_subset_real_coding He
  exact injects_into_of_injection_into (le_iSup_of_le F (HF.trans inf_le_left))

/-- Internal CH bounds the family of all internally countable subsets
of every omega-one-small name, without a regularity premise. -/
theorem countableSubsets_injects_omegaOne {A : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HA : Γ ≤ injects_into A omegaOne) :
    Γ ≤ injects_into (countableSubsets A) omegaOne :=
  injects_into_trans
    (countableSubsets_injects_reals (injects_into_trans HA ErdosCantor.omegaOne_injects_powerset_omega))
    (ErdosCHHartogs.CH_iff_powerset_omega_injects_omegaOne.mp HCH)

end bSet.ErdosCountableSubsetCodes
