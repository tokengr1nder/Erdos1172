/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRunEndpointCongruence
public import Erdos1172.Part4InternalSimultaneousRunTotal
public import Erdos1172.Part4InternalSmallFiberBound

@[expose] public section

/-!
Bounded internal choice constructs one actual supported run-valued function
on all omega-two endpoints. Every value is a full lawful simultaneous run
for its own endpoint. No external family of chosen names, successful run,
or common stopped history is supplied as a premise.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosSimultaneousEntry ErdosSimultaneousRowChoice

def runCodes : bSet 𝔹 := bv_powerset (prod omegaOne entrySpace)

theorem function_mem_runCodes {P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P) : Γ ≤ P ∈ᴮ runCodes :=
  mem_powerset_iff.mpr (HP.trans inf_le_right)

def endpointRunFamilyLaw (color : Bool) (R S F : bSet 𝔹) : 𝔹 :=
  ⨅ top, ⨅ P, _root_.imp (top ∈ᴮ omegaTwo ⊓ pair top P ∈ᴮ F)
    (is_function omegaOne entrySpace P ⊓ runLaw color R S top P)

theorem endpointRunFamilyLaw_apply
    {color : Bool} {R S F top P : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ endpointRunFamilyLaw color R S F)
    (Htop : Γ ≤ top ∈ᴮ omegaTwo) (HP : Γ ≤ pair top P ∈ᴮ F) :
    Γ ≤ is_function omegaOne entrySpace P ⊓ runLaw color R S top P :=
  (le_inf (HF.trans ((iInf_le _ top).trans (iInf_le _ P)))
    (le_inf Htop HP)).trans bv_imp_elim

theorem exists_endpoint_run_family
    {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J)) :
    ∃ F : bSet 𝔹, Γ ≤ is_function omegaTwo runCodes F ⊓
      endpointRunFamilyLaw color R S F := by
  apply ErdosSmallFiberBound.exists_selector_of_pointwise
    (P := fun top P => is_function omegaOne entrySpace P ⊓ runLaw color R S top P)
    (fun P => B_ext_inf B_ext_const (runLaw_ext_top color R S P))
    (fun top => B_ext_inf B_ext_is_function_right (runLaw_ext_graph color R S top))
  apply le_iInf
  intro top
  rw [← deduction]
  obtain ⟨P, HP⟩ := exists_simultaneous_run (color := color) (R := R)
    (show Γ ⊓ top ∈ᴮ omegaTwo ≤ top ∈ᴮ omegaTwo from inf_le_right)
    (inf_le_left.trans HS) (inf_le_left.trans Hrows)
  exact le_iSup_of_le P (le_inf (function_mem_runCodes (HP.trans inf_le_left)) HP)

theorem endpoint_run_family_value
    {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J)) :
    Γ ≤ ⨆ F, is_function omegaTwo runCodes F ⊓ endpointRunFamilyLaw color R S F := by
  obtain ⟨F, HF⟩ := exists_endpoint_run_family (color := color) (R := R) HS Hrows
  exact le_iSup_of_le F HF

end bSet.ErdosSimultaneousRun
