/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionPreparation
public import Erdos1172.Part4InternalFusionRunSuccess

@[expose] public section

/-!
# Constructing the complete prepared successful fusion run

The enumeration, fixed selector, closed pools and common future are first
constructed from the original ideal and cardinal hypotheses. The successful
run theorem then supplies an actual terminal and a full nonstopping run,
without assuming any preparation data or a run in the final endpoint.

All witnesses and all displayed laws hold at the original Boolean condition.
Both exact two-block target exclusions remain explicit. The separate mask
positivity and countable-tail argument, and ideal/model existence, are not
claimed here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionPreparedSuccess

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosDenseBasis ErdosPartition
open ErdosFusionPreparation ErdosFusionRun ErdosFusionRunSuccess

/-- The input contains only CH, the actual proper countably closed
absorbing normal ideal with its small positive dense basis, both exact
target exclusions, and the original large future. Every other witness
is constructed, in the order enumeration, selector, pools, future, run. -/
theorem exists_prepared_successful_fusion_run
    {color : Bool} {R J I D S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HJ : Γ ≤ properIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hdiag : Γ ≤ diagonalClosure omegaOne J)
    (HD : Γ ≤ is_function I (bv_powerset omegaOne) D)
    (HDpos : Γ ≤ positiveValues omegaOne J I D)
    (Hdense : Γ ≤ denseValues omegaOne J I D)
    (HI : Γ ≤ injects_into I omegaOne)
    (Hno : Γ ≤ (hasTwoBlock color R omegaOne bSet.omega omegaTwo)ᶜ)
    (HnoOpp : Γ ≤ (hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo)ᶜ)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (HSlarge : Γ ≤ injects_into omegaTwo S) :
    ∃ E F B P Y top Run : bSet 𝔹,
      Γ ≤ fusionPreparationData color R J S E F B P Y ⊓
        (top ∈ᴮ Y ⊓ (is_function omegaOne runSpace Run ⊓
          (runLaw color R E F top Run ⊓ successfulRun Run))) := by
  obtain ⟨E, F, B, P, Y, Hdata⟩ := exists_fusion_preparation
    HCH HJ Habsorb Hclosure HD HDpos Hdense HI Hno HnoOpp HS HSlarge
  have Henum := Hdata.trans inf_le_left
  have Hselector := Hdata.trans inf_le_right
  have Hrest := Hselector.trans inf_le_right
  have HpoolFuture := Hrest.trans inf_le_right
  have Hfuture := HpoolFuture.trans inf_le_right
  obtain ⟨top, Run, Hsuccess⟩ := exists_successful_fusion_run
    HCH HJ Habsorb Hclosure Hdiag HD HDpos Hdense HI
    (Henum.trans inf_le_left) (Henum.trans inf_le_right)
    (Hselector.trans inf_le_left) (Hrest.trans inf_le_left)
    (HpoolFuture.trans inf_le_left)
    (Hfuture.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    Hno HnoOpp HS (Hfuture.trans inf_le_left)
    (Hfuture.trans (inf_le_right.trans inf_le_left))
  exact ⟨E, F, B, P, Y, top, Run, le_inf Hdata Hsuccess⟩

end bSet.ErdosFusionPreparedSuccess
