/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRunMasks
public import Erdos1172.Part4InternalFusionRunBlockOrder
public import Erdos1172.Part4InternalFusionPreparedSuccess
public import Erdos1172.Part4InternalFusionRunActiveLaw

@[expose] public section

/-!
# Constructing the actual ordered fusion with co-large active masks

Only the original ideal/cardinal assumptions, the original large future,
and the two exact target exclusions are inputs. The same-condition
enumeration, fixed selector, closed pools, retained future, terminal, and
successful run are constructed. Their literal decoded histories satisfy
the least-coordinate, inclusive-color, whole-block-order, and co-large
active-mask laws. No successful family or positive masks are premises.

This endpoint supplies the concrete family for the subsequent countable
tail argument; it does not assert ideal existence or model consistency.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionMaskedFamily

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosDenseBasis ErdosPartition
open ErdosFusionPreparation ErdosFusionPreparedSuccess ErdosFusionRun ErdosFusionRunSuccess
open ErdosFusionGlobalRowLaw ErdosFusionRunActiveLaw ErdosFusionRunBlockOrder
open ErdosFusionMaskedTail ErdosFusionRunMasks ErdosColargeIntersection

theorem exists_prepared_masked_fusion_run
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
        ((top ∈ᴮ Y ⊓ (is_function omegaOne runSpace Run ⊓
          (runLaw color R E F top Run ⊓ successfulRun Run))) ⊓
        (fullCoordinateLeastLaw color R E top Run ⊓
          (inclusiveActiveLaw (!color) R E (fullBlocks Run) (fullCoordinates Run) ⊓
            (fullBlockOrder Run ⊓
              (⨅ ν, _root_.imp (ν ∈ᴮ omegaOne)
                (colarge omegaOne J (activeMask (fullCoordinates Run) ν))))))) := by
  obtain ⟨E, F, B, P, Y, top, Run, Hdata⟩ := exists_prepared_successful_fusion_run
    HCH HJ Habsorb Hclosure Hdiag HD HDpos Hdense HI Hno HnoOpp HS HSlarge
  have Hprep := Hdata.trans inf_le_left
  have Henum := Hprep.trans inf_le_left
  have Hselector := Hprep.trans inf_le_right
  have Hrest := Hselector.trans inf_le_right
  have HpoolFuture := Hrest.trans inf_le_right
  have Hfuture := HpoolFuture.trans inf_le_right
  have HE := Henum.trans inf_le_left
  have HElaw := Henum.trans inf_le_right
  have HF := Hselector.trans inf_le_left
  have HFlaw := Hrest.trans inf_le_left
  have Hhull := HpoolFuture.trans inf_le_left
  have Hseeds := Hfuture.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have HrunData := Hdata.trans inf_le_right
  have Htop := HrunData.trans inf_le_left
  have HRun := HrunData.trans (inf_le_right.trans inf_le_left)
  have Hlaw := HrunData.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have Hsuccess := HrunData.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  exact ⟨E, F, B, P, Y, top, Run, le_inf Hprep (le_inf HrunData
    (le_inf (fusion_full_coordinateLeastLaw HJ Habsorb Hclosure HE HElaw HF HFlaw
      Hhull Hseeds Htop HRun Hlaw Hsuccess)
      (le_inf (fusion_run_inclusiveActiveLaw HE HElaw HF HFlaw HRun Hlaw)
        (le_inf (fusion_full_blockOrder HE HElaw HF HFlaw HRun Hlaw Hsuccess)
          (fusion_activeMasks_colarge HJ Habsorb Hclosure Hdiag HE HElaw HF HFlaw
            Hhull Hseeds Htop HRun Hlaw Hsuccess)))))⟩

end bSet.ErdosFusionMaskedFamily
