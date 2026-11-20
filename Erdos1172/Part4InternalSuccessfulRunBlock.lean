/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousRunSuccess
public import Erdos1172.Part4InternalSimultaneousCommonRowFamily
public import Erdos1172.Part4InternalEndpointCutoffFamily

@[expose] public section

/-!
# The exact successful-block branch of the simultaneous construction

A successful run supplies its actual decoded increasing homogeneous
omega-one graph and its canonical coherent family of common row sets.
These sets are co-large in every applicable supplied normal row ideal.
Internal existence of such ideals is recorded, so the row assertion is
not merely a vacuous implication.

For any family obeying the run laws, local Boolean case splitting gives
this successful block or stopping on every stationary endpoint. This is
a Boolean join, not an external choice of a globally true branch. The
block has order type omega-one; no omega-one-plus-omega partition result
is asserted here.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSuccessfulRunBlock

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosColargeIntersection
open ErdosSimultaneousRun ErdosSimultaneousEntry ErdosSimultaneousHistory
open ErdosStationaryEndpoints

def normalRowAvailability (S : bSet 𝔹) : 𝔹 :=
  ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowNormalIdealData S σ J)

def blockRowContainment (S f C : bSet 𝔹) : 𝔹 :=
  ⨅ σ, ⨅ A, ⨅ y, ⨅ B, _root_.imp
    ((pair σ A ∈ᴮ C ⊓ rangeMem omegaOne f y) ⊓ pair (pair σ y) B ∈ᴮ S)
    (A ⊆ᴮ B)

/-- A coherent common-row family, with actual normal-ideal availability
and the co-large law for every applicable row-specific ideal. -/
def commonBlockRows (S f C : bSet 𝔹) : 𝔹 :=
  is_function omegaOne (bv_powerset omegaOne) C ⊓
    (normalRowAvailability S ⊓
      ((⨅ σ, ⨅ J, ⨅ A, _root_.imp
        (rowNormalIdealData S σ J ⊓ pair σ A ∈ᴮ C) (colarge omegaOne J A)) ⊓
        blockRowContainment S f C))

def successfulBlockData (color : Bool) (R S f C : bSet 𝔹) : 𝔹 :=
  is_injective_function omegaOne omegaTwo f ⊓
    (increasingOn omegaOne f ⊓
      (homogeneousUnion color R omegaOne omegaOne f f ⊓ commonBlockRows S f C))

def hasSuccessfulBlock (color : Bool) (R S : bSet 𝔹) : 𝔹 :=
  ⨆ f, ⨆ C, successfulBlockData color R S f C

theorem commonRows_blockRowContainment (S P : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ blockRowContainment S (vertexHistory P) (commonRows S P) := by
  apply le_iInf
  intro σ
  apply le_iInf
  intro A
  apply le_iInf
  intro y
  apply le_iInf
  intro B
  rw [← deduction]
  let Δ := Γ ⊓ ((pair σ A ∈ᴮ commonRows S P ⊓
    rangeMem omegaOne (vertexHistory P) y) ⊓ pair (pair σ y) B ∈ᴮ S)
  have HC : Δ ≤ pair σ A ∈ᴮ commonRows S P :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  exact subset_trans' (subset_of_eq (commonRows_apply HC))
    (commonRow_subset_range_section
      (show Δ ≤ rangeMem omegaOne (vertexHistory P) y from
        inf_le_right.trans (inf_le_left.trans inf_le_right))
      (show Δ ≤ pair (pair σ y) B ∈ᴮ S from inf_le_right.trans inf_le_right))

/-- Common-row extraction is valid even if the run stops. -/
theorem commonBlockRows_of_run
    {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Htop : Γ ≤ top ∈ᴮ omegaTwo) (Hrows : Γ ≤ normalRowAvailability S) :
    Γ ≤ commonBlockRows S (vertexHistory P) (commonRows S P) :=
  le_inf (commonRows_is_function S P) (le_inf Hrows
    (le_inf (run_commonRows_colarge_values HP Hlaw HS Htop)
      (commonRows_blockRowContainment S P)))

/-- The successful graph is the original decoded graph, and the common
rows are the original canonical family, not independently supplied masks. -/
theorem successfulBlockData_of_run
    {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Htop : Γ ≤ top ∈ᴮ omegaTwo) (Hrows : Γ ≤ normalRowAvailability S)
    (Hsuccess : Γ ≤ (rangeMem omegaOne (vertexHistory P) top)ᶜ) :
    Γ ≤ successfulBlockData color R S (vertexHistory P) (commonRows S P) :=
  le_inf (run_vertex_is_injective HP Hlaw Hsuccess)
    (le_inf (run_vertex_increasing Hlaw Hsuccess)
      (le_inf (run_vertex_homogeneous HP Hlaw Hsuccess)
        (commonBlockRows_of_run HP Hlaw HS Htop Hrows)))

theorem hasSuccessfulBlock_of_run
    {color : Bool} {R S top P : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Htop : Γ ≤ top ∈ᴮ omegaTwo) (Hrows : Γ ≤ normalRowAvailability S)
    (Hsuccess : Γ ≤ (rangeMem omegaOne (vertexHistory P) top)ᶜ) :
    Γ ≤ hasSuccessfulBlock color R S :=
  le_iSup_of_le (vertexHistory P) (le_iSup_of_le (commonRows S P)
    (successfulBlockData_of_run HP Hlaw HS Htop Hrows Hsuccess))

theorem commonBlockRows_section_apply {S f C σ A y B : bSet 𝔹} {Γ : 𝔹}
    (Hcommon : Γ ≤ commonBlockRows S f C) (HC : Γ ≤ pair σ A ∈ᴮ C)
    (Hy : Γ ≤ rangeMem omegaOne f y) (HB : Γ ≤ pair (pair σ y) B ∈ᴮ S) :
    Γ ≤ A ⊆ᴮ B :=
  (le_inf ((Hcommon.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))).trans
    ((iInf_le _ σ).trans ((iInf_le _ A).trans ((iInf_le _ y).trans (iInf_le _ B)))))
    (le_inf (le_inf HC Hy) HB)).trans bv_imp_elim

/-- Absence of the successful-block value forces each encoded endpoint
run to stop, locally at the same Boolean condition. -/
theorem endpointRunFamilyStops_of_no_successfulBlock
    {color : Bool} {R S F : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ endpointRunFamilyLaw color R S F)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ normalRowAvailability S)
    (Hno : Γ ≤ (hasSuccessfulBlock color R S)ᶜ) :
    Γ ≤ endpointRunFamilyStops F := by
  apply le_iInf
  intro top
  apply le_iInf
  intro P
  rw [← deduction]
  apply bv_by_contra
  rw [← deduction]
  let Δ := (Γ ⊓ (top ∈ᴮ stationaryEndpoints ⊓ pair top P ∈ᴮ F)) ⊓
    (rangeMem omegaOne (vertexHistory P) top)ᶜ
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Htop : Δ ≤ top ∈ᴮ omegaTwo :=
    (mem_stationaryEndpoints_iff.mp (show Δ ≤ top ∈ᴮ stationaryEndpoints from
      inf_le_left.trans (inf_le_right.trans inf_le_left))).1
  have Hrun := endpointRunFamilyLaw_apply (HΔ.trans Hlaw) Htop
    (show Δ ≤ pair top P ∈ᴮ F from inf_le_left.trans (inf_le_right.trans inf_le_right))
  exact bv_absurd _
    (hasSuccessfulBlock_of_run (Hrun.trans inf_le_left) (Hrun.trans inf_le_right)
      (HΔ.trans HS) Htop (HΔ.trans Hrows) (show Δ ≤
        (rangeMem omegaOne (vertexHistory P) top)ᶜ from inf_le_right))
    (HΔ.trans Hno)

/-- This exact internal branch split requires neither CH nor a supplied
successful run. Totality of the run family is only needed by the later
construction of the opposite-clique branch. -/
theorem successfulBlock_or_endpoint_stops
    {color : Bool} {R S F : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ endpointRunFamilyLaw color R S F)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ normalRowAvailability S) :
    Γ ≤ hasSuccessfulBlock color R S ⊔ endpointRunFamilyStops F := by
  have Hsplit : Γ ≤ hasSuccessfulBlock color R S ⊔ (hasSuccessfulBlock color R S)ᶜ := by
    simp only [sup_compl_eq_top]
    exact le_top
  apply (le_inf le_rfl Hsplit).trans
  rw [inf_sup_left]
  apply sup_le
  · exact inf_le_right.trans le_sup_left
  · exact (endpointRunFamilyStops_of_no_successfulBlock
      (inf_le_left.trans Hlaw) (inf_le_left.trans HS) (inf_le_left.trans Hrows)
      inf_le_right).trans le_sup_right

end bSet.ErdosSuccessfulRunBlock
