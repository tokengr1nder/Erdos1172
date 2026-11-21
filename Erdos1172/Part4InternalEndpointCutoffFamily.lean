/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalEndpointRunFamily
public import Erdos1172.Part4InternalLeastStoppedHistory
public import Erdos1172.Part4InternalStationaryEndpoints

@[expose] public section

/-!
# A coherent regressive cutoff function for stopped endpoint runs

The supplied run family is an actual internal function. Stopping of its
values on the stationary endpoint set remains explicit. Bounded choice
constructs one internal cutoff function; pressing down then yields a
stationary, omega-two-large fiber with a common bound. The witnesses retain
the chosen run and its least stopping stage. No equality of prior histories
or success-versus-clique dichotomy is asserted.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousRun

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosOrdinalLeast ErdosSimultaneousHistory
open ErdosStationaryEndpoints ErdosOmegaOneIdealBounded ErdosIdeal ErdosNonstationary

theorem stoppingIndices_congr {P Q a b : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ P =ᴮ Q) (Hab : Γ ≤ a =ᴮ b) :
    Γ ≤ stoppingIndices P a =ᴮ stoppingIndices Q b := by
  apply mem_ext
  · apply le_iInf
    intro i
    rw [← deduction]
    have Hi := mem_stoppingIndices_iff.mp
      (show Γ ⊓ i ∈ᴮ stoppingIndices P a ≤ i ∈ᴮ stoppingIndices P a from inf_le_right)
    exact mem_stoppingIndices_iff.mpr ⟨Hi.1,
      mem_congr (pair_congr bv_refl (inf_le_left.trans Hab))
        (vertexHistory_congr (inf_le_left.trans HP)) Hi.2⟩
  · apply le_iInf
    intro i
    rw [← deduction]
    have Hi := mem_stoppingIndices_iff.mp
      (show Γ ⊓ i ∈ᴮ stoppingIndices Q b ≤ i ∈ᴮ stoppingIndices Q b from inf_le_right)
    exact mem_stoppingIndices_iff.mpr ⟨Hi.1,
      mem_congr (pair_congr bv_refl (inf_le_left.trans (bv_symm Hab)))
        (vertexHistory_congr (inf_le_left.trans (bv_symm HP))) Hi.2⟩

theorem stoppingIndices_congr_top (P : bSet 𝔹) : B_congr (stoppingIndices P) := by
  intro a b Γ H
  exact stoppingIndices_congr bv_refl H

theorem stoppingIndices_congr_graph (top : bSet 𝔹) : B_congr (fun P => stoppingIndices P top) := by
  intro P Q Γ H
  exact stoppingIndices_congr H bv_refl

theorem priorVertices_congr_stage (P : bSet 𝔹) :
    B_congr (fun ρ => priorVertices ρ P) := B_congr_image_left

theorem priorVertices_congr_graph (ρ : bSet 𝔹) : B_congr (priorVertices ρ) := by
  intro P Q Γ H
  exact B_congr_image_right (vertexHistory_congr H)

def stoppedCutoff (P top ρ b : bSet 𝔹) : 𝔹 :=
  leastIn (stoppingIndices P top) ρ ⊓ priorVertices ρ P ⊆ᴮ b

theorem stoppedCutoff_ext_top (P ρ b : bSet 𝔹) :
    B_ext (fun top => stoppedCutoff P top ρ b) :=
  B_ext_inf
    (B_ext_term (ϕ := fun A => leastIn A ρ) (t := stoppingIndices P)
      (leastIn_ext_set ρ) (stoppingIndices_congr_top P)) B_ext_const

theorem stoppedCutoff_ext_bound (P top ρ : bSet 𝔹) :
    B_ext (stoppedCutoff P top ρ) :=
  B_ext_inf B_ext_const B_ext_subset_right

theorem stoppedCutoff_ext_stage (P top b : bSet 𝔹) :
    B_ext (fun ρ => stoppedCutoff P top ρ b) :=
  B_ext_inf (leastIn_ext_value (stoppingIndices P top))
    (B_ext_term (ϕ := fun A => A ⊆ᴮ b) (t := fun ρ => priorVertices ρ P)
      B_ext_subset_left (priorVertices_congr_stage P))

theorem stoppedCutoff_ext_graph (top ρ b : bSet 𝔹) :
    B_ext (fun P => stoppedCutoff P top ρ b) :=
  B_ext_inf
    (B_ext_term (ϕ := fun A => leastIn A ρ) (t := fun P => stoppingIndices P top)
      (leastIn_ext_set ρ) (stoppingIndices_congr_graph top))
    (B_ext_term (ϕ := fun A => A ⊆ᴮ b) (t := priorVertices ρ)
      B_ext_subset_left (priorVertices_congr_graph ρ))

/-- The selected family graph, not an external choice of names, identifies
the run whose actual strict prior history is bounded. -/
def endpointCutoffWitness (F top b : bSet 𝔹) : 𝔹 :=
  b ∈ᴮ top ⊓ ⨆ P, pair top P ∈ᴮ F ⊓ ⨆ ρ, stoppedCutoff P top ρ b

theorem endpointCutoffWitness_ext_top (F b : bSet 𝔹) :
    B_ext (fun top => endpointCutoffWitness F top b) :=
  B_ext_inf B_ext_mem_right (B_ext_iSup (h := fun P =>
    B_ext_inf B_ext_pair_mem_left (B_ext_iSup (h := fun ρ => stoppedCutoff_ext_top P ρ b))))

theorem endpointCutoffWitness_ext_bound (F top : bSet 𝔹) :
    B_ext (endpointCutoffWitness F top) :=
  B_ext_inf B_ext_mem_left (B_ext_iSup (h := fun P =>
    B_ext_inf B_ext_const (B_ext_iSup (h := fun ρ => stoppedCutoff_ext_bound P top ρ))))

theorem endpointCutoffWitness_exists {F top b : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ endpointCutoffWitness F top b) :
    ∃ P ρ : bSet 𝔹, Γ ≤ pair top P ∈ᴮ F ⊓
      (leastIn (stoppingIndices P top) ρ ⊓ priorVertices ρ P ⊆ᴮ b) := by
  obtain ⟨P, HP⟩ := exists_convert (H.trans inf_le_right)
    (B_ext_inf B_ext_pair_mem_right (B_ext_iSup (h := fun ρ => stoppedCutoff_ext_graph top ρ b)))
  obtain ⟨ρ, Hρ⟩ := exists_convert (HP.trans inf_le_right) (stoppedCutoff_ext_stage P top b)
  exact ⟨P, ρ, le_inf (HP.trans inf_le_left) Hρ⟩

def endpointRunFamilyStops (F : bSet 𝔹) : 𝔹 :=
  ⨅ top, ⨅ P, _root_.imp (top ∈ᴮ stationaryEndpoints ⊓ pair top P ∈ᴮ F)
    (rangeMem omegaOne (vertexHistory P) top)

theorem endpointRunFamilyStops_apply {F top P : bSet 𝔹} {Γ : 𝔹}
    (Hstop : Γ ≤ endpointRunFamilyStops F) (Htop : Γ ≤ top ∈ᴮ stationaryEndpoints)
    (HP : Γ ≤ pair top P ∈ᴮ F) : Γ ≤ rangeMem omegaOne (vertexHistory P) top :=
  (le_inf (Hstop.trans ((iInf_le _ top).trans (iInf_le _ P))) (le_inf Htop HP)).trans bv_imp_elim

def endpointCutoffFamilyLaw (F g : bSet 𝔹) : 𝔹 :=
  ⨅ top, ⨅ b, _root_.imp (top ∈ᴮ stationaryEndpoints ⊓ pair top b ∈ᴮ g)
    (endpointCutoffWitness F top b)

theorem endpointCutoffFamilyLaw_apply {F g top b : bSet 𝔹} {Γ : 𝔹}
    (Hlaw : Γ ≤ endpointCutoffFamilyLaw F g) (Htop : Γ ≤ top ∈ᴮ stationaryEndpoints)
    (Hb : Γ ≤ pair top b ∈ᴮ g) : Γ ≤ endpointCutoffWitness F top b :=
  (le_inf (Hlaw.trans ((iInf_le _ top).trans (iInf_le _ b))) (le_inf Htop Hb)).trans bv_imp_elim

/-- Coherent bounded choice is needed even though every endpoint has a
pointwise least stopping stage. This theorem supplies that actual function. -/
theorem exists_endpoint_cutoff_family {color : Bool} {R S F : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function omegaTwo runCodes F)
    (Hlaw : Γ ≤ endpointRunFamilyLaw color R S F)
    (Hstop : Γ ≤ endpointRunFamilyStops F) :
    ∃ g : bSet 𝔹, Γ ≤ is_function stationaryEndpoints omegaTwo g ⊓ endpointCutoffFamilyLaw F g := by
  apply ErdosSmallFiberBound.exists_selector_of_pointwise
    (endpointCutoffWitness_ext_top F) (endpointCutoffWitness_ext_bound F)
  apply le_iInf
  intro top
  rw [← deduction]
  let Δ := Γ ⊓ top ∈ᴮ stationaryEndpoints
  have HE : Δ ≤ top ∈ᴮ stationaryEndpoints := inf_le_right
  have Htop := (mem_stationaryEndpoints_iff.mp HE).1
  have Hbounded := (mem_stationaryEndpoints_iff.mp HE).2
  have Htotal : Δ ≤ ⨆ P, P ∈ᴮ runCodes ⊓ pair top P ∈ᴮ F :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function HF).trans (iInf_le _ top)))
      Htop).trans bv_imp_elim
  obtain ⟨P, HP⟩ := exists_convert Htotal (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hrun := endpointRunFamilyLaw_apply (inf_le_left.trans Hlaw) Htop (HP.trans inf_le_right)
  obtain ⟨ρ, b, Hcut⟩ := exists_least_stopped_history_cutoff
    (Hrun.trans inf_le_left) (Hrun.trans inf_le_right)
    (endpointRunFamilyStops_apply (inf_le_left.trans Hstop) HE (HP.trans inf_le_right))
    Hbounded
  have Hb : Δ ≤ b ∈ᴮ top ⊓ priorVertices ρ P ⊆ᴮ b :=
    Hcut.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  apply le_iSup_of_le b
  exact le_inf (mem_of_mem_Ord (Hb.trans inf_le_left) Htop omegaTwo_Ord)
    (le_inf (Hb.trans inf_le_left) (le_iSup_of_le P (le_inf (HP.trans inf_le_right)
      (le_iSup_of_le ρ (le_inf (Hcut.trans inf_le_left) (Hb.trans inf_le_right))))))

theorem endpoint_cutoff_regressive {F g : bSet 𝔹} {Γ : 𝔹}
    (Hg : Γ ≤ is_function stationaryEndpoints omegaTwo g)
    (Hlaw : Γ ≤ endpointCutoffFamilyLaw F g) :
    Γ ≤ ⨅ top, ⨅ b, _root_.imp (pair top b ∈ᴮ g) (b ∈ᴮ top) := by
  apply le_iInf
  intro top
  apply le_iInf
  intro b
  rw [← deduction]
  have Htop : Γ ⊓ pair top b ∈ᴮ g ≤ top ∈ᴮ stationaryEndpoints :=
    (mem_prod_iff.mp (mem_of_mem_subset (inf_le_left.trans (Hg.trans inf_le_right)) inf_le_right)).1
  exact (endpointCutoffFamilyLaw_apply (inf_le_left.trans Hlaw) Htop inf_le_right).trans inf_le_left

theorem endpoint_cutoff_fiber_law {F g b : bSet 𝔹} {Γ : 𝔹}
    (Hg : Γ ≤ is_function stationaryEndpoints omegaTwo g)
    (Hlaw : Γ ≤ endpointCutoffFamilyLaw F g) :
    Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ ErdosIdeal.fiber omegaTwo g b)
      (endpointCutoffWitness F top b) := by
  apply le_iInf
  intro top
  rw [← deduction]
  have Hpair : Γ ⊓ top ∈ᴮ ErdosIdeal.fiber omegaTwo g b ≤ pair top b ∈ᴮ g := by
    rw [ErdosIdeal.mem_fiber]
    exact inf_le_right.trans inf_le_right
  have Htop : Γ ⊓ top ∈ᴮ ErdosIdeal.fiber omegaTwo g b ≤ top ∈ᴮ stationaryEndpoints :=
    (mem_prod_iff.mp (mem_of_mem_subset (inf_le_left.trans (Hg.trans inf_le_right)) Hpair)).1
  exact endpointCutoffFamilyLaw_apply (inf_le_left.trans Hlaw) Htop Hpair

private theorem stationary_cutoff_fiber_ext (g : bSet 𝔹) :
    B_ext (fun b => b ∈ᴮ omegaTwo ⊓
      (positive omegaTwo nonstationaryIdeal (ErdosIdeal.fiber omegaTwo g b) ⊓
        (injects_into omegaTwo (ErdosIdeal.fiber omegaTwo g b) ⊓
          ErdosIdeal.fiber omegaTwo g b ⊆ᴮ stationaryEndpoints))) :=
  B_ext_inf B_ext_mem_left (B_ext_inf
    (B_ext_term (ϕ := positive omegaTwo nonstationaryIdeal)
      (t := ErdosIdeal.fiber omegaTwo g)
      (B_ext_inf B_ext_subset_left (B_ext_neg (h := B_ext_mem_left)))
      (ErdosSmallFiberBound.fiber_congr omegaTwo g))
    (B_ext_inf
      (B_ext_term (ϕ := injects_into omegaTwo) (t := ErdosIdeal.fiber omegaTwo g)
        B_ext_injects_into_right (ErdosSmallFiberBound.fiber_congr omegaTwo g))
      (B_ext_term (ϕ := fun T => T ⊆ᴮ stationaryEndpoints)
        (t := ErdosIdeal.fiber omegaTwo g) B_ext_subset_left
        (ErdosSmallFiberBound.fiber_congr omegaTwo g))))

/-- The common bound is an actual name, and its actual inverse fiber is
stationary and omega-two-large. The least-stop and prior-history witnesses
remain attached to each endpoint through the supplied run-family graph. -/
theorem exists_common_endpoint_cutoff {color : Bool} {R S F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ countablyBounded omegaOne)
    (HF : Γ ≤ is_function omegaTwo runCodes F)
    (Hlaw : Γ ≤ endpointRunFamilyLaw color R S F)
    (Hstop : Γ ≤ endpointRunFamilyStops F) :
    ∃ g b : bSet 𝔹,
      (Γ ≤ is_function stationaryEndpoints omegaTwo g) ∧
      (Γ ≤ endpointCutoffFamilyLaw F g) ∧ (Γ ≤ b ∈ᴮ omegaTwo) ∧
      (Γ ≤ positive omegaTwo nonstationaryIdeal (ErdosIdeal.fiber omegaTwo g b)) ∧
      (Γ ≤ injects_into omegaTwo (ErdosIdeal.fiber omegaTwo g b)) ∧
      (Γ ≤ ErdosIdeal.fiber omegaTwo g b ⊆ᴮ stationaryEndpoints) ∧
      Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ ErdosIdeal.fiber omegaTwo g b)
        (endpointCutoffWitness F top b) := by
  obtain ⟨g, Hg⟩ := exists_endpoint_cutoff_family HF Hlaw Hstop
  have Hfunction := Hg.trans inf_le_left
  have Hfamily := Hg.trans inf_le_right
  have Hfiber := stationary_large_subfiber_of_regressiveFunction HCH
    (stationaryEndpoints_stationary HCH HB) Hfunction
    (endpoint_cutoff_regressive Hfunction Hfamily)
  obtain ⟨b, Hb⟩ := exists_convert Hfiber (stationary_cutoff_fiber_ext g)
  exact ⟨g, b, Hfunction, Hfamily, Hb.trans inf_le_left,
    Hb.trans (inf_le_right.trans inf_le_left),
    Hb.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)),
    Hb.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)),
    endpoint_cutoff_fiber_law Hfunction Hfamily⟩

end bSet.ErdosSimultaneousRun
