/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalEndpointCutoffFamily
public import Erdos1172.Part4InternalStationarySmallLabels
public import Erdos1172.Part4InternalStoppedVertexGraph
public import Erdos1172.Part4InternalStoppedCoordinateCodes

@[expose] public section

/-!
# Stationary freezing of whole stopped histories

Three actual bounded selectors freeze the least stopping stage, the full
strict-prior vertex graph, and the full active coordinate triangle. The
last triangle includes its failed row. Each refinement uses the concrete
nonstationary ideal's small-union theorem, through stationary small-label
thinning, and retains stationarity at the original Boolean condition.

The result assumes an actual family of runs which stop on the stationary
endpoint set. It does not assert that the stopped alternative occurs or
that it is impossible.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosStoppedHistoryFreezing

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosNonstationary ErdosStationarySmallLabels
open ErdosSimultaneousRun ErdosOrdinalLeast ErdosOmegaOneIdealBounded
open ErdosStationaryEndpoints ErdosStoppedVertexGraph ErdosStoppedCoordinateTriangle
open ErdosStoppedCoordinateCodes

/-- A pointwise internal bounded choice can be made constant on an actual
stationary subfamily, without changing the Boolean condition. -/
theorem exists_stationary_constant_label
    {S K : bSet 𝔹} {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ positive omegaTwo nonstationaryIdeal S)
    (HK : Γ ≤ injects_into K omegaOne)
    (Hleft : ∀ k, B_ext (fun top => P top k))
    (Hright : ∀ top, B_ext (P top))
    (Hex : Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ S) (⨆ k, k ∈ᴮ K ⊓ P top k)) :
    ∃ k T : bSet 𝔹, (Γ ≤ k ∈ᴮ K) ∧
      (Γ ≤ positive omegaTwo nonstationaryIdeal T) ∧
      (Γ ≤ injects_into omegaTwo T) ∧ (Γ ≤ T ⊆ᴮ S) ∧
      Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ T) (P top k) := by
  obtain ⟨f, Hf⟩ := ErdosSmallFiberBound.exists_selector_of_pointwise Hleft Hright Hex
  have Hfunction := Hf.trans inf_le_left
  have Hchoice := Hf.trans inf_le_right
  obtain ⟨k, Hk⟩ := exists_stationary_large_subfiber_of_small_labels HCH HS Hfunction HK
  have Hsub := Hk.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  refine ⟨k, fiber omegaTwo f k, Hk.trans inf_le_left,
    Hk.trans (inf_le_right.trans inf_le_left),
    Hk.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)), Hsub, ?_⟩
  apply le_iInf
  intro top
  rw [← deduction]
  let Δ := Γ ⊓ top ∈ᴮ fiber omegaTwo f k
  have Htop : Δ ≤ top ∈ᴮ S := mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right
  have Hpair : Δ ≤ pair top k ∈ᴮ f := by
    exact (show Δ ≤ top ∈ᴮ fiber omegaTwo f k from inf_le_right).trans
      ((le_of_eq (mem_fiber omegaTwo f k top)).trans inf_le_right)
  exact (le_inf (inf_le_left.trans (Hchoice.trans ((iInf_le _ top).trans (iInf_le _ k))))
    (le_inf Htop Hpair)).trans bv_imp_elim

def stoppedStageWitness (F b top ρ : bSet 𝔹) : 𝔹 :=
  ⨆ P, pair top P ∈ᴮ F ⊓ stoppedCutoff P top ρ b

def stoppedVertexWitness (F b ρ top V : bSet 𝔹) : 𝔹 :=
  ⨆ P, pair top P ∈ᴮ F ⊓
    (stoppedCutoff P top ρ b ⊓ priorVertexGraph ρ P =ᴮ V)

/-- This fixes graphs, not merely their ranges. The coordinate graph uses
`stoppedCoordinateTriangle`, whose domain includes the stopping row. -/
def frozenHistoryWitness (F b ρ V top X : bSet 𝔹) : 𝔹 :=
  ⨆ P, pair top P ∈ᴮ F ⊓
    (stoppedCutoff P top ρ b ⊓
      (priorVertexGraph ρ P =ᴮ V ⊓ stoppedCoordinateTriangle ρ P =ᴮ X))

theorem stoppedStageWitness_ext_top (F b ρ : bSet 𝔹) :
    B_ext (fun top => stoppedStageWitness F b top ρ) :=
  B_ext_iSup (h := fun P =>
    B_ext_inf B_ext_pair_mem_left (stoppedCutoff_ext_top P ρ b))

theorem stoppedStageWitness_ext_stage (F b top : bSet 𝔹) :
    B_ext (stoppedStageWitness F b top) :=
  B_ext_iSup (h := fun P =>
    B_ext_inf B_ext_const (stoppedCutoff_ext_stage P top b))

theorem stoppedStageWitness_exists {F b top ρ : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ stoppedStageWitness F b top ρ) :
    ∃ P : bSet 𝔹, Γ ≤ pair top P ∈ᴮ F ⊓ stoppedCutoff P top ρ b :=
  exists_convert H (B_ext_inf B_ext_pair_mem_right (stoppedCutoff_ext_graph top ρ b))

theorem stoppedVertexWitness_ext_top (F b ρ V : bSet 𝔹) :
    B_ext (fun top => stoppedVertexWitness F b ρ top V) :=
  B_ext_iSup (h := fun P => B_ext_inf B_ext_pair_mem_left
    (B_ext_inf (stoppedCutoff_ext_top P ρ b) B_ext_const))

theorem stoppedVertexWitness_ext_value (F b ρ top : bSet 𝔹) :
    B_ext (stoppedVertexWitness F b ρ top) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const
    (B_ext_inf B_ext_const B_ext_bv_eq_right))

theorem stoppedVertexWitness_exists {F b ρ top V : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ stoppedVertexWitness F b ρ top V) :
    ∃ P : bSet 𝔹, Γ ≤ pair top P ∈ᴮ F ⊓
      (stoppedCutoff P top ρ b ⊓ priorVertexGraph ρ P =ᴮ V) :=
  exists_convert H (B_ext_inf B_ext_pair_mem_right
    (B_ext_inf (stoppedCutoff_ext_graph top ρ b)
      (B_ext_term (ϕ := fun g => g =ᴮ V) (t := priorVertexGraph ρ)
        B_ext_bv_eq_left (priorVertexGraph_congr_graph ρ))))

theorem frozenHistoryWitness_ext_top (F b ρ V X : bSet 𝔹) :
    B_ext (fun top => frozenHistoryWitness F b ρ V top X) :=
  B_ext_iSup (h := fun P => B_ext_inf B_ext_pair_mem_left
    (B_ext_inf (stoppedCutoff_ext_top P ρ b) B_ext_const))

theorem frozenHistoryWitness_ext_value (F b ρ V top : bSet 𝔹) :
    B_ext (frozenHistoryWitness F b ρ V top) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const
    (B_ext_inf B_ext_const (B_ext_inf B_ext_const B_ext_bv_eq_right)))

theorem frozenHistoryWitness_exists {F b ρ V top X : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ frozenHistoryWitness F b ρ V top X) :
    ∃ P : bSet 𝔹, Γ ≤ pair top P ∈ᴮ F ⊓
      ((leastIn (stoppingIndices P top) ρ ⊓ priorVertices ρ P ⊆ᴮ b) ⊓
        (priorVertexGraph ρ P =ᴮ V ⊓ stoppedCoordinateTriangle ρ P =ᴮ X)) :=
  exists_convert H (B_ext_inf B_ext_pair_mem_right
    (B_ext_inf (stoppedCutoff_ext_graph top ρ b)
      (B_ext_inf
        (B_ext_term (ϕ := fun g => g =ᴮ V) (t := priorVertexGraph ρ)
          B_ext_bv_eq_left (priorVertexGraph_congr_graph ρ))
        (B_ext_term (ϕ := fun g => g =ᴮ X) (t := stoppedCoordinateTriangle ρ)
          B_ext_bv_eq_left (stoppedCoordinateTriangle_congr_graph ρ)))))

/-- The common labels describe the full actual stopped graphs on a
stationary omega-two-large subfamily. All three choices and all run
witnesses are internal, and retain the original Boolean condition. -/
theorem exists_stationary_frozen_stopped_histories
    {color : Bool} {R S F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ countablyBounded omegaOne)
    (HF : Γ ≤ is_function omegaTwo runCodes F)
    (Hlaw : Γ ≤ endpointRunFamilyLaw color R S F)
    (Hstop : Γ ≤ endpointRunFamilyStops F) :
    ∃ b ρ V X T : bSet 𝔹,
      (Γ ≤ b ∈ᴮ omegaTwo) ∧ (Γ ≤ ρ ∈ᴮ omegaOne) ∧
      (Γ ≤ V ∈ᴮ vertexHistoryCodes b) ∧ (Γ ≤ X ∈ᴮ coordinateHistoryCodes) ∧
      (Γ ≤ positive omegaTwo nonstationaryIdeal T) ∧
      (Γ ≤ injects_into omegaTwo T) ∧ (Γ ≤ T ⊆ᴮ stationaryEndpoints) ∧
      Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ T)
        (b ∈ᴮ top ⊓ frozenHistoryWitness F b ρ V top X) := by
  obtain ⟨g, b, _, _, Hb, HUpos, _, HUsub, HUlaw⟩ :=
    exists_common_endpoint_cutoff HCH HB HF Hlaw Hstop
  let U := fiber omegaTwo g b
  have Hstage : Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ U)
      (⨆ ρ, ρ ∈ᴮ omegaOne ⊓ stoppedStageWitness F b top ρ) := by
    apply le_iInf
    intro top
    rw [← deduction]
    let Δ := Γ ⊓ top ∈ᴮ U
    have Hcut : Δ ≤ endpointCutoffWitness F top b :=
      (le_inf (inf_le_left.trans (HUlaw.trans (iInf_le _ top))) inf_le_right).trans bv_imp_elim
    obtain ⟨P, ρ, HP⟩ := endpointCutoffWitness_exists Hcut
    exact le_iSup_of_le ρ (le_inf
      (least_stop_mem_omegaOne (HP.trans (inf_le_right.trans inf_le_left)))
      (le_iSup_of_le P HP))
  obtain ⟨ρ, U₁, Hρ, HU₁pos, _, HU₁sub, HU₁law⟩ :=
    exists_stationary_constant_label HCH HUpos injects_into_refl
      (stoppedStageWitness_ext_top F b) (stoppedStageWitness_ext_stage F b) Hstage
  have Hvertex : Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ U₁)
      (⨆ V, V ∈ᴮ vertexHistoryCodes b ⊓ stoppedVertexWitness F b ρ top V) := by
    apply le_iInf
    intro top
    rw [← deduction]
    let Δ := Γ ⊓ top ∈ᴮ U₁
    have Hstage' : Δ ≤ stoppedStageWitness F b top ρ :=
      (le_inf (inf_le_left.trans (HU₁law.trans (iInf_le _ top))) inf_le_right).trans bv_imp_elim
    obtain ⟨P, HP⟩ := stoppedStageWitness_exists Hstage'
    have Htop : Δ ≤ top ∈ᴮ omegaTwo :=
      mem_of_mem_subset (inf_le_left.trans (HU₁pos.trans inf_le_left)) inf_le_right
    have Hrun := endpointRunFamilyLaw_apply (inf_le_left.trans Hlaw) Htop (HP.trans inf_le_left)
    have Hcode : Δ ≤ priorVertexGraph ρ P ∈ᴮ vertexHistoryCodes b :=
      priorVertexGraph_mem_codes
        (Hrun.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
        (inf_le_left.trans Hρ) (HP.trans (inf_le_right.trans inf_le_right))
    exact le_iSup_of_le (priorVertexGraph ρ P) (le_inf Hcode
      (le_iSup_of_le P (le_inf (HP.trans inf_le_left)
        (le_inf (HP.trans inf_le_right) bv_refl))))
  obtain ⟨V, U₂, HV, HU₂pos, _, HU₂sub, HU₂law⟩ :=
    exists_stationary_constant_label HCH HU₁pos (vertexHistoryCodes_small HCH Hb)
      (stoppedVertexWitness_ext_top F b ρ) (stoppedVertexWitness_ext_value F b ρ) Hvertex
  have Hcoordinates : Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ U₂)
      (⨆ X, X ∈ᴮ coordinateHistoryCodes ⊓ frozenHistoryWitness F b ρ V top X) := by
    apply le_iInf
    intro top
    rw [← deduction]
    let Δ := Γ ⊓ top ∈ᴮ U₂
    have Hvertex' : Δ ≤ stoppedVertexWitness F b ρ top V :=
      (le_inf (inf_le_left.trans (HU₂law.trans (iInf_le _ top))) inf_le_right).trans bv_imp_elim
    obtain ⟨P, HP⟩ := stoppedVertexWitness_exists Hvertex'
    have Htop : Δ ≤ top ∈ᴮ omegaTwo :=
      mem_of_mem_subset (inf_le_left.trans (HU₂pos.trans inf_le_left)) inf_le_right
    have Hrun := endpointRunFamilyLaw_apply (inf_le_left.trans Hlaw) Htop (HP.trans inf_le_left)
    have Hcode : Δ ≤ stoppedCoordinateTriangle ρ P ∈ᴮ coordinateHistoryCodes :=
      stoppedCoordinateTriangle_mem_codes (Hrun.trans inf_le_left)
        (Hrun.trans inf_le_right) (inf_le_left.trans Hρ)
    exact le_iSup_of_le (stoppedCoordinateTriangle ρ P) (le_inf Hcode
      (le_iSup_of_le P (le_inf (HP.trans inf_le_left)
        (le_inf (HP.trans (inf_le_right.trans inf_le_left))
          (le_inf (HP.trans (inf_le_right.trans inf_le_right)) bv_refl)))))
  obtain ⟨X, T, HX, HTpos, HTlarge, HTsub, HTlaw⟩ :=
    exists_stationary_constant_label HCH HU₂pos (coordinateHistoryCodes_small HCH)
      (frozenHistoryWitness_ext_top F b ρ V) (frozenHistoryWitness_ext_value F b ρ V) Hcoordinates
  have HTU : Γ ≤ T ⊆ᴮ U := subset_trans' HTsub (subset_trans' HU₂sub HU₁sub)
  refine ⟨b, ρ, V, X, T, Hb, Hρ, HV, HX, HTpos, HTlarge,
    subset_trans' HTU HUsub, ?_⟩
  apply le_iInf
  intro top
  rw [← deduction]
  have HtopU : Γ ⊓ top ∈ᴮ T ≤ top ∈ᴮ U :=
    mem_of_mem_subset (inf_le_left.trans HTU) inf_le_right
  have Hcut : Γ ⊓ top ∈ᴮ T ≤ endpointCutoffWitness F top b :=
    (le_inf (inf_le_left.trans (HUlaw.trans (iInf_le _ top))) HtopU).trans bv_imp_elim
  exact le_inf (Hcut.trans inf_le_left)
    ((le_inf (inf_le_left.trans (HTlaw.trans (iInf_le _ top))) inf_le_right).trans bv_imp_elim)

end bSet.ErdosStoppedHistoryFreezing
