/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalStoppedHistoryFreezing
public import Erdos1172.Part4InternalOrderedDushnikMiller
public import Erdos1172.Part4InternalLargeTwoBlock

@[expose] public section

/-!
# Frozen stopped histories force the opposite-color large clique

An edge between two frozen endpoints would make the earlier endpoint a
legal next vertex at the later endpoint's failed stage. The full prior
vertex graph transfers all prior order/color constraints; the full active
coordinate graph, including its failed row, transfers all section
constraints to the earlier run's seed. Exact fallback emptiness rules out
that edge. Stationary history freezing then supplies the independent large
set from the explicit all-runs-stop premise. No successful run or equality
of histories is assumed by the final stopped-branch theorems.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFrozenStoppedRunExtension

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosOrdinalLeast ErdosSimultaneousRun
open ErdosSimultaneousHistory ErdosSimultaneousEntry ErdosSimultaneousVertex
open ErdosStoppedVertexGraph ErdosStoppedCoordinateTriangle ErdosStoppedHistoryFreezing
open ErdosIdeal ErdosNonstationary ErdosOmegaOneIdealBounded ErdosIndependentMaximal

theorem priorVertexGraph_eq_apply {ρ P Q i y : bSet 𝔹} {Γ : 𝔹}
    (Hgraphs : Γ ≤ priorVertexGraph ρ P =ᴮ priorVertexGraph ρ Q)
    (Hi : Γ ≤ i ∈ᴮ ρ) (Hpair : Γ ≤ pair i y ∈ᴮ vertexHistory P) :
    Γ ≤ pair i y ∈ᴮ vertexHistory Q :=
  (mem_priorVertexGraph_iff.mp (mem_congr bv_refl Hgraphs
    (mem_priorVertexGraph_iff.mpr ⟨Hi, Hpair⟩))).2

theorem coordinateTriangle_eq_apply {ρ P Q ξ σ w : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ Ord ρ)
    (Hgraphs : Γ ≤ stoppedCoordinateTriangle ρ P =ᴮ stoppedCoordinateTriangle ρ Q)
    (Hξ : Γ ≤ ξ ∈ᴮ succ ρ) (Hσ : Γ ≤ σ ∈ᴮ ξ)
    (Hpair : Γ ≤ pair (pair ξ σ) w ∈ᴮ coordinateHistory P) :
    Γ ≤ pair (pair ξ σ) w ∈ᴮ coordinateHistory Q :=
  ((stoppedCoordinateTriangle_pair_iff Hρ).mp (mem_congr bv_refl Hgraphs
    ((stoppedCoordinateTriangle_pair_iff Hρ).mpr ⟨Hξ, Hσ, Hpair⟩))).2.2

/-- Equality of the frozen graphs transfers exactly the constraints used
by the failed-stage candidate predicate. No future or inactive coordinate
is required to agree. -/
theorem earlier_endpoint_mem_future_of_frozen_histories
    {color : Bool} {R S α β P Q ρ Z : bSet 𝔹} {Γ : 𝔹}
    (HlawP : Γ ≤ runLaw color R S α P) (HlawQ : Γ ≤ runLaw color R S β Q)
    (HleastP : Γ ≤ leastIn (stoppingIndices P α) ρ)
    (HV : Γ ≤ priorVertexGraph ρ P =ᴮ priorVertexGraph ρ Q)
    (HX : Γ ≤ stoppedCoordinateTriangle ρ P =ᴮ stoppedCoordinateTriangle ρ Q)
    (HentryQ : Γ ≤ pair ρ (pair β Z) ∈ᴮ Q)
    (Hαβ : Γ ≤ α ∈ᴮ β) (Hedge : Γ ≤ graphColor color R α β) :
    Γ ≤ α ∈ᴮ futureCandidates color ρ R S (vertexHistory Q) (coordinateHistory Q) Z β := by
  have Hρ : Γ ≤ ρ ∈ᴮ omegaOne := least_stop_mem_omegaOne HleastP
  have HρOrd : Γ ≤ Ord ρ := Ord_of_mem_Ord Hρ omegaOne_Ord
  have HZ : Γ ≤ is_function omegaOne omegaOne Z := (runLaw_apply HlawQ HentryQ).trans inf_le_left
  apply mem_futureCandidates_iff.mpr
  refine ⟨Hαβ, ?_⟩
  unfold futureRequirements
  refine le_inf ?_ (le_inf Hedge (le_inf ?_ ?_))
  · apply le_iInf
    intro j
    apply le_iInf
    intro y
    rw [← deduction]
    let Δ := Γ ⊓ (j ∈ᴮ ρ ⊓ pair j y ∈ᴮ vertexHistory Q)
    have Hj : Δ ≤ j ∈ᴮ ρ := inf_le_right.trans inf_le_left
    have HpairP : Δ ≤ pair j y ∈ᴮ vertexHistory P :=
      priorVertexGraph_eq_apply (inf_le_left.trans (bv_symm HV)) Hj
        (inf_le_right.trans inf_le_right)
    exact prior_vertex_below_top_color (inf_le_left.trans HlawP)
      (inf_le_left.trans HleastP) Hj HpairP
  · apply le_iInf
    intro j
    apply le_iInf
    intro σ
    apply le_iInf
    intro w
    apply le_iInf
    intro A
    rw [← deduction]
    let Δ := Γ ⊓ ((j ∈ᴮ ρ ⊓ σ ∈ᴮ j) ⊓
      (pair (pair j σ) w ∈ᴮ coordinateHistory Q ⊓ pair (pair σ α) A ∈ᴮ S))
    have Hj : Δ ≤ j ∈ᴮ ρ := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have Hσ : Δ ≤ σ ∈ᴮ j := inf_le_right.trans (inf_le_left.trans inf_le_right)
    have HpairP : Δ ≤ pair (pair j σ) w ∈ᴮ coordinateHistory P :=
      coordinateTriangle_eq_apply (inf_le_left.trans HρOrd)
        (inf_le_left.trans (bv_symm HX)) (mem_of_mem_subset subset_succ Hj) Hσ
        (inf_le_right.trans (inf_le_right.trans inf_le_left))
    exact coordinate_mem_seed_of_run (inf_le_left.trans HlawP) HpairP
      (inf_le_right.trans (inf_le_right.trans inf_le_right))
  · apply le_iInf
    intro σ
    apply le_iInf
    intro w
    apply le_iInf
    intro A
    rw [← deduction]
    let Δ := Γ ⊓ (σ ∈ᴮ ρ ⊓ (pair σ w ∈ᴮ Z ⊓ pair (pair σ α) A ∈ᴮ S))
    have Hσ : Δ ≤ σ ∈ᴮ ρ := inf_le_right.trans inf_le_left
    have Hrow : Δ ≤ pair σ w ∈ᴮ Z := inf_le_right.trans (inf_le_right.trans inf_le_left)
    have HcoordQ : Δ ≤ pair (pair ρ σ) w ∈ᴮ coordinateHistory Q :=
      coordinateHistory_apply (inf_le_left.trans Hρ)
        (mem_of_mem_Ord Hσ (inf_le_left.trans Hρ) omegaOne_Ord)
        (mem_codomain_of_is_function Hrow (inf_le_left.trans HZ))
        (inf_le_left.trans HentryQ) Hrow
    have HtriangleQ : Δ ≤ pair (pair ρ σ) w ∈ᴮ stoppedCoordinateTriangle ρ Q :=
      (stoppedCoordinateTriangle_failed_row_iff (inf_le_left.trans HρOrd)).mpr ⟨Hσ, HcoordQ⟩
    have HcoordP : Δ ≤ pair (pair ρ σ) w ∈ᴮ coordinateHistory P :=
      ((stoppedCoordinateTriangle_failed_row_iff (inf_le_left.trans HρOrd)).mp
        (mem_congr bv_refl (inf_le_left.trans (bv_symm HX)) HtriangleQ)).2
    exact coordinate_mem_seed_of_run (inf_le_left.trans HlawP) HcoordP
      (inf_le_right.trans (inf_le_right.trans inf_le_right))

/-- A same-color edge contradicts the exact empty-candidate rule at the
later stopped endpoint. All hypotheses describe the actual two run names. -/
theorem frozen_stopped_runs_not_graphColor
    {color : Bool} {R S α β P Q ρ : bSet 𝔹} {Γ : 𝔹}
    (HlawP : Γ ≤ runLaw color R S α P) (HlawQ : Γ ≤ runLaw color R S β Q)
    (HleastP : Γ ≤ leastIn (stoppingIndices P α) ρ)
    (HleastQ : Γ ≤ leastIn (stoppingIndices Q β) ρ)
    (HV : Γ ≤ priorVertexGraph ρ P =ᴮ priorVertexGraph ρ Q)
    (HX : Γ ≤ stoppedCoordinateTriangle ρ P =ᴮ stoppedCoordinateTriangle ρ Q)
    (Hαβ : Γ ≤ α ∈ᴮ β) : Γ ≤ (graphColor color R α β)ᶜ := by
  obtain ⟨Z, HentryQ⟩ := vertexHistory_witness (least_stop_pair HleastQ)
  have Hempty : Γ ≤ futureCandidates color ρ R S (vertexHistory Q)
      (coordinateHistory Q) Z β =ᴮ (∅ : bSet 𝔹) :=
    next_vertex_eq_top_empty
      ((runLaw_apply HlawQ HentryQ).trans (inf_le_right.trans inf_le_right)) bv_refl
  rw [← imp_bot, ← deduction]
  have Hcandidate := earlier_endpoint_mem_future_of_frozen_histories
    (inf_le_left.trans HlawP) (inf_le_left.trans HlawQ)
    (inf_le_left.trans HleastP) (inf_le_left.trans HV) (inf_le_left.trans HX)
    (inf_le_left.trans HentryQ) (inf_le_left.trans Hαβ)
    (show Γ ⊓ graphColor color R α β ≤ graphColor color R α β from inf_le_right)
  exact bot_of_mem_empty (mem_congr bv_refl (inf_le_left.trans Hempty) Hcandidate)

theorem frozenHistoryWitness_not_graphColor
    {color : Bool} {R S F b ρ V X α β : bSet 𝔹} {Γ : 𝔹}
    (Hfamily : Γ ≤ endpointRunFamilyLaw color R S F)
    (Hα : Γ ≤ α ∈ᴮ omegaTwo) (Hβ : Γ ≤ β ∈ᴮ omegaTwo)
    (Hfrozenα : Γ ≤ frozenHistoryWitness F b ρ V α X)
    (Hfrozenβ : Γ ≤ frozenHistoryWitness F b ρ V β X)
    (Hαβ : Γ ≤ α ∈ᴮ β) : Γ ≤ (graphColor color R α β)ᶜ := by
  obtain ⟨P, HP⟩ := frozenHistoryWitness_exists Hfrozenα
  obtain ⟨Q, HQ⟩ := frozenHistoryWitness_exists Hfrozenβ
  have HlawP := (endpointRunFamilyLaw_apply Hfamily Hα (HP.trans inf_le_left)).trans inf_le_right
  have HlawQ := (endpointRunFamilyLaw_apply Hfamily Hβ (HQ.trans inf_le_left)).trans inf_le_right
  exact frozen_stopped_runs_not_graphColor HlawP HlawQ
    (HP.trans (inf_le_right.trans (inf_le_left.trans inf_le_left)))
    (HQ.trans (inf_le_right.trans (inf_le_left.trans inf_le_left)))
    (bv_trans (HP.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
      (bv_symm (HQ.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))))
    (bv_trans (HP.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
      (bv_symm (HQ.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))))) Hαβ

private theorem graphColor_le_orientation (color : Bool) (R α β : bSet 𝔹) :
    graphColor color R α β ≤ α ∈ᴮ β ⊔ β ∈ᴮ α :=
  sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

/-- Frozen history labels rule out the color on the whole set. The graph
color already supplies one of the two orientations, so no external choice
of an ordering of mixed endpoint names is made. -/
theorem independent_of_frozen_histories
    {color : Bool} {R S F b ρ V X T : bSet 𝔹} {Γ : 𝔹}
    (Hfamily : Γ ≤ endpointRunFamilyLaw color R S F) (HT : Γ ≤ T ⊆ᴮ omegaTwo)
    (Hfrozen : Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ T) (frozenHistoryWitness F b ρ V top X)) :
    Γ ≤ independent color R T := by
  apply le_iInf
  intro α
  apply le_iInf
  intro β
  rw [← deduction, ← imp_bot, ← deduction]
  let Δ := (Γ ⊓ (α ∈ᴮ T ⊓ β ∈ᴮ T)) ⊓ graphColor color R α β
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have HαT : Δ ≤ α ∈ᴮ T := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have HβT : Δ ≤ β ∈ᴮ T := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have Hα : Δ ≤ α ∈ᴮ omegaTwo := mem_of_mem_subset (HΔ.trans HT) HαT
  have Hβ : Δ ≤ β ∈ᴮ omegaTwo := mem_of_mem_subset (HΔ.trans HT) HβT
  have Hfα : Δ ≤ frozenHistoryWitness F b ρ V α X :=
    (le_inf (HΔ.trans (Hfrozen.trans (iInf_le _ α))) HαT).trans bv_imp_elim
  have Hfβ : Δ ≤ frozenHistoryWitness F b ρ V β X :=
    (le_inf (HΔ.trans (Hfrozen.trans (iInf_le _ β))) HβT).trans bv_imp_elim
  have Horder : Δ ≤ α ∈ᴮ β ⊔ β ∈ᴮ α := inf_le_right.trans (graphColor_le_orientation color R α β)
  apply (le_inf (le_refl Δ) Horder).trans
  rw [inf_sup_left]
  apply sup_le
  · have Hnot := frozenHistoryWitness_not_graphColor (inf_le_left.trans (HΔ.trans Hfamily))
      (inf_le_left.trans Hα) (inf_le_left.trans Hβ) (inf_le_left.trans Hfα)
      (inf_le_left.trans Hfβ) (show Δ ⊓ α ∈ᴮ β ≤ α ∈ᴮ β from inf_le_right)
    exact bv_absurd _ (inf_le_left.trans (show Δ ≤ graphColor color R α β from inf_le_right)) Hnot
  · have Hnot := frozenHistoryWitness_not_graphColor (inf_le_left.trans (HΔ.trans Hfamily))
      (inf_le_left.trans Hβ) (inf_le_left.trans Hα) (inf_le_left.trans Hfβ)
      (inf_le_left.trans Hfα) (show Δ ⊓ β ∈ᴮ α ≤ β ∈ᴮ α from inf_le_right)
    have Hedge : Δ ⊓ β ∈ᴮ α ≤ graphColor color R β α := by
      rw [graphColor_symm color R β α]
      exact inf_le_left.trans (show Δ ≤ graphColor color R α β from inf_le_right)
    exact bv_absurd _ Hedge Hnot

/-- Stopping remains explicit, but frozen histories and the stationary
independent set are now constructed, not supplied. -/
theorem exists_stationary_independent_of_all_runs_stop
    {color : Bool} {R S F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ countablyBounded omegaOne)
    (HF : Γ ≤ is_function omegaTwo runCodes F)
    (Hfamily : Γ ≤ endpointRunFamilyLaw color R S F)
    (Hstop : Γ ≤ endpointRunFamilyStops F) :
    ∃ T : bSet 𝔹, (Γ ≤ positive omegaTwo nonstationaryIdeal T) ∧
      (Γ ≤ injects_into omegaTwo T) ∧ (Γ ≤ T ⊆ᴮ omegaTwo) ∧ Γ ≤ independent color R T := by
  obtain ⟨b, ρ, V, X, T, _, _, _, _, HTpos, HTlarge, _, Hfrozen⟩ :=
    exists_stationary_frozen_stopped_histories HCH HB HF Hfamily Hstop
  have Hlaw : Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ T) (frozenHistoryWitness F b ρ V top X) := by
    apply le_iInf
    intro top
    rw [← deduction]
    exact ((le_inf (inf_le_left.trans (Hfrozen.trans (iInf_le _ top))) inf_le_right).trans
      bv_imp_elim).trans inf_le_right
  exact ⟨T, HTpos, HTlarge, HTpos.trans inf_le_left,
    independent_of_frozen_histories Hfamily (HTpos.trans inf_le_left) Hlaw⟩

theorem ordered_opposite_clique_of_all_runs_stop
    {color : Bool} {R S F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ countablyBounded omegaOne)
    (HF : Γ ≤ is_function omegaTwo runCodes F)
    (Hfamily : Γ ≤ endpointRunFamilyLaw color R S F)
    (Hstop : Γ ≤ endpointRunFamilyStops F) :
    Γ ≤ ErdosOrderedDushnikMiller.orderedLargeClique (!color) R omegaTwo := by
  obtain ⟨T, _, HTlarge, HTsub, HTind⟩ :=
    exists_stationary_independent_of_all_runs_stop HCH HB HF Hfamily Hstop
  obtain ⟨f, Hf⟩ := ErdosOrderedDushnikMiller.exists_ordered_homogeneous_injection
    omegaTwo_Ord HTsub HTsub omegaTwo_initial HTlarge HTind
  exact le_iSup_of_le f Hf

end bSet.ErdosFrozenStoppedRunExtension
