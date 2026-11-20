/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSuccessfulRunBlock
public import Erdos1172.Part4InternalFrozenStoppedRunExtension

@[expose] public section

/-!
# The internal simultaneous block dichotomy

An actual run-valued function is constructed on all omega-two endpoints.
Its local successful alternative supplies a single increasing homogeneous
omega-one block with a coherent family of co-large common rows. On the
complementary Boolean condition every selected run stops, so stationary
freezing and the extension contradiction supply an increasing opposite-
color omega-two clique. Neither success, stopping, a run family, nor frozen
histories are supplied as additional premises of the final theorem.

This is the simultaneous block dichotomy under CH and normal row ideal
data, from which countable boundedness is derived. It is not yet the two-block
omega-one-plus-omega partition relation or an ideal/model construction.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosInternalSimultaneousBlockDichotomy

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosOmegaOneIdealBounded ErdosSimultaneousRun
open ErdosSimultaneousRowChoice ErdosSuccessfulRunBlock
open ErdosFrozenStoppedRunExtension ErdosOrderedDushnikMiller

/-- Forgetting diagonal closure retains the exact row data needed to
construct the actual endpoint run family. -/
theorem rowIdealAvailability_of_normal {S : bSet 𝔹} {Γ : 𝔹}
    (Hrows : Γ ≤ normalRowAvailability S) :
    Γ ≤ ⨅ σ, _root_.imp (σ ∈ᴮ omegaOne) (⨆ J, rowIdealData S σ J) := by
  apply le_iInf
  intro σ
  rw [← deduction]
  have Hex : Γ ⊓ σ ∈ᴮ omegaOne ≤ ⨆ J, rowNormalIdealData S σ J :=
    (le_inf (inf_le_left.trans (Hrows.trans (iInf_le _ σ))) inf_le_right).trans
      bv_imp_elim
  apply Hex.trans
  apply iSup_le
  intro J
  exact le_iSup_of_le J
    (show rowNormalIdealData S σ J ≤ rowIdealData S σ J from inf_le_left)

/-- Both branches are derived at their local Boolean conditions; an
external global choice of a successful endpoint or of a color is not used. -/
theorem successful_block_or_ordered_opposite_of_family
    {color : Bool} {R S F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HB : Γ ≤ countablyBounded omegaOne)
    (HF : Γ ≤ is_function omegaTwo runCodes F)
    (Hlaw : Γ ≤ endpointRunFamilyLaw color R S F)
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ normalRowAvailability S) :
    Γ ≤ hasSuccessfulBlock color R S ⊔ orderedLargeClique (!color) R omegaTwo := by
  apply (le_inf le_rfl (successfulBlock_or_endpoint_stops Hlaw HS Hrows)).trans
  rw [inf_sup_left]
  exact sup_le (inf_le_right.trans le_sup_left)
    ((ordered_opposite_clique_of_all_runs_stop
      (inf_le_left.trans HCH) (inf_le_left.trans HB)
      (inf_le_left.trans HF) (inf_le_left.trans Hlaw)
      (show Γ ⊓ endpointRunFamilyStops F ≤ endpointRunFamilyStops F from inf_le_right)).trans
      le_sup_right)

/-- The complete internal analogue of the simultaneous block dichotomy:
all runs, choices, stopping histories and opposite-color enumeration are
constructed from the displayed hypotheses. -/
theorem successful_block_or_ordered_opposite
    {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HS : Γ ≤ is_func' (prod omegaOne omegaTwo) (bv_powerset omegaOne) S)
    (Hrows : Γ ≤ normalRowAvailability S) :
    Γ ≤ hasSuccessfulBlock color R S ⊔ orderedLargeClique (!color) R omegaTwo := by
  have Hbasic := rowIdealAvailability_of_normal Hrows
  obtain ⟨F, HF⟩ := exists_endpoint_run_family (color := color) (R := R) HS Hbasic
  exact successful_block_or_ordered_opposite_of_family HCH (countablyBounded_of_rowIdeals Hbasic)
    (HF.trans inf_le_left) (HF.trans inf_le_right) HS Hrows

end bSet.ErdosInternalSimultaneousBlockDichotomy
