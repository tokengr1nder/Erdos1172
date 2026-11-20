/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRun
public import Erdos1172.Part4InternalImageRecursionInvariant

@[expose] public section

/-!
# Countability of the actual stored fusion active histories

Internal ordinal invariant induction applies to the tagged recursion.
The strict-prefix image is the actual earlier entry graph. Its good
members make the decoded active family countable-valued, so its union
and the current physical points are countable. The current block may
fail: its active points are still stored and covered by this proof.

No countability invariant, CH, ideal hypothesis, or selector law is an
input. Only the actual canonical enumeration function and its law are
used to bound the current points.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionRunCountable

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosCanonicalBlocks ErdosFusionEntrySpace ErdosFusionRun
open ErdosFusionActiveHistory ErdosCountableFamilyUnion ErdosTaggedPrefix
open ErdosImageRecursionInvariant ErdosBoundedImageRecursion

def countableActiveState (q : bSet 𝔹) : 𝔹 :=
  ⨅ i, ⨅ A, ⨅ Z, ⨅ U, _root_.imp (q =ᴮ pair i (entry A Z U))
    (injects_into U bSet.omega)

theorem countableActiveState_ext :
    B_ext (countableActiveState : bSet 𝔹 → 𝔹) :=
  B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_bv_eq_left) (h₂ := B_ext_const)))))

theorem countableActiveState_apply {i A Z U : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ countableActiveState (pair i (entry A Z U))) :
    Γ ≤ injects_into U bSet.omega :=
  (le_inf (H.trans ((iInf_le _ i).trans ((iInf_le _ A).trans
    ((iInf_le _ Z).trans (iInf_le _ U))))) bv_refl).trans bv_imp_elim

theorem countableActiveState_of_entry {i A Z U : bSet 𝔹} {Γ : 𝔹}
    (HU : Γ ≤ injects_into U bSet.omega) :
    Γ ≤ countableActiveState (pair i (entry A Z U)) := by
  apply le_iInf
  intro j
  apply le_iInf
  intro B
  apply le_iInf
  intro W
  apply le_iInf
  intro V
  rw [← deduction]
  exact bv_rw'' (ϕ := fun X => injects_into X bSet.omega)
    (eq_of_eq_pair_right' (eq_of_eq_pair_right' (eq_of_eq_pair_right' inf_le_right)))
    (inf_le_left.trans HU) B_ext_injects_into_left

/-- Decoding an earlier entry preserves its actual stored active value.
No functionality or external enumeration is used in this implication. -/
theorem activeFamily_countableValues_of_allGood {ξ T : bSet 𝔹} {Γ : 𝔹}
    (Hgood : Γ ≤ allGood countableActiveState T) :
    Γ ≤ countableValues ξ (activeFamily T) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro U
  rw [← deduction]
  obtain ⟨A, Z, Hentry⟩ := activeFamily_witness
    (show Γ ⊓ (i ∈ᴮ ξ ⊓ pair i U ∈ᴮ activeFamily T) ≤
      pair i U ∈ᴮ activeFamily T from inf_le_right.trans inf_le_right)
  exact countableActiveState_apply (allGood_apply (inf_le_left.trans Hgood) Hentry)

/-- The induction step only assumes goodness of the strict-prefix image.
Actual prefix totality follows independently from the tagged run law. -/
theorem fusion_active_countable_invariant_step
    {color : Bool} {R E F top Run : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ imageRecInvariantStep omegaOne runSpace
      (fun i T => pair i (nextEntry color R E F top i T)) Run countableActiveState := by
  apply le_iInf
  intro i
  rw [← deduction]
  let Δ := Γ ⊓ (i ∈ᴮ omegaOne ⊓ allGood countableActiveState (image i runSpace Run))
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hi : Δ ≤ i ∈ᴮ omegaOne := inf_le_right.trans inf_le_left
  have Hicut : Δ ≤ i ⊆ᴮ omegaOne := subset_of_mem_Ord Hi omegaOne_Ord
  have Hprefix : Δ ≤ is_function i entrySpace (taggedPrefix i omegaOne entrySpace Run) :=
    fusion_prefix_is_function (HΔ.trans HRun) (HΔ.trans Hlaw) Hicut
  have Hgood : Δ ≤ allGood countableActiveState (taggedPrefix i omegaOne entrySpace Run) :=
    inf_le_right.trans inf_le_right
  have Hvalues : Δ ≤ countableValues i
      (activeFamily (taggedPrefix i omegaOne entrySpace Run)) :=
    activeFamily_countableValues_of_allGood Hgood
  have Hactive : Δ ≤ injects_into
      (nextActive color R E top i (taggedPrefix i omegaOne entrySpace Run)) bSet.omega :=
    activeHistory_countable
      (is_func'_of_is_function (activeFamily_is_function Hicut Hprefix)) Hvalues
      (HΔ.trans HE) (HΔ.trans HElaw) nextIndices_is_function Hicut
      (omegaOne_member_injects Hi)
  exact countableActiveState_of_entry Hactive

/-- Every actual tagged entry has countable active history, by the
internal least-bad-stage induction theorem. -/
theorem fusion_run_active_countable
    {color : Bool} {R E F top Run ξ A Z U : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run)
    (Hpair : Γ ≤ pair ξ (pair ξ (entry A Z U)) ∈ᴮ Run) :
    Γ ≤ injects_into U bSet.omega :=
  countableActiveState_apply
    (good_of_imageRecLaw_pair omegaOne_Ord HRun Hlaw countableActiveState_ext
      (fusion_active_countable_invariant_step HE HElaw HRun Hlaw) Hpair)

/-- The decoded active family on any prefix is countable-valued. The
stage guard does not require support of the entire run on that prefix. -/
theorem fusion_prefix_countableValues
    {color : Bool} {R E F top Run ξ : bSet 𝔹} {Γ : 𝔹}
    (HE : Γ ≤ is_function (blockObjects color R) blockEnumerationCodes E)
    (HElaw : Γ ≤ blockEnumerationFamilyLaw color R E)
    (HRun : Γ ≤ is_function omegaOne runSpace Run)
    (Hlaw : Γ ≤ runLaw color R E F top Run) :
    Γ ≤ countableValues ξ (activeFamily (taggedPrefix ξ omegaOne entrySpace Run)) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro U
  rw [← deduction]
  let Δ := Γ ⊓ (i ∈ᴮ ξ ⊓ pair i U ∈ᴮ
    activeFamily (taggedPrefix ξ omegaOne entrySpace Run))
  have HΔ : Δ ≤ Γ := inf_le_left
  obtain ⟨A, Z, Hentry⟩ := activeFamily_witness
    (show Δ ≤ pair i U ∈ᴮ activeFamily (taggedPrefix ξ omegaOne entrySpace Run) from
      inf_le_right.trans inf_le_right)
  have Hpair := (mem_taggedPrefix_pair_iff (HΔ.trans HRun)
    (HΔ.trans (fusion_run_tagging HRun Hlaw))).mp Hentry
  exact fusion_run_active_countable (HΔ.trans HE) (HΔ.trans HElaw)
    (HΔ.trans HRun) (HΔ.trans Hlaw) Hpair.2

end bSet.ErdosFusionRunCountable
