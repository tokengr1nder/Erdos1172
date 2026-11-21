/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountableImage
public import Erdos1172.Part4InternalDenseBasis

@[expose] public section

/-!
# Internally countably centered large families

A common positive base modulo a countably complete ideal yields an actual
positive common subset for every internally countable subfamily of indices.
The selected indices, the countable subfamily, and their value image are
arbitrary Boolean-valued names. Their external presentations need not be
countable. The shared base and large index set are obtained from the dense
basis theorem, not assumed in the final theorem.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountablyCentered

open ErdosIdeal ErdosDenseBasis ErdosOmegaTwo

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- A set is contained in every value indexed by the given internal family. -/
def indexedCommon (F T C : bSet 𝔹) : 𝔹 :=
  ⨅ x : bSet 𝔹, ⨅ A : bSet 𝔹,
    _root_.imp (x ∈ᴮ T ⊓ pair x A ∈ᴮ F) (C ⊆ᴮ A)

/-- Every internally countable subfamily of indices has a positive common
subset. Empty subfamilies are included, without an extra nonempty premise. -/
def countablyCenteredFamily (κ J F U : bSet 𝔹) : 𝔹 :=
  ⨅ T : bSet 𝔹,
    _root_.imp (T ⊆ᴮ U ⊓ injects_into T bSet.omega)
      (⨆ C : bSet 𝔹, positive κ J C ⊓ indexedCommon F T C)

/-- There is an internally omega-two-large countably centered subfamily
of the original indexed family. -/
noncomputable def countablyCentered (κ J S F : bSet 𝔹) : 𝔹 :=
  ⨆ U : bSet 𝔹, (U ⊆ᴮ S ⊓ injects_into omegaTwo U) ⊓
    countablyCenteredFamily κ J F U

theorem indexedCommon_apply {F T C x A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ indexedCommon F T C) (Hx : Γ ≤ x ∈ᴮ T)
    (Hpair : Γ ≤ pair x A ∈ᴮ F) : Γ ≤ C ⊆ᴮ A :=
  (le_inf (H.trans ((iInf_le _ x).trans (iInf_le _ A))) (le_inf Hx Hpair)).trans bv_imp_elim

/-- Shared small losses pass from the indexed family to its actual value
image. No countability or functionality is needed for this implication. -/
theorem commonLoss_image_small {J F U A₀ T Y : bSet 𝔹} {Γ : 𝔹}
    (Hloss : Γ ≤ commonLoss J F U A₀) (HT : Γ ≤ T ⊆ᴮ U) :
    Γ ≤ ⨅ A : bSet 𝔹, _root_.imp (A ∈ᴮ image T Y F) (difference A₀ A ∈ᴮ J) := by
  apply le_iInf
  intro A
  rw [← deduction]
  have Hex := (mem_image_iff.mp (show Γ ⊓ A ∈ᴮ image T Y F ≤ A ∈ᴮ image T Y F from inf_le_right)).2
  obtain ⟨x, Hx⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have HU : Γ ⊓ A ∈ᴮ image T Y F ≤ x ∈ᴮ U :=
    mem_of_mem_subset (inf_le_left.trans HT) (Hx.trans inf_le_left)
  exact (le_inf
    (inf_le_left.trans (Hloss.trans ((iInf_le _ x).trans (iInf_le _ A))))
    (le_inf HU (Hx.trans inf_le_right))).trans bv_imp_elim

/-- A common subset of the bounded value image is common to all indexed
values; the actual function support supplies the codomain guard. -/
theorem indexedCommon_of_image_common {S Y F T C : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function S Y F)
    (Hcommon : Γ ≤ ⨅ A : bSet 𝔹, _root_.imp (A ∈ᴮ image T Y F) (C ⊆ᴮ A)) :
    Γ ≤ indexedCommon F T C := by
  apply le_iInf
  intro x
  apply le_iInf
  intro A
  rw [← deduction]
  have Hpair : Γ ⊓ (x ∈ᴮ T ⊓ pair x A ∈ᴮ F) ≤ pair x A ∈ᴮ F := inf_le_right.trans inf_le_right
  have Hmem : Γ ⊓ (x ∈ᴮ T ⊓ pair x A ∈ᴮ F) ≤ A ∈ᴮ image T Y F :=
    mem_image Hpair (inf_le_right.trans inf_le_left)
      (mem_codomain_of_is_function Hpair (inf_le_left.trans HF))
  exact (le_inf (inf_le_left.trans (Hcommon.trans (iInf_le _ A))) Hmem).trans bv_imp_elim

/-- The concrete remainder of the countable loss family is a positive
common subset of any internally countable family of selected indices. -/
theorem positive_common_of_countable_indices {κ J S F U A₀ T : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (Hclosure : Γ ≤ countableClosure J)
    (HF : Γ ≤ is_function S (bv_powerset κ) F)
    (HU : Γ ≤ U ⊆ᴮ S) (HA₀ : Γ ≤ positive κ J A₀)
    (Hloss : Γ ≤ commonLoss J F U A₀) (HT : Γ ≤ T ⊆ᴮ U)
    (Hcount : Γ ≤ injects_into T bSet.omega) :
    Γ ≤ ⨆ C : bSet 𝔹, positive κ J C ⊓ indexedCommon F T C := by
  let V := image T (bv_powerset κ) F
  have HVcount : Γ ≤ injects_into V bSet.omega :=
    ErdosCountableImage.restricted_image_countable
      (is_func'_of_is_function HF) (subset_trans' HT HU) Hcount
  have HVsmall : Γ ≤ ⨅ A : bSet 𝔹,
      _root_.imp (A ∈ᴮ V) (difference A₀ A ∈ᴮ J) :=
    commonLoss_image_small Hloss HT
  have HC := positive_commonRemainder_of_countable HJ Hclosure HA₀ HVcount HVsmall
  apply le_iSup_of_le (commonRemainder A₀ (lossFamily A₀ V))
  exact le_inf (HC.trans inf_le_left)
    (indexedCommon_of_image_common HF (HC.trans (inf_le_right.trans inf_le_right)))

/-- One shared positive base with small losses centers every internal
countable subfamily; it need not itself be a member of the indexed family. -/
theorem countablyCenteredFamily_of_commonLoss {κ J S F U A₀ : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (Hclosure : Γ ≤ countableClosure J)
    (HF : Γ ≤ is_function S (bv_powerset κ) F)
    (HU : Γ ≤ U ⊆ᴮ S) (HA₀ : Γ ≤ positive κ J A₀)
    (Hloss : Γ ≤ commonLoss J F U A₀) :
    Γ ≤ countablyCenteredFamily κ J F U := by
  apply le_iInf
  intro T
  rw [← deduction]
  exact positive_common_of_countable_indices
    (inf_le_left.trans HJ) (inf_le_left.trans Hclosure)
    (inf_le_left.trans HF) (inf_le_left.trans HU) (inf_le_left.trans HA₀)
    (inf_le_left.trans Hloss) (inf_le_right.trans inf_le_left)
    (inf_le_right.trans inf_le_right)

/-- Internal CH, a countably complete ideal, and an internally omega-one-
sized positive dense basis center an internally omega-two-large subfamily
of any positive family with an omega-two-large domain. No normality,
nonempty, external enumeration, or ground-name restriction is assumed. -/
theorem countablyCentered_of_dense_basis {κ J S I F B : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (Hclosure : Γ ≤ countableClosure J)
    (HCH : Γ ≤ (CH : 𝔹)) (Hlarge : Γ ≤ injects_into omegaTwo S)
    (HF : Γ ≤ is_function S (bv_powerset κ) F)
    (HFpos : Γ ≤ positiveValues κ J S F)
    (HB : Γ ≤ is_function I (bv_powerset κ) B)
    (HBpos : Γ ≤ positiveValues κ J I B)
    (Hdense : Γ ≤ denseValues κ J I B) (HI : Γ ≤ injects_into I omegaOne) :
    Γ ≤ countablyCentered κ J S F := by
  have Hbase := exists_large_common_basis HCH Hlarge HF HFpos HB HBpos Hdense HI
  apply (le_inf (le_refl Γ) Hbase).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro A₀
  rw [← inf_assoc, inf_iSup_eq]
  apply iSup_le
  intro U
  apply le_iSup_of_le U
  refine le_inf (inf_le_right.trans inf_le_left) ?_
  exact countablyCenteredFamily_of_commonLoss
    (inf_le_left.trans (inf_le_left.trans HJ))
    (inf_le_left.trans (inf_le_left.trans Hclosure))
    (inf_le_left.trans (inf_le_left.trans HF))
    (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)

end bSet.ErdosCountablyCentered
