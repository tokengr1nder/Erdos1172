/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountablyCentered

@[expose] public section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIndexedIntersection

open ErdosIdeal ErdosCountablyCentered ErdosDenseBasis ErdosOmegaTwo

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- The actual intersection of the indexed values, bounded by the row.
For an empty index set it is the entire row. -/
def indexedIntersection (κ F T : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun z => ⨅ x, ⨅ A,
    _root_.imp ((x ∈ᴮ T) ⊓ pair x A ∈ᴮ F) (z ∈ᴮ A)) κ

theorem mem_indexedIntersection_iff {κ F T z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ indexedIntersection κ F T ↔
      Γ ≤ z ∈ᴮ κ ∧ Γ ≤ ⨅ x, ⨅ A, _root_.imp ((x ∈ᴮ T) ⊓ pair x A ∈ᴮ F) (z ∈ᴮ A) :=
  ErdosRelationGraph.mem_comprehend_and (B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_mem_left))))

theorem indexedIntersection_subset {κ F T : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ indexedIntersection κ F T ⊆ᴮ κ :=
  comprehend_subset (ϕ := fun z => ⨅ x, ⨅ A,
    _root_.imp ((x ∈ᴮ T) ⊓ pair x A ∈ᴮ F) (z ∈ᴮ A)) κ

theorem subset_indexedIntersection {κ F T C : bSet 𝔹} {Γ : 𝔹}
    (HC : Γ ≤ C ⊆ᴮ κ) (Hcommon : Γ ≤ indexedCommon F T C) :
    Γ ≤ C ⊆ᴮ indexedIntersection κ F T := by
  rw [subset_unfold']
  apply le_iInf; intro z; rw [← deduction]
  apply mem_indexedIntersection_iff.mpr
  refine ⟨mem_of_mem_subset (inf_le_left.trans HC) inf_le_right, ?_⟩
  apply le_iInf; intro x
  apply le_iInf; intro A
  rw [← deduction]
  exact mem_of_mem_subset
    (indexedCommon_apply (inf_le_left.trans (inf_le_left.trans Hcommon))
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right))
    (inf_le_left.trans inf_le_right)

theorem indexedIntersection_positive {κ J F T C : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (HC : Γ ≤ positive κ J C)
    (Hcommon : Γ ≤ indexedCommon F T C) :
    Γ ≤ positive κ J (indexedIntersection κ F T) := by
  refine le_inf indexedIntersection_subset ?_
  rw [← imp_bot, ← deduction]
  exact bv_absurd _
    (small_of_subset (downwardClosed_of_isIdeal (inf_le_left.trans HJ))
      inf_le_right
      (subset_indexedIntersection (inf_le_left.trans (HC.trans inf_le_left))
        (inf_le_left.trans Hcommon)))
    (inf_le_left.trans (HC.trans inf_le_right))

def positiveCountableIntersections (κ J F U : bSet 𝔹) : 𝔹 :=
  ⨅ T, _root_.imp ((T ⊆ᴮ U) ⊓ injects_into T bSet.omega)
    (positive κ J (indexedIntersection κ F T))

theorem positiveCountableIntersections_of_centered {κ J F U : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J)
    (Hcenter : Γ ≤ countablyCenteredFamily κ J F U) :
    Γ ≤ positiveCountableIntersections κ J F U := by
  apply le_iInf; intro T; rw [← deduction]
  let Δ := Γ ⊓ ((T ⊆ᴮ U) ⊓ injects_into T bSet.omega)
  have Hcommon : Δ ≤ ⨆ C, positive κ J C ⊓ indexedCommon F T C :=
    (le_inf (inf_le_left.trans (Hcenter.trans (iInf_le _ T))) inf_le_right).trans bv_imp_elim
  apply (le_inf (le_refl Δ) Hcommon).trans
  rw [inf_iSup_eq]
  apply iSup_le; intro C
  exact indexedIntersection_positive (inf_le_left.trans (inf_le_left.trans HJ))
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)

/-- All internally omega-two-sized indexed positive families in omega-two
have a same-sized subfamily whose countable bounded intersections are positive.
The index set and all function values range over arbitrary internal names. -/
noncomputable def countablyCenteredOn (κ J : bSet 𝔹) : 𝔹 :=
  ⨅ S, ⨅ F, _root_.imp
    (((S ⊆ᴮ omegaTwo) ⊓ injects_into omegaTwo S) ⊓
      (is_function S (bv_powerset κ) F ⊓ positiveValues κ J S F))
    (⨆ U, ((U ⊆ᴮ S) ⊓ injects_into omegaTwo U) ⊓
      positiveCountableIntersections κ J F U)

/-- The concrete internal positive-intersection counterpart of the dense
ideal centering theorem. No nonempty countable-subfamily premise is needed. -/
theorem countablyCenteredOn_of_dense_basis {κ J I B : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal κ J) (Hclosure : Γ ≤ countableClosure J)
    (HCH : Γ ≤ (CH : 𝔹))
    (HB : Γ ≤ is_function I (bv_powerset κ) B)
    (HBpos : Γ ≤ positiveValues κ J I B)
    (Hdense : Γ ≤ denseValues κ J I B) (HI : Γ ≤ injects_into I omegaOne) :
    Γ ≤ countablyCenteredOn κ J := by
  apply le_iInf; intro S
  apply le_iInf; intro F
  rw [← deduction]
  let Δ := Γ ⊓ (((S ⊆ᴮ omegaTwo) ⊓ injects_into omegaTwo S) ⊓
    (is_function S (bv_powerset κ) F ⊓ positiveValues κ J S F))
  have Hcenter : Δ ≤ countablyCentered κ J S F :=
    countablyCentered_of_dense_basis
      (inf_le_left.trans HJ) (inf_le_left.trans Hclosure) (inf_le_left.trans HCH)
      (inf_le_right.trans (inf_le_left.trans inf_le_right))
      (inf_le_right.trans (inf_le_right.trans inf_le_left))
      (inf_le_right.trans (inf_le_right.trans inf_le_right))
      (inf_le_left.trans HB) (inf_le_left.trans HBpos)
      (inf_le_left.trans Hdense) (inf_le_left.trans HI)
  apply (le_inf (le_refl Δ) Hcenter).trans
  unfold countablyCentered
  rw [inf_iSup_eq]
  apply iSup_le; intro U
  apply le_iSup_of_le U
  refine le_inf (inf_le_right.trans inf_le_left) ?_
  exact positiveCountableIntersections_of_centered
    (inf_le_left.trans (inf_le_left.trans HJ)) (inf_le_right.trans inf_le_right)

end bSet.ErdosIndexedIntersection
