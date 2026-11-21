/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFusionRowCandidates

@[expose] public section

/-!
# The actual active coordinate masks see entire later blocks

The mask of a row is constructed from its recorded coordinates at stages
strictly after its birth. Candidate membership handles target blocks
before the selection stage; the inclusive active law handles the current
block and all later blocks. All comparisons and witnesses are internal.

The candidate law also retains strict coordinate growth across failed
intermediate block stages. No prebirth coordinate is treated as active.
These are local implications from actual graph laws, not an assumed final
compatible mask or a claim that the masks are positive. Normal co-largeness
of the birth-guarded ranges and the final countable block tail are separate
obligations.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosFusionMaskedTail

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosCanonicalBlocks ErdosFusionRowCandidates

/-- The actual active range of one coordinate row. The birth stage and
all earlier coordinates are excluded from the domain, not from a later
arbitrarily chosen family of values. -/
def activeMask (X ν : bSet 𝔹) : bSet 𝔹 :=
  comprehend (fun v => ⨆ ξ, (ξ ∈ᴮ omegaOne ⊓ ν ∈ᴮ ξ) ⊓
    pair (pair ξ ν) v ∈ᴮ X) omegaOne

theorem mem_activeMask_iff {X ν v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ v ∈ᴮ activeMask X ν ↔ Γ ≤ v ∈ᴮ omegaOne ∧
      Γ ≤ ⨆ ξ, (ξ ∈ᴮ omegaOne ⊓ ν ∈ᴮ ξ) ⊓ pair (pair ξ ν) v ∈ᴮ X :=
  ErdosRelationGraph.mem_comprehend_and
    (B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_pair_mem_right))

theorem activeMask_subset {X ν : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ activeMask X ν ⊆ᴮ omegaOne :=
  comprehend_subset (ϕ := fun v => ⨆ ξ, (ξ ∈ᴮ omegaOne ⊓ ν ∈ᴮ ξ) ⊓
    pair (pair ξ ν) v ∈ᴮ X) omegaOne

/-- Fullness supplies a genuinely active stage for an arbitrary mixed
mask value, without shrinking its original Boolean condition. -/
theorem activeMask_witness {X ν v : bSet 𝔹} {Γ : 𝔹}
    (Hv : Γ ≤ v ∈ᴮ activeMask X ν) :
    ∃ ξ : bSet 𝔹, (Γ ≤ ξ ∈ᴮ omegaOne) ∧ (Γ ≤ ν ∈ᴮ ξ) ∧ Γ ≤ pair (pair ξ ν) v ∈ᴮ X := by
  obtain ⟨ξ, Hξ⟩ := exists_convert (mem_activeMask_iff.mp Hv).2
    (B_ext_inf (B_ext_inf B_ext_mem_left B_ext_mem_right)
      (B_ext_pair_left (ϕ := fun q => pair q v ∈ᴮ X) B_ext_pair_mem_left))
  exact ⟨ξ, Hξ.trans (inf_le_left.trans inf_le_left),
    Hξ.trans (inf_le_left.trans inf_le_right), Hξ.trans inf_le_right⟩

theorem mem_activeMask_of_coordinate {X ν ξ v : bSet 𝔹} {Γ : 𝔹}
    (Hξ : Γ ≤ ξ ∈ᴮ omegaOne) (Hνξ : Γ ≤ ν ∈ᴮ ξ) (Hv : Γ ≤ v ∈ᴮ omegaOne)
    (Hcoord : Γ ≤ pair (pair ξ ν) v ∈ᴮ X) : Γ ≤ v ∈ᴮ activeMask X ν :=
  mem_activeMask_iff.mpr ⟨Hv, le_iSup_of_le ξ (le_inf (le_inf Hξ Hνξ) Hcoord)⟩

/-- Membership in the original activated candidate set, with the same
whole-block graph and fixed canonical enumeration. Leastness implies this
law, but is not needed for the cross-edge implication itself. -/
def coordinateCandidateLaw (edgeColor : Bool) (R E top Blocks X : bSet 𝔹) : 𝔹 :=
  ⨅ ν, ⨅ ξ, ⨅ b, ⨅ v, _root_.imp
    ((ν ∈ᴮ ξ ⊓ ξ ∈ᴮ omegaOne) ⊓
      (pair ν b ∈ᴮ Blocks ⊓ pair (pair ξ ν) v ∈ᴮ X))
    (v ∈ᴮ fusionRowCandidates edgeColor R E b top ξ ν Blocks X)

theorem coordinateCandidateLaw_apply
    {edgeColor : Bool} {R E top Blocks X ν ξ b v : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ coordinateCandidateLaw edgeColor R E top Blocks X)
    (Hνξ : Γ ≤ ν ∈ᴮ ξ) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne)
    (Hνb : Γ ≤ pair ν b ∈ᴮ Blocks) (Hcoord : Γ ≤ pair (pair ξ ν) v ∈ᴮ X) :
    Γ ≤ v ∈ᴮ fusionRowCandidates edgeColor R E b top ξ ν Blocks X :=
  (le_inf (H.trans ((iInf_le _ ν).trans ((iInf_le _ ξ).trans
    ((iInf_le _ b).trans (iInf_le _ v)))))
    (le_inf (le_inf Hνξ Hξ) (le_inf Hνb Hcoord))).trans bv_imp_elim

/-- Inclusive activity is essential: the block selected at the same
stage must obey the coordinate selected immediately before it. -/
def inclusiveActiveLaw (edgeColor : Bool) (R E Blocks X : bSet 𝔹) : 𝔹 :=
  ⨅ ν, ⨅ ξ, ⨅ μ, ⨅ b, ⨅ c, ⨅ v, _root_.imp
    ((ν ∈ᴮ ξ ⊓ ξ ∈ᴮ omegaOne) ⊓
      ((ξ =ᴮ μ ⊔ ξ ∈ᴮ μ) ⊓ (pair ν b ∈ᴮ Blocks ⊓
        (pair μ c ∈ᴮ Blocks ⊓ pair (pair ξ ν) v ∈ᴮ X))))
    (⨅ x, ⨅ y, _root_.imp (pair v x ∈ᴮ canonicalRow E b ⊓ y ∈ᴮ c)
      (graphColor edgeColor R x y))

theorem inclusiveActiveLaw_apply
    {edgeColor : Bool} {R E Blocks X ν ξ μ b c v x y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ inclusiveActiveLaw edgeColor R E Blocks X)
    (Hνξ : Γ ≤ ν ∈ᴮ ξ) (Hξ : Γ ≤ ξ ∈ᴮ omegaOne)
    (Hξμ : Γ ≤ ξ =ᴮ μ ⊔ ξ ∈ᴮ μ)
    (Hνb : Γ ≤ pair ν b ∈ᴮ Blocks) (Hμc : Γ ≤ pair μ c ∈ᴮ Blocks)
    (Hcoord : Γ ≤ pair (pair ξ ν) v ∈ᴮ X)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b) (Hy : Γ ≤ y ∈ᴮ c) :
    Γ ≤ graphColor edgeColor R x y := by
  have Hcross := (le_inf (H.trans ((iInf_le _ ν).trans ((iInf_le _ ξ).trans
    ((iInf_le _ μ).trans ((iInf_le _ b).trans ((iInf_le _ c).trans (iInf_le _ v)))))))
    (le_inf (le_inf Hνξ Hξ) (le_inf Hξμ (le_inf Hνb (le_inf Hμc Hcoord))))).trans bv_imp_elim
  exact (le_inf (Hcross.trans ((iInf_le _ x).trans (iInf_le _ y)))
    (le_inf Hvx Hy)).trans bv_imp_elim

/-- Every actual active-mask value sees every point of an entire later
block. The target is not shrunk to a separately chosen mask. -/
theorem activeMask_cross_whole_block
    {edgeColor : Bool} {R E top Blocks X ν μ b c v x y : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func' (prod omegaOne omegaOne) omegaOne X)
    (Hlaw : Γ ≤ coordinateCandidateLaw edgeColor R E top Blocks X)
    (Hactive : Γ ≤ inclusiveActiveLaw edgeColor R E Blocks X)
    (Hμ : Γ ≤ μ ∈ᴮ omegaOne) (Hνμ : Γ ≤ ν ∈ᴮ μ)
    (Hνb : Γ ≤ pair ν b ∈ᴮ Blocks) (Hμc : Γ ≤ pair μ c ∈ᴮ Blocks)
    (Hv : Γ ≤ v ∈ᴮ activeMask X ν)
    (Hvx : Γ ≤ pair v x ∈ᴮ canonicalRow E b) (Hy : Γ ≤ y ∈ᴮ c) :
    Γ ≤ graphColor edgeColor R x y := by
  obtain ⟨ξ, Hξ, Hνξ, Hcoord⟩ := activeMask_witness Hv
  have Hinclusive : Γ ⊓ (ξ =ᴮ μ ⊔ ξ ∈ᴮ μ) ≤ graphColor edgeColor R x y :=
    inclusiveActiveLaw_apply (inf_le_left.trans Hactive)
      (inf_le_left.trans Hνξ) (inf_le_left.trans Hξ) inf_le_right
      (inf_le_left.trans Hνb) (inf_le_left.trans Hμc) (inf_le_left.trans Hcoord)
      (inf_le_left.trans Hvx) (inf_le_left.trans Hy)
  have Hprior : Γ ⊓ μ ∈ᴮ ξ ≤ graphColor edgeColor R x y := by
    have HXξ : Γ ≤ is_func' (prod ξ omegaOne) omegaOne X :=
      is_func'_subset_of_is_func' HX
        (ErdosPartialInjection.prod_domain_mono (subset_of_mem_Ord Hξ omegaOne_Ord))
    exact fusionCandidate_cross_previous_block (inf_le_left.trans HXξ)
      (inf_le_left.trans (mem_of_mem_Ord Hνμ Hμ omegaOne_Ord))
      (inf_le_left.trans (coordinateCandidateLaw_apply Hlaw Hνξ Hξ Hνb Hcoord))
      inf_le_right (inf_le_left.trans Hνμ) (inf_le_left.trans Hμc)
      (inf_le_left.trans Hvx) (inf_le_left.trans Hy)
  apply (le_inf (le_refl Γ) (epsilon_trichotomy_of_Ord Hξ Hμ omegaOne_Ord)).trans
  rw [inf_sup_left]
  exact sup_le Hinclusive Hprior

end bSet.ErdosFusionMaskedTail
