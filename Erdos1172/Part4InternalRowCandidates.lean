/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountablePast
public import Erdos1172.Part4InternalColargeIntersection
public import Erdos1172.Part4InternalOrdinalLeast

@[expose] public section

/-!
The exact admissible set at an arbitrary internal countable row stage.
Its members satisfy the seed, all earlier section constraints, and strict
order above every earlier value. Countable closure makes this entire set
co-large; properness then supplies its actual least member. This is one
constructed stage, not an assumed full successful omega-one run.
-/

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosRowCandidates

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosIndexedIntersection
open ErdosCountablePast ErdosColargeIntersection ErdosOrdinalLeast

def rowCandidates (δ seed F h : bSet 𝔹) : bSet 𝔹 :=
  difference (indexedIntersection omegaOne F δ)
    (binary_union (difference omegaOne seed) (past (image δ omegaOne h)))

def rowAdmissible (δ seed F h x : bSet 𝔹) : 𝔹 :=
  x ∈ᴮ omegaOne ⊓ (x ∈ᴮ seed ⊓
    ((⨅ j, ⨅ A, _root_.imp (j ∈ᴮ δ ⊓ pair j A ∈ᴮ F) (x ∈ᴮ A)) ⊓
      (⨅ j, ⨅ v, _root_.imp (j ∈ᴮ δ ⊓ pair j v ∈ᴮ h) (v ∈ᴮ x))))

theorem rowCandidates_subset {δ seed F h : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ rowCandidates δ seed F h ⊆ᴮ omegaOne :=
  subset_trans' difference_subset indexedIntersection_subset

/-- The concrete loss-removal set is precisely the full admissible set,
not a smaller chosen set. Totality is required only on the guarded prefix. -/
theorem mem_rowCandidates_iff {δ seed F h x : bSet 𝔹} {Γ : 𝔹}
    (Hh : Γ ≤ is_func' δ omegaOne h) :
    Γ ≤ x ∈ᴮ rowCandidates δ seed F h ↔ Γ ≤ rowAdmissible δ seed F h x := by
  constructor
  · intro Hx
    have Hdata : Γ ≤ x ∈ᴮ indexedIntersection omegaOne F δ ⊓
        ((x ∈ᴮ difference omegaOne seed)ᶜ ⊓ (x ∈ᴮ past (image δ omegaOne h))ᶜ) := by
      simpa only [rowCandidates, mem_difference, mem_binary_union, compl_sup] using Hx
    have Hinter := mem_indexedIntersection_iff.mp (Hdata.trans inf_le_left)
    have Hseed : Γ ≤ x ∈ᴮ seed := by
      rw [← compl_compl (x ∈ᴮ seed), ← imp_bot, ← deduction]
      have Hbad : Γ ⊓ (x ∈ᴮ seed)ᶜ ≤ x ∈ᴮ difference omegaOne seed := by
        rw [mem_difference]
        exact le_inf (inf_le_left.trans Hinter.1) inf_le_right
      exact bv_absurd _ Hbad (inf_le_left.trans (Hdata.trans (inf_le_right.trans inf_le_left)))
    refine le_inf Hinter.1 (le_inf Hseed (le_inf Hinter.2 ?_))
    have Habove : Γ ≤ ⨅ v, _root_.imp (v ∈ᴮ image δ omegaOne h) (v ∈ᴮ x) :=
      above_past image_subset Hinter.1 (Hdata.trans (inf_le_right.trans inf_le_right))
    apply le_iInf
    intro j
    apply le_iInf
    intro v
    rw [← deduction]
    let Δ := Γ ⊓ (j ∈ᴮ δ ⊓ pair j v ∈ᴮ h)
    have Hrange : Δ ≤ rangeMem δ h v := le_iSup_of_le j inf_le_right
    have Hv : Δ ≤ v ∈ᴮ image δ omegaOne h :=
      mem_image_iff.mpr ⟨rangeMem_le_codomain (inf_le_left.trans Hh) Hrange, Hrange⟩
    exact (le_inf (inf_le_left.trans (Habove.trans (iInf_le _ v))) Hv).trans bv_imp_elim
  · intro Hlegal
    have Hxω : Γ ≤ x ∈ᴮ omegaOne := Hlegal.trans inf_le_left
    have Hseed : Γ ≤ x ∈ᴮ seed := Hlegal.trans (inf_le_right.trans inf_le_left)
    have Hsections : Γ ≤ ⨅ j, ⨅ A,
        _root_.imp (j ∈ᴮ δ ⊓ pair j A ∈ᴮ F) (x ∈ᴮ A) :=
      Hlegal.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    have Hprevious : Γ ≤ ⨅ j, ⨅ v,
        _root_.imp (j ∈ᴮ δ ⊓ pair j v ∈ᴮ h) (v ∈ᴮ x) :=
      Hlegal.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
    have Habove : Γ ≤ ⨅ v, _root_.imp (v ∈ᴮ image δ omegaOne h) (v ∈ᴮ x) := by
      apply le_iInf
      intro v
      rw [← deduction]
      obtain ⟨j, Hj⟩ := exists_convert
        (mem_image_iff.mp (show Γ ⊓ v ∈ᴮ image δ omegaOne h ≤
          v ∈ᴮ image δ omegaOne h from inf_le_right)).2
        (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
      exact (le_inf (inf_le_left.trans
        (Hprevious.trans ((iInf_le _ j).trans (iInf_le _ v)))) Hj).trans bv_imp_elim
    have HnotSeedLoss : Γ ≤ (x ∈ᴮ difference omegaOne seed)ᶜ := by
      rw [← imp_bot, ← deduction, mem_difference]
      exact bv_absurd _ (inf_le_left.trans Hseed) (inf_le_right.trans inf_le_right)
    change Γ ≤ x ∈ᴮ difference (indexedIntersection omegaOne F δ)
      (binary_union (difference omegaOne seed) (past (image δ omegaOne h)))
    rw [mem_difference, mem_binary_union, compl_sup]
    exact le_inf (mem_indexedIntersection_iff.mpr ⟨Hxω, Hsections⟩)
      (le_inf HnotSeedLoss (not_mem_past_of_above Habove))

/-- The whole set of admissible next coordinates is co-large. The actual
past image is internally countable; it need not have a countable external
presentation, and the original graph may contain later coordinates. -/
theorem rowCandidates_colarge {J δ seed F h : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J) (Hδ : Γ ≤ δ ∈ᴮ omegaOne)
    (Hseed : Γ ≤ colarge omegaOne J seed)
    (HF : Γ ≤ is_func' δ (bv_powerset omegaOne) F)
    (Hvalues : Γ ≤ ⨅ j, ⨅ A, _root_.imp (j ∈ᴮ δ ⊓ pair j A ∈ᴮ F) (difference omegaOne A ∈ᴮ J))
    (Hh : Γ ≤ is_func' δ omegaOne h) :
    Γ ≤ colarge omegaOne J (rowCandidates δ seed F h) := by
  have Hinter : Γ ≤ colarge omegaOne J (indexedIntersection omegaOne F δ) :=
    indexedIntersection_colarge HJ Hclosure HF (omegaOne_member_injects Hδ) Hvalues
  have Hpast : Γ ≤ past (image δ omegaOne h) ∈ᴮ J := image_past_small HJ Habsorb Hclosure Hh Hδ
  exact colarge_difference_of_small HJ Hinter
    (small_union (unionClosed_of_isIdeal HJ) (Hseed.trans inf_le_right) Hpast)

end bSet.ErdosRowCandidates
