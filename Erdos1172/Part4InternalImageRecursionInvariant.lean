/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBoundedImageRecursion
public import Erdos1172.Part4InternalOrdinalLeast

@[expose] public section

/-!
# Internal invariant induction for bounded image recursion

The bad stages form an actual separated subset of the internal ordinal.
If a bad value exists, fullness selects a least bad stage at that same
Boolean condition. Every member of its strict-prefix image is good,
since a bad predecessor would contradict leastness. The step implication
and the exact recursion equation then contradict the bad value.

This is internal ordinal induction via leastness, not induction on a
ground presentation of the stages or an assumed completed invariant.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosImageRecursionInvariant

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosBoundedImageRecursion ErdosOrdinalLeast ErdosRelationGraph

def allGood (Good : bSet 𝔹 → 𝔹) (T : bSet 𝔹) : 𝔹 :=
  ⨅ y, _root_.imp (y ∈ᴮ T) (Good y)

def imageRecInvariantStep (θ V : bSet 𝔹) (Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹)
    (Run : bSet 𝔹) (Good : bSet 𝔹 → 𝔹) : 𝔹 :=
  ⨅ i, _root_.imp (i ∈ᴮ θ ⊓ allGood Good (image i V Run)) (Good (Φ i (image i V Run)))

theorem allGood_ext_set (Good : bSet 𝔹 → 𝔹) : B_ext (allGood Good) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))

theorem allGood_apply {Good : bSet 𝔹 → 𝔹} {T y : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ allGood Good T) (Hy : Γ ≤ y ∈ᴮ T) : Γ ≤ Good y :=
  (le_inf (H.trans (iInf_le _ y)) Hy).trans bv_imp_elim

theorem imageRecInvariantStep_apply {θ V Run i : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Good : bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hstep : Γ ≤ imageRecInvariantStep θ V Φ Run Good)
    (Hi : Γ ≤ i ∈ᴮ θ) (Hpast : Γ ≤ allGood Good (image i V Run)) :
    Γ ≤ Good (Φ i (image i V Run)) :=
  (le_inf (Hstep.trans (iInf_le _ i)) (le_inf Hi Hpast)).trans bv_imp_elim

def badStages (θ Run : bSet 𝔹) (Good : bSet 𝔹 → 𝔹) : bSet 𝔹 :=
  comprehend (fun i => ⨆ y, pair i y ∈ᴮ Run ⊓ (Good y)ᶜ) θ

private theorem mem_badStages_iff {θ Run i : bSet 𝔹} {Good : bSet 𝔹 → 𝔹} {Γ : 𝔹} :
    Γ ≤ i ∈ᴮ badStages θ Run Good ↔
      Γ ≤ i ∈ᴮ θ ∧ Γ ≤ ⨆ y, pair i y ∈ᴮ Run ⊓ (Good y)ᶜ :=
  mem_comprehend_and (B_ext_iSup (h := fun _ => B_ext_inf B_ext_pair_mem_left B_ext_const))

private theorem badStages_subset {θ Run : bSet 𝔹} {Good : bSet 𝔹 → 𝔹} {Γ : 𝔹} :
    Γ ≤ badStages θ Run Good ⊆ᴮ θ :=
  comprehend_subset (ϕ := fun i => ⨆ y, pair i y ∈ᴮ Run ⊓ (Good y)ᶜ) θ

private theorem least_bad_prefix_allGood {θ V Run j : bSet 𝔹}
    {Good : bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hθ : Γ ≤ Ord θ) (Hleast : Γ ≤ leastIn (badStages θ Run Good) j) :
    Γ ≤ allGood Good (image j V Run) := by
  have Hjθ : Γ ≤ j ∈ᴮ θ := (mem_badStages_iff.mp (leastIn_mem Hleast)).1
  apply le_iInf
  intro y
  rw [← deduction, ← compl_compl (Good y), ← imp_bot, ← deduction]
  let Δ := (Γ ⊓ y ∈ᴮ image j V Run) ⊓ (Good y)ᶜ
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  obtain ⟨k, Hk⟩ := exists_convert ((mem_image_iff.mp
    (show Δ ≤ y ∈ᴮ image j V Run from inf_le_left.trans inf_le_right)).2)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hkθ : Δ ≤ k ∈ᴮ θ :=
    mem_of_mem_Ord (Hk.trans inf_le_left) (HΔ.trans Hjθ) (HΔ.trans Hθ)
  have Hkbad : Δ ≤ k ∈ᴮ badStages θ Run Good :=
    mem_badStages_iff.mpr ⟨Hkθ, le_iSup_of_le y (le_inf (Hk.trans inf_le_right) inf_le_right)⟩
  have Hcases : Δ ≤ j =ᴮ k ⊔ j ∈ᴮ k := leastIn_apply (HΔ.trans Hleast) Hkbad
  apply (le_inf (le_refl Δ) Hcases).trans
  rw [inf_sup_left]
  apply sup_le
  · exact bot_of_mem_self'
      (mem_congr bv_refl inf_le_right (inf_le_left.trans (Hk.trans inf_le_left)))
  · exact bot_of_mem_mem' k j (inf_le_left.trans (Hk.trans inf_le_left)) inf_le_right

private theorem bot_of_bad_value {θ V Run i y : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Good : bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hθ : Γ ≤ Ord θ) (Hlaw : Γ ≤ imageRecLaw V Φ Run) (HGood : B_ext Good)
    (Hstep : Γ ≤ imageRecInvariantStep θ V Φ Run Good)
    (Hi : Γ ≤ i ∈ᴮ θ) (Hpair : Γ ≤ pair i y ∈ᴮ Run) (Hbad : Γ ≤ (Good y)ᶜ) :
    Γ ≤ ⊥ := by
  have Hibad : Γ ≤ i ∈ᴮ badStages θ Run Good :=
    mem_badStages_iff.mpr ⟨Hi, le_iSup_of_le y (le_inf Hpair Hbad)⟩
  have Hnonempty : Γ ≤ (badStages θ Run Good =ᴮ ∅)ᶜ :=
    nonempty_of_exists_mem _ (le_iSup_of_le i Hibad)
  obtain ⟨j, Hj⟩ := exists_least_of_nonempty Hθ badStages_subset Hnonempty
  have Hjbad := mem_badStages_iff.mp (leastIn_mem Hj)
  obtain ⟨z, Hz⟩ := exists_convert Hjbad.2
    (B_ext_inf B_ext_pair_mem_right (B_ext_neg (h := HGood)))
  have Hnext : Γ ≤ Good (Φ j (image j V Run)) :=
    imageRecInvariantStep_apply Hstep Hjbad.1 (least_bad_prefix_allGood Hθ Hj)
  have Hgoodz : Γ ≤ Good z :=
    bv_rw' (ϕ := Good) (imageRecLaw_apply Hlaw (Hz.trans inf_le_left))
      (h_congr := HGood) (H_new := Hnext)
  exact bv_absurd _ Hgoodz (Hz.trans inf_le_right)

/-- Every actual graph value satisfies the invariant. Actual support
supplies its stage bound; the step premise only assumes goodness of the
strict-prefix image at the current stage. -/
theorem values_good_of_imageRecLaw {θ V Run : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Good : bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hθ : Γ ≤ Ord θ) (HF : Γ ≤ is_function θ V Run)
    (Hlaw : Γ ≤ imageRecLaw V Φ Run) (HGood : B_ext Good)
    (Hstep : Γ ≤ imageRecInvariantStep θ V Φ Run Good) :
    Γ ≤ ⨅ i, ⨅ y, _root_.imp (pair i y ∈ᴮ Run) (Good y) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro y
  rw [← deduction, ← compl_compl (Good y), ← imp_bot, ← deduction]
  let Δ := (Γ ⊓ pair i y ∈ᴮ Run) ⊓ (Good y)ᶜ
  have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
  have Hpair : Δ ≤ pair i y ∈ᴮ Run := inf_le_left.trans inf_le_right
  exact bot_of_bad_value (HΔ.trans Hθ) (HΔ.trans Hlaw) HGood (HΔ.trans Hstep)
    (mem_domain_of_is_function Hpair (HΔ.trans HF)) Hpair inf_le_right

theorem good_of_imageRecLaw_pair {θ V Run i y : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Good : bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hθ : Γ ≤ Ord θ) (HF : Γ ≤ is_function θ V Run)
    (Hlaw : Γ ≤ imageRecLaw V Φ Run) (HGood : B_ext Good)
    (Hstep : Γ ≤ imageRecInvariantStep θ V Φ Run Good)
    (Hpair : Γ ≤ pair i y ∈ᴮ Run) : Γ ≤ Good y :=
  (le_inf ((values_good_of_imageRecLaw Hθ HF Hlaw HGood Hstep).trans
    ((iInf_le _ i).trans (iInf_le _ y))) Hpair).trans bv_imp_elim

theorem image_allGood_of_imageRecLaw {θ V Run : bSet 𝔹}
    {Φ : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Good : bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hθ : Γ ≤ Ord θ) (HF : Γ ≤ is_function θ V Run)
    (Hlaw : Γ ≤ imageRecLaw V Φ Run) (HGood : B_ext Good)
    (Hstep : Γ ≤ imageRecInvariantStep θ V Φ Run Good) :
    Γ ≤ allGood Good (image θ V Run) := by
  have Hvalues := values_good_of_imageRecLaw Hθ HF Hlaw HGood Hstep
  apply le_iInf
  intro y
  rw [← deduction]
  obtain ⟨i, Hi⟩ := exists_convert ((mem_image_iff.mp
    (show Γ ⊓ y ∈ᴮ image θ V Run ≤ y ∈ᴮ image θ V Run from inf_le_right)).2)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact (le_inf (inf_le_left.trans (Hvalues.trans ((iInf_le _ i).trans (iInf_le _ y))))
    (Hi.trans inf_le_right)).trans bv_imp_elim

end bSet.ErdosImageRecursionInvariant
