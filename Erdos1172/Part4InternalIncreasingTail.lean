/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalClosurePoints
public import Erdos1172.Part4InternalPartitionOrder

@[expose] public section

/-!
Removing the past of one actual value of an increasing omega-one row
leaves only values from strictly later stages. If the full range is
co-large, the remaining tail is co-large as well. No enumeration of
names or successful vertex run is assumed.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosIncreasingTail

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition ErdosCountablePast
open ErdosClosurePoints ErdosColargeIntersection

/-- Strict increase reflects strict membership on an ordinal domain. -/
theorem index_mem_of_value_mem {κ f i j x y : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (Hfunc : Γ ≤ is_func f)
    (Hinc : Γ ≤ increasingOn κ f) (Hi : Γ ≤ i ∈ᴮ κ) (Hj : Γ ≤ j ∈ᴮ κ)
    (Hix : Γ ≤ pair i x ∈ᴮ f) (Hjy : Γ ≤ pair j y ∈ᴮ f)
    (Hxy : Γ ≤ x ∈ᴮ y) : Γ ≤ i ∈ᴮ j := by
  have Htri := epsilon_trichotomy_of_Ord Hi Hj Hκ
  apply (le_inf (le_refl Γ) Htri).trans
  rw [inf_sup_left, inf_sup_left]
  apply sup_le
  · apply sup_le
    · have Heq : Γ ⊓ i =ᴮ j ≤ x =ᴮ y :=
        eq_of_is_func_of_eq (inf_le_left.trans Hfunc) inf_le_right
          (inf_le_left.trans Hix) (inf_le_left.trans Hjy)
      exact (bot_of_mem_self' (mem_congr Heq bv_refl (inf_le_left.trans Hxy))).trans bot_le
    · exact inf_le_right
  · have Hyx : Γ ⊓ j ∈ᴮ i ≤ y ∈ᴮ x :=
      increasingOn_apply (inf_le_left.trans Hinc) (inf_le_left.trans Hj)
        (inf_le_left.trans Hi) inf_le_right (inf_le_left.trans Hjy)
        (inf_le_left.trans Hix)
    exact (bot_of_mem_mem' x y (inf_le_left.trans Hxy) Hyx).trans bot_le

theorem value_above_of_not_mem_singleton_past {v x : bSet 𝔹} {Γ : 𝔹}
    (Hv : Γ ≤ v ∈ᴮ omegaOne) (Hx : Γ ≤ x ∈ᴮ omegaOne)
    (Hnot : Γ ≤ (x ∈ᴮ past ({v} : bSet 𝔹))ᶜ) : Γ ≤ v ∈ᴮ x := by
  rw [← compl_compl (v ∈ᴮ x), ← imp_bot, ← deduction]
  exact bv_absurd _
    (mem_singleton_past_of_not_after (inf_le_left.trans Hv)
      (inf_le_left.trans Hx) inf_le_right) (inf_le_left.trans Hnot)

def tailRange (f v : bSet 𝔹) : bSet 𝔹 :=
  difference (image omegaOne omegaOne f) (past ({v} : bSet 𝔹))

theorem mem_tailRange_iff {f v x : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ∈ᴮ tailRange f v ↔
      Γ ≤ x ∈ᴮ image omegaOne omegaOne f ∧ Γ ≤ (x ∈ᴮ past ({v} : bSet 𝔹))ᶜ := by
  simp only [tailRange, mem_difference, le_inf_iff]

theorem tailRange_colarge {J f v : bSet 𝔹} {Γ : 𝔹}
    (HJ : Γ ≤ isIdeal omegaOne J)
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (Hclosure : Γ ≤ countableClosure J)
    (Hrange : Γ ≤ colarge omegaOne J (image omegaOne omegaOne f))
    (Hv : Γ ≤ v ∈ᴮ omegaOne) : Γ ≤ colarge omegaOne J (tailRange f v) :=
  colarge_difference_of_small HJ Hrange (singleton_past_small HJ Habsorb Hclosure Hv)

/-- Every remaining range value has an actual stage strictly above the
stage of the cut value, at the original Boolean condition. -/
theorem tailRange_witness {f σ v x : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' omegaOne omegaOne f)
    (Hinc : Γ ≤ increasingOn omegaOne f) (Hσ : Γ ≤ σ ∈ᴮ omegaOne)
    (Hσv : Γ ≤ pair σ v ∈ᴮ f) (Hx : Γ ≤ x ∈ᴮ tailRange f v) :
    ∃ i : bSet 𝔹, Γ ≤ i ∈ᴮ omegaOne ∧ Γ ≤ σ ∈ᴮ i ∧ Γ ≤ pair i x ∈ᴮ f := by
  have Hparts := mem_tailRange_iff.mp Hx
  have Him := mem_image_iff.mp Hparts.1
  obtain ⟨i, Hi⟩ := exists_convert Him.2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  have Hvx : Γ ≤ v ∈ᴮ x := value_above_of_not_mem_singleton_past
    (value_mem_codomain Hf Hσ Hσv) Him.1 Hparts.2
  exact ⟨i, Hi.trans inf_le_left,
    index_mem_of_value_mem omegaOne_Ord (Hf.trans inf_le_left) Hinc Hσ
      (Hi.trans inf_le_left) Hσv (Hi.trans inf_le_right) Hvx,
    Hi.trans inf_le_right⟩

end bSet.ErdosIncreasingTail
