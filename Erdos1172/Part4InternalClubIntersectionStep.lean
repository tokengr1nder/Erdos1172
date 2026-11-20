/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalClubs
public import Erdos1172.Part4InternalOmegaTwoBounded
public import Erdos1172.Part4InternalCountableImage

@[expose] public section

/-!
A single step simultaneously meets every member of an internally
omega-one-small family of unbounded sets. Bounded internal choice and
the proved omega-two bound theorem construct the next endpoint. Strict
growth is imposed separately, so an empty family is covered as well.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosClubs

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosOmegaTwoBounded ErdosSmallFiberBound ErdosCountableImage

theorem exists_above_two {x d : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (Hx : Γ ≤ x ∈ᴮ omegaTwo) (Hd : Γ ≤ d ∈ᴮ omegaTwo) :
    ∃ y : bSet 𝔹, Γ ≤ y ∈ᴮ omegaTwo ⊓ (x ∈ᴮ y ⊓ d ∈ᴮ y) := by
  have Hex : Γ ≤ ⨆ y, y ∈ᴮ omegaTwo ⊓ (x ∈ᴮ y ⊓ d ∈ᴮ y) := by
    have Htri := epsilon_trichotomy_of_Ord Hx Hd omegaTwo_Ord
    apply (le_inf (le_refl Γ) Htri).trans
    rw [inf_sup_left, inf_sup_left]
    apply sup_le
    · apply sup_le
      · obtain ⟨y, Hy⟩ := exists_above_omegaTwo_member (inf_le_left.trans HCH)
          (inf_le_left.trans Hd)
        exact le_iSup_of_le y (le_inf (Hy.trans inf_le_left)
          (le_inf (mem_congr (bv_symm inf_le_right) bv_refl (Hy.trans inf_le_right))
            (Hy.trans inf_le_right)))
      · obtain ⟨y, Hy⟩ := exists_above_omegaTwo_member (inf_le_left.trans HCH)
          (inf_le_left.trans Hd)
        exact le_iSup_of_le y (le_inf (Hy.trans inf_le_left)
          (le_inf (mem_of_mem_Ord inf_le_right (Hy.trans inf_le_right)
            (Ord_of_mem_Ord (Hy.trans inf_le_left) omegaTwo_Ord))
            (Hy.trans inf_le_right)))
    · obtain ⟨y, Hy⟩ := exists_above_omegaTwo_member (inf_le_left.trans HCH)
        (inf_le_left.trans Hx)
      exact le_iSup_of_le y (le_inf (Hy.trans inf_le_left)
        (le_inf (Hy.trans inf_le_right)
          (mem_of_mem_Ord inf_le_right (Hy.trans inf_le_right)
            (Ord_of_mem_Ord (Hy.trans inf_le_left) omegaTwo_Ord))))
  exact exists_convert Hex
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_mem_right B_ext_mem_right))

def intervalHits (Q F x y : bSet 𝔹) : 𝔹 :=
  ⨅ q, ⨅ C, _root_.imp (q ∈ᴮ Q ⊓ pair q C ∈ᴮ F)
    (⨆ z, z ∈ᴮ C ⊓ (x ∈ᴮ z ⊓ z ∈ᴮ y))

theorem intervalHits_apply {Q F x y q C : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ intervalHits Q F x y) (Hq : Γ ≤ q ∈ᴮ Q)
    (HC : Γ ≤ pair q C ∈ᴮ F) :
    Γ ≤ ⨆ z, z ∈ᴮ C ⊓ (x ∈ᴮ z ⊓ z ∈ᴮ y) :=
  (le_inf (H.trans ((iInf_le _ q).trans (iInf_le _ C))) (le_inf Hq HC)).trans bv_imp_elim

/-- The selector is an actual supported function; its selected values
belong to every graph value at that index and lie above the old endpoint. -/
theorem exists_above_selector {Q F x : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_func' Q (bv_powerset omegaTwo) F)
    (Hvalues : Γ ≤ ⨅ q, ⨅ C, _root_.imp
      (q ∈ᴮ Q ⊓ pair q C ∈ᴮ F) (unboundedIn omegaTwo C))
    (Hx : Γ ≤ x ∈ᴮ omegaTwo) :
    ∃ f : bSet 𝔹, Γ ≤ is_function Q omegaTwo f ⊓
      (⨅ q, ⨅ z, _root_.imp (q ∈ᴮ Q ⊓ pair q z ∈ᴮ f)
        (⨅ C, _root_.imp (pair q C ∈ᴮ F) (z ∈ᴮ C ⊓ x ∈ᴮ z))) := by
  apply exists_selector_of_pointwise
    (P := fun q z => ⨅ C, _root_.imp (pair q C ∈ᴮ F) (z ∈ᴮ C ⊓ x ∈ᴮ z))
  · intro z
    exact B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_pair_mem_left) (h₂ := B_ext_const))
  · intro q
    exact B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_inf B_ext_mem_left B_ext_mem_right))
  · apply le_iInf
    intro q
    rw [← deduction]
    let Δ := Γ ⊓ q ∈ᴮ Q
    have HCex : Δ ≤ ⨆ C, C ∈ᴮ bv_powerset omegaTwo ⊓ pair q C ∈ᴮ F :=
      (le_inf (inf_le_left.trans ((HF.trans inf_le_right).trans (iInf_le _ q)))
        inf_le_right).trans bv_imp_elim
    obtain ⟨C, HC⟩ := exists_convert HCex
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    have HU : Δ ≤ unboundedIn omegaTwo C :=
      (le_inf (inf_le_left.trans (Hvalues.trans ((iInf_le _ q).trans (iInf_le _ C))))
        (le_inf inf_le_right (HC.trans inf_le_right))).trans bv_imp_elim
    obtain ⟨z, Hz⟩ := exists_unbounded_above HU (inf_le_left.trans Hx)
    apply le_iSup_of_le z
    refine le_inf (Hz.trans (inf_le_left.trans inf_le_right)) ?_
    apply le_iInf
    intro D
    rw [← deduction]
    have HCD : Δ ⊓ pair q D ∈ᴮ F ≤ C =ᴮ D :=
      eq_of_is_func_of_eq (inf_le_left.trans (inf_le_left.trans (HF.trans inf_le_left)))
        bv_refl (inf_le_left.trans (HC.trans inf_le_right)) inf_le_right
    exact le_inf (mem_congr bv_refl HCD
      (inf_le_left.trans (Hz.trans (inf_le_left.trans inf_le_left))))
      (inf_le_left.trans (Hz.trans inf_le_right))

/-- A next endpoint retains an interval witness for every indexed set.
The proof covers empty and internally mixed index sets at the same Γ. -/
theorem exists_simultaneous_bound {Q F x : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (HF : Γ ≤ is_func' Q (bv_powerset omegaTwo) F)
    (HQ : Γ ≤ injects_into Q omegaOne)
    (Hvalues : Γ ≤ ⨅ q, ⨅ C, _root_.imp
      (q ∈ᴮ Q ⊓ pair q C ∈ᴮ F) (unboundedIn omegaTwo C))
    (Hx : Γ ≤ x ∈ᴮ omegaTwo) :
    ∃ y : bSet 𝔹, Γ ≤ y ∈ᴮ omegaTwo ⊓ (x ∈ᴮ y ⊓ intervalHits Q F x y) := by
  obtain ⟨f, Hf⟩ := exists_above_selector HF Hvalues Hx
  have Hweak := is_func'_of_is_function (Hf.trans inf_le_left)
  obtain ⟨d, Hd⟩ := exists_strict_upper_bound HCH image_subset
    (image_injects_into_ordinal Hweak HQ omegaOne_Ord)
  obtain ⟨y, Hy⟩ := exists_above_two HCH Hx (Hd.trans inf_le_left)
  refine ⟨y, le_inf (Hy.trans inf_le_left)
    (le_inf (Hy.trans (inf_le_right.trans inf_le_left)) ?_)⟩
  apply le_iInf
  intro q
  apply le_iInf
  intro C
  rw [← deduction]
  let Δ := Γ ⊓ (q ∈ᴮ Q ⊓ pair q C ∈ᴮ F)
  have Hq : Δ ≤ q ∈ᴮ Q := inf_le_right.trans inf_le_left
  have Hzex : Δ ≤ ⨆ z, z ∈ᴮ omegaTwo ⊓ pair q z ∈ᴮ f :=
    (le_inf (inf_le_left.trans ((Hweak.trans inf_le_right).trans (iInf_le _ q))) Hq).trans
      bv_imp_elim
  obtain ⟨z, Hz⟩ := exists_convert Hzex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  have Hzspec : Δ ≤ ⨅ A, _root_.imp (pair q A ∈ᴮ F) (z ∈ᴮ A ⊓ x ∈ᴮ z) :=
    (le_inf (inf_le_left.trans ((Hf.trans inf_le_right).trans
      ((iInf_le _ q).trans (iInf_le _ z)))) (le_inf Hq (Hz.trans inf_le_right))).trans
        bv_imp_elim
  have Hzc : Δ ≤ z ∈ᴮ C ⊓ x ∈ᴮ z :=
    (le_inf (Hzspec.trans (iInf_le _ C)) (inf_le_right.trans inf_le_right)).trans bv_imp_elim
  have Hzd : Δ ≤ z ∈ᴮ d := mem_of_mem_subset (inf_le_left.trans (Hd.trans inf_le_right))
    (mem_image (Hz.trans inf_le_right) Hq (Hz.trans inf_le_left))
  have Hzy : Δ ≤ z ∈ᴮ y := mem_of_mem_Ord Hzd
    (inf_le_left.trans (Hy.trans (inf_le_right.trans inf_le_right)))
    (Ord_of_mem_Ord (inf_le_left.trans (Hy.trans inf_le_left)) omegaTwo_Ord)
  exact le_iSup_of_le z (le_inf (Hzc.trans inf_le_left)
    (le_inf (Hzc.trans inf_le_right) Hzy))

end bSet.ErdosClubs
