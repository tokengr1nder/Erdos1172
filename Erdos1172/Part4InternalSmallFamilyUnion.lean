/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaTwoBounded
public import Erdos1172.Part4InternalCountableImage

@[expose] public section

/-!
An internally omega-one-small family of internally omega-one-small sets has
an internally omega-one-small union under CH. The proof constructs an
actual selector from the union to the family, and rules out the large branch
of internal cardinal comparison by the checked pigeonhole theorem.
Indexed families use their actual internal value image; no externally small
indexing or independently supplied coherent choices are assumed.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSmallFamilyUnion

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosFiberInjection

/-- Every guarded value of the internal indexed graph is omega-one-small. -/
noncomputable def smallValues (Q F : bSet 𝔹) : 𝔹 :=
  ⨅ q, ⨅ A, _root_.imp (q ∈ᴮ Q ⊓ pair q A ∈ᴮ F) (injects_into A omegaOne)

theorem smallValues_apply {Q F q A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ smallValues Q F) (Hq : Γ ≤ q ∈ᴮ Q)
    (HA : Γ ≤ pair q A ∈ᴮ F) : Γ ≤ injects_into A omegaOne :=
  (le_inf (H.trans ((iInf_le _ q).trans (iInf_le _ A))) (le_inf Hq HA)).trans
    bv_imp_elim

/-- The pointwise indexed law holds for every arbitrary name in the actual
value image. Functionality is not needed for this transfer. -/
theorem smallValues_image {Q K F : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ smallValues Q F) :
    Γ ≤ ⨅ A, _root_.imp (A ∈ᴮ image Q K F) (injects_into A omegaOne) := by
  apply le_iInf
  intro A
  rw [← deduction]
  have Hex := (mem_image_iff.mp
    (show Γ ⊓ A ∈ᴮ image Q K F ≤ A ∈ᴮ image Q K F from inf_le_right)).2
  obtain ⟨q, Hq⟩ := exists_convert Hex
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact smallValues_apply (inf_le_left.trans H) (Hq.trans inf_le_left)
    (Hq.trans inf_le_right)

/-- A small family of small sets has small union. All families and their
members are arbitrary Boolean-valued names, with no ambient containment
or nonemptiness assumption. -/
theorem union_injects_omegaOne {T : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HT : Γ ≤ injects_into T omegaOne)
    (Hmembers : Γ ≤ ⨅ A, _root_.imp (A ∈ᴮ T) (injects_into A omegaOne)) :
    Γ ≤ injects_into (bv_union T) omegaOne := by
  have Hnot : Γ ≤ (injects_into omegaTwo (bv_union T))ᶜ := by
    rw [← imp_bot, ← deduction]
    let Δ := Γ ⊓ injects_into omegaTwo (bv_union T)
    obtain ⟨f, Hf⟩ := ErdosOmegaTwoBounded.exists_union_selector T (Γ := Δ)
    have Hfound := ErdosSmallCodomainPigeonhole.omegaTwo_pigeonhole_of_small_codomain
      (inf_le_left.trans HCH) (Hf.trans inf_le_left) (inf_le_left.trans HT)
      (show Δ ≤ injects_into omegaTwo (bv_union T) from inf_le_right)
    change Δ ≤ ⊥
    apply (le_inf (le_refl Δ) Hfound).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro A
    let Θ := Δ ⊓ (A ∈ᴮ T ⊓ injects_into omegaTwo (fiber (bv_union T) f A))
    have HAsmall : Θ ≤ injects_into A omegaOne :=
      (le_inf (inf_le_left.trans (inf_le_left.trans (Hmembers.trans (iInf_le _ A))))
        (inf_le_right.trans inf_le_left)).trans bv_imp_elim
    have Hsub : Θ ≤ fiber (bv_union T) f A ⊆ᴮ A :=
      ErdosOmegaTwoBounded.union_selector_fiber_subset
        (inf_le_left.trans (Hf.trans inf_le_right))
    have Hbad : Θ ≤ injects_into omegaTwo omegaOne :=
      injects_into_trans (inf_le_right.trans inf_le_right)
        (injects_into_trans (injects_into_of_subset Hsub) HAsmall)
    exact bv_absurd _ Hbad omegaTwo_not_injects
  apply (le_inf (le_refl Γ)
    (ErdosPartialInjection.omegaTwo_cardinal_dichotomy (S := bv_union T) (Γ := Γ))).trans
  rw [inf_sup_left]
  exact sup_le inf_le_right
    ((bv_absurd _ inf_le_right (inf_le_left.trans Hnot)).trans bot_le)

/-- The actual union of a small internal indexed family is small when each
guarded value is small. The arbitrary base may in particular be omega-two. -/
theorem indexed_union_injects_omegaOne {Q κ F : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HF : Γ ≤ is_function Q (bv_powerset κ) F)
    (HQ : Γ ≤ injects_into Q omegaOne) (Hvalues : Γ ≤ smallValues Q F) :
    Γ ≤ injects_into (bv_union (image Q (bv_powerset κ) F)) omegaOne :=
  union_injects_omegaOne HCH
    (ErdosCountableImage.image_injects_into_ordinal
      (is_func'_of_is_function HF) HQ omegaOne_Ord)
    (smallValues_image Hvalues)

/-- An arbitrary name in the indexed union has an actual internal index
and an actual graph value containing it, at the same Boolean condition. -/
theorem exists_indexed_union_witness {Q K F x : bSet 𝔹} {Γ : 𝔹}
    (Hx : Γ ≤ x ∈ᴮ bv_union (image Q K F)) :
    ∃ q A : bSet 𝔹, Γ ≤ (q ∈ᴮ Q ⊓ pair q A ∈ᴮ F) ⊓ x ∈ᴮ A := by
  obtain ⟨A, HA⟩ := exists_convert (mem_bv_union_iff.mp Hx)
    (B_ext_inf B_ext_mem_left B_ext_mem_right)
  obtain ⟨q, Hq⟩ := exists_convert ((mem_image_iff.mp (HA.trans inf_le_left)).2)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact ⟨q, A, le_inf Hq (HA.trans inf_le_right)⟩

/-- Every member of a guarded function value lies in the actual indexed
union; the actual function supplies the required codomain support. -/
theorem mem_indexed_union_of_value {Q K F q A x : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function Q K F) (Hq : Γ ≤ q ∈ᴮ Q)
    (HA : Γ ≤ pair q A ∈ᴮ F) (Hx : Γ ≤ x ∈ᴮ A) :
    Γ ≤ x ∈ᴮ bv_union (image Q K F) :=
  mem_bv_union_iff.mpr (le_iSup_of_le A
    (le_inf (mem_image HA Hq (mem_codomain_of_is_function HA HF)) Hx))

/-- The powerset codomain bounds the indexed union without any cardinal
assumption and even without functionality. -/
theorem indexed_union_subset {Q κ F : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ bv_union (image Q (bv_powerset κ) F) ⊆ᴮ κ := by
  apply ErdosInitialSegments.union_subset_of_members_subset
  apply le_iInf
  intro A
  rw [← deduction]
  exact mem_powerset_iff.mp (mem_of_mem_subset image_subset inf_le_right)

end bSet.ErdosSmallFamilyUnion
