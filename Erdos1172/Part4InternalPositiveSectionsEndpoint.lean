/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCenteredAttachment
public import Erdos1172.Part4InternalLargeTwoBlock

@[expose] public section

/-!
The local positive-forward-section endpoint. A real section function is
constructed, its large centered subfamily is selected, and the countable
clique alternative is attached to a positive common part of the row.
Both conclusions are exact omega-one-plus-omega witnesses. The theorem
retains its explicit ideal, CH, homogeneous-row, and section hypotheses;
it does not supply a model, a global block fusion, or normality.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPositiveSectionsEndpoint

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIdeal ErdosDenseBasis
open ErdosIndexedIntersection ErdosForwardSections

/-- Enlarging a codomain preserves a total functional relation without
discarding any of its original graph pairs. -/
theorem is_func'_codomain_mono {K U V f : bSet 𝔹} {Γ : 𝔹}
    (HUV : Γ ≤ U ⊆ᴮ V) (Hf : Γ ≤ is_func' K U f) :
    Γ ≤ is_func' K V f := by
  refine le_inf (Hf.trans inf_le_left) ?_
  apply le_iInf
  intro i
  rw [← deduction]
  have Htotal : Γ ⊓ i ∈ᴮ K ≤ ⨆ x, x ∈ᴮ U ⊓ pair i x ∈ᴮ f :=
    (le_inf (inf_le_left.trans ((Hf.trans inf_le_right).trans (iInf_le _ i)))
      inf_le_right).trans bv_imp_elim
  obtain ⟨x, Hx⟩ := exists_convert Htotal (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  exact le_iSup_of_le x (le_inf
    (mem_of_mem_subset (inf_le_left.trans HUV) (Hx.trans inf_le_left))
    (Hx.trans inf_le_right))

theorem twoBlockWitness_codomain_mono
    {color : Bool} {R A B U V f g : bSet 𝔹} {Γ : 𝔹}
    (HUV : Γ ≤ U ⊆ᴮ V) (H : Γ ≤ twoBlockWitness color R A B U f g) :
    Γ ≤ twoBlockWitness color R A B V f g :=
  le_inf
    (le_inf
      (is_func'_codomain_mono HUV (H.trans (inf_le_left.trans inf_le_left)))
      (is_func'_codomain_mono HUV (H.trans (inf_le_left.trans inf_le_right))))
    (H.trans inf_le_right)

theorem hasTwoBlock_codomain_mono
    {color : Bool} {R A B U V : bSet 𝔹} {Γ : 𝔹}
    (HUV : Γ ≤ U ⊆ᴮ V) (H : Γ ≤ hasTwoBlock color R A B U) :
    Γ ≤ hasTwoBlock color R A B V := by
  apply (le_inf (le_refl Γ) H).trans
  unfold hasTwoBlock
  rw [inf_iSup_eq]
  apply iSup_le
  intro f
  rw [inf_iSup_eq]
  apply iSup_le
  intro g
  exact le_iSup_of_le f (le_iSup_of_le g
    (twoBlockWitness_codomain_mono (inf_le_left.trans HUV) inf_le_right))

/-- A monochromatic omega-one row and an omega-two-large family of positive
forward sections produce an exact balanced target in one of the two colors.
The centered subfamily, the tail, and the positive common core are all
constructed. Normality and preassigned compatible masks are not assumed. -/
theorem target_of_large_positive_sections
    {color : Bool} {R J I B r S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (HJ : Γ ≤ isIdeal omegaOne J) (Hclosure : Γ ≤ countableClosure J)
    (HB : Γ ≤ is_function I (bv_powerset omegaOne) B)
    (HBpos : Γ ≤ positiveValues omegaOne J I B)
    (Hdense : Γ ≤ denseValues omegaOne J I B)
    (HI : Γ ≤ injects_into I omegaOne)
    (Hr : Γ ≤ is_injective_function omegaOne omegaTwo r)
    (Hrow : Γ ≤ homogeneousUnion color R omegaOne omegaOne r r)
    (HS : Γ ≤ S ⊆ᴮ omegaTwo) (Hlarge : Γ ≤ injects_into omegaTwo S)
    (Hpositive : Γ ≤ ⨅ y, _root_.imp (y ∈ᴮ S) (positive omegaOne J (forwardSection color R r y))) :
    Γ ≤ hasTwoBlock color R omegaOne bSet.omega omegaTwo ⊔
      hasTwoBlock (!color) R omegaOne bSet.omega omegaTwo := by
  obtain ⟨F, HF⟩ := exists_forwardSection_family color R r S (Γ := Γ)
  have Hfunction : Γ ≤ is_function S (bv_powerset omegaOne) F := HF.trans inf_le_left
  have Hsections : Γ ≤ sectionFamily color R r S F := HF.trans inf_le_right
  have HFpos : Γ ≤ positiveValues omegaOne J S F :=
    positiveValues_of_sectionFamily Hsections Hpositive
  have Hcenter : Γ ≤ countablyCenteredOn omegaOne J :=
    countablyCenteredOn_of_dense_basis HJ Hclosure HCH HB HBpos Hdense HI
  have Hselected : Γ ≤ ⨆ U, ((U ⊆ᴮ S) ⊓ injects_into omegaTwo U) ⊓
      positiveCountableIntersections omegaOne J F U :=
    (le_inf (Hcenter.trans ((iInf_le _ S).trans (iInf_le _ F)))
      (le_inf (le_inf HS Hlarge) (le_inf Hfunction HFpos))).trans bv_imp_elim
  apply (le_inf (le_refl Γ) Hselected).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro U
  let Δ := Γ ⊓ (((U ⊆ᴮ S) ⊓ injects_into omegaTwo U) ⊓
    positiveCountableIntersections omegaOne J F U)
  have HΔ : Δ ≤ Γ := inf_le_left
  have HUS : Δ ≤ U ⊆ᴮ S := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have HUlarge : Δ ≤ injects_into omegaTwo U := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have HUcenter : Δ ≤ positiveCountableIntersections omegaOne J F U :=
    inf_le_right.trans inf_le_right
  have HUtwo : Δ ≤ U ⊆ᴮ omegaTwo := subset_trans' HUS (HΔ.trans HS)
  have Hsplit := ErdosLargeTwoBlock.omega_clique_or_twoBlock (color := color) (R := R)
    (HΔ.trans HCH) HUtwo HUlarge
  change Δ ≤ _
  apply (le_inf (le_refl Δ) Hsplit).trans
  rw [inf_sup_left]
  apply sup_le
  · change Δ ⊓ (⨆ g, is_injective_function bSet.omega U g ⊓
      (increasingOn bSet.omega g ⊓ homogeneousUnion color R bSet.omega bSet.omega g g)) ≤ _
    rw [inf_iSup_eq]
    apply iSup_le
    intro g
    let Θ := Δ ⊓ (is_injective_function bSet.omega U g ⊓
      (increasingOn bSet.omega g ⊓ homogeneousUnion color R bSet.omega bSet.omega g g))
    have HΘ : Θ ≤ Γ := inf_le_left.trans HΔ
    have Htarget : Θ ≤ hasTwoBlock color R omegaOne bSet.omega omegaTwo :=
      ErdosCenteredAttachment.hasTwoBlock_of_centered_sections_and_clique
        (HΘ.trans Habsorb) (HΘ.trans Hr) (HΘ.trans Hrow) (HΘ.trans HS)
        (HΘ.trans Hfunction) (HΘ.trans Hsections)
        (inf_le_left.trans HUS) (inf_le_left.trans HUcenter)
        (inf_le_right.trans inf_le_left)
        (inf_le_right.trans (inf_le_right.trans inf_le_left))
        (inf_le_right.trans (inf_le_right.trans inf_le_right))
    exact Htarget.trans le_sup_left
  · exact (hasTwoBlock_codomain_mono (inf_le_left.trans HUtwo) inf_le_right).trans le_sup_right

end bSet.ErdosPositiveSectionsEndpoint
