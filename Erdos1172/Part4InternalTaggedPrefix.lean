/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalBoundedImageRecursion

@[expose] public section

/-!
# Stage tags preserve the actual ordered prefix graph

When the value at stage j is tagged by j, the image of a prefix is itself
the graph of the earlier stage-to-entry function. The proof uses arbitrary
internal names and keeps the same Boolean condition. Entries may repeat:
their stage tags retain every coordinate. No external enumeration or
successful-run condition is required.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosTaggedPrefix

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosBoundedImageRecursion

def taggingLaw (V Run : bSet 𝔹) : 𝔹 :=
  ⨅ j, ⨅ z, _root_.imp (pair j z ∈ᴮ Run) (⨆ x, x ∈ᴮ V ⊓ z =ᴮ pair j x)

def taggedPrefix (i θ V Run : bSet 𝔹) : bSet 𝔹 :=
  image i (prod θ V) Run

theorem taggingLaw_witness {V Run j z : bSet 𝔹} {Γ : 𝔹}
    (Htag : Γ ≤ taggingLaw V Run) (Hpair : Γ ≤ pair j z ∈ᴮ Run) :
    ∃ x : bSet 𝔹, Γ ≤ x ∈ᴮ V ⊓ z =ᴮ pair j x :=
  exists_convert
    ((le_inf (Htag.trans ((iInf_le _ j).trans (iInf_le _ z))) Hpair).trans bv_imp_elim)
    (B_ext_inf B_ext_mem_left (B_ext_pair_right B_ext_bv_eq_right))

/-- The graph-pair identity itself needs no inclusion of the prefix in
the full domain: actual function support already bounds its image values. -/
theorem mem_taggedPrefix_pair_iff {i θ V Run j x : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function θ (prod θ V) Run) (Htag : Γ ≤ taggingLaw V Run) :
    (Γ ≤ pair j x ∈ᴮ taggedPrefix i θ V Run) ↔
      Γ ≤ j ∈ᴮ i ∧ Γ ≤ pair j (pair j x) ∈ᴮ Run := by
  constructor
  · intro H
    obtain ⟨k, Hk⟩ := exists_convert (mem_image_iff.mp H).2
      (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    obtain ⟨v, Hv⟩ := taggingLaw_witness Htag (Hk.trans inf_le_right)
    have Hjk : Γ ≤ j =ᴮ k := eq_of_eq_pair_left' (Hv.trans inf_le_right)
    exact ⟨mem_congr (bv_symm Hjk) bv_refl (Hk.trans inf_le_left),
      mem_congr (pair_congr (bv_symm Hjk) bv_refl) bv_refl (Hk.trans inf_le_right)⟩
  · rintro ⟨Hji, Hpair⟩
    exact mem_image Hpair Hji (mem_codomain_of_is_function Hpair HF)

theorem taggedPrefix_subset {i θ V Run : bSet 𝔹} {Γ : 𝔹}
    (Htag : Γ ≤ taggingLaw V Run) : Γ ≤ taggedPrefix i θ V Run ⊆ᴮ prod i V := by
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction]
  obtain ⟨j, Hj⟩ := exists_convert ((mem_image_iff.mp
    (show Γ ⊓ z ∈ᴮ taggedPrefix i θ V Run ≤ z ∈ᴮ taggedPrefix i θ V Run from inf_le_right)).2)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  obtain ⟨x, Hx⟩ := taggingLaw_witness (inf_le_left.trans Htag) (Hj.trans inf_le_right)
  exact mem_prod_iff₂.mpr
    ⟨j, Hj.trans inf_le_left, x, Hx.trans inf_le_left, Hx.trans inf_le_right⟩

/-- The exact tagged image, not a newly chosen restriction graph, is an
actual function on the whole prefix. The entries need not be distinct. -/
theorem taggedPrefix_is_function {i θ V Run : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function θ (prod θ V) Run) (Htag : Γ ≤ taggingLaw V Run)
    (Hicut : Γ ≤ i ⊆ᴮ θ) : Γ ≤ is_function i V (taggedPrefix i θ V Run) := by
  refine le_inf (le_inf ?_ ?_) (taggedPrefix_subset Htag)
  · apply le_iInf
    intro j
    apply le_iInf
    intro k
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    rw [← deduction, ← deduction]
    let Δ := (Γ ⊓ (pair j x ∈ᴮ taggedPrefix i θ V Run ⊓
      pair k y ∈ᴮ taggedPrefix i θ V Run)) ⊓ j =ᴮ k
    have HΔ : Δ ≤ Γ := inf_le_left.trans inf_le_left
    have Hj := (mem_taggedPrefix_pair_iff (HΔ.trans HF) (HΔ.trans Htag)).mp
      (show Δ ≤ pair j x ∈ᴮ taggedPrefix i θ V Run from
        inf_le_left.trans (inf_le_right.trans inf_le_left))
    have Hk := (mem_taggedPrefix_pair_iff (HΔ.trans HF) (HΔ.trans Htag)).mp
      (show Δ ≤ pair k y ∈ᴮ taggedPrefix i θ V Run from
        inf_le_left.trans (inf_le_right.trans inf_le_right))
    exact eq_of_eq_pair_right' (eq_of_is_function_of_eq (HΔ.trans HF) inf_le_right Hj.2 Hk.2)
  · apply le_iInf
    intro j
    rw [← deduction]
    let Δ := Γ ⊓ j ∈ᴮ i
    have Hjθ : Δ ≤ j ∈ᴮ θ := mem_of_mem_subset (inf_le_left.trans Hicut) inf_le_right
    have Hzex : Δ ≤ ⨆ z, z ∈ᴮ prod θ V ⊓ pair j z ∈ᴮ Run :=
      (le_inf (inf_le_left.trans ((is_total_of_is_function HF).trans (iInf_le _ j))) Hjθ).trans
        bv_imp_elim
    obtain ⟨z, Hz⟩ := exists_convert Hzex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
    obtain ⟨x, Hx⟩ := taggingLaw_witness (inf_le_left.trans Htag) (Hz.trans inf_le_right)
    have Hpair : Δ ≤ pair j (pair j x) ∈ᴮ Run :=
      mem_congr (pair_congr bv_refl (Hx.trans inf_le_right)) bv_refl (Hz.trans inf_le_right)
    exact le_iSup_of_le x (le_inf (Hx.trans inf_le_left)
      ((mem_taggedPrefix_pair_iff (inf_le_left.trans HF) (inf_le_left.trans Htag)).mpr
        ⟨inf_le_right, Hpair⟩))

/-- A tagged recursion equation supplies the tagging law from the actual
product support. No independent boundedness or congruence assumption on
the next-entry term is needed for this implication. -/
theorem taggingLaw_of_imageRecLaw {θ V Run : bSet 𝔹}
    {nextEntry : bSet 𝔹 → bSet 𝔹 → bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_function θ (prod θ V) Run)
    (Hlaw : Γ ≤ imageRecLaw (prod θ V) (fun j T => pair j (nextEntry j T)) Run) :
    Γ ≤ taggingLaw V Run := by
  apply le_iInf
  intro j
  apply le_iInf
  intro z
  rw [← deduction]
  let Δ := Γ ⊓ pair j z ∈ᴮ Run
  have Hz : Δ ≤ z =ᴮ pair j (nextEntry j (image j (prod θ V) Run)) :=
    imageRecLaw_apply (inf_le_left.trans Hlaw) inf_le_right
  have Hvalue : Δ ≤ pair j (nextEntry j (image j (prod θ V) Run)) ∈ᴮ prod θ V :=
    mem_congr Hz bv_refl (mem_codomain_of_is_function inf_le_right (inf_le_left.trans HF))
  exact le_iSup_of_le (nextEntry j (image j (prod θ V) Run))
    (le_inf (mem_prod_iff.mp Hvalue).2 Hz)

end bSet.ErdosTaggedPrefix
