/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCardinalSquare
public import Erdos1172.Part4InternalSmallFiberBound

@[expose] public section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOmegaTwoPigeonhole

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosFiberInjection

/-- Under internal CH, a function from any internally omega-two-large domain
to omega-one has a fiber admitting an injection of the full internal omega-two. -/
theorem omegaTwo_pigeonhole_of_large_domain {X f : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (Hf : Γ ≤ is_function X omegaOne f)
    (Hlarge : Γ ≤ injects_into omegaTwo X) :
    Γ ≤ ⨆ i, (i ∈ᴮ omegaOne) ⊓ injects_into omegaTwo (fiber X f i) := by
  let T : 𝔹 := ⨆ i, (i ∈ᴮ omegaOne) ⊓ injects_into omegaTwo (fiber X f i)
  change Γ ≤ T
  rw [← compl_compl T, ← imp_bot, ← deduction]
  have Hsmall : Γ ⊓ Tᶜ ≤ ⨅ i, _root_.imp (i ∈ᴮ omegaOne)
      (injects_into (fiber X f i) omegaOne) := by
    apply le_iInf
    intro i
    rw [← deduction]
    let Δ := (Γ ⊓ Tᶜ) ⊓ i ∈ᴮ omegaOne
    apply (le_inf (le_refl Δ)
      (ErdosPartialInjection.omegaTwo_cardinal_dichotomy
        (S := fiber X f i) (Γ := Δ))).trans
    rw [inf_sup_left]
    apply sup_le
    · exact inf_le_right
    · have HT : Δ ⊓ injects_into omegaTwo (fiber X f i) ≤ T :=
        le_iSup_of_le i (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      exact (bv_absurd _ HT
        (inf_le_left.trans (inf_le_left.trans inf_le_right))).trans bot_le
  have Hbound : Γ ⊓ Tᶜ ≤ injects_into X (prod omegaOne omegaOne) :=
    ErdosSmallFiberBound.injects_into_product_of_small_fibers
      (inf_le_left.trans Hf) Hsmall
  exact bv_absurd _
    (injects_into_trans (inf_le_left.trans Hlarge) (injects_into_trans Hbound
      (ErdosCardinalSquare.omegaOne_square_injects (inf_le_left.trans HCH))))
    omegaTwo_not_injects

theorem omegaTwo_pigeonhole_of_is_function {f : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (Hf : Γ ≤ is_function omegaTwo omegaOne f) :
    Γ ≤ ⨆ i, (i ∈ᴮ omegaOne) ⊓ injects_into omegaTwo (fiber omegaTwo f i) :=
  omegaTwo_pigeonhole_of_large_domain HCH Hf injects_into_refl

theorem fiber_mono {X f g i : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ f ⊆ᴮ g) : Γ ≤ fiber X f i ⊆ᴮ fiber X g i := by
  rw [subset_unfold']
  apply le_iInf; intro x; rw [← deduction]
  have Hx := (ErdosRelationGraph.mem_comprehend_and B_ext_pair_mem_left).mp
    (show Γ ⊓ x ∈ᴮ fiber X f i ≤ x ∈ᴮ comprehend (fun x => pair x i ∈ᴮ f) X
      from inf_le_right)
  exact (ErdosRelationGraph.mem_comprehend_and B_ext_pair_mem_left).mpr
    ⟨Hx.1, mem_of_mem_subset (inf_le_left.trans Hsub) Hx.2⟩

/-- Extra unused graph entries are harmless: restrict to the supported
function, find its full-sized fiber, and include that fiber in the original. -/
theorem omegaTwo_pigeonhole {f : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (Hf : Γ ≤ is_func' omegaTwo omegaOne f) :
    Γ ≤ ⨆ i, (i ∈ᴮ omegaOne) ⊓ injects_into omegaTwo (fiber omegaTwo f i) := by
  have Hfound := omegaTwo_pigeonhole_of_is_function HCH
    (function_of_func'_is_function Hf)
  apply (le_inf (le_refl Γ) Hfound).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  refine le_inf (inf_le_right.trans inf_le_left) ?_
  exact injects_into_trans (inf_le_right.trans inf_le_right)
    (injects_into_of_subset (fiber_mono
      (inf_le_left.trans (function_of_func'_subset (H_is_func' := Hf)))))

end bSet.ErdosOmegaTwoPigeonhole
