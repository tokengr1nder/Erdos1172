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
  have Hsmall : Γ ⊓ Tᶜ ≤ ⨅ i, _root_.imp (i ∈ᴮ omegaOne) (injects_into (fiber X f i) omegaOne) := by
    apply le_iInf
    intro i
    rw [← deduction]
    let Δ := (Γ ⊓ Tᶜ) ⊓ i ∈ᴮ omegaOne
    apply (le_inf (le_refl Δ)
      (ErdosPartialInjection.omegaTwo_cardinal_dichotomy (S := fiber X f i) (Γ := Δ))).trans
    rw [inf_sup_left]
    apply sup_le
    · exact inf_le_right
    · have HT : Δ ⊓ injects_into omegaTwo (fiber X f i) ≤ T :=
        le_iSup_of_le i (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      exact (bv_absurd _ HT (inf_le_left.trans (inf_le_left.trans inf_le_right))).trans bot_le
  have Hbound : Γ ⊓ Tᶜ ≤ injects_into X (prod omegaOne omegaOne) :=
    ErdosSmallFiberBound.injects_into_product_of_small_fibers (inf_le_left.trans Hf) Hsmall
  exact bv_absurd _
    (injects_into_trans (inf_le_left.trans Hlarge) (injects_into_trans Hbound
      (ErdosCardinalSquare.omegaOne_square_injects (inf_le_left.trans HCH))))
    omegaTwo_not_injects

end bSet.ErdosOmegaTwoPigeonhole
