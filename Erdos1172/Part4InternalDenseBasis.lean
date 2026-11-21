/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalDenseBasisCore
public import Erdos1172.Part4InternalSmallCodomainPigeonhole

@[expose] public section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosDenseBasis

open ErdosIdeal ErdosOmegaTwo ErdosFiberInjection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- A large indexed family shares one positive dense basis value, modulo
small losses. The original basis index is only assumed omega-one-small.
No normality, ideal closure, distinct-value or nonempty-index premise is added. -/
theorem exists_large_common_basis {κ J S I F B : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹))
    (Hlarge : Γ ≤ injects_into omegaTwo S)
    (HF : Γ ≤ is_function S (bv_powerset κ) F)
    (HFpos : Γ ≤ positiveValues κ J S F)
    (HB : Γ ≤ is_function I (bv_powerset κ) B)
    (HBpos : Γ ≤ positiveValues κ J I B)
    (Hdense : Γ ≤ denseValues κ J I B)
    (HI : Γ ≤ injects_into I omegaOne) :
    Γ ≤ ⨆ A0, positive κ J A0 ⊓
      ⨆ U, ((U ⊆ᴮ S) ⊓ injects_into omegaTwo U) ⊓ commonLoss J F U A0 := by
  obtain ⟨g, Hg⟩ := exists_basis_selector HF HFpos Hdense
  have Hfound :=
    ErdosSmallCodomainPigeonhole.omegaTwo_pigeonhole_of_small_codomain
      HCH (Hg.trans inf_le_left) HI Hlarge
  apply (le_inf (le_refl Γ) Hfound).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  let U := fiber S g i
  let Δ := Γ ⊓ ((i ∈ᴮ I) ⊓ injects_into omegaTwo U)
  have Hi : Δ ≤ i ∈ᴮ I := inf_le_right.trans inf_le_left
  have Hbase : Δ ≤ ⨆ A0, (A0 ∈ᴮ bv_powerset κ) ⊓ pair i A0 ∈ᴮ B :=
    (le_inf (inf_le_left.trans ((is_total_of_is_function HB).trans (iInf_le _ i)))
      Hi).trans bv_imp_elim
  obtain ⟨A0, HA0⟩ := exists_convert Hbase (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  apply le_iSup_of_le A0
  refine le_inf (positiveValues_apply (inf_le_left.trans HBpos) Hi (HA0.trans inf_le_right)) ?_
  apply le_iSup_of_le U
  refine le_inf (le_inf fiber_subset (inf_le_right.trans inf_le_right)) ?_
  apply le_iInf; intro x
  apply le_iInf; intro A
  rw [← deduction]
  let Λ := Δ ⊓ ((x ∈ᴮ U) ⊓ pair x A ∈ᴮ F)
  have Hx := mem_fiber_iff.mp (show Λ ≤ x ∈ᴮ fiber S g i from inf_le_right.trans inf_le_left)
  have Hchoice : Λ ≤ basisChoice J F B x i :=
    (le_inf
      (inf_le_left.trans (inf_le_left.trans
        (Hg.trans (inf_le_right.trans ((iInf_le _ x).trans (iInf_le _ i))))))
      (le_inf Hx.1 Hx.2)).trans bv_imp_elim
  exact loss_of_basisChoice
    (inf_le_left.trans (inf_le_left.trans HF))
    (inf_le_left.trans (inf_le_left.trans HB))
    Hchoice (inf_le_right.trans inf_le_right)
    (inf_le_left.trans (HA0.trans inf_le_right))

end bSet.ErdosDenseBasis
