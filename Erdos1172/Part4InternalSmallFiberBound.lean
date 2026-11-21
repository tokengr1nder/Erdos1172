/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationChoice
public import Erdos1172.Part4InternalFiberInjection
public import Erdos1172.Part4InternalPartialInjectionDomain

@[expose] public section

/-!
# Coherently choosing bounded injection codes for small fibers

Pointwise existence of internal injections is converted to a single
internal function selecting their graph codes. This uses the proved
bounded-relation choice theorem; no externally coherent witness family
is supplied as a hypothesis.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSmallFiberBound

open ErdosRelationGraph ErdosFiberInjection

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Coherence is obtained from the constructed internal choice function,
not from the arbitrary names witnessing the pointwise existential. -/
theorem exists_selector_of_pointwise {D C : bSet 𝔹}
    {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (Hleft : ∀ f, B_ext (fun i => P i f)) (Hright : ∀ i, B_ext (P i))
    (Hpointwise : Γ ≤ ⨅ i : bSet 𝔹, _root_.imp (i ∈ᴮ D) (⨆ f : bSet 𝔹, f ∈ᴮ C ⊓ P i f)) :
    ∃ s : bSet 𝔹, Γ ≤ is_function D C s ⊓
      ⨅ i : bSet 𝔹, ⨅ f : bSet 𝔹, _root_.imp (i ∈ᴮ D ⊓ pair i f ∈ᴮ s) (P i f) := by
  have Htotal : Γ ≤ is_total D C (relationGraph D C P) := by
    apply le_iInf
    intro i
    rw [← deduction]
    have Hex : Γ ⊓ i ∈ᴮ D ≤ ⨆ f : bSet 𝔹, f ∈ᴮ C ⊓ P i f :=
      (le_inf (inf_le_left.trans (Hpointwise.trans (iInf_le _ i))) inf_le_right).trans bv_imp_elim
    obtain ⟨f, Hf⟩ := exists_convert Hex (B_ext_inf B_ext_mem_left (Hright i))
    apply le_iSup_of_le f
    exact le_inf (Hf.trans inf_le_left)
      ((mem_relationGraph_iff Hleft Hright).mpr
        ⟨inf_le_right, Hf.trans inf_le_left, Hf.trans inf_le_right⟩)
  obtain ⟨s, Hs⟩ := ErdosRelationChoice.exists_function_subrelation Htotal
  refine ⟨s, le_inf (Hs.trans inf_le_left) ?_⟩
  apply le_iInf
  intro i
  apply le_iInf
  intro f
  rw [← deduction]
  have Hrel : Γ ⊓ (i ∈ᴮ D ⊓ pair i f ∈ᴮ s) ≤
      pair i f ∈ᴮ relationGraph D C P :=
    mem_of_mem_subset (inf_le_left.trans (Hs.trans inf_le_right)) (inf_le_right.trans inf_le_right)
  exact ((mem_relationGraph_iff Hleft Hright).mp Hrel).2.2

private theorem B_ext_inj : B_ext (is_inj : bSet 𝔹 → 𝔹) := by
  unfold is_inj
  exact B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_inf (B_ext_inf B_ext_mem_right B_ext_mem_right)
        B_ext_const) (h₂ := B_ext_const)))))

theorem B_ext_injective_code {A K : bSet 𝔹} :
    B_ext (fun f => is_injective_function A K f) :=
  B_ext_inf B_ext_is_function_right B_ext_inj

/-- Every graph used as a fiber-injection code has a fixed set-sized bound. -/
def injectionCodes (X K : bSet 𝔹) : bSet 𝔹 := bv_powerset (prod X K)

theorem mem_injectionCodes_of_injective_function {A X K f : bSet 𝔹} {Γ : 𝔹}
    (HA : Γ ≤ A ⊆ᴮ X) (Hf : Γ ≤ is_injective_function A K f) :
    Γ ≤ f ∈ᴮ injectionCodes X K :=
  mem_powerset_iff.mpr
    (subset_trans' (subset_prod_of_is_function (Hf.trans inf_le_left))
      (ErdosPartialInjection.prod_domain_mono HA))

theorem fiber_congr (X f : bSet 𝔹) : B_congr (fiber X f) := by
  intro i j Γ Hij
  apply mem_ext
  · apply le_iInf
    intro x
    rw [← deduction]
    have Hmem := mem_fiber_iff.mp (show Γ ⊓ x ∈ᴮ fiber X f i ≤ x ∈ᴮ fiber X f i from inf_le_right)
    exact mem_fiber_iff.mpr ⟨Hmem.1,
      bv_rw'' (ϕ := fun a => pair x a ∈ᴮ f) (inf_le_left.trans Hij)
        Hmem.2 B_ext_pair_mem_right⟩
  · apply le_iInf
    intro x
    rw [← deduction]
    have Hmem := mem_fiber_iff.mp (show Γ ⊓ x ∈ᴮ fiber X f j ≤ x ∈ᴮ fiber X f j from inf_le_right)
    exact mem_fiber_iff.mpr ⟨Hmem.1,
      bv_rw' (ϕ := fun a => pair x a ∈ᴮ f) (inf_le_left.trans Hij)
        (h_congr := B_ext_pair_mem_right) (H_new := Hmem.2)⟩

theorem B_ext_fiber_injective_code (X f K g : bSet 𝔹) :
    B_ext (fun i => is_injective_function (fiber X f i) K g) :=
  B_ext_term (ϕ := fun A => is_injective_function A K g)
    (t := fiber X f) B_ext_is_injective_function_left (fiber_congr X f)

/-- Pointwise small fibers admit one actual internal function selecting
supported injection graphs from the fixed powerset of `X × K`. -/
theorem exists_fiber_injection_selector {X I K f : bSet 𝔹} {Γ : 𝔹}
    (Hsmall : Γ ≤ ⨅ i : bSet 𝔹, _root_.imp (i ∈ᴮ I) (injects_into (fiber X f i) K)) :
    ∃ F : bSet 𝔹, Γ ≤ is_function I (injectionCodes X K) F ⊓ fiberInjectionFamily X I K f F := by
  apply exists_selector_of_pointwise
    (fun g => B_ext_fiber_injective_code X f K g)
    (fun _ => B_ext_injective_code)
  apply le_iInf
  intro i
  rw [← deduction]
  have Hinj : Γ ⊓ i ∈ᴮ I ≤ injects_into (fiber X f i) K :=
    (le_inf (inf_le_left.trans (Hsmall.trans (iInf_le _ i))) inf_le_right).trans bv_imp_elim
  obtain ⟨g, Hg⟩ := exists_convert (injection_into_of_injects_into Hinj) B_ext_injective_code
  exact le_iSup_of_le g (le_inf (mem_injectionCodes_of_injective_function fiber_subset Hg) Hg)

/-- A total map with pointwise K-small fibers gives an internal injection
of its domain into the product of its label set and K. The coherent
family of local injections is constructed, not assumed. -/
theorem injects_into_product_of_small_fibers {X I K f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function X I f)
    (Hsmall : Γ ≤ ⨅ i : bSet 𝔹, _root_.imp (i ∈ᴮ I) (injects_into (fiber X f i) K)) :
    Γ ≤ injects_into X (prod I K) := by
  obtain ⟨F, HF⟩ := exists_fiber_injection_selector Hsmall
  exact injects_into_product_of_fiber_injections Hf (HF.trans inf_le_left) (HF.trans inf_le_right)

end bSet.ErdosSmallFiberBound
