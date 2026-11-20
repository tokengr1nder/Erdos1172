/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaTwoPigeonhole

@[expose] public section

/-!
Internal omega-two pigeonhole for any codomain injecting into omega-one.
The original label is recovered from a member of the large composite fiber;
no nonemptiness assumption on the codomain or padding function is used.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSmallCodomainPigeonhole

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosFiberInjection

/-- An injection carries every inhabited source to an inhabited target,
at the same arbitrary Boolean context. -/
theorem exists_mem_of_injects_into {A B a : bSet 𝔹} {Γ : 𝔹}
    (HAB : Γ ≤ injects_into A B) (Ha : Γ ≤ a ∈ᴮ A) :
    ∃ b : bSet 𝔹, Γ ≤ b ∈ᴮ B := by
  obtain ⟨g, Hg⟩ := exists_convert (injection_into_of_injects_into HAB)
    ErdosSmallFiberBound.B_ext_injective_code
  have Hbex : Γ ≤ ⨆ b, b ∈ᴮ B ⊓ pair a b ∈ᴮ g :=
    (le_inf ((is_total_of_is_function (Hg.trans inf_le_left)).trans (iInf_le _ a))
      Ha).trans bv_imp_elim
  obtain ⟨b, Hb⟩ := exists_convert Hbex
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)
  exact ⟨b, Hb.trans inf_le_left⟩

/-- Injectivity of the codomain map pulls a composite fiber back into the
original fiber at any label mapping to its output. The context for the
inclusion can be smaller than, or independent of, the construction context. -/
theorem fiber_function_comp_subset {X I J f e i j : bSet 𝔹} {Γ Δ : 𝔹}
    (Hf : Γ ≤ is_function X I f) (He : Γ ≤ is_function I J e)
    (Hinj : Δ ≤ is_inj e) (Hij : Δ ≤ pair i j ∈ᴮ e) :
    Δ ≤ fiber X (function_comp Hf He) j ⊆ᴮ fiber X f i := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Θ := Δ ⊓ x ∈ᴮ fiber X (function_comp Hf He) j
  have Hx : Θ ≤ x ∈ᴮ fiber X (function_comp Hf He) j := inf_le_right
  have Hxparts := mem_fiber_iff.mp Hx
  have Hcomp := (mem_is_func'_comp_iff (is_func'_of_is_function Hf)
    (is_func'_of_is_function He)).mp Hxparts.2
  obtain ⟨i', Hi'⟩ := exists_convert Hcomp.2.2
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))
  have Hii : Θ ≤ i' =ᴮ i := eq_of_is_inj_of_eq (inf_le_left.trans Hinj)
    bv_refl (Hi'.trans (inf_le_right.trans inf_le_right)) (inf_le_left.trans Hij)
  exact mem_fiber_iff.mpr ⟨Hxparts.1,
    mem_congr (pair_congr bv_refl Hii) bv_refl
      (Hi'.trans (inf_le_right.trans inf_le_left))⟩

/-- Under internal CH, a function from an internally omega-two-large set
to any internally omega-one-small codomain has a full omega-two-sized fiber.
All sets, functions, and labels are arbitrary Boolean names. -/
theorem omegaTwo_pigeonhole_of_small_codomain {X I f : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (Hf : Γ ≤ is_function X I f)
    (HI : Γ ≤ injects_into I omegaOne) (HX : Γ ≤ injects_into omegaTwo X) :
    Γ ≤ ⨆ i, (i ∈ᴮ I) ⊓ injects_into omegaTwo (fiber X f i) := by
  obtain ⟨e, He⟩ := exists_convert (injection_into_of_injects_into HI)
    ErdosSmallFiberBound.B_ext_injective_code
  have Hef : Γ ≤ is_function I omegaOne e := He.trans inf_le_left
  let h := function_comp Hf Hef
  have Hh : Γ ≤ is_function X omegaOne h :=
    function_comp_is_function (H₁ := Hf) (H₂ := Hef)
  have Hfound := ErdosOmegaTwoPigeonhole.omegaTwo_pigeonhole_of_large_domain
    HCH Hh HX
  apply (le_inf (le_refl Γ) Hfound).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro j
  let Δ := Γ ⊓ (j ∈ᴮ omegaOne ⊓ injects_into omegaTwo (fiber X h j))
  have Hbig : Δ ≤ injects_into omegaTwo (fiber X h j) :=
    inf_le_right.trans inf_le_right
  obtain ⟨x, Hx⟩ := exists_mem_of_injects_into Hbig omegaOne_mem_omegaTwo
  have Hxparts := mem_fiber_iff.mp Hx
  have Hcomp := (mem_is_func'_comp_iff (is_func'_of_is_function Hf)
    (is_func'_of_is_function Hef)).mp Hxparts.2
  obtain ⟨i, Hi⟩ := exists_convert Hcomp.2.2
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))
  have Hpull : Δ ≤ fiber X h j ⊆ᴮ fiber X f i :=
    fiber_function_comp_subset Hf Hef (inf_le_left.trans (He.trans inf_le_right))
      (Hi.trans (inf_le_right.trans inf_le_right))
  exact le_iSup_of_le i (le_inf (Hi.trans inf_le_left)
    (injects_into_trans Hbig (injects_into_of_subset Hpull)))

end bSet.ErdosSmallCodomainPigeonhole
