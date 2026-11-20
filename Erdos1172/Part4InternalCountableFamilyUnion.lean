/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalOmegaTwoBounded
public import Erdos1172.Part4InternalCountableProduct
public import Erdos1172.Part4InternalMixedProductInjection
public import Erdos1172.Part4InternalCountableImage

@[expose] public section

/-!
# Countable internal unions of countable internal sets

An actual union-membership selector sends each point to a member of the
family containing it. Its fibers are countable. The proved bounded
fiber-injection choice theorem constructs their coherent injection codes,
giving an injection of the union into the family times omega. The actual
natural-number pairing injection finishes the proof.

All family members, indices, and conditions may be Boolean-mixed. No CH,
ideal closure, nonempty-family, external enumeration, or supplied coherent
choice of enumerations is assumed. Fullness also supplies an actual
injection graph at the original condition.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableFamilyUnion

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosFiberInjection ErdosSmallFiberBound ErdosOmegaTwoBounded
open ErdosCountableProduct ErdosCountableImage

/-- A countable family of internally countable sets has countable union.
The memberwise injections need not be given coherently. -/
theorem union_countable {T : bSet 𝔹} {Γ : 𝔹}
    (HT : Γ ≤ injects_into T bSet.omega)
    (Hmembers : Γ ≤ ⨅ A, _root_.imp (A ∈ᴮ T) (injects_into A bSet.omega)) :
    Γ ≤ injects_into (bv_union T) bSet.omega := by
  obtain ⟨f, Hf⟩ := exists_union_selector T (Γ := Γ)
  have Hfibers : Γ ≤ ⨅ A, _root_.imp (A ∈ᴮ T)
      (injects_into (fiber (bv_union T) f A) bSet.omega) := by
    apply le_iInf
    intro A
    rw [← deduction]
    have Hcount : Γ ⊓ A ∈ᴮ T ≤ injects_into A bSet.omega :=
      (le_inf (inf_le_left.trans (Hmembers.trans (iInf_le _ A))) inf_le_right).trans
        bv_imp_elim
    have Hsub : Γ ⊓ A ∈ᴮ T ≤ fiber (bv_union T) f A ⊆ᴮ A :=
      union_selector_fiber_subset (inf_le_left.trans (Hf.trans inf_le_right))
    exact injects_into_trans (injects_into_of_subset Hsub) Hcount
  have Hproduct : Γ ≤ injects_into (bv_union T) (prod T bSet.omega) :=
    injects_into_product_of_small_fibers (Hf.trans inf_le_left) Hfibers
  exact injects_into_trans Hproduct
    (injects_into_trans (ErdosMixedProductInjection.injects_into_prod HT injects_into_refl)
      omega_square_injects)

/-- The countability law is guarded by actual internal indices and
actual graph values. It imposes no external presentation on the family. -/
def countableValues (Q F : bSet 𝔹) : 𝔹 :=
  ⨅ q, ⨅ A, _root_.imp (q ∈ᴮ Q ⊓ pair q A ∈ᴮ F) (injects_into A bSet.omega)

theorem countableValues_apply {Q F q A : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ countableValues Q F) (Hq : Γ ≤ q ∈ᴮ Q)
    (HA : Γ ≤ pair q A ∈ᴮ F) : Γ ≤ injects_into A bSet.omega :=
  (le_inf (H.trans ((iInf_le _ q).trans (iInf_le _ A))) (le_inf Hq HA)).trans
    bv_imp_elim

/-- Every member of the actual bounded image inherits countability.
Functionality is not needed for this value-law transfer. -/
theorem countableValues_image {Q K F : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ countableValues Q F) :
    Γ ≤ ⨅ A, _root_.imp (A ∈ᴮ image Q K F) (injects_into A bSet.omega) := by
  apply le_iInf
  intro A
  rw [← deduction]
  obtain ⟨q, Hq⟩ := exists_convert ((mem_image_iff.mp
    (show Γ ⊓ A ∈ᴮ image Q K F ≤ A ∈ᴮ image Q K F from inf_le_right)).2)
    (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  exact countableValues_apply (inf_le_left.trans H)
    (Hq.trans inf_le_left) (Hq.trans inf_le_right)

/-- Union of a countable internal indexed family of countable values.
Weak total functionality suffices, so a full history graph may be used
on any supplied countable prefix without falsely restricting its support. -/
theorem indexed_union_countable {Q K F : bSet 𝔹} {Γ : 𝔹}
    (HF : Γ ≤ is_func' Q K F) (HQ : Γ ≤ injects_into Q bSet.omega)
    (Hvalues : Γ ≤ countableValues Q F) :
    Γ ≤ injects_into (bv_union (image Q K F)) bSet.omega :=
  union_countable (image_countable HF HQ) (countableValues_image Hvalues)

end bSet.ErdosCountableFamilyUnion
