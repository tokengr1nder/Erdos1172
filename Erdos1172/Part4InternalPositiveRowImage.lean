/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalFunctionRestriction
public import Erdos1172.Part4InternalIncreasingEnumeration
public import Erdos1172.Part4InternalCountableAbsorption

@[expose] public section

/-!
A positive internal set of row indices has an omega-one-sized row image.
Restricting an arbitrary injective row produces an actual supported graph;
the image then has an increasing omega-one enumeration. The row itself need
not be increasing. Positivity is used only for the size of the index set,
and no positivity assertion is made about its image inside omega-two.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPositiveRowImage

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosIdeal ErdosPartition

/-- The actual image of an injective restriction has full omega-one size
when its index set is positive and internally countable sets are absorbed. -/
theorem omegaOne_injects_row_image {J C h : bSet 𝔹} {Γ : 𝔹}
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (HC : Γ ≤ positive omegaOne J C)
    (Hh : Γ ≤ is_injective_function C omegaTwo h) :
    Γ ≤ injects_into omegaOne (image C omegaTwo h) :=
  injects_into_trans (omegaOne_injects_positive Habsorb HC)
    (injects_into_of_injection_into
      (le_iSup_of_le h (factor_image_is_injective_function Hh)))

/-- Restrict an actual injective row to positive indices and increasingly
enumerate its image. No increasingness of the given row, CH, normality,
or positivity of the row image is assumed. -/
theorem exists_positive_row_image {J C r : bSet 𝔹} {Γ : 𝔹}
    (Habsorb : Γ ≤ countableAbsorption omegaOne J)
    (HC : Γ ≤ positive omegaOne J C)
    (Hr : Γ ≤ is_injective_function omegaOne omegaTwo r) :
    ∃ h f : bSet 𝔹, Γ ≤ is_injective_function C omegaTwo h ⊓
      (h ⊆ᴮ r ⊓ (is_injective_function omegaOne (image C omegaTwo h) f ⊓
        increasingOn omegaOne f)) := by
  obtain ⟨h, Hh⟩ := ErdosFunctionRestriction.exists_restricted_function
    (HC.trans inf_le_left) (Hr.trans inf_le_left)
  have Hhr : Γ ≤ h ⊆ᴮ r := Hh.trans inf_le_right
  have Hhinj : Γ ≤ is_injective_function C omegaTwo h :=
    le_inf (Hh.trans inf_le_left)
      (ErdosFunctionRestriction.is_inj_of_subset Hhr (Hr.trans inf_le_right))
  have Hlarge : Γ ≤ injects_into omegaOne (image C omegaTwo h) :=
    omegaOne_injects_row_image Habsorb HC Hhinj
  have Himage : Γ ≤ image C omegaTwo h ⊆ᴮ omegaTwo := image_subset
  obtain ⟨f, Hf⟩ := ErdosIncreasingPartial.exists_increasing_injection
    omegaTwo_Ord Himage omegaOne_initial Hlarge
  exact ⟨h, f, le_inf Hhinj (le_inf Hhr
    (le_inf (Hf.trans inf_le_left) (Hf.trans (inf_le_right.trans inf_le_left))))⟩

end bSet.ErdosPositiveRowImage
