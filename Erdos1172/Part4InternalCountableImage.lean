/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCHHartogs

@[expose] public section

/-!
# Images of arbitrary internally countable names

A functional image of a name injecting into an ordinal also injects into
that ordinal. A partial surjection is transported along the injection of
the source, then least preimages in the ordinal give the required injection.
The countable specialization uses the actual internal omega name. No
external enumeration, nonempty premise, or CH hypothesis is required.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableImage

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- The original functional relation surjects onto its bounded image. -/
theorem larger_than_image {X Y f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' X Y f) : Γ ≤ larger_than X (image X Y f) := by
  apply le_iSup_of_le X
  apply le_iSup_of_le f
  exact le_inf (le_inf subset_self (factor_image_is_func' Hf)) (surj_image Hf)

/-- Transport a partial surjection along an injection of its source.
This is the positive Boolean form of the existing composition theorem. -/
theorem larger_than_of_injects_into_of_larger_than {X K Y : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ injects_into X K) (HY : Γ ≤ larger_than X Y) :
    Γ ≤ larger_than K Y := by
  have Hbad : (larger_than K Y)ᶜ ⊓ Γ ≤ ⊥ := by
    have Hnot : (larger_than K Y)ᶜ ⊓ Γ ≤ (larger_than X Y)ᶜ :=
      bSet_lt_of_le_of_lt (inf_le_right.trans HX) inf_le_left
    exact bv_absurd _ (inf_le_right.trans HY) Hnot
  have Hresult : Γ ≤ ((larger_than K Y)ᶜ)ᶜ := le_neg_of_inf_eq_bot (bot_unique Hbad)
  simpa only [compl_compl] using Hresult

/-- Any functional image preserves an arbitrary internal ordinal bound. -/
theorem image_injects_into_ordinal {X Y K f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' X Y f) (HX : Γ ≤ injects_into X K)
    (HK : Γ ≤ Ord K) : Γ ≤ injects_into (image X Y f) K :=
  ErdosCHHartogs.injects_into_of_larger_than_ordinal HK
    (larger_than_of_injects_into_of_larger_than HX (larger_than_image Hf))

/-- A functional image of an internally countable name is internally
countable, even when the source has no externally countable presentation. -/
theorem image_countable {X Y f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' X Y f) (Hcount : Γ ≤ injects_into X bSet.omega) :
    Γ ≤ injects_into (image X Y f) bSet.omega :=
  image_injects_into_ordinal Hf Hcount Ord_omega

/-- The same conclusion for an actual function graph. -/
theorem image_countable_of_function {X Y f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_function X Y f) (Hcount : Γ ≤ injects_into X bSet.omega) :
    Γ ≤ injects_into (image X Y f) bSet.omega :=
  image_countable (is_func'_of_is_function Hf) Hcount

/-- An internally countable part of any domain has countable image. -/
theorem restricted_image_countable {T X Y f : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func' X Y f) (HT : Γ ≤ T ⊆ᴮ X)
    (Hcount : Γ ≤ injects_into T bSet.omega) :
    Γ ≤ injects_into (image T Y f) bSet.omega :=
  image_countable (is_func'_subset_of_is_func' Hf HT) Hcount

end bSet.ErdosCountableImage
