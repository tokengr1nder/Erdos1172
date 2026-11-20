/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalIncreasingEnumeration
public import Erdos1172.Part4InternalDushnikMiller
public import Erdos1172.Part4InternalCountableAbsorption

@[expose] public section

/-!
The increasing enumeration theorem upgrades the internal cardinal
Dushnik--Miller dichotomy to actual ordered homogeneous injections in
both branches. It also supplies increasing omega-one cores of positive
sets under countable absorption. This does not construct the separate
omega-one-plus-omega balanced block fusion or a GCH/ideal model.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosOrderedDushnikMiller

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIncreasingPartial ErdosIndependentMaximal

/-- Positive internal subsets of omega-one have actual increasing omega-one
cores. Countable absorption is an explicit premise, distinct from closure. -/
theorem positive_increasing_core {J A : bSet 𝔹} {Γ : 𝔹}
    (Habsorb : Γ ≤ ErdosIdeal.countableAbsorption omegaOne J)
    (HA : Γ ≤ ErdosIdeal.positive omegaOne J A) :
    ∃ f : bSet 𝔹, Γ ≤ is_injective_function omegaOne A f ⊓
      (increasingOn omegaOne f ⊓ rangeInitial omegaOne A f) :=
  exists_increasing_injection omegaOne_Ord (HA.trans inf_le_left) omegaOne_initial
    (ErdosIdeal.omegaOne_injects_positive Habsorb HA)

/-- Independence, initial cardinal size, and an ordinal upper bound give
an actual order-preserving homogeneous injection in the opposite color. -/
theorem exists_ordered_homogeneous_injection
    {color : Bool} {R θ κ A S : bSet 𝔹} {Γ : 𝔹}
    (Hκ : Γ ≤ Ord κ) (HAκ : Γ ≤ A ⊆ᴮ κ) (HAS : Γ ≤ A ⊆ᴮ S)
    (Hθ : Γ ≤ ErdosHartogs.initialOrdinal θ) (Hlarge : Γ ≤ injects_into θ A)
    (Hind : Γ ≤ independent color R A) :
    ∃ f : bSet 𝔹, Γ ≤ is_injective_function θ S f ⊓
      (increasingOn θ f ⊓ homogeneousUnion (!color) R θ θ f f) := by
  obtain ⟨f, Hf⟩ := exists_increasing_injection Hκ HAκ Hθ Hlarge
  exact ⟨f, le_inf
    (ErdosIndependentHomogeneous.is_injective_function_codomain_mono HAS
      (Hf.trans inf_le_left))
    (le_inf (Hf.trans (inf_le_right.trans inf_le_left))
      (ErdosIndependentHomogeneous.homogeneousUnion_of_independent Hind
        (Hf.trans (inf_le_left.trans inf_le_left))))⟩

noncomputable def orderedLargeClique (color : Bool) (R S : bSet 𝔹) : 𝔹 :=
  ⨆ f, is_injective_function omegaTwo S f ⊓
    (increasingOn omegaTwo f ⊓ homogeneousUnion color R omegaTwo omegaTwo f f)

theorem ordered_large_clique_of_independent
    {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹} (HS : Γ ≤ S ⊆ᴮ omegaTwo) :
    Γ ⊓ ErdosInternalDushnikMiller.largeIndependent color R S ≤
      orderedLargeClique (!color) R S := by
  change Γ ⊓ (⨆ A, (A ⊆ᴮ S ⊓ independent color R A) ⊓ injects_into omegaTwo A) ≤ _
  rw [inf_iSup_eq]
  apply iSup_le
  intro A
  let Δ := Γ ⊓ ((A ⊆ᴮ S ⊓ independent color R A) ⊓ injects_into omegaTwo A)
  have HAS : Δ ≤ A ⊆ᴮ S := inf_le_right.trans (inf_le_left.trans inf_le_left)
  obtain ⟨f, Hf⟩ := exists_ordered_homogeneous_injection omegaTwo_Ord
    (subset_trans' HAS (inf_le_left.trans HS)) HAS omegaTwo_initial
    (show Δ ≤ injects_into omegaTwo A from inf_le_right.trans inf_le_right)
    (show Δ ≤ independent color R A from inf_le_right.trans (inf_le_left.trans inf_le_right))
  exact le_iSup_of_le f Hf

/-- Both alternatives are now genuine increasing internal injections.
The Boolean disjunction does not assert a globally fixed external color. -/
theorem omega_two_ordered_dushnik_miller {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo S) :
    Γ ≤ ErdosInternalDushnikMiller.omegaClique color R S ⊔ orderedLargeClique (!color) R S := by
  apply (le_inf (le_refl Γ)
    (ErdosInternalDushnikMiller.omega_clique_or_large_independent HCH HS Hlarge)).trans
  rw [inf_sup_left]
  exact sup_le (inf_le_right.trans le_sup_left)
    ((ordered_large_clique_of_independent HS).trans le_sup_right)

theorem omega_two_ordered_dushnik_miller_univ {color : Bool} {R : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) :
    Γ ≤ ErdosInternalDushnikMiller.omegaClique color R omegaTwo ⊔
      orderedLargeClique (!color) R omegaTwo :=
  omega_two_ordered_dushnik_miller HCH subset_self injects_into_refl

end bSet.ErdosOrderedDushnikMiller
