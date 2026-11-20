/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSparseLarge
public import Erdos1172.Part4InternalIndependentHomogeneous

@[expose] public section

/-!
An internal cardinal Dushnik--Miller dichotomy under CH, for arbitrary
Boolean-valued colorings and arbitrary omega-two-large ordinal subsets.
The countable clique is increasing. The omega-two-sized opposite-color
clique is an actual injection with homogeneous range; no increasing
enumeration of that range is claimed. This is not the omega-one-plus-omega
partition relation, a normal-dense-ideal model, or a consistency theorem.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosInternalDushnikMiller

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosPartition ErdosIndependentMaximal ErdosSparseReservoir

def omegaClique (color : Bool) (R S : bSet 𝔹) : 𝔹 :=
  ⨆ f, is_injective_function bSet.omega S f ⊓
    (increasingOn bSet.omega f ⊓ homogeneousUnion color R bSet.omega bSet.omega f f)

noncomputable def largeIndependent (color : Bool) (R S : bSet 𝔹) : 𝔹 :=
  ⨆ A, (A ⊆ᴮ S ⊓ independent color R A) ⊓ injects_into omegaTwo A

noncomputable def largeClique (color : Bool) (R S : bSet 𝔹) : 𝔹 :=
  ⨆ f, is_injective_function omegaTwo S f ⊓
    homogeneousUnion color R omegaTwo omegaTwo f f

theorem omega_clique_or_large_independent {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo S) :
    Γ ≤ omegaClique color R S ⊔ largeIndependent color R S := by
  have Hsplit := omega_clique_or_sparse_reservoir (color := color) (R := R) HCH HS Hlarge
  apply (le_inf (le_refl Γ) Hsplit).trans
  rw [inf_sup_left]
  apply sup_le
  · exact inf_le_right.trans le_sup_left
  · change Γ ⊓ (⨆ X, (X ⊆ᴮ S ⊓ injects_into omegaTwo X) ⊓
      sparseNeighborhoods color R X) ≤ _
    rw [inf_iSup_eq]
    apply iSup_le
    intro X
    let Δ := Γ ⊓ ((X ⊆ᴮ S ⊓ injects_into omegaTwo X) ⊓
      sparseNeighborhoods color R X)
    have HXS : Δ ≤ X ⊆ᴮ S := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have HA := ErdosSparseLarge.large_independent_value
      (inf_le_left.trans HCH)
      (show Δ ≤ injects_into omegaTwo X from
        inf_le_right.trans (inf_le_left.trans inf_le_right))
      (show Δ ≤ sparseNeighborhoods color R X from inf_le_right.trans inf_le_right)
    apply le_sup_of_le_right
    apply (le_inf (le_refl Δ) HA).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro A
    apply le_iSup_of_le A
    refine le_inf (le_inf ?_ (inf_le_right.trans (inf_le_left.trans inf_le_right)))
      (inf_le_right.trans inf_le_right)
    exact subset_trans' (inf_le_right.trans (inf_le_left.trans inf_le_left))
      (inf_le_left.trans HXS)

/-- Independence in one symmetric color produces a supported internal
injection whose entire range is homogeneous in the complementary color. -/
theorem largeIndependent_le_largeClique (color : Bool) (R S : bSet 𝔹) :
    largeIndependent color R S ≤ largeClique (!color) R S := by
  apply iSup_le
  intro A
  obtain ⟨f, Hf⟩ := ErdosIndependentHomogeneous.exists_homogeneous_injection
    (show (A ⊆ᴮ S ⊓ independent color R A) ⊓ injects_into omegaTwo A ≤ A ⊆ᴮ S from
      inf_le_left.trans inf_le_left)
    (show (A ⊆ᴮ S ⊓ independent color R A) ⊓ injects_into omegaTwo A ≤
      injects_into omegaTwo A from inf_le_right)
    (show (A ⊆ᴮ S ⊓ independent color R A) ⊓ injects_into omegaTwo A ≤
      independent color R A from inf_le_left.trans inf_le_right)
  exact le_iSup_of_le f Hf

/-- Full cardinal dichotomy: either an increasing omega-clique in the
specified color or an omega-two-sized clique in its complementary color. -/
theorem omega_two_cardinal_dushnik_miller {color : Bool} {R S : bSet 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ S ⊆ᴮ omegaTwo)
    (Hlarge : Γ ≤ injects_into omegaTwo S) :
    Γ ≤ omegaClique color R S ⊔ largeClique (!color) R S :=
  (omega_clique_or_large_independent HCH HS Hlarge).trans
    (sup_le_sup le_rfl (largeIndependent_le_largeClique color R S))

end bSet.ErdosInternalDushnikMiller
