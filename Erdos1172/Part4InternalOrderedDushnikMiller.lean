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

end bSet.ErdosOrderedDushnikMiller
