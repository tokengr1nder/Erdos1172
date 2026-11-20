/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaLocalMatrix
public import Erdos1172.Part4ShioyaMatrixSurjection

@[expose] public section

/-! # Reading a local matrix from the dual Shioya generic string

Fix positions in a condition's string for the entries of a Boolean
matrix. When its point forces totality, single-valuedness and surjectivity,
the condition forces the corresponding graph read from the generic string
to be a surjective function between the two checked ordinals.
-/

set_option autoImplicit false
noncomputable section
open bSet Erdos1172PosetCompletion
open scoped Flypitch
universe u

namespace Erdos1172Shioya

variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)] [Nonempty (Condition κ θ)]
variable (γ δ : Ordinal.{u}) (w : Condition κ θ)
variable (slot : γ.ToType → δ.ToType → w.length.toOrd.val.ToType)

def genericMatrixGraph : bSet (Algebra κ θ) :=
  matrixGraph γ δ (fun i j => genericBit κ θ (ambientSlot w (slot i j)))

theorem genericMatrixGraph_pair (i : γ.ToType) (j : δ.ToType) :
    (pair (StringName.label i) (StringName.label j) ∈ᴮ genericMatrixGraph γ δ w slot) =
      genericBit κ θ (ambientSlot w (slot i j)) :=
  matrixGraph_pair γ δ _ i j

theorem genericMatrixGraph_surjection
    (hrow : ∀ i, condition w.point ≤ ⨆ j, w.bits (slot i j))
    (hcol : ∀ j, condition w.point ≤ ⨆ i, w.bits (slot i j))
    (hdisj : ∀ i j k, j ≠ k → condition w.point ⊓ (w.bits (slot i j) ⊓ w.bits (slot i k)) = ⊥) :
    condition w ≤ is_function (check (PSet.ordinalMk γ)) (check (PSet.ordinalMk δ)) (genericMatrixGraph γ δ w slot) ⊓
      is_surj (check (PSet.ordinalMk γ)) (check (PSet.ordinalMk δ)) (genericMatrixGraph γ δ w slot) :=
  matrixGraph_surjection γ δ _ (condition w)
    (fun i => condition_le_iSup_genericBit_of_local_cover w (slot i) (hrow i))
    (fun j => condition_le_iSup_genericBit_of_local_cover w (fun i => slot i j) (hcol j))
    (fun i j k hne => (condition_inf_genericBits_eq_bot_of_local_disjoint w
      (slot i j) (slot i k) (hdisj i j k hne)).le)

end Erdos1172Shioya
