/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenGenericBits
public import Erdos1172.Part4GeneratedSubsetName

@[expose] public section

/-!
# The subset name obtained from actual second-stage Cohen bit values

The coefficients are the assignment weights of the constructed iteration,
not weights supplied by an assumed generic subset. The name is supported on
a ground check set. For inequivalent ground children its membership values
are exactly those coefficients, and actual zero/one decisions force the
corresponding nonmembership/membership statements.

The membership-generated complete subalgebra contains an actual localized
name whose transport recovers the subset at top. This is complete generation,
not a density-cardinality, quotient-distributivity, preservation, or ideal
claim. For an arbitrary ground set no claim is made that all its children
belong to the first-stage internal omega-one or have total binary coverage.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet Erdos1172CompleteSubalgebra

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- An actual subset name with the constructed second-stage one-bit weights. -/
def subsetName (A : PSet.{u}) : bSet (omegaOneAlgebra B) :=
  .mk A.Type (fun i => check (A.Func i))
    (fun i => bitValue (ErdosOmegaTwo.omegaOne : bSet B)
      (check (A.Func i)) (1 : bSet B))

theorem subsetName_subset (A : PSet.{u}) :
    (⊤ : omegaOneAlgebra B) ≤ subsetName (B := B) A ⊆ᴮ check A := by
  rw [check_unfold, subset_unfold]
  apply le_iInf
  intro i
  change (⊤ : omegaOneAlgebra B) ≤ _root_.imp
    (bitValue (ErdosOmegaTwo.omegaOne : bSet B) (check (A.Func i)) (1 : bSet B))
    (check (A.Func i) ∈ᴮ .mk A.Type
      (fun j => check (A.Func j)) (fun _ => ⊤))
  rw [← deduction]
  exact le_top.trans (mem_mk' (check'' (fun j => check (A.Func j))) i)

/-- Separation of the ground children makes the membership sum diagonal. -/
theorem subsetName_member_eq_bitValue {A : PSet.{u}}
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    (i : A.Type) :
    (check (A.Func i) : bSet (omegaOneAlgebra B)) ∈ᴮ subsetName (B := B) A =
      bitValue (ErdosOmegaTwo.omegaOne : bSet B) (check (A.Func i)) (1 : bSet B) := by
  classical
  rw [mem_unfold]
  change (⨆ j : A.Type,
    bitValue (ErdosOmegaTwo.omegaOne : bSet B) (check (A.Func j)) (1 : bSet B) ⊓
      ((check (A.Func i) : bSet (omegaOneAlgebra B)) =ᴮ check (A.Func j))) = _
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases hij : i = j
    · subst j
      rw [bv_eq_refl]
      exact inf_le_left
    · rw [check_bv_eq_bot_of_not_equiv (Hsep i j hij)]
      exact inf_le_right.trans bot_le
  · apply le_iSup_of_le i
    rw [bv_eq_refl]
    exact le_inf le_rfl le_top

/-- The least complete subalgebra containing this actual name's membership values. -/
def generatedAlgebra (A : PSet.{u}) : CompleteSubalgebra (omegaOneAlgebra B) :=
  ErdosGeneratedSubset.nameAlgebra A (subsetName (B := B) A)

/-- A name over the smaller algebra, not merely the ambient subset name. -/
def generatedName (A : PSet.{u}) : bSet (generatedAlgebra (B := B) A) :=
  ErdosGeneratedSubset.localizedName A (subsetName (B := B) A)

theorem generatedName_subset (A : PSet.{u}) :
    (⊤ : generatedAlgebra (B := B) A) ≤ generatedName (B := B) A ⊆ᴮ check A :=
  ErdosGeneratedSubset.localizedName_subset A (subsetName (B := B) A)

theorem generatedName_recovers (A : PSet.{u}) :
    (⊤ : omegaOneAlgebra B) ≤ subsetName (B := B) A =ᴮ
      ErdosNameTransport.mapNames (inclusion (generatedAlgebra (B := B) A))
        (generatedName (B := B) A) :=
  ErdosGeneratedSubset.localizedName_recovers (subsetName_subset (B := B) A)

theorem generatedAlgebra_le_iff (A : PSet.{u})
    (S : CompleteSubalgebra (omegaOneAlgebra B)) :
    generatedAlgebra (B := B) A ≤ S ↔
      ∀ i : A.Type,
        ((check (A.Func i) : bSet (omegaOneAlgebra B)) ∈ᴮ subsetName (B := B) A) ∈ S :=
  ErdosGeneratedSubset.nameAlgebra_le_iff A (subsetName (B := B) A) S

/-- Under separation the actual assignment weights themselves are precisely
the generators needed for this complete subalgebra. -/
theorem generatedAlgebra_le_iff_bitValues {A : PSet.{u}}
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    (S : CompleteSubalgebra (omegaOneAlgebra B)) :
    generatedAlgebra (B := B) A ≤ S ↔
      ∀ i : A.Type,
        bitValue (ErdosOmegaTwo.omegaOne : bSet B) (check (A.Func i)) (1 : bSet B) ∈ S := by
  rw [generatedAlgebra_le_iff]
  constructor
  · intro H i
    rw [← subsetName_member_eq_bitValue Hsep i]
    exact H i
  · intro H i
    rw [subsetName_member_eq_bitValue Hsep i]
    exact H i

theorem bitValue_mem_generatedAlgebra {A : PSet.{u}}
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    (i : A.Type) :
    bitValue (ErdosOmegaTwo.omegaOne : bSet B) (check (A.Func i)) (1 : bSet B) ∈
      generatedAlgebra (B := B) A :=
  (generatedAlgebra_le_iff_bitValues Hsep (generatedAlgebra (B := B) A)).mp le_rfl i

end Erdos1172CohenIteration
