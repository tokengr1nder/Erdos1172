/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalPowersetPairCoding
public import Mathlib.Data.Nat.Pairing

@[expose] public section

/-!
# Actual real codes for partial real-valued omega graphs

A domain-marker stream records whether each row is defined. A separate
membership matrix records every natural-number bit of its real value.
Their interleaving is an actual internal subset of omega. Markers retain
the distinction between an absent row and a present row with empty value.
Local code equality reflects equality of supported functional graphs.
Arbitrary internal natural names are handled by Boolean-join distribution,
not by extracting a single external numeral at the original condition.
This module does not yet prove a countable-subset cardinality bound.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableRealMatrix

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosPowersetPairCoding

local notation "Pω" => bv_powerset (bSet.omega : bSet 𝔹)

def rowPresent (f : bSet 𝔹) (n : ℕ) : 𝔹 :=
  ⨆ r, pair (of_nat n) r ∈ᴮ f

def rowBit (f : bSet 𝔹) (n m : ℕ) : 𝔹 :=
  ⨆ r, pair (of_nat n) r ∈ᴮ f ⊓ (of_nat m : bSet 𝔹) ∈ᴮ r

def domainIndicator (f : bSet 𝔹) : (bSet.omega : bSet 𝔹).type → 𝔹 :=
  fun n => rowPresent f n.down

def matrixIndicator (f : bSet 𝔹) : (bSet.omega : bSet 𝔹).type → 𝔹 :=
  fun k => rowBit f (Nat.unpair k.down).1 (Nat.unpair k.down).2

def domainCode (f : bSet 𝔹) : bSet 𝔹 :=
  set_of_indicator (u := bSet.omega) (domainIndicator f)

def matrixCode (f : bSet 𝔹) : bSet 𝔹 :=
  set_of_indicator (u := bSet.omega) (matrixIndicator f)

def realGraphCode (f : bSet 𝔹) : bSet 𝔹 :=
  set_of_indicator (u := bSet.omega) (interleave (domainIndicator f) (matrixIndicator f))

theorem mem_domainCode (f : bSet 𝔹) (n : ℕ) :
    (of_nat n : bSet 𝔹) ∈ᴮ domainCode f = rowPresent f n :=
  mem_of_nat_indicator (domainIndicator f) n

theorem mem_matrixCode (f : bSet 𝔹) (n m : ℕ) :
    (of_nat (Nat.pair n m) : bSet 𝔹) ∈ᴮ matrixCode f = rowBit f n m := by
  rw [matrixCode, mem_of_nat_indicator]
  simp only [matrixIndicator, Nat.unpair_pair]

private theorem indicator_subset_omega (χ : (bSet.omega : bSet 𝔹).type → 𝔹)
    {Γ : 𝔹} : Γ ≤ set_of_indicator (u := bSet.omega) χ ⊆ᴮ bSet.omega := by
  apply set_of_indicator_subset
  intro n
  change χ n ≤ (⊤ : 𝔹)
  exact le_top

theorem realGraphCode_subset (f : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ realGraphCode f ⊆ᴮ bSet.omega := indicator_subset_omega _

theorem realGraphCode_mem (f : bSet 𝔹) {Γ : 𝔹} :
    Γ ≤ realGraphCode f ∈ᴮ Pω := mem_powerset_iff.mpr (realGraphCode_subset f)

theorem rowPresent_ext_graph (n : ℕ) :
    B_ext (fun f : bSet 𝔹 => rowPresent f n) :=
  B_ext_iSup (h := fun _ => B_ext_mem_right)

theorem rowBit_ext_graph (n m : ℕ) :
    B_ext (fun f : bSet 𝔹 => rowBit f n m) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)

private theorem indicator_congr
    (χ : bSet 𝔹 → (bSet.omega : bSet 𝔹).type → 𝔹)
    (Hχ : ∀ n, B_ext (fun f => χ f n)) :
    B_congr (fun f => set_of_indicator (u := bSet.omega) (χ f)) := by
  intro f g Γ H
  apply indicator_eq_iff.mpr
  constructor
  · intro n
    exact (le_inf (inf_le_left.trans H) inf_le_right).trans (Hχ n f g)
  · intro n
    exact (le_inf (inf_le_left.trans (bv_symm H)) inf_le_right).trans (Hχ n g f)

theorem domainCode_congr : B_congr (domainCode : bSet 𝔹 → bSet 𝔹) :=
  indicator_congr domainIndicator (fun n => rowPresent_ext_graph n.down)

theorem matrixCode_congr : B_congr (matrixCode : bSet 𝔹 → bSet 𝔹) :=
  indicator_congr matrixIndicator
    (fun n => rowBit_ext_graph (Nat.unpair n.down).1 (Nat.unpair n.down).2)

theorem realGraphCode_congr : B_congr (realGraphCode : bSet 𝔹 → bSet 𝔹) := by
  intro f g Γ H
  exact interleave_eq_iff.mpr ⟨domainCode_congr H, matrixCode_congr H⟩

/-- Numeral membership implications extend to every mixed internal
natural name by retaining and distributing the original context. -/
theorem real_subset_of_numeral_membership {r s : bSet 𝔹} {Γ : 𝔹}
    (Hr : Γ ≤ r ⊆ᴮ bSet.omega)
    (Hbits : ∀ n : ℕ, Γ ⊓ (of_nat n : bSet 𝔹) ∈ᴮ r ≤ (of_nat n : bSet 𝔹) ∈ᴮ s) :
    Γ ≤ r ⊆ᴮ s := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← deduction]
  let Δ := Γ ⊓ x ∈ᴮ r
  have Hxω : Δ ≤ x ∈ᴮ bSet.omega := mem_of_mem_subset (inf_le_left.trans Hr) inf_le_right
  rw [mem_unfold] at Hxω
  change Δ ≤ ⨆ n : ULift.{u} ℕ, (⊤ : 𝔹) ⊓ x =ᴮ of_nat n.down at Hxω
  simp only [top_inf_eq] at Hxω
  apply (le_inf (le_refl Δ) Hxω).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro n
  have Hnr : Δ ⊓ x =ᴮ of_nat n.down ≤ (of_nat n.down : bSet 𝔹) ∈ᴮ r :=
    mem_congr inf_le_right bv_refl (inf_le_left.trans inf_le_right)
  have Hns : Δ ⊓ x =ᴮ of_nat n.down ≤ (of_nat n.down : bSet 𝔹) ∈ᴮ s :=
    (le_inf (inf_le_left.trans inf_le_left) Hnr).trans (Hbits n.down)
  exact mem_congr (bv_symm inf_le_right) bv_refl Hns

theorem real_eq_of_numeral_membership {r s : bSet 𝔹} {Γ : 𝔹}
    (Hr : Γ ≤ r ⊆ᴮ bSet.omega) (Hs : Γ ≤ s ⊆ᴮ bSet.omega)
    (Hrs : ∀ n : ℕ, Γ ⊓ (of_nat n : bSet 𝔹) ∈ᴮ r ≤ (of_nat n : bSet 𝔹) ∈ᴮ s)
    (Hsr : ∀ n : ℕ, Γ ⊓ (of_nat n : bSet 𝔹) ∈ᴮ s ≤ (of_nat n : bSet 𝔹) ∈ᴮ r) :
    Γ ≤ r =ᴮ s :=
  subset_ext (real_subset_of_numeral_membership Hr Hrs)
    (real_subset_of_numeral_membership Hs Hsr)

theorem rowBit_of_pair {f r : bSet 𝔹} {n m : ℕ} {Γ : 𝔹}
    (Hrow : Γ ≤ pair (of_nat n) r ∈ᴮ f)
    (Hbit : Γ ≤ (of_nat m : bSet 𝔹) ∈ᴮ r) : Γ ≤ rowBit f n m :=
  le_iSup_of_le r (le_inf Hrow Hbit)

/-- Functionality identifies the unique row value; domain markers will
provide such a value even when its membership-bit stream is everywhere zero. -/
theorem mem_of_rowBit {f r : bSet 𝔹} {n m : ℕ} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func f) (Hrow : Γ ≤ pair (of_nat n) r ∈ᴮ f)
    (Hbit : Γ ≤ rowBit f n m) : Γ ≤ (of_nat m : bSet 𝔹) ∈ᴮ r := by
  apply (le_inf (le_refl Γ) Hbit).trans
  rw [show rowBit f n m = ⨆ s, pair (of_nat n) s ∈ᴮ f ⊓ (of_nat m : bSet 𝔹) ∈ᴮ s
    from rfl, inf_iSup_eq]
  apply iSup_le
  intro s
  have Hrs : Γ ⊓ (pair (of_nat n) s ∈ᴮ f ⊓ (of_nat m : bSet 𝔹) ∈ᴮ s) ≤ r =ᴮ s :=
    eq_of_is_func_of_eq (inf_le_left.trans Hfunc) bv_refl
      (inf_le_left.trans Hrow) (inf_le_right.trans inf_le_left)
  exact mem_congr bv_refl (bv_symm Hrs) (inf_le_right.trans inf_le_right)

/-- Equal marker and matrix codes recover every numeral-indexed row.
The marker equality, rather than a nonempty-real premise, supplies its
matching row in the second graph. -/
theorem numeral_row_mem_of_codes {f g r : bSet 𝔹} {n : ℕ} {Γ : 𝔹}
    (Hf : Γ ≤ is_func f) (Hfsub : Γ ≤ f ⊆ᴮ prod bSet.omega Pω)
    (Hg : Γ ≤ is_func g) (Hgsub : Γ ≤ g ⊆ᴮ prod bSet.omega Pω)
    (Hdomain : Γ ≤ domainCode f =ᴮ domainCode g)
    (Hmatrix : Γ ≤ matrixCode f =ᴮ matrixCode g)
    (Hrow : Γ ≤ pair (of_nat n) r ∈ᴮ f) : Γ ≤ pair (of_nat n) r ∈ᴮ g := by
  have Hpresent : Γ ≤ rowPresent g n := by
    have Hcode : Γ ≤ (of_nat n : bSet 𝔹) ∈ᴮ domainCode f := by
      rw [mem_domainCode]
      exact le_iSup_of_le r Hrow
    have Hcode' := mem_congr bv_refl Hdomain Hcode
    rw [mem_domainCode] at Hcode'
    exact Hcode'
  obtain ⟨s, Hsrow⟩ := exists_convert Hpresent B_ext_pair_mem_right
  have Hrω : Γ ≤ r ⊆ᴮ bSet.omega := mem_powerset_iff.mp
    (mem_prod_iff.mp (mem_of_mem_subset Hfsub Hrow)).2
  have Hsω : Γ ≤ s ⊆ᴮ bSet.omega := mem_powerset_iff.mp
    (mem_prod_iff.mp (mem_of_mem_subset Hgsub Hsrow)).2
  have Hrs : Γ ≤ r =ᴮ s := by
    apply real_eq_of_numeral_membership Hrω Hsω
    · intro m
      have Hbit : Γ ⊓ (of_nat m : bSet 𝔹) ∈ᴮ r ≤ rowBit f n m :=
        rowBit_of_pair (inf_le_left.trans Hrow) inf_le_right
      have Hcode : Γ ⊓ (of_nat m : bSet 𝔹) ∈ᴮ r ≤
          (of_nat (Nat.pair n m) : bSet 𝔹) ∈ᴮ matrixCode f := by
        rw [mem_matrixCode]
        exact Hbit
      have Hcode' := mem_congr bv_refl (inf_le_left.trans Hmatrix) Hcode
      rw [mem_matrixCode] at Hcode'
      exact mem_of_rowBit (inf_le_left.trans Hg) (inf_le_left.trans Hsrow) Hcode'
    · intro m
      have Hbit : Γ ⊓ (of_nat m : bSet 𝔹) ∈ᴮ s ≤ rowBit g n m :=
        rowBit_of_pair (inf_le_left.trans Hsrow) inf_le_right
      have Hcode : Γ ⊓ (of_nat m : bSet 𝔹) ∈ᴮ s ≤
          (of_nat (Nat.pair n m) : bSet 𝔹) ∈ᴮ matrixCode g := by
        rw [mem_matrixCode]
        exact Hbit
      have Hcode' := mem_congr bv_refl (inf_le_left.trans (bv_symm Hmatrix)) Hcode
      rw [mem_matrixCode] at Hcode'
      exact mem_of_rowBit (inf_le_left.trans Hf) (inf_le_left.trans Hrow) Hcode'
  exact mem_congr (pair_congr bv_refl (bv_symm Hrs)) bv_refl Hsrow

/-- The numeral-row statement extends to arbitrary graph members by
their supported product witnesses and a local numeral join. -/
theorem graph_subset_of_codes {f g : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func f) (Hfsub : Γ ≤ f ⊆ᴮ prod bSet.omega Pω)
    (Hg : Γ ≤ is_func g) (Hgsub : Γ ≤ g ⊆ᴮ prod bSet.omega Pω)
    (Hdomain : Γ ≤ domainCode f =ᴮ domainCode g)
    (Hmatrix : Γ ≤ matrixCode f =ᴮ matrixCode g) : Γ ≤ f ⊆ᴮ g := by
  rw [subset_unfold']
  apply le_iInf
  intro z
  rw [← deduction]
  let Δ := Γ ⊓ z ∈ᴮ f
  obtain ⟨i, Hi, r, _, Hz⟩ := mem_prod_iff₂.mp
    (mem_of_mem_subset (inf_le_left.trans Hfsub) (show Δ ≤ z ∈ᴮ f from inf_le_right))
  have Hrow : Δ ≤ pair i r ∈ᴮ f := mem_congr Hz bv_refl inf_le_right
  conv_rhs at Hi => rw [mem_unfold]
  change Δ ≤ ⨆ n : ULift.{u} ℕ, (⊤ : 𝔹) ⊓ i =ᴮ of_nat n.down at Hi
  simp only [top_inf_eq] at Hi
  apply (le_inf (le_refl Δ) Hi).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro n
  let Λ := Δ ⊓ i =ᴮ of_nat n.down
  have HΛ : Λ ≤ Γ := inf_le_left.trans inf_le_left
  have Hnrow : Λ ≤ pair (of_nat n.down) r ∈ᴮ f :=
    mem_congr (pair_congr inf_le_right bv_refl) bv_refl (inf_le_left.trans Hrow)
  have Hgrow : Λ ≤ pair (of_nat n.down) r ∈ᴮ g :=
    numeral_row_mem_of_codes (HΛ.trans Hf) (HΛ.trans Hfsub)
      (HΛ.trans Hg) (HΛ.trans Hgsub) (HΛ.trans Hdomain) (HΛ.trans Hmatrix) Hnrow
  have Hir : Λ ≤ pair i r ∈ᴮ g :=
    mem_congr (pair_congr (bv_symm inf_le_right) bv_refl) bv_refl Hgrow
  exact mem_congr (bv_symm (inf_le_left.trans Hz)) bv_refl Hir

theorem eq_of_domain_matrix_codes {f g : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func f) (Hfsub : Γ ≤ f ⊆ᴮ prod bSet.omega Pω)
    (Hg : Γ ≤ is_func g) (Hgsub : Γ ≤ g ⊆ᴮ prod bSet.omega Pω)
    (Hdomain : Γ ≤ domainCode f =ᴮ domainCode g)
    (Hmatrix : Γ ≤ matrixCode f =ᴮ matrixCode g) : Γ ≤ f =ᴮ g :=
  subset_ext (graph_subset_of_codes Hf Hfsub Hg Hgsub Hdomain Hmatrix)
    (graph_subset_of_codes Hg Hgsub Hf Hfsub (bv_symm Hdomain) (bv_symm Hmatrix))

/-- Equality of the single real code preserves and reflects graph
equality under the same arbitrary Boolean condition. -/
theorem realGraphCode_eq_iff {f g : bSet 𝔹} {Γ : 𝔹}
    (Hf : Γ ≤ is_func f) (Hfsub : Γ ≤ f ⊆ᴮ prod bSet.omega Pω)
    (Hg : Γ ≤ is_func g) (Hgsub : Γ ≤ g ⊆ᴮ prod bSet.omega Pω) :
    (Γ ≤ realGraphCode f =ᴮ realGraphCode g) ↔ Γ ≤ f =ᴮ g := by
  constructor
  · intro H
    have Hparts := interleave_eq_iff.mp H
    exact eq_of_domain_matrix_codes Hf Hfsub Hg Hgsub Hparts.1 Hparts.2
  · intro H
    exact realGraphCode_congr H

end bSet.ErdosCountableRealMatrix
