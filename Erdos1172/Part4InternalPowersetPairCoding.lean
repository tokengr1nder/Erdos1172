/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Flypitch4.BvmExtras
public import Mathlib.Logic.Equiv.Nat

@[expose] public section

/-!
Interleaving the Boolean membership values of two arbitrary internal subsets
of omega. All equality and injectivity statements are valid under an arbitrary
Boolean context; no top-equality lemma for indicators is localized by assumption.
-/

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosPowersetPairCoding

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

local notation "Pω" => bv_powerset (bSet.omega : bSet 𝔹)

/-- Exact Boolean membership, not just an equivalence at truth value top. -/
theorem mem_of_nat_indicator (χ : (bSet.omega : bSet 𝔹).type → 𝔹) (n : ℕ) :
    (of_nat n : bSet 𝔹) ∈ᴮ set_of_indicator (u := bSet.omega) χ = χ ⟨n⟩ := by
  rw [mem_unfold]
  change (⨆ i : ULift.{u} ℕ, χ i ⊓ (of_nat n : bSet 𝔹) =ᴮ of_nat i.down) = χ ⟨n⟩
  apply le_antisymm
  · apply iSup_le
    rintro ⟨k⟩
    by_cases h : n = k
    · subst k
      exact inf_le_left
    · rw [of_nat_inj' h, inf_bot_eq]
      exact bot_le
  · apply le_iSup_of_le ⟨n⟩
    simp only [bv_eq_refl, inf_top_eq]
    exact le_rfl

theorem indicator_subset_value (χ ψ : (bSet.omega : bSet 𝔹).type → 𝔹) :
    set_of_indicator (u := bSet.omega) χ ⊆ᴮ set_of_indicator ψ =
      ⨅ n : (bSet.omega : bSet 𝔹).type, χ n ⟹ ψ n := by
  rw [subset_unfold]
  change (⨅ n : ULift.{u} ℕ, χ n ⟹
    (of_nat n.down : bSet 𝔹) ∈ᴮ set_of_indicator (u := bSet.omega) ψ) = _
  apply iInf_congr
  intro n
  rw [mem_of_nat_indicator]

/-- Local inclusion is pointwise implication under precisely the same context. -/
theorem indicator_subset_iff {χ ψ : (bSet.omega : bSet 𝔹).type → 𝔹} {Γ : 𝔹} :
    Γ ≤ set_of_indicator (u := bSet.omega) χ ⊆ᴮ set_of_indicator ψ ↔ ∀ n, Γ ⊓ χ n ≤ ψ n := by
  rw [indicator_subset_value]
  constructor
  · intro H n
    rw [deduction]
    exact H.trans (iInf_le _ n)
  · intro H
    apply le_iInf; intro n; rw [← deduction]
    exact H n

theorem indicator_eq_iff {χ ψ : (bSet.omega : bSet 𝔹).type → 𝔹} {Γ : 𝔹} :
    Γ ≤ set_of_indicator (u := bSet.omega) χ =ᴮ set_of_indicator ψ ↔
      (∀ n, Γ ⊓ χ n ≤ ψ n) ∧ (∀ n, Γ ⊓ ψ n ≤ χ n) := by
  rw [eq_iff_subset_subset, le_inf_iff, indicator_subset_iff, indicator_subset_iff]

/-- Even and odd positions carry the two Boolean indicators. -/
def interleave (χ ψ : (bSet.omega : bSet 𝔹).type → 𝔹) :
    (bSet.omega : bSet 𝔹).type → 𝔹 := fun n =>
  match Equiv.natSumNatEquivNat.symm n.down with
  | Sum.inl k => χ ⟨k⟩
  | Sum.inr k => ψ ⟨k⟩

theorem interleave_left (χ ψ : (bSet.omega : bSet 𝔹).type → 𝔹) (n : ℕ) :
    interleave χ ψ ⟨Equiv.natSumNatEquivNat (Sum.inl n)⟩ = χ ⟨n⟩ := by
  simp only [interleave, Equiv.symm_apply_apply]

theorem interleave_right (χ ψ : (bSet.omega : bSet 𝔹).type → 𝔹) (n : ℕ) :
    interleave χ ψ ⟨Equiv.natSumNatEquivNat (Sum.inr n)⟩ = ψ ⟨n⟩ := by
  simp only [interleave, Equiv.symm_apply_apply]

theorem interleave_subset_of_subsets
    {χ₁ ψ₁ χ₂ ψ₂ : (bSet.omega : bSet 𝔹).type → 𝔹} {Γ : 𝔹}
    (Hχ : Γ ≤ set_of_indicator (u := bSet.omega) χ₁ ⊆ᴮ set_of_indicator χ₂)
    (Hψ : Γ ≤ set_of_indicator (u := bSet.omega) ψ₁ ⊆ᴮ set_of_indicator ψ₂) :
    Γ ≤ set_of_indicator (u := bSet.omega) (interleave χ₁ ψ₁) ⊆ᴮ
      set_of_indicator (interleave χ₂ ψ₂) := by
  apply indicator_subset_iff.mpr
  intro n
  cases h : Equiv.natSumNatEquivNat.symm n.down with
  | inl k =>
      simpa only [interleave, h] using (indicator_subset_iff.mp Hχ) ⟨k⟩
  | inr k =>
      simpa only [interleave, h] using (indicator_subset_iff.mp Hψ) ⟨k⟩

/-- The encoded equality both preserves and reflects the two local equalities. -/
theorem interleave_eq_iff
    {χ₁ ψ₁ χ₂ ψ₂ : (bSet.omega : bSet 𝔹).type → 𝔹} {Γ : 𝔹} :
    Γ ≤ set_of_indicator (u := bSet.omega) (interleave χ₁ ψ₁) =ᴮ
        set_of_indicator (interleave χ₂ ψ₂) ↔
      Γ ≤ set_of_indicator (u := bSet.omega) χ₁ =ᴮ set_of_indicator χ₂ ∧
      Γ ≤ set_of_indicator (u := bSet.omega) ψ₁ =ᴮ set_of_indicator ψ₂ := by
  constructor
  · intro H
    have Hpoint := indicator_eq_iff.mp H
    constructor
    · apply indicator_eq_iff.mpr
      constructor
      · rintro ⟨n⟩
        simpa only [interleave_left] using Hpoint.1 ⟨Equiv.natSumNatEquivNat (Sum.inl n)⟩
      · rintro ⟨n⟩
        simpa only [interleave_left] using Hpoint.2 ⟨Equiv.natSumNatEquivNat (Sum.inl n)⟩
    · apply indicator_eq_iff.mpr
      constructor
      · rintro ⟨n⟩
        simpa only [interleave_right] using Hpoint.1 ⟨Equiv.natSumNatEquivNat (Sum.inr n)⟩
      · rintro ⟨n⟩
        simpa only [interleave_right] using Hpoint.2 ⟨Equiv.natSumNatEquivNat (Sum.inr n)⟩
  · rintro ⟨Hχ, Hψ⟩
    rw [eq_iff_subset_subset] at Hχ Hψ ⊢
    exact le_inf
      (interleave_subset_of_subsets (Hχ.trans inf_le_left) (Hψ.trans inf_le_left))
      (interleave_subset_of_subsets (Hχ.trans inf_le_right) (Hψ.trans inf_le_right))

def pairCodeIndex : (prod Pω Pω).type → (Pω).type :=
  fun p => interleave p.1 p.2

theorem pairCodeIndex_ext (i j : (prod Pω Pω).type) {Γ : 𝔹}
    (H : Γ ≤ (prod Pω Pω).func i =ᴮ (prod Pω Pω).func j) :
    Γ ≤ (Pω).func (pairCodeIndex i) =ᴮ (Pω).func (pairCodeIndex j) := by
  change Γ ≤ set_of_indicator (u := bSet.omega) (interleave i.1 i.2) =ᴮ
    set_of_indicator (interleave j.1 j.2)
  exact interleave_eq_iff.mpr (pair_eq_pair_iff.mp H)

theorem pairCodeIndex_inj (i j : (prod Pω Pω).type) {Γ : 𝔹}
    (H : Γ ≤ (Pω).func (pairCodeIndex i) =ᴮ (Pω).func (pairCodeIndex j)) :
    Γ ≤ (prod Pω Pω).func i =ᴮ (prod Pω Pω).func j := by
  change Γ ≤ set_of_indicator (u := bSet.omega) (interleave i.1 i.2) =ᴮ
    set_of_indicator (interleave j.1 j.2) at H
  exact pair_eq_pair_iff.mpr (interleave_eq_iff.mp H)

theorem pairCodeIndex_mem (i : (prod Pω Pω).type) {Γ : 𝔹} : Γ ≤ (Pω).bval (pairCodeIndex i) := by
  change Γ ≤ set_of_indicator (u := bSet.omega) (pairCodeIndex i) ⊆ᴮ bSet.omega
  apply set_of_indicator_subset (x := bSet.omega)
  intro n
  change interleave i.1 i.2 n ≤ (⊤ : 𝔹)
  exact le_top

/-- The actual internal graph coding pairs of arbitrary subsets of omega. -/
noncomputable def powersetPairCode : bSet 𝔹 :=
  functionMk' (x := prod Pω Pω) (y := Pω) pairCodeIndex (fun _ => ⊤) pairCodeIndex_ext
    (fun i {_} _ => ⟨pairCodeIndex_mem i, le_top⟩)

theorem powersetPairCode_is_injective {Γ : 𝔹} :
    Γ ≤ is_injective_function (prod Pω Pω) Pω powersetPairCode := by
  unfold powersetPairCode
  exact le_inf (functionMk'_is_function _ _ _ _) (functionMk'_is_inj _ _ _ _ pairCodeIndex_inj)

/-- This is unconditional and quantifies over all internal powerset members. -/
theorem powerset_omega_square_injects {Γ : 𝔹} :
    Γ ≤ injects_into (prod Pω Pω) Pω :=
  injects_into_of_injection_into (le_iSup_of_le powersetPairCode powersetPairCode_is_injective)

end bSet.ErdosPowersetPairCoding
