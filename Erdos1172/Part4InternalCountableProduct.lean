/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalProductInjection
public import Mathlib.Data.Nat.Pairing

@[expose] public section

/-!
# Actual countable-square injections

The numeral pairing map is lifted by the checked internal function
constructor. Its congruence and equality reflection are proved under
every Boolean condition on representation indices, so the resulting
graph handles arbitrary mixed internal natural arguments. No CH is used.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosCountableProduct

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

def pairIndex : (prod bSet.omega bSet.omega : bSet 𝔹).type →
    (bSet.omega : bSet 𝔹).type :=
  fun p => ⟨Nat.pair p.1.down p.2.down⟩

theorem pairIndex_ext (i j : (prod bSet.omega bSet.omega : bSet 𝔹).type)
    {Γ : 𝔹}
    (H : Γ ≤ (prod bSet.omega bSet.omega : bSet 𝔹).func i =ᴮ
      (prod bSet.omega bSet.omega : bSet 𝔹).func j) :
    Γ ≤ (bSet.omega : bSet 𝔹).func (pairIndex i) =ᴮ
      (bSet.omega : bSet 𝔹).func (pairIndex j) := by
  change Γ ≤ pair (of_nat i.1.down) (of_nat i.2.down) =ᴮ
    pair (of_nat j.1.down) (of_nat j.2.down) at H
  change Γ ≤ (of_nat (Nat.pair i.1.down i.2.down) : bSet 𝔹) =ᴮ
    of_nat (Nat.pair j.1.down j.2.down)
  by_cases h₁ : i.1.down = j.1.down
  · by_cases h₂ : i.2.down = j.2.down
    · rw [h₁, h₂]
      exact bv_refl
    · have Hbad := eq_of_eq_pair_right' H
      rw [of_nat_inj' h₂] at Hbad
      exact Hbad.trans bot_le
  · have Hbad := eq_of_eq_pair_left' H
    rw [of_nat_inj' h₁] at Hbad
    exact Hbad.trans bot_le

private theorem pairIndex_inj (i j : (prod bSet.omega bSet.omega : bSet 𝔹).type)
    {Γ : 𝔹}
    (H : Γ ≤ (bSet.omega : bSet 𝔹).func (pairIndex i) =ᴮ
      (bSet.omega : bSet 𝔹).func (pairIndex j)) :
    Γ ≤ (prod bSet.omega bSet.omega : bSet 𝔹).func i =ᴮ
      (prod bSet.omega bSet.omega : bSet 𝔹).func j := by
  change Γ ≤ (of_nat (Nat.pair i.1.down i.2.down) : bSet 𝔹) =ᴮ
    of_nat (Nat.pair j.1.down j.2.down) at H
  change Γ ≤ pair (of_nat i.1.down) (of_nat i.2.down) =ᴮ
    pair (of_nat j.1.down) (of_nat j.2.down)
  by_cases h : Nat.pair i.1.down i.2.down = Nat.pair j.1.down j.2.down
  · obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.mp h
    rw [h₁, h₂]
    exact bv_refl
  · rw [of_nat_inj' h] at H
    exact H.trans bot_le

def omegaPairCode : bSet 𝔹 :=
  functionMk' (x := prod bSet.omega bSet.omega) (y := bSet.omega)
    pairIndex (fun _ => ⊤) pairIndex_ext (fun _ {_} _ => ⟨le_top, le_top⟩)

theorem omegaPairCode_is_injective {Γ : 𝔹} :
    Γ ≤ is_injective_function (prod bSet.omega bSet.omega) bSet.omega
      (omegaPairCode : bSet 𝔹) := by
  unfold omegaPairCode
  exact le_inf (functionMk'_is_function _ _ _ _)
    (functionMk'_is_inj _ _ _ _ pairIndex_inj)

theorem omega_square_injects {Γ : 𝔹} :
    Γ ≤ injects_into (prod bSet.omega bSet.omega) (bSet.omega : bSet 𝔹) :=
  injects_into_of_injection_into
    (le_iSup_of_le omegaPairCode omegaPairCode_is_injective)

theorem countable_square {X : bSet 𝔹} {Γ : 𝔹}
    (Hcount : Γ ≤ injects_into X bSet.omega) :
    Γ ≤ injects_into (prod X X) bSet.omega :=
  injects_into_trans (ErdosProductInjection.injects_into_prod_self Hcount)
    omega_square_injects

end bSet.ErdosCountableProduct
