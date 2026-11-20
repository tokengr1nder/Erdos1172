/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerOperations
public import Erdos1172.Part4BooleanUltrapowerConstants
public import Erdos1172.Part4BooleanFactorPoset
public import Erdos1172.Part4InternalOmegaOneCountablyBounded
public import Erdos1172.Part4InternalIdealNormality

@[expose] public section

/-! # Countable families in the hereditary Boolean ultrapower

At a condition witnessing an injection of a family into ω, fullness
chooses a potential member for each numeral. Every member of the family
locally equals one of these witnesses. Countable completeness transfers
this cover to arbitrary represented children, and expansion of membership
then covers even mixed target members. This yields countable closure of
the seed kernel for the complete embedding of constants.
-/

set_option autoImplicit false
noncomputable section

open Filter bSet Lattice
open scoped Flypitch

universe u

namespace Erdos1172BooleanUltrapower

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- A single ambient injection supplies a fixed countable sequence of
names. Their validity may vary from one Boolean piece to another. -/
theorem exists_countable_member_cover (F : bSet B) (Γ : B) (hcnt : Γ ≤ injects_into F omega) :
    ∃ x : ULift.{u} ℕ → bSet B, ∀ z : bSet B,
      Γ ⊓ (z ∈ᴮ F) ≤ ⨆ n, (x n ∈ᴮ F) ⊓ (z =ᴮ x n) := by
  classical
  have hext : B_ext (fun g : bSet B => is_injective_function F omega g) := by
    apply B_ext_inf B_ext_is_function_right
    unfold is_inj
    exact B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ => B_ext_iInf (h := fun _ =>
      B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_inf
        (B_ext_inf B_ext_mem_right B_ext_mem_right) B_ext_const) (h₂ := B_ext_const)))))
  obtain ⟨g, hg⟩ := exists_convert (injection_into_of_injects_into hcnt) hext
  let pred (n : ULift.{u} ℕ) (v : bSet B) : B := v ∈ᴮ F ⊓ pair v (of_nat n.down) ∈ᴮ g
  have hm (n : ULift.{u} ℕ) : ∃ v : bSet B, (⨆ z, pred n z) = pred n v :=
    maximum_principle _ (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
  choose x hx using hm
  refine ⟨x, ?_⟩
  intro z
  let d := Γ ⊓ (z ∈ᴮ F)
  have ht : d ≤ ⨆ v : bSet B, v ∈ᴮ omega ⊓ pair z v ∈ᴮ g := by
    have htotal := (is_func'_of_is_injective_function hg).trans inf_le_right
    exact (le_inf (inf_le_left.trans (htotal.trans (iInf_le _ z))) inf_le_right).trans bv_imp_elim
  rw [← bounded_exists (h_congr := B_ext_pair_mem_right)] at ht
  change d ≤ ⨆ n : ULift.{u} ℕ, ⊤ ⊓ pair z (of_nat n.down) ∈ᴮ g at ht
  simp only [top_inf_eq] at ht
  apply (le_inf (le_refl d) ht).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro n
  let p := d ⊓ (pair z (of_nat n.down) ∈ᴮ g)
  have hpx : p ≤ pred n (x n) :=
    (le_inf (show p ≤ z ∈ᴮ F from inf_le_left.trans inf_le_right) inf_le_right).trans
      ((le_iSup (pred n) z).trans_eq (hx n))
  apply le_iSup_of_le n
  exact le_inf (hpx.trans inf_le_left)
    (eq_of_is_inj_of_eq ((show p ≤ Γ from inf_le_left.trans inf_le_left).trans
      (is_inj_of_is_injective_function hg)) bv_refl inf_le_right (hpx.trans inf_le_right))

end Erdos1172BooleanUltrapower
