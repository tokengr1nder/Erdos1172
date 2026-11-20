/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerOperations
public import Erdos1172.Part4BooleanUltrapowerConstants
public import Erdos1172.Part4BooleanSeedKernelClosure

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

variable {I : Type u} (U : Ultrafilter I) [CountableInterFilter (U : Filter I)]

private theorem represented_countable_cover (Γ : B) (F : bSet B)
    (hcnt : Γ ≤ injects_into F omega) (Z : I → bSet B) :
    value U (fun i => Γ ⊓ (Z i ∈ᴮ F)) ≤ ⨆ v : bSet B,
      constant U (v ∈ᴮ F) ⊓ (hereditary U Z =ᴮ hereditary U (fun _ => v)) := by
  obtain ⟨x, hx⟩ := exists_countable_member_cover F Γ hcnt
  have hcard : Cardinal.mk (ULift.{u} ℕ) < Cardinal.aleph 1 := by simp
  apply (show value U (fun i => Γ ⊓ (Z i ∈ᴮ F)) ≤
    value U (fun i => ⨆ n, (x n ∈ᴮ F) ⊓ (Z i =ᴮ x n)) from
      (value_le_value_iff U).mpr (Eventually.of_forall fun i => hx (Z i))).trans
  rw [value_small_iSup U (Cardinal.aleph 1) hcard (fun i n => (x n ∈ᴮ F) ⊓ (Z i =ᴮ x n))]
  apply iSup_le
  intro n
  apply le_iSup_of_le (x n)
  rw [value_inf, value_name_eq U Z (fun _ => x n)]
  exact le_rfl

/-- All members of the lifted countable family, including arbitrary mixed
target names, are locally represented by diagonal images of actual members. -/
theorem hereditary_countable_cover (Γ : B) (F : bSet B) (y : bSet (Algebra U B)) :
    constant U (Γ ⊓ injects_into F omega) ⊓ (y ∈ᴮ hereditary U (fun _ => F)) ≤
      ⨆ v : bSet B, constant U (v ∈ᴮ F) ⊓ (y =ᴮ hereditary U (fun _ => v)) := by
  let X := fun _ : I => F
  let δ := Γ ⊓ injects_into F omega
  rw [show hereditary U X = _ from liftName_eq U _ X, mem_unfold]
  change constant U δ ⊓ (⨆ a : Children U X, value U (weight U X a) ⊓
    (y =ᴮ hereditary U (child U X a))) ≤ _
  erw [inf_iSup_eq]
  apply iSup_le
  intro a
  let d := constant U δ ⊓ (value U (weight U X a) ⊓ (y =ᴮ hereditary U (child U X a)))
  have hweight : value U (weight U X a) ≤ value U (fun i => child U X a i ∈ᴮ F) := by
    apply (value_le_value_iff U).mpr
    filter_upwards [a.large] with i hi
    simpa only [child, weight, selected, dif_pos hi, X] using (mem_mk' F (a.pick ⟨i, hi⟩))
  have hd : d ≤ value U (fun i => δ ⊓ (child U X a i ∈ᴮ F)) := by
    rw [value_inf]
    exact le_inf inf_le_left ((inf_le_right.trans inf_le_left).trans hweight)
  have hc := hd.trans (represented_countable_cover U δ F inf_le_right (child U X a))
  apply (le_inf (le_refl d) hc).trans
  erw [inf_iSup_eq]
  apply iSup_le
  intro v
  apply le_iSup_of_le v
  exact le_inf (inf_le_right.trans inf_le_left)
    (bv_trans (inf_le_left.trans (show d ≤ y =ᴮ hereditary U (child U X a) from
      inf_le_right.trans inf_le_right)) (inf_le_right.trans inf_le_right))

theorem hereditary_seed_countableClosure (κ : Cardinal.{u})
    [CardinalInterFilter (U : Filter I) κ] (hcc : StrictCC B κ)
    (K : bSet B) (s : bSet (Algebra U B)) :
    (⊤ : B) ≤ ErdosIdeal.countableClosure (ErdosSeedKernel.seedKernelName
      (constantCompleteHom U κ hcc) (fun x => hereditary U (fun _ => x)) s K) := by
  apply ErdosSeedKernel.seedKernelName_countableClosure
    (constantCompleteHom U κ hcc) (fun x => hereditary U (fun _ => x)) s
    (fun x y => (value_name_eq U (fun _ => x) (fun _ => y)).le) K
  · exact fun F => le_top.trans (hereditary_union_subset U (fun _ => F))
  · exact hereditary_countable_cover U ⊤

end Erdos1172BooleanUltrapower
