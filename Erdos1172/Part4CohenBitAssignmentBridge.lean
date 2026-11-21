/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4CohenReadingBridge
public import Erdos1172.Part4CohenGenericBits

@[expose] public section

/-!
# Ambient Boolean agreement from conditional Cohen assignments

A conditional pair assignment becomes an ambient bit bound by shrinking
the original condition's first-stage value, without changing its canonical
graph. The zero intersection is treated separately. Complementary binary
assignments then give actual Boolean agreement on the original cone.

No total coordinate-coverage, Hartogs, or independent decision-density
hypothesis is required by either bridge.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172CohenIteration

open bSet Erdos1172PosetCompletion

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- A pair assigned only on a first-stage Boolean piece gives the
corresponding ambient bit bound on that piece of the original cone. -/
theorem condition_inf_firstStageHom_le_bitValue
    {K a y : bSet B} {r : Conditions K} {b : B}
    (Hpair : r.value ⊓ b ≤ pair a y ∈ᴮ Erdos1172BooleanNameIteration.name r) :
    condition r ⊓ firstStageHom K b ≤ bitValue K a y := by
  classical
  have Hrvalue : condition r ≤ firstStageHom K r.value :=
    (condition_le_firstStageHom_iff K r r.value).mpr le_rfl
  have Hcap : condition r ⊓ firstStageHom K b ≤ firstStageHom K (r.value ⊓ b) := by
    change (condition r ⊓ firstStageHom K b).val ≤ (firstStageHom K (r.value ⊓ b)).val
    intro s Hs
    change s ∈ (condition r).val ∧ s ∈ (firstStageHom K b).val at Hs
    apply condition_le_iff.mp
    apply (condition_le_firstStageHom_iff K s (r.value ⊓ b)).mpr
    exact le_inf
      ((condition_le_firstStageHom_iff K s r.value).mp ((condition_le_iff.mpr Hs.1).trans Hrvalue))
      ((condition_le_firstStageHom_iff K s b).mp (condition_le_iff.mpr Hs.2))
  by_cases Hzero : r.value ⊓ b = ⊥
  · rw [Hzero, map_bot] at Hcap
    exact Hcap.trans bot_le
  · let s : Conditions K := Erdos1172BooleanNameIteration.shrink r (r.value ⊓ b) Hzero inf_le_left
    have Hcone : condition r ⊓ firstStageHom K (r.value ⊓ b) ≤ condition s :=
      condition_inf_firstStageHom_le_condition r s le_rfl subset_self
    have Hbit : condition s ≤ bitValue K a y := condition_le_bitValue (p := s) Hpair
    exact (le_inf inf_le_left Hcap).trans (Hcone.trans Hbit)

/-- Complementary local assignments identify the Cohen bit with the
embedded coefficient on the whole original completed condition. -/
theorem condition_binary_agreement
    {K a : bSet B} {r : Conditions K} {b : B}
    (H1 : r.value ⊓ b ≤ pair a (1 : bSet B) ∈ᴮ Erdos1172BooleanNameIteration.name r)
    (H0 : r.value ⊓ bᶜ ≤ pair a (0 : bSet B) ∈ᴮ Erdos1172BooleanNameIteration.name r) :
    condition r ≤
      (bitValue K a 1 ⊓ firstStageHom K b) ⊔ ((bitValue K a 1)ᶜ ⊓ (firstStageHom K b)ᶜ) := by
  have Hzero : bitValue K a 0 ≤ (bitValue K a 1)ᶜ :=
    le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr (bitValue_zero_inf_one_eq_bot K a).le)
  have Hone : condition r ⊓ firstStageHom K b ≤ bitValue K a 1 :=
    condition_inf_firstStageHom_le_bitValue H1
  have Hother : condition r ⊓ (firstStageHom K b)ᶜ ≤ (bitValue K a 1)ᶜ := by
    rw [← firstStageHom_compl K b]
    exact (condition_inf_firstStageHom_le_bitValue H0).trans Hzero
  calc
    condition r ≤ condition r ⊓
        (firstStageHom K b ⊔ (firstStageHom K b)ᶜ) :=
      le_inf le_rfl (by rw [sup_compl_eq_top]; exact le_top)
    _ = (condition r ⊓ firstStageHom K b) ⊔
        (condition r ⊓ (firstStageHom K b)ᶜ) := inf_sup_left _ _ _
    _ ≤ (bitValue K a 1 ⊓ firstStageHom K b) ⊔
        ((bitValue K a 1)ᶜ ⊓ (firstStageHom K b)ᶜ) :=
      sup_le_sup (le_inf Hone inf_le_right) (le_inf Hother inf_le_right)

end Erdos1172CohenIteration
