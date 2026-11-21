/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCardinalPreservation

@[expose] public section

/-!
# The checked upper ordinal remains uncountable

In the actual Boolean completion of the below-κ product, the checked ground
ordinal κ.ord does not inject into internal omega when κ is regular and
uncountable. The chain condition is already proved for this concrete algebra;
it is not an additional hypothesis here. All injection and surjection values
quantify over arbitrary internal graph names.

This does not identify the checked ordinal with internal omegaOne or assert
GCH, a normal ideal, or the final consistency construction.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172LevyCollapse

open bSet Erdos1172PosetCompletion

/-- The checked upper ordinal has an actual member at the top condition. -/
theorem forces_below_upper_exists_mem (κ : Cardinal.{u}) (Hκ : κ.IsRegular) :
    (⊤ : Completion (BelowCondition κ)) ≤ exists_mem (check (PSet.ordinalMk κ.ord)) := by
  obtain ⟨z, Hz⟩ := PSet.exists_mem_of_nonzero Hκ.ord_pos
  change (⊤ : Completion (BelowCondition κ)) ≤
    ⨆ x : bSet (Completion (BelowCondition κ)), x ∈ᴮ check (PSet.ordinalMk κ.ord)
  exact le_iSup_of_le (check z) (check_mem Hz)

/-- No internal graph surjects from omega onto the checked upper ordinal. -/
theorem below_omega_surjects_upper_eq_bot (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ) :
    (surjects_onto omega (check (PSet.ordinalMk κ.ord)) : Completion (BelowCondition κ)) = ⊥ := by
  exact below_small_domain_surjects_onto_eq_bot κ Hκ Hunc
    PSet.omega (PSet.ordinalMk κ.ord)
    (by simpa only [PSet.mk_omega_eq_mk_omega] using Hunc)
    (by simpa only [PSet.mk_type_mk_eq κ Hunc.le] using (le_rfl : κ ≤ κ))
    (PSet.ordinalMk_inj κ.ord)

/-- Uncountability is preserved for the checked upper ordinal, even allowing
arbitrary mixed internal injection names. -/
theorem below_upper_injects_omega_eq_bot (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ) :
    (injects_into (check (PSet.ordinalMk κ.ord)) omega : Completion (BelowCondition κ)) = ⊥ := by
  have Hsurj :
      (injects_into (check (PSet.ordinalMk κ.ord)) omega : Completion (BelowCondition κ)) ≤
      surjects_onto omega (check (PSet.ordinalMk κ.ord)) :=
    surjects_onto_of_injects_into' le_rfl (le_top.trans (forces_below_upper_exists_mem κ Hκ))
  rw [below_omega_surjects_upper_eq_bot κ Hκ Hunc] at Hsurj
  exact bot_unique Hsurj

theorem forces_below_upper_uncountable (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ) :
    (⊤ : Completion (BelowCondition κ)) ≤ (injects_into (check (PSet.ordinalMk κ.ord)) omega)ᶜ := by
  simpa only [below_upper_injects_omega_eq_bot κ Hκ Hunc, compl_bot] using
    (le_rfl : (⊤ : Completion (BelowCondition κ)) ≤ ⊤)

end Erdos1172LevyCollapse
