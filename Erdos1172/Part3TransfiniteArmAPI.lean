/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CHAsymmetric

@[expose] public section

open Cardinal Ordinal Set

namespace Erdos1172Part3TransfiniteArmAPI

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3CHAsymmetric

/-- Any family of points of `ω₂` indexed by fewer than `ℵ₂` objects has
a strict upper bound still inside `ω₂`.  This is the regularity input
needed at limit stages of a transfinite arm construction. -/
theorem exists_strict_upper_bound_of_mk_lt_alephTwo
    {ι : Type} (f : ι → W2) (hι : #ι < ℵ_ 2) :
    ∃ m : W2, ∀ i, f i < m := by
  let bound : Ordinal := ⨆ i, (f i : Ordinal) + 1
  have hcof : #ι < (ω_ 2 : Ordinal.{0}).cof := by
    simpa only [← Cardinal.ord_aleph,
      show (2 : Ordinal.{0}) = 1 + 1 by norm_num,
      (Cardinal.isRegular_aleph_add_one 1).cof_ord] using hι
  have hbound : bound < (ω_ 2 : Ordinal.{0}) := by
    exact Ordinal.iSup_add_one_lt_of_lt_cof hcof
      (fun i ↦ (f i).toOrd.2)
  let m : W2 := Ordinal.ToType.mk ⟨bound, hbound⟩
  refine ⟨m, fun i ↦ ?_⟩
  rw [← Ordinal.ToType.mk.apply_symm_apply (f i)]
  apply (Ordinal.ToType.mk.lt_iff_lt).mpr
  change ((f i).toOrd : Ordinal) < bound
  exact Ordinal.lt_iSup_add_one (fun j ↦ (f j : Ordinal)) i

/-- Under CH and failure of the red Part 3 target, every tail of `ω₂`
contains a blue clique of exact type `ω₁ + 1`. -/
theorem exists_blue_omegaOne_add_one_above
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (m : W2) :
    ∃ arm : Set W2, arm ⊆ Set.Ioi m ∧
      blue.IsClique arm ∧ typeLT arm = ω_ 1 + 1 := by
  exact exists_blue_omegaOne_add_one_in_every_alephTwo_set
    hCH red blue hcompl hnoRed (mk_Ioi_omegaTwo_eq m)

/-- Limit-stage package: above every family of fewer than `ℵ₂` previous
points there is a fresh blue `ω₁ + 1` arm, provided the exact red target
has not already occurred. -/
theorem exists_blue_omegaOne_add_one_above_small_family
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    {ι : Type} (f : ι → W2) (hι : #ι < ℵ_ 2) :
    ∃ (m : W2) (arm : Set W2),
      (∀ i, f i < m) ∧ arm ⊆ Set.Ioi m ∧
      blue.IsClique arm ∧ typeLT arm = ω_ 1 + 1 := by
  obtain ⟨m, hm⟩ := exists_strict_upper_bound_of_mk_lt_alephTwo f hι
  obtain ⟨arm, harmTail, harmBlue, harmType⟩ :=
    exists_blue_omegaOne_add_one_above hCH red blue hcompl hnoRed m
  exact ⟨m, arm, hm, harmTail, harmBlue, harmType⟩

end Erdos1172Part3TransfiniteArmAPI
