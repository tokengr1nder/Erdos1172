/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Tactic.NormNum.Ordinal
public import Erdos1172.ForMathlib.SetTheory.Cardinal.ContinuumHypothesis
public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueExtension
public import Erdos1172.ForMathlib.SetTheory.Ordinal.DushnikMillerCountable

@[expose] public section

open Cardinal Ordinal Set Function

/-!
# Stationary `ω₁`-suprema in `ω₂`
-/

namespace ErdosRadoCHAsym

abbrev W1 : Type := (ω_ 1 : Ordinal.{0}).ToType
abbrev W2 : Type := (ω_ 2 : Ordinal.{0}).ToType

/-- A point which is the supremum of a strictly increasing `ω₁`-sequence. -/
def IsOmegaOneSup (top : W2) : Prop :=
  ∃ seq : W1 → W2, StrictMono seq ∧ IsLUB (Set.range seq) top

private theorem cof_omega_succ (n : Ordinal.{0}) :
    Order.cof (ω_ (n + 1)).ToType = ℵ_ (n + 1) := by simp_all

/-- The points which are `ω₁`-suprema form a stationary subset of `ω₂`. -/
theorem isStationary_isOmegaOneSup_omegaTwo :
    IsStationary {top : W2 | IsOmegaOneSup top} := by
  let _ : Nonempty W1 := by
    change Nonempty ((ω_ 1 : Ordinal.{0}).ToType); rw [← Cardinal.ord_aleph]
    exact Cardinal.nonempty_ord_toType (Cardinal.aleph0_pos.trans_le (Cardinal.aleph0_le_aleph 1)).ne'
  let _ : Nonempty W2 := by
    change Nonempty ((ω_ 2 : Ordinal.{0}).ToType); rw [← Cardinal.ord_aleph]
    exact Cardinal.nonempty_ord_toType (Cardinal.aleph0_pos.trans_le (Cardinal.aleph0_le_aleph 2)).ne'
  refine Set.isStationary_exists_strictMono_isLUB ?_
  have hcof : Order.cof W2 = ℵ_ 2 := by
    simpa [W2, show (1 : Ordinal.{0}) + 1 = 2 by norm_num] using cof_omega_succ 1
  simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, hcof]
  exact Cardinal.aleph_lt_aleph.mpr (by norm_num)

/-- A countable set below an `ω₁`-supremum has a strict upper bound below it. -/
theorem exists_strict_bound_of_countable_of_IsOmegaOneSup
    {top : W2} (htop : IsOmegaOneSup top) {seed : Set W2}
    (hseedCard : #seed ≤ ℵ₀) (hseedTop : ∀ y ∈ seed, y < top) :
    ∃ cutoff : W2, cutoff < top ∧ ∀ y ∈ seed, y < cutoff := by
  let _ : NoMaxOrder W1 := by
    change NoMaxOrder ((ω_ 1 : Ordinal.{0}).ToType); rw [← Cardinal.ord_aleph]
    exact Cardinal.noMaxOrder (Cardinal.aleph0_le_aleph 1)
  obtain ⟨seq, hseq, hlub⟩ := htop
  refine Set.exists_strict_bound_of_strictMono_isLUB hseq hlub ?_ hseedTop
  have hcof : Order.cof W1 = ℵ_ 1 := by
    simpa [W1, zero_add] using cof_omega_succ 0
  exact hseedCard.trans_lt (hcof ▸ Cardinal.aleph0_lt_aleph.mpr (by norm_num))

end ErdosRadoCHAsym
