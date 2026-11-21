/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Cardinal.GCHConsequences1172
public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueExtension
public import Erdos1172.ForMathlib.SetTheory.Ordinal.DushnikMillerCountable

@[expose] public section

open Cardinal Ordinal Set Function

/-!
# Stationary `ω₂`-suprema in `ω₃`
-/

namespace ErdosRadoGCHAsym

abbrev W2 : Type := (ω_ 2 : Ordinal.{0}).ToType
abbrev W3 : Type := (ω_ 3 : Ordinal.{0}).ToType

/-- A point which is the supremum of a strictly increasing `ω₂`-sequence. -/
def IsOmegaTwoSup (top : W3) : Prop :=
  ∃ seq : W2 → W3, StrictMono seq ∧ IsLUB (Set.range seq) top

private theorem cof_omega_succ (n : Ordinal.{0}) :
    Order.cof (ω_ (n + 1)).ToType = ℵ_ (n + 1) := by simp_all

/-- The points which are `ω₂`-suprema form a stationary subset of `ω₃`. -/
theorem isStationary_isOmegaTwoSup_omegaThree :
    IsStationary {top : W3 | IsOmegaTwoSup top} := by
  let _ : Nonempty W2 := by
    change Nonempty ((ω_ 2 : Ordinal.{0}).ToType); rw [← Cardinal.ord_aleph]
    exact Cardinal.nonempty_ord_toType (Cardinal.aleph0_pos.trans_le (Cardinal.aleph0_le_aleph 2)).ne'
  let _ : Nonempty W3 := by
    change Nonempty ((ω_ 3 : Ordinal.{0}).ToType); rw [← Cardinal.ord_aleph]
    exact Cardinal.nonempty_ord_toType (Cardinal.aleph0_pos.trans_le (Cardinal.aleph0_le_aleph 3)).ne'
  refine Set.isStationary_exists_strictMono_isLUB ?_
  have hcof : Order.cof W3 = ℵ_ 3 := by
    simpa [W3, show (2 : Ordinal.{0}) + 1 = 3 by norm_num] using cof_omega_succ 2
  simp only [W2, Cardinal.mk_toType, Ordinal.card_omega, hcof]
  exact Cardinal.aleph_lt_aleph.mpr (by norm_num)

/-- A set of cardinality at most `ℵ₁` below an `ω₂`-supremum has a strict upper bound below it. -/
theorem exists_strict_bound_of_small_of_IsOmegaTwoSup
    {top : W3} (htop : IsOmegaTwoSup top) {seed : Set W3}
    (hseedCard : #seed ≤ ℵ_ 1) (hseedTop : ∀ y ∈ seed, y < top) :
    ∃ cutoff : W3, cutoff < top ∧ ∀ y ∈ seed, y < cutoff := by
  let _ : NoMaxOrder W2 := by
    change NoMaxOrder ((ω_ 2 : Ordinal.{0}).ToType); rw [← Cardinal.ord_aleph]
    exact Cardinal.noMaxOrder (Cardinal.aleph0_le_aleph 2)
  obtain ⟨seq, hseq, hlub⟩ := htop
  refine Set.exists_strict_bound_of_strictMono_isLUB hseq hlub ?_ hseedTop
  have hcof : Order.cof W2 = ℵ_ 2 := by
    simpa [W2, show (1 : Ordinal.{0}) + 1 = 2 by norm_num] using cof_omega_succ 1
  exact hseedCard.trans_lt (hcof ▸ Cardinal.aleph_lt_aleph.mpr (by norm_num))

end ErdosRadoGCHAsym
