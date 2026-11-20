/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Erdos1172.ForMathlib.SetTheory.Ordinal.DushnikMillerCountable

@[expose] public section

/-! The cofinality and club-tail lemmas used by the neighborhood closure arguments,
recovered from the earlier StationarySplitting source. No stationary-set
splitting theorem is assumed or supplied by this module. -/

open Cardinal Order

namespace Set

universe u
variable {V : Type u} [LinearOrder V]

theorem nonempty_of_aleph0_lt_cof (hcof : ℵ₀ < Order.cof V) : Nonempty V := by
  by_contra h
  have hcofinal : IsCofinal (∅ : Set V) := fun x => (h ⟨x⟩).elim
  have hle : Order.cof V ≤ 0 := by simpa using Order.cof_le hcofinal
  exact (not_le_of_gt hcof) (hle.trans (Cardinal.zero_le ℵ₀))

theorem exists_gt_of_aleph0_lt_cof (hcof : ℵ₀ < Order.cof V) (x : V) :
    ∃ y, x < y := by
  by_contra h
  push Not at h
  have hcofinal : IsCofinal ({x} : Set V) :=
    fun y => ⟨x, Set.mem_singleton x, h y⟩
  have hle := Order.cof_le hcofinal
  rw [Cardinal.mk_singleton] at hle
  exact (not_le_of_gt hcof) (hle.trans Cardinal.one_le_aleph0)

theorem isClub_Ioi_of_aleph0_lt_cof (hcof : ℵ₀ < Order.cof V) (a : V) :
    IsClub (Set.Ioi a) := by
  refine ⟨?_, ?_⟩
  · intro d hd hne _ top htop
    obtain ⟨x, hx⟩ := hne
    exact lt_of_lt_of_le (hd hx) (htop.1 hx)
  · intro x
    obtain ⟨y, hy⟩ := exists_gt_of_aleph0_lt_cof hcof (max a x)
    exact ⟨y, lt_of_le_of_lt (le_max_left a x) hy,
      (le_max_right a x).trans hy.le⟩

end Set
