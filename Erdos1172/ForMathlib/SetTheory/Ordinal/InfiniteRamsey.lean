/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.Combinatorics.SimpleGraph.InfiniteRamsey
public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelation

@[expose] public section

/-!
# The countable ordinal Ramsey theorem

This file translates infinite Ramsey's theorem for graphs into the ordinal partition relation
`ω → (ω, ω)²`.
-/

open Cardinal

namespace Ordinal

universe u

/-- An infinite subset of a well-order of type `ω` still has order type `ω`. -/
theorem typeLT_eq_omega0_of_infinite {s : Set (ω : Ordinal.{u}).ToType} (hs : s.Infinite) :
    typeLT s = ω := by
  have hle : typeLT s ≤ ω := by
    simpa using Ordinal.type_set_le s
  apply hle.antisymm
  letI : Infinite s := hs.to_subtype
  exact le_of_not_gt fun hlt ↦ by
    have hcardlt : (typeLT s).card < ℵ₀ := Ordinal.card_lt_aleph0.mpr hlt
    have hinf : ℵ₀ ≤ #s := Cardinal.aleph0_le_mk s
    exact (not_lt_of_ge hinf) (by simpa using hcardlt)

/-- The countable infinite ordinal Ramsey theorem `ω → (ω, ω)²`. -/
theorem ordinalRamsey_omega0 : OrdinalRamsey (ω : Ordinal.{u}) ω ω := by
  intro red blue hcompl
  letI : Infinite (ω : Ordinal.{u}).ToType := by
    rw [← Cardinal.aleph0_le_mk_iff]
    simp
  rcases red.exists_infinite_clique_or_compl with
    ⟨s, hs, hred⟩ | ⟨s, hs, hblue⟩
  · exact Or.inl ⟨s, hred, typeLT_eq_omega0_of_infinite hs⟩
  · rw [hcompl.compl_eq] at hblue
    exact Or.inr ⟨s, hblue, typeLT_eq_omega0_of_infinite hs⟩

end Ordinal
