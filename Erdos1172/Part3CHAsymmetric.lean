/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.ErdosRadoCHAsymmetric
public import Erdos1172.Part3FiniteStars

@[expose] public section

open Cardinal Ordinal Set

namespace Erdos1172Part3CHAsymmetric

open Erdos1172Part3Failure Erdos1172Part3FiniteStars

/-- Under CH, the classical asymmetric relation already gives the exact
Part 3 red target against the one-point-short blue target. -/
theorem red_target_or_blue_omegaOne_add_one (hCH : CH) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0}) RedTarget (ω_ 1 + 1) :=
  (ErdosRadoCHAsym.ordinalRamsey_omegaTwo_omegaTwo_omegaOne_add_one hCH).mono_red
    part3_red_target_lt_omegaTwo.le

/-- In the absence of the exact red target, every set of cardinality `ℵ₂`
contains a blue clique of type `ω₁ + 1`. -/
theorem exists_blue_omegaOne_add_one_in_every_alephTwo_set
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    {s : Set W2} (hs : #s = ℵ_ 2) :
    ∃ t : Set W2, t ⊆ s ∧ blue.IsClique t ∧ typeLT t = ω_ 1 + 1 := by
  have hstype : typeLT s = ω_ 2 := typeLT_eq_omegaTwo_of_mk_eq hs
  obtain ⟨t, htSub, htRed, htType⟩ | ⟨t, htSub, htBlue, htType⟩ :=
    OrdinalRamsey.on_set_of_type
      (red_target_or_blue_omegaOne_add_one hCH)
      red blue hcompl s hstype
  · exact (hnoRed ⟨t, htRed, htType⟩).elim
  · exact ⟨t, htSub, htBlue, htType⟩

/-- CH strengthens the finite Part 3 star obstruction: the later arm can
have type `ω₁ + 1`, not merely `ω + 1`. -/
theorem red_target_or_all_finite_by_omegaOne_add_one_bicolored_stars
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      ∀ n : ℕ, ∃ (centers : Finset W2) (arm : Set W2),
        centers.card = n ∧ (centers : Set W2) ⊆ base ∧
        blue.IsClique (centers : Set W2) ∧
        blue.IsClique arm ∧ typeLT arm = ω_ 1 + 1 ∧
        ∀ y ∈ centers, ∀ x ∈ arm, red.Adj y x := by
  by_cases hred : OrdinalRamsey.HasCliqueOfType red RedTarget
  · exact Or.inl hred
  · right
    obtain ⟨m, -, hfinite⟩ :=
      exists_arbitrarily_large_finite_star_reservoirs red blue hcompl
        hbase hbaseType hred hnoBlue
    intro n
    obtain ⟨centers, reservoir, hcard, hcentersBase, hcentersBlue,
      hreservoirCard, -, hstar⟩ := hfinite n
    obtain ⟨arm, harmSub, harmBlue, harmType⟩ :=
      exists_blue_omegaOne_add_one_in_every_alephTwo_set
        hCH red blue hcompl hred hreservoirCard
    exact ⟨centers, arm, hcard, hcentersBase, hcentersBlue,
      harmBlue, harmType,
      fun y hy x hx ↦ hstar y hy x (harmSub hx)⟩

/-- Global counterexample normal form for Part 3 under CH.  If neither
exact target occurs, one blue predecessor base supports finite blue centres
of every size, each completely red-joined to a later blue `ω₁ + 1` arm. -/
theorem part3_exact_or_omegaOne_arm_star_obstruction
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
    ∃ base : Set W2,
      blue.IsClique base ∧ typeLT base = ω_ 1 + 1 ∧
      ∀ n : ℕ, ∃ (centers : Finset W2) (arm : Set W2),
        centers.card = n ∧ (centers : Set W2) ⊆ base ∧
        blue.IsClique (centers : Set W2) ∧
        blue.IsClique arm ∧ typeLT arm = ω_ 1 + 1 ∧
        ∀ y ∈ centers, ∀ x ∈ arm, red.Adj y x := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain ⟨base, hbase, hbaseType⟩ | ⟨base, hbase, hbaseType⟩ :=
      red_target_or_blue_omegaOne_add_one hCH red blue hcompl
    · exact (hnone.1 ⟨base, hbase, hbaseType⟩).elim
    · obtain hred | hstars :=
        red_target_or_all_finite_by_omegaOne_add_one_bicolored_stars
          hCH red blue hcompl hbase hbaseType hnone.2
      · exact (hnone.1 hred).elim
      · exact ⟨base, hbase, hbaseType, hstars⟩

end Erdos1172Part3CHAsymmetric
