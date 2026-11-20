/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.NeighborhoodFutureTransfer

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part2NeighborhoodClosure

open Erdos1172NeighborhoodCode Erdos1172NeighborhoodIdeal
  Erdos1172NeighborhoodIdealCore Erdos1172NeighborhoodDerivedIdeal
  Erdos1172NeighborhoodStableSpectrum Erdos1172NeighborhoodFutureTransfer
  Erdos1172NeighborhoodFavorableClosure

theorem target_of_absent_extension {r : Code ↪ W3}
    (G H : SimpleGraph W3) (hcompl : IsCompl G H) (system : StableSystem r G H)
    (p q : WordCode) (hp : p ∈ system.patterns) (hq : q ∉ system.patterns)
    (color : Bool) (hcolor : color ∈ word p) (hword : word q = (!color) :: word p)
    (γ : Ordinal.{0}) (hγ : γ ≤ ω_ 2) (hγcard : γ.card < ℵ_ 2) :
    OrdinalRamsey.HasCliqueOfType (colorGraph G H color) (ω_ 2 + γ) := by
  classical
  obtain ⟨club, hclub, hstable⟩ := system.stable system.source Set.Subset.rfl system.stationary
  let domain := system.source ∩ club
  have hd : IsStationary domain := stationary_inter_club system.stationary hclub
  have hdGood : ∀ a ∈ domain, GoodCut r G H a := fun a ha => system.good a ha.1
  have hext : ∀ a ∈ domain,
      DerivedSmall r G H ((!color) :: word p) a (system.source ∩ Set.Iio a) := by
    intro a ha
    rw [← hword]
    by_contra h
    have hmem : q ∈ spectrum r G H a system.source := mem_spectrum.mpr h
    rw [hstable a ha.1 ha.2] at hmem
    exact hq hmem
  obtain ⟨a, had, future, hfDomain, hf, hloss⟩ := exists_stationary_smallLoss
    (word p) (!color) system.source domain hd hdGood hext
  have hpositive : ¬DerivedSmall r G H (word p) a (system.source ∩ Set.Iio a) := by
    apply mem_spectrum.mp
    rwa [hstable a had.1 had.2]
  exact target_of_stationary_smallLoss G H hcompl system p hp color hcolor γ hγ hγcard
    (hdGood a had) (system.source ∩ Set.Iio a) Set.inter_subset_right hpositive
    future (fun _ h => (hfDomain h).1) hf hloss

theorem part2Targets_of_favorable_pattern (hCH : CH) {r : Code ↪ W3}
    (G H : SimpleGraph W3) (hcompl : IsCompl G H) (system : StableSystem r G H)
    (hp : (2 : WordCode) ∈ system.patterns) : Part2Targets G H := by
  obtain ⟨club, hclub, hstable⟩ := system.stable system.source Set.Subset.rfl system.stationary
  obtain ⟨a, has, hac⟩ := system.stationary hclub
  obtain ⟨b, hbs, hbc, hab⟩ := system.stationary
    (hclub.inter alephZero_lt_cof_W3.ne' (Set.isClub_Ioi_of_aleph0_lt_cof
      alephZero_lt_cof_W3 a))
  have hpa : ¬DerivedSmall r G H (word 2) a (system.source ∩ Set.Iio a) :=
    mem_spectrum.mp (by rwa [hstable a has hac])
  have hpb : ¬DerivedSmall r G H [false, true] b (Set.Iio b) := by
    intro h
    have htrace : ¬DerivedSmall r G H (word 2) b (system.source ∩ Set.Iio b) :=
      mem_spectrum.mp (by rwa [hstable b hbs hbc])
    exact htrace (derivedSmall_mono _ (system.good b hbs) Set.inter_subset_right h)
  exact part2Targets_of_two_cuts hCH G H hcompl (system.good a has) (system.good b hbs)
    hab (word 2) (by simp [word]) (by simp [word])
    (system.source ∩ Set.Iio a) Set.inter_subset_right hpa hpb

theorem red_target_of_hard_pattern_and_no_targets (hCH : CH) {r : Code ↪ W3}
    (G H : SimpleGraph W3) (hcompl : IsCompl G H) (system : StableSystem r G H)
    (hno : ¬Part2Targets G H) (hp : (3 : WordCode) ∈ system.patterns) :
    OrdinalRamsey.HasCliqueOfType G (ω_ 2 + ω_ 1) := by
  obtain ⟨club, hclub, hstable⟩ := system.stable system.source Set.Subset.rfl system.stationary
  obtain ⟨first, hfirstS, hfirstC⟩ := system.stationary hclub
  have hfirst : ¬DerivedSmall r G H (word 3) first (system.source ∩ Set.Iio first) :=
    mem_spectrum.mp (by rwa [hstable first hfirstS hfirstC])
  let domain := system.source ∩ (club ∩ Set.Ioi first)
  have hd : IsStationary domain := stationary_inter_club system.stationary
    (hclub.inter alephZero_lt_cof_W3.ne'
      (Set.isClub_Ioi_of_aleph0_lt_cof alephZero_lt_cof_W3 first))
  have hdGood : ∀ a ∈ domain, GoodCut r G H a := fun a ha => system.good a ha.1
  have hext : ∀ a ∈ domain,
      DerivedSmall r G H (false :: word 3) a (system.source ∩ Set.Iio a) := by
    intro a ha
    have hfav : DerivedSmall r G H [false, true] a (Set.Iio a) :=
      favorable_small_of_no_targets hCH G H hcompl hno (system.good first hfirstS)
        (hdGood a ha) ha.2.2 (word 3) (by simp [word]) (by simp [word])
        (system.source ∩ Set.Iio first) Set.inter_subset_right hfirst
    have hlong : DerivedSmall r G H [false, true, false] a (Set.Iio a) :=
      derivedSmall_append [false, true] [false] (hdGood a ha) hfav
    exact derivedSmall_mono _ (hdGood a ha) Set.inter_subset_right hlong
  obtain ⟨a, had, future, hfDomain, hf, hloss⟩ := exists_stationary_smallLoss
    (word 3) false system.source domain hd hdGood hext
  have hpositive : ¬DerivedSmall r G H (word 3) a (system.source ∩ Set.Iio a) :=
    mem_spectrum.mp (by rwa [hstable a had.1 had.2.1])
  have htarget := target_of_stationary_smallLoss G H hcompl system 3 hp true
    (by simp [word]) (ω_ 1) (Ordinal.omega_le_omega.mpr (by norm_num))
    (by rw [Ordinal.card_omega]; exact Cardinal.aleph_lt_aleph.mpr (by norm_num))
    (hdGood a had) (system.source ∩ Set.Iio a) Set.inter_subset_right hpositive
    future (fun _ h => (hfDomain h).1) hf hloss
  exact htarget

theorem part2Targets_of_stableSystem (hCH : CH) {r : Code ↪ W3}
    (G H : SimpleGraph W3) (hcompl : IsCompl G H) (system : StableSystem r G H) :
    Part2Targets G H := by
  classical
  by_contra hno
  have h2 : (2 : WordCode) ∉ system.patterns := fun hp =>
    hno (part2Targets_of_favorable_pattern hCH G H hcompl system hp)
  have h3 : (3 : WordCode) ∉ system.patterns := fun hp =>
    hno (Or.inl (red_target_of_hard_pattern_and_no_targets hCH G H hcompl system hno hp))
  obtain ⟨p, hp⟩ := system.nonempty
  fin_cases p
  · apply hno
    apply Or.inr
    exact target_of_absent_extension G H hcompl system 0 3 hp h3 false
      (by simp [word]) (by simp [word]) ω (Ordinal.omega0_le_omega 2)
      (by rw [Ordinal.card_omega0, ← Cardinal.aleph_zero]
          exact Cardinal.aleph_lt_aleph.mpr (by norm_num))
  · apply hno
    apply Or.inl
    exact target_of_absent_extension G H hcompl system 1 2 hp h2 true
      (by simp [word]) (by simp [word]) (ω_ 1)
      (Ordinal.omega_le_omega.mpr (by norm_num))
      (by rw [Ordinal.card_omega]; exact Cardinal.aleph_lt_aleph.mpr (by norm_num))
  · exact h2 hp
  · exact h3 hp

/-- The exact Part 2 statement, with its original GCH hypothesis. -/
theorem part2_of_gch (hGCH : GCH) :
    OrdinalRamsey (ω_ 3 : Ordinal.{0}) (ω_ 2 + ω_ 1) (ω_ 2 + ω) := by
  intro G H hcompl
  let r := Erdos1172NeighborhoodCode.rank hGCH
  obtain ⟨system⟩ := exists_stableSystem hGCH r G H hcompl
  exact part2Targets_of_stableSystem hGCH.toCH G H hcompl system

end Erdos1172Part2NeighborhoodClosure
