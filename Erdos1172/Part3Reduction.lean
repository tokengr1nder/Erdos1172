/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ErdosRado
public import Erdos1172.Part2Reduction

@[expose] public section

open Cardinal Ordinal

namespace Erdos1172

open OrdinalRamsey

/-- Under GCH, the binary Erdős--Rado theorem reduces Part 3 exactly to
extending either possible `ω₁ + 1` homogeneous outcome to one of the two
prescribed Part 3 targets. -/
theorem part3_iff_extension_from_omegaOne_add_one (hGCH : GCH) :
    OrdinalRamsey (ω_ 2 : Ordinal.{0})
        (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2) ↔
      ∀ red blue : SimpleGraph (ω_ 2 : Ordinal.{0}).ToType,
        IsCompl red blue →
          (HasCliqueOfType red (ω_ 1 + 1) →
              HasCliqueOfType red (ω_ 1 ^ (ω + 2) + 2) ∨
                HasCliqueOfType blue (ω_ 1 + 2)) ∧
          (HasCliqueOfType blue (ω_ 1 + 1) →
              HasCliqueOfType red (ω_ 1 ^ (ω + 2) + 2) ∨
                HasCliqueOfType blue (ω_ 1 + 2)) :=
  OrdinalRamsey.iff_extension_from_base
    (ErdosRado.ordinalRamsey_omegaTwo_omegaOne_add_one hGCH.toCH)

/-- Any proposed counterexample to Part 3 under GCH contains a homogeneous
`ω₁ + 1` set in one color which fails to extend to either exact Part 3 target. -/
theorem part3_exact_or_successor_obstruction
    (hGCH : GCH)
    (red blue : SimpleGraph (ω_ 2 : Ordinal.{0}).ToType)
    (hcompl : IsCompl red blue) :
    (HasCliqueOfType red (ω_ 1 ^ (ω + 2) + 2) ∨
        HasCliqueOfType blue (ω_ 1 + 2)) ∨
      (HasCliqueOfType red (ω_ 1 + 1) ∧
        ¬HasCliqueOfType red (ω_ 1 ^ (ω + 2) + 2) ∧
        ¬HasCliqueOfType blue (ω_ 1 + 2)) ∨
      (HasCliqueOfType blue (ω_ 1 + 1) ∧
        ¬HasCliqueOfType red (ω_ 1 ^ (ω + 2) + 2) ∧
        ¬HasCliqueOfType blue (ω_ 1 + 2)) := by
  classical
  by_cases hexact : HasCliqueOfType red (ω_ 1 ^ (ω + 2) + 2) ∨
      HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl hexact
  · have hnone := not_or.mp hexact
    obtain hred | hblue :=
      ErdosRado.ordinalRamsey_omegaTwo_omegaOne_add_one hGCH.toCH red blue hcompl
    · exact Or.inr (Or.inl ⟨hred, hnone.1, hnone.2⟩)
    · exact Or.inr (Or.inr ⟨hblue, hnone.1, hnone.2⟩)

end Erdos1172
