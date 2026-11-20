/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.ErdosRadoHigher

@[expose] public section

open Cardinal Ordinal

universe u

namespace OrdinalRamsey

/-- A graph has a clique of the specified ordinal order type. -/
def HasCliqueOfType {α : Ordinal.{u}} (G : SimpleGraph α.ToType)
    (β : Ordinal.{u}) : Prop :=
  ∃ s, G.IsClique s ∧ typeLT s = β

/-- Once a weaker Ramsey relation supplies one of two base homogeneous sets,
proving a stronger relation is equivalent to extending either possible base
outcome to the stronger disjunction. -/
theorem iff_extension_from_base
    {α β₀ γ₀ β γ : Ordinal.{u}}
    (hbase : OrdinalRamsey α β₀ γ₀) :
    OrdinalRamsey α β γ ↔
      ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
        (HasCliqueOfType red β₀ →
            HasCliqueOfType red β ∨ HasCliqueOfType blue γ) ∧
        (HasCliqueOfType blue γ₀ →
            HasCliqueOfType red β ∨ HasCliqueOfType blue γ) := by
  constructor
  · intro h red blue hcompl
    have hout : HasCliqueOfType red β ∨ HasCliqueOfType blue γ :=
      h red blue hcompl
    exact ⟨fun _ ↦ hout, fun _ ↦ hout⟩
  · intro hext red blue hcompl
    obtain hred | hblue := hbase red blue hcompl
    · exact (hext red blue hcompl).1 hred
    · exact (hext red blue hcompl).2 hblue

end OrdinalRamsey

namespace Erdos1172

open OrdinalRamsey

/-- Under GCH, the higher symmetric Erdős--Rado theorem reduces Part 2
exactly to two successor-extension obligations, one for each possible color
of its `ω₂ + 1` homogeneous set. -/
theorem part2_iff_extension_from_omegaTwo_add_one (hGCH : GCH) :
    OrdinalRamsey (ω_ 3 : Ordinal.{0}) (ω_ 2 + ω_ 1) (ω_ 2 + ω) ↔
      ∀ red blue : SimpleGraph (ω_ 3 : Ordinal.{0}).ToType,
        IsCompl red blue →
          (HasCliqueOfType red (ω_ 2 + 1) →
              HasCliqueOfType red (ω_ 2 + ω_ 1) ∨
                HasCliqueOfType blue (ω_ 2 + ω)) ∧
          (HasCliqueOfType blue (ω_ 2 + 1) →
              HasCliqueOfType red (ω_ 2 + ω_ 1) ∨
                HasCliqueOfType blue (ω_ 2 + ω)) :=
  OrdinalRamsey.iff_extension_from_base
    (ErdosRadoHigher.ordinalRamsey_omegaThree_omegaTwo_add_one hGCH)

/-- Any proposed counterexample to Part 2 under GCH contains an explicit
successor-extension obstruction: a homogeneous set of type `ω₂ + 1` in one
color, while neither exact Part 2 target exists. -/
theorem part2_exact_or_successor_obstruction
    (hGCH : GCH)
    (red blue : SimpleGraph (ω_ 3 : Ordinal.{0}).ToType)
    (hcompl : IsCompl red blue) :
    (HasCliqueOfType red (ω_ 2 + ω_ 1) ∨
        HasCliqueOfType blue (ω_ 2 + ω)) ∨
      (HasCliqueOfType red (ω_ 2 + 1) ∧
        ¬HasCliqueOfType red (ω_ 2 + ω_ 1) ∧
        ¬HasCliqueOfType blue (ω_ 2 + ω)) ∨
      (HasCliqueOfType blue (ω_ 2 + 1) ∧
        ¬HasCliqueOfType red (ω_ 2 + ω_ 1) ∧
        ¬HasCliqueOfType blue (ω_ 2 + ω)) := by
  classical
  by_cases hexact : HasCliqueOfType red (ω_ 2 + ω_ 1) ∨
      HasCliqueOfType blue (ω_ 2 + ω)
  · exact Or.inl hexact
  · have hnone := not_or.mp hexact
    obtain hred | hblue :=
      ErdosRadoHigher.ordinalRamsey_omegaThree_omegaTwo_add_one hGCH red blue hcompl
    · exact Or.inr (Or.inl ⟨hred, hnone.1, hnone.2⟩)
    · exact Or.inr (Or.inr ⟨hblue, hnone.1, hnone.2⟩)

end Erdos1172
