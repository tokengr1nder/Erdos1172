/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueBlockExtension
public import Erdos1172.Part2Reduction

@[expose] public section

open Cardinal Ordinal Set

namespace Erdos1172BlockCriterion

abbrev W3 : Type := (ω_ 3 : Ordinal.{0}).ToType

/-- A later homogeneous block, completely joined to a fixed base clique. -/
def HasLaterCliqueBlock (G : SimpleGraph W3) (s : Set W3)
    (γ : Ordinal.{0}) : Prop :=
  ∃ t : Set W3, G.IsClique t ∧ typeLT t = γ ∧
    (∀ x ∈ s, ∀ y ∈ t, x < y) ∧
    ∀ x ∈ s, ∀ y ∈ t, G.Adj x y

/-- Every clique of type `ω₂ + 1` contains a clique subset of exact type
`ω₂`. This isolates the long base block needed by Part 2. -/
theorem exists_omegaTwo_clique_subset_of_omegaTwo_add_one
    (G : SimpleGraph W3) {base : Set W3}
    (hbase : G.IsClique base) (hbaseType : typeLT base = ω_ 2 + 1) :
    ∃ core : Set W3, core ⊆ base ∧ G.IsClique core ∧ typeLT core = ω_ 2 := by
  have hle : (ω_ 2 : Ordinal.{0}) ≤ typeLT base := by
    rw [hbaseType]
    exact le_self_add
  obtain ⟨core, hsub, htype⟩ :=
    Ordinal.exists_subset_typeLT_eq base (β := (ω_ 2 : Ordinal.{0})) hle
  exact ⟨core, hsub, hbase.subset hsub, htype⟩

/-- A fully joined later block extends an `ω₂` clique to the corresponding
ordinal-sum target. -/
theorem exists_clique_type_omegaTwo_add_of_later_block
    (G : SimpleGraph W3) {core : Set W3} {γ : Ordinal.{0}}
    (hcore : G.IsClique core) (hcoreType : typeLT core = ω_ 2)
    (hblock : HasLaterCliqueBlock G core γ) :
    OrdinalRamsey.HasCliqueOfType G (ω_ 2 + γ) := by
  obtain ⟨t, ht, httype, hlater, hcross⟩ := hblock
  exact G.exists_clique_type_add_of_later_block
    hcore ht hcoreType httype hlater hcross

/-- A Lean-exact sufficient criterion for Erdős Problem 1172, Part 2.

The higher Erdős--Rado theorem first supplies a red or blue `ω₂ + 1`
clique. We extract an `ω₂` clique subset. The two hypotheses say that every
such extracted red core has a fully joined later red block of type `ω₁`, and
every such blue core has a fully joined later blue block of type `ω`. The
block-extension theorem then gives exactly `ω₂ + ω₁` or `ω₂ + ω`. -/
theorem part2_of_full_later_block_obligations
    (hGCH : GCH)
    (hred : ∀ (red blue : SimpleGraph W3), IsCompl red blue →
      ∀ (base core : Set W3), red.IsClique base →
        typeLT base = ω_ 2 + 1 → core ⊆ base →
        red.IsClique core → typeLT core = ω_ 2 →
        HasLaterCliqueBlock red core (ω_ 1))
    (hblue : ∀ (red blue : SimpleGraph W3), IsCompl red blue →
      ∀ (base core : Set W3), blue.IsClique base →
        typeLT base = ω_ 2 + 1 → core ⊆ base →
        blue.IsClique core → typeLT core = ω_ 2 →
        HasLaterCliqueBlock blue core ω) :
    OrdinalRamsey (ω_ 3 : Ordinal.{0}) (ω_ 2 + ω_ 1) (ω_ 2 + ω) := by
  intro red blue hcompl
  obtain ⟨base, hbase, hbaseType⟩ | ⟨base, hbase, hbaseType⟩ :=
    ErdosRadoHigher.ordinalRamsey_omegaThree_omegaTwo_add_one hGCH red blue hcompl
  · obtain ⟨core, hsub, hcore, hcoreType⟩ :=
      exists_omegaTwo_clique_subset_of_omegaTwo_add_one red hbase hbaseType
    exact Or.inl <| exists_clique_type_omegaTwo_add_of_later_block red
      hcore hcoreType
        (hred red blue hcompl base core hbase hbaseType hsub hcore hcoreType)
  · obtain ⟨core, hsub, hcore, hcoreType⟩ :=
      exists_omegaTwo_clique_subset_of_omegaTwo_add_one blue hbase hbaseType
    exact Or.inr <| exists_clique_type_omegaTwo_add_of_later_block blue
      hcore hcoreType
        (hblue red blue hcompl base core hbase hbaseType hsub hcore hcoreType)

end Erdos1172BlockCriterion
