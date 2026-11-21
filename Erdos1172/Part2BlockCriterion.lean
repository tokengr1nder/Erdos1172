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

/-- A fully joined later block extends an `ω₂` clique to the corresponding
ordinal-sum target. -/
theorem exists_clique_type_omegaTwo_add_of_later_block
    (G : SimpleGraph W3) {core : Set W3} {γ : Ordinal.{0}}
    (hcore : G.IsClique core) (hcoreType : typeLT core = ω_ 2)
    (hblock : HasLaterCliqueBlock G core γ) :
    OrdinalRamsey.HasCliqueOfType G (ω_ 2 + γ) := by
  obtain ⟨t, ht, httype, hlater, hcross⟩ := hblock
  exact G.exists_clique_type_add_of_later_block hcore ht hcoreType httype hlater hcross

end Erdos1172BlockCriterion
