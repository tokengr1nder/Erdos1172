/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteArmChain

@[expose] public section

open Cardinal Ordinal Set Function
open Order

namespace Erdos1172Part3TransfiniteIncidence

open Erdos1172Part3Failure Erdos1172Part3TransfiniteArmChain

/-- The index type of the full `ω₂` arm chain. -/
abbrev ArmIndex : Type 1 := Set.Iio (ω_ 2 : Ordinal.{0})

/-- Ordered pairs of distinct arm indices. -/
def OrderedArmPairs := {p : ArmIndex × ArmIndex // p.1 < p.2}

/-- Full cross-arm incidence obstruction left by failure of the exact
blue target.  The arms form the transfinite ordered chain, retain the
successor red stars, and every vertex of every later arm has at least
one red predecessor in every earlier arm. -/
def FullOmegaTwoIncidenceObstruction
    (red blue : SimpleGraph W2) : Prop :=
  ∃ arms : ArmIndex → Set W2,
    (∀ i, blue.IsClique (arms i) ∧ typeLT (arms i) = ω_ 1 + 1) ∧
    (∀ i j, i < j → ∀ z ∈ arms i, ∀ x ∈ arms j, z < x) ∧
    (∀ (o : Ordinal.{0}) (ho : o + 1 < ω_ 2),
      ∃ witness : W2,
        witness ∈ arms ⟨o, (lt_add_one o).trans ho⟩ ∧
        ∀ x ∈ arms ⟨o + 1, ho⟩, red.Adj witness x) ∧
    ∀ i j, i < j → ∀ y ∈ arms j,
      ∃ x ∈ arms i, red.Adj x y

/-- A global choice of one red predecessor for every ordered arm pair
and every vertex in the later arm. -/
def HasChosenIncidencePredecessors
    (red : SimpleGraph W2) (arms : ArmIndex → Set W2) : Prop :=
  ∃ predecessor : ∀ p : OrderedArmPairs,
      (arms p.val.2) → (arms p.val.1),
    ∀ p y, red.Adj (predecessor p y) y

/-- Failure of the exact blue target upgrades every full transfinite arm
chain to the full cross-arm incidence obstruction.  If a later vertex
had no red predecessor in some earlier arm, it would be a common later
blue neighbor of that entire blue `ω₁ + 1` arm, producing exact type
`ω₁ + 2`. -/
theorem fullOmegaTwoIncidenceObstruction_of_chain
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (hchain : TransfiniteBlueArmChain red blue (ω_ 2)) :
    FullOmegaTwoIncidenceObstruction red blue := by
  classical
  obtain ⟨arms, harms, hordered, hsuccessor⟩ := hchain
  refine ⟨arms, harms, hordered, hsuccessor, ?_⟩
  intro i j hij y hy
  by_contra hnone
  push Not at hnone
  have hlater : ∀ x ∈ arms i, x < y :=
    fun x hx ↦ hordered i j hij x hx y hy
  have hblueAdj : ∀ x ∈ arms i, blue.Adj x y := by
    intro x hx
    rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
    exact ⟨(hlater x hx).ne, hnone x hx⟩
  apply hnoBlue
  obtain ⟨clique, hclique, hcliqueType⟩ :=
    blue.exists_clique_type_add_one_of_common_later
      (harms i).1 (harms i).2 hlater hblueAdj
  refine ⟨clique, hclique, ?_⟩
  calc
    typeLT clique = (ω_ 1 + 1) + 1 := hcliqueType
    _ = ω_ 1 + 2 := by norm_num [add_assoc]

/-- The incidence relation admits simultaneous chosen predecessors.
This packages all pairwise existential witnesses into one dependent
choice function while retaining the full arm-chain presentation. -/
theorem FullOmegaTwoIncidenceObstruction.exists_presentation_with_chosenPredecessors
    {red blue : SimpleGraph W2}
    (hobs : FullOmegaTwoIncidenceObstruction red blue) :
    ∃ arms : ArmIndex → Set W2,
      (∀ i, blue.IsClique (arms i) ∧ typeLT (arms i) = ω_ 1 + 1) ∧
      (∀ i j, i < j → ∀ z ∈ arms i, ∀ x ∈ arms j, z < x) ∧
      (∀ (o : Ordinal.{0}) (ho : o + 1 < ω_ 2),
        ∃ witness : W2,
          witness ∈ arms ⟨o, (lt_add_one o).trans ho⟩ ∧
          ∀ x ∈ arms ⟨o + 1, ho⟩, red.Adj witness x) ∧
      (∀ i j, i < j → ∀ y ∈ arms j,
        ∃ x ∈ arms i, red.Adj x y) ∧
      HasChosenIncidencePredecessors red arms := by
  classical
  obtain ⟨arms, harms, hordered, hsuccessor, hincidence⟩ := hobs
  have hwitness (p : OrderedArmPairs) (y : arms p.val.2) :
      ∃ x : arms p.val.1, red.Adj x y := by
    obtain ⟨x, hx, hred⟩ :=
      hincidence p.val.1 p.val.2 p.property y y.property
    exact ⟨⟨x, hx⟩, hred⟩
  let predecessor : ∀ p : OrderedArmPairs,
      (arms p.val.2) → (arms p.val.1) :=
    fun p y ↦ Classical.choose (hwitness p y)
  have hpredecessor (p : OrderedArmPairs) (y : arms p.val.2) :
      red.Adj (predecessor p y) y :=
    Classical.choose_spec (hwitness p y)
  exact ⟨arms, harms, hordered, hsuccessor, hincidence,
    ⟨predecessor, hpredecessor⟩⟩

/-- Global exact-target-or-incidence normal form under CH. -/
theorem part3_exact_or_fullOmegaTwoIncidenceObstruction
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      FullOmegaTwoIncidenceObstruction red blue := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red
          Erdos1172Part3FiniteStars.RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain hexact | hchain :=
      part3_exact_or_transfiniteBlueArmChain_omegaTwo
        hCH red blue hcompl
    · exact (htarget hexact).elim
    · exact fullOmegaTwoIncidenceObstruction_of_chain
        red blue hcompl hnone.2 hchain

end Erdos1172Part3TransfiniteIncidence
