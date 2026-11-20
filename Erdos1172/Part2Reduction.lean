/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Pigeonhole
public import Erdos1172.ForMathlib.SetTheory.Cardinal.GCHConsequences1172
public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelationAPI

@[expose] public section

open Cardinal Ordinal

universe u

namespace OrdinalRamsey

/-- A graph has a clique of the specified ordinal order type. -/
def HasCliqueOfType {α : Ordinal.{u}} (G : SimpleGraph α.ToType)
    (β : Ordinal.{u}) : Prop :=
  ∃ s, G.IsClique s ∧ typeLT s = β

end OrdinalRamsey
