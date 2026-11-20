/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3ConvergentCore
public import Erdos1172.Part3RedPredecessorReflection
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

/-!
# A maximal centered family supplies stationary small blue losses

Only finite ideal closure is used. A maximal family of blue columns with
positive finite intersections is red homogeneous when every positive row
set contains a blue omegaOne core and blue omegaOne+2 is forbidden. If
there is no source-sized red clique, this family is bounded. Its finite
maximality witnesses can then be frozen on a stationary future.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3CenteredStationaryLoss

open Erdos1172Part3NeighborhoodCode (W2 cof_W2 alephZero_lt_cof_W2)
open Erdos1172Part3FiniteIdealEndpoint
open Erdos1172Part3TwoSuccessorBootstrap (stationary_inter_club isCofinal_of_stationary)
open Erdos1172Part3RedCoreIdeal (mk_eq_alephTwo_of_isCofinal)
open OrdinalRamsey (HasCliqueOfType)

theorem exists_stationary_fiber_of_small {I : Type} (hI : #I < ℵ_ 2)
    {s : Set W2} (hs : IsStationary s) (f : s → I) :
    ∃ i : I, IsStationary {a : W2 | ∃ ha : a ∈ s, f ⟨a, ha⟩ = i} := by
  classical
  by_contra h
  push Not at h
  choose clubs hclubs hdisjoint using fun i => not_isStationary_iff.mp (h i)
  have hc : IsClub (⋂ i, clubs i) := IsClub.iInter alephZero_lt_cof_W2.ne'
    (by simpa only [Cardinal.lift_id, cof_W2] using hI) hclubs
  obtain ⟨a, has, hac⟩ := hs hc
  exact Set.disjoint_left.mp (hdisjoint (f ⟨a, has⟩)) ⟨has, rfl⟩
    (Set.mem_iInter.mp hac (f ⟨a, has⟩))

def rowsMeet (H : SimpleGraph W2) (rows : Set W2) (t : Finset W2) : Set W2 :=
  {x | x ∈ rows ∧ ∀ b ∈ t, H.Adj x b}

def Centered (J : FiniteSmallness W2) (H : SimpleGraph W2)
    (rows family : Set W2) : Prop :=
  ∀ t : Finset W2, (↑t : Set W2) ⊆ family → ¬J.small (rowsMeet H rows t)

end Erdos1172Part3CenteredStationaryLoss
