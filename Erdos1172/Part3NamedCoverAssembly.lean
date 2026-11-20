/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CofinalPowerCoverAssembly
public import Erdos1172.Part3SupportedCoverTransport
public import Erdos1172.Part3FunctionProfileEncoding

@[expose] public section

/-!
# Actual membership in an assembled named cover

The head and row functions are encoded into one coherent function name.
Finite certificates for an endpoint and for a point below that endpoint
can therefore be combined using common decisions. This construction uses
actual regular membership throughout and has no ground domination premise.

The final theorem assembles a dense local covering relation. Constructing
that relation for every higher-rank cofinal name remains a separate step.
-/

open Set

namespace Erdos1172Part3NamedCoverAssembly

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3CofinalLineCover (LineCoverData)
open Erdos1172Part3CofinalPowerCoverAssembly (LowerCovers addedRow cover)
open Erdos1172Part3CoverProfileTools (head row decode)
open Erdos1172Part3FunctionProfileEncoding
open Erdos1172Part3SupportedCoverRealization (coverName holds_of_certificate)
open Erdos1172Part3SupportedCoverTransport

variable {P V : Type} [Preorder P] [LinearOrder V] [WellFoundedLT V] {n : ℕ}

noncomputable def family (data : LineCoverData V) (L : LowerCovers n V)
    (seed : Set V) (f : W1 → W1) : Set V := cover data L seed (decode f)

theorem holds_head (data : LineCoverData V) (L : LowerCovers n V)
    (seed : Set V) (F : FunctionDecisions P W1 W1)
    (R : W1 → FunctionDecisions P W1 W1) {p : P} {x : V}
    (hx : (coverName F data.cover).holds p x) :
    (coverName (encodedName F R) (family data L seed)).holds p x := by
  have hhead : (coverName (encodedName F R)
      (fun f => data.cover (head (decode f)))).holds p x :=
    holds_precompose headCoordinate
      (fun _ _ _ _ _ hv hw => (F.unique hv
        ((encodedName_head_decides_iff F R _ _ _).mp hw)).le) hx
  exact holds_of_family_subset (fun _ _ h => Or.inr (Or.inl h)) hhead

theorem holds_seed (data : LineCoverData V) (L : LowerCovers n V)
    (seed : Set V) (H : FunctionDecisions P W1 W1) {p : P} {x : V}
    (hx : x ∈ seed) : (coverName H (family data L seed)).holds p x := by
  apply holds_of_certificate
  refine ⟨(fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩), ∅, ?_, ?_⟩
  · intro i hi
    exact False.elim (Finset.notMem_empty i hi)
  · intro _ _
    exact Or.inl hx

/-- Both membership certificates now use the same encoded function, so
their finite supports may be joined without choosing incompatible values. -/
theorem holds_addedRow (data : LineCoverData V) (L : LowerCovers n V)
    (F : FunctionDecisions P W1 W1) (R : W1 → FunctionDecisions P W1 W1)
    {p : P} {i : W1} {y x : V} {k : Fin n}
    (hrow : data.row x = i) (hycut : y ≤ data.cut i)
    (hy : (coverName F data.cover).holds p y)
    (hx : (coverName (R i) (L.into y k)).holds p x) :
    (coverName (encodedName F R) (fun f => addedRow data L (decode f) i)).holds p x := by
  have hhead : (coverName (encodedName F R)
      (fun f => data.cover (head (decode f)))).holds p y :=
    holds_precompose headCoordinate
      (fun _ _ _ _ _ hv hw => (F.unique hv
        ((encodedName_head_decides_iff F R _ _ _).mp hw)).le) hy
  have hlocal : (coverName (encodedName F R)
      (fun f => L.into y k (row (decode f) i))).holds p x :=
    holds_precompose (rowCoordinate i)
      (fun _ _ _ _ _ hv hw => ((R i).unique hv
        ((encodedName_row_decides_iff F R _ _ _ _).mp hw)).le) hx
  apply holds_combine hhead hlocal
  intro f hyf hxf
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨⟨hyf, hycut⟩,
    Set.mem_iUnion.mpr ⟨k, hrow, hxf⟩⟩⟩

theorem holds_piece (data : LineCoverData V) (L : LowerCovers n V)
    (seed : Set V) (F : FunctionDecisions P W1 W1)
    (R : W1 → FunctionDecisions P W1 W1)
    {p : P} {i : W1} {y x : V} {k : Fin n}
    (hrow : data.row x = i) (hycut : y ≤ data.cut i)
    (hy : (coverName F data.cover).holds p y)
    (hx : (coverName (R i) (L.into y k)).holds p x) :
    (coverName (encodedName F R) (family data L seed)).holds p x := by
  exact holds_of_family_subset
    (fun _ _ h => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨i, h⟩)))
    (holds_addedRow data L F R hrow hycut hy hx)

/-- Local witnesses may depend on the refinement. Regularity upgrades
their dense assembly to coverage at the original condition. -/
theorem exists_assembled_name (data : LineCoverData V) (L : LowerCovers n V)
    (seed : Set V) (U : RegularName P V) (F : FunctionDecisions P W1 W1)
    (R : W1 → FunctionDecisions P W1 W1)
    (hlocal : ∀ p : P, ∀ x : V, U.holds p x → ∃ q : P, q ≤ p ∧
      (x ∈ seed ∨ (coverName F data.cover).holds q x ∨
        ∃ i : W1, ∃ y : V, ∃ k : Fin n, data.row x = i ∧ y ≤ data.cut i ∧
          (coverName F data.cover).holds q y ∧
          (coverName (R i) (L.into y k)).holds q x)) :
    ∃ H : FunctionDecisions P W1 W1,
      ∀ p : P, ∀ x : V, U.holds p x → (coverName H (family data L seed)).holds p x := by
  refine ⟨encodedName F R, ?_⟩
  intro p x hx
  apply (coverName (encodedName F R) (family data L seed)).of_dense p x
  intro q hqp
  obtain ⟨r, hrq, hr⟩ := hlocal q x (U.persistent hqp hx)
  refine ⟨r, hrq, ?_⟩
  rcases hr with hs | hh | ⟨i, y, k, hrow, hycut, hy, hpiece⟩
  · exact holds_seed data L seed (encodedName F R) hs
  · exact holds_head data L seed F R hh
  · exact holds_piece data L seed F R hrow hycut hy hpiece

end Erdos1172Part3NamedCoverAssembly
