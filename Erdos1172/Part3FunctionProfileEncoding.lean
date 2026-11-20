/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FunctionDecisions
public import Erdos1172.Part3CoverProfileTools

@[expose] public section

/-!
# Encoding a head and row function names into one decision name

An injective coordinate map extends a decision system without changing
any decision on the image. Unused coordinates take a fixed default value.
Applying this to the existing profile coding combines a head name and
omegaOne many row names into one name on omegaOne.

Density here concerns only one coordinate at a time. No simultaneous
decision, countable closure, or ground dominating function is needed.
-/

open Set

namespace Erdos1172Part3FunctionProfileEncoding

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3CoverProfileTools (ProfileIndex profileRank)

variable {P I J V : Type} [Preorder P]

/-- Extend a decision system along an injective coordinate map, with a
fixed value on every coordinate outside its image. -/
def extendAlong (e : I ↪ J) (fallback : V) (F : FunctionDecisions P I V) :
    FunctionDecisions P J V where
  decides p i v := (∃ j : I, e j = i ∧ F.decides p j v) ∨
    ((¬∃ j : I, e j = i) ∧ v = fallback)
  dense p i := by
    classical
    by_cases h : ∃ j : I, e j = i
    · obtain ⟨j, hj⟩ := h
      obtain ⟨q, hqp, v, hv⟩ := F.dense p j
      exact ⟨q, hqp, v, Or.inl ⟨j, hj, hv⟩⟩
    · exact ⟨p, le_rfl, fallback, Or.inr ⟨h, rfl⟩⟩
  persistent := by
    rintro p q i v hqp (⟨j, hj, hv⟩ | hoff)
    · exact Or.inl ⟨j, hj, F.persistent hqp hv⟩
    · exact Or.inr hoff
  unique := by
    rintro p i v w (⟨j, hj, hv⟩ | ⟨hoff, hv⟩)
      (⟨k, hk, hw⟩ | ⟨hoff', hw⟩)
    · have heq : j = k := e.injective (hj.trans hk.symm)
      subst k
      exact F.unique hv hw
    · exact (hoff' ⟨j, hj⟩).elim
    · exact (hoff ⟨k, hk⟩).elim
    · exact hv.trans hw.symm

/-- Extension preserves decisions exactly, not only after refinement. -/
theorem extendAlong_decides_iff (e : I ↪ J) (fallback : V)
    (F : FunctionDecisions P I V) (p : P) (i : I) (v : V) :
    (extendAlong e fallback F).decides p (e i) v ↔ F.decides p i v := by
  constructor
  · rintro (⟨j, hj, hv⟩ | ⟨hoff, _⟩)
    · have heq : j = i := e.injective hj
      simpa only [heq] using hv
    · exact (hoff ⟨i, rfl⟩).elim
  · intro hv
    exact Or.inl ⟨i, rfl, hv⟩

/-- The head and rows as one decision system on the uncoded profile. -/
def profileDecisions (F : FunctionDecisions P W1 W1)
    (R : W1 → FunctionDecisions P W1 W1) : FunctionDecisions P ProfileIndex W1 where
  decides p i v := match i with
    | .inl j => F.decides p j v
    | .inr ij => (R ij.1).decides p ij.2 v
  dense p i := by
    cases i with
    | inl j => exact F.dense p j
    | inr ij => exact (R ij.1).dense p ij.2
  persistent := by
    intro p q i v hqp hv
    cases i with
    | inl j => exact F.persistent hqp hv
    | inr ij => exact (R ij.1).persistent hqp hv
  unique := by
    intro p i v w hv hw
    cases i with
    | inl j => exact F.unique hv hw
    | inr ij => exact (R ij.1).unique hv hw

noncomputable def headCoordinate (j : W1) : W1 := profileRank (Sum.inl j)

noncomputable def rowCoordinate (i j : W1) : W1 := profileRank (Sum.inr (i, j))

/-- A single global name with exactly the original head and row decisions. -/
noncomputable def encodedName (F : FunctionDecisions P W1 W1)
    (R : W1 → FunctionDecisions P W1 W1) : FunctionDecisions P W1 W1 :=
  extendAlong profileRank (Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩)
    (profileDecisions F R)

theorem encodedName_head_decides_iff (F : FunctionDecisions P W1 W1)
    (R : W1 → FunctionDecisions P W1 W1) (p : P) (j v : W1) :
    (encodedName F R).decides p (headCoordinate j) v ↔ F.decides p j v :=
  extendAlong_decides_iff profileRank _ (profileDecisions F R) p (Sum.inl j) v

theorem encodedName_row_decides_iff (F : FunctionDecisions P W1 W1)
    (R : W1 → FunctionDecisions P W1 W1) (p : P) (i j v : W1) :
    (encodedName F R).decides p (rowCoordinate i j) v ↔ (R i).decides p j v :=
  extendAlong_decides_iff profileRank _ (profileDecisions F R) p (Sum.inr (i, j)) v

theorem exists_encoded_name (F : FunctionDecisions P W1 W1)
    (R : W1 → FunctionDecisions P W1 W1) :
    ∃ H : FunctionDecisions P W1 W1,
      (∀ p j v, H.decides p (headCoordinate j) v ↔ F.decides p j v) ∧
      ∀ p i j v, H.decides p (rowCoordinate i j) v ↔ (R i).decides p j v :=
  ⟨encodedName F R, encodedName_head_decides_iff F R, encodedName_row_decides_iff F R⟩

end Erdos1172Part3FunctionProfileEncoding
