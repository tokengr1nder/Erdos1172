/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedLocalRowCover
public import Erdos1172.Part3FunctionNameMixing

@[expose] public section

/-!
# Coherent mixing of local row covers

A predense antichain is chosen separately for each source row. The
endpoint-set decision and the row function name use the same selected
local cover on every branch. Consequently a later local piece-cover
membership transfers to the global row name while the endpoint set stays
fixed on that branch. The conclusion is dense coverage of actual source
members in their own rows, with actual supported-cover membership at the
displayed strengthening.

The mixing step uses no closure assumption. It does not posit one global
countable enumeration of all condition-dependent endpoint families.
-/

open Set

namespace Erdos1172Part3NamedRowMixing

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (DenseBelow)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3CofinalLineCover (LineCoverData)
open Erdos1172Part3CofinalPowerCoverAssembly (LowerCovers)
open Erdos1172Part3NamedLocalRowCover (LocalRowCover)
open Erdos1172Part3FunctionNameMixing (mix branch_eq coverName_mix_iff)
open Erdos1172Part3SupportedCoverRealization (coverName)

variable {P V : Type} [Preorder P] [LinearOrder V] [WellFoundedLT V] {n : ℕ}

/-- Mix endpoint sets and row functions using exactly the same antichain
branches. Their countability, bounds, row witnesses, and dense local
coverage therefore survive together. -/
theorem exists_mixed_row_covers (data : LineCoverData V) (L : LowerCovers n V)
    (U : RegularName P V)
    (hlocal : ∀ p : P, ∀ i : W1, ∃ q : P, q ≤ p ∧ Nonempty (LocalRowCover data L U i q)) :
    ∃ B : FunctionDecisions P W1 (Set V),
      ∃ R : W1 → FunctionDecisions P W1 W1,
        (∀ p : P, ∀ i : W1, ∀ S : Set V, B.decides p i S →
          S.Countable ∧ (∀ y ∈ S, y ≤ data.cut i) ∧ ∀ y ∈ S, ∃ x : V, data.row x = i ∧ x ≤ y) ∧
        ∀ p : P, ∀ x : V, U.holds p x →
          ∃ q : P, q ≤ p ∧ ∃ S : Set V, B.decides q (data.row x) S ∧
            (x ∈ S ∨ ∃ y ∈ S, ∃ k : Fin n,
              (coverName (R (data.row x)) (L.into y k)).holds q x) := by
  classical
  let good (i : W1) : Set P := {q | Nonempty (LocalRowCover data L U i q)}
  have hgood (i : W1) : DenseBelow (good i) := by
    intro p
    obtain ⟨q, hqp, hq⟩ := hlocal p i
    exact ⟨q, hq, hqp⟩
  choose A hAD hAA hAP using fun i : W1 => exists_predense_antichain (good i) (hgood i)
  let localData (i : W1) (a : A i) : LocalRowCover data L U i a.val :=
    Classical.choice (hAD i a.property)
  let R (i : W1) : FunctionDecisions P W1 W1 :=
    mix (A i) (hAA i) (hAP i) (fun a => (localData i a).functionName)
  let B : FunctionDecisions P W1 (Set V) := {
    decides := fun p i S => ∃ a : A i, p ≤ a.val ∧ (localData i a).endpoints = S
    dense := by
      intro p i
      obtain ⟨a, ha, q, hqp, hqa⟩ := hAP i p
      exact ⟨q, hqp, (localData i ⟨a, ha⟩).endpoints, ⟨a, ha⟩, hqa, rfl⟩
    persistent := by
      rintro p q i S hqp ⟨a, hpa, hS⟩
      exact ⟨a, hqp.trans hpa, hS⟩
    unique := by
      rintro p i S T ⟨a, hpa, hS⟩ ⟨b, hpb, hT⟩
      have hab : a = b := branch_eq (hAA i) hpa hpb
      subst b
      exact hS.symm.trans hT }
  refine ⟨B, R, ?_, ?_⟩
  · intro p i S hS
    rcases hS with ⟨a, hpa, rfl⟩
    exact ⟨(localData i a).countable, (localData i a).endpoint_le, (localData i a).row_witness⟩
  · intro p x hx
    let i : W1 := data.row x
    obtain ⟨a, ha, q, hqp, hqa⟩ := hAP i p
    let branch : A i := ⟨a, ha⟩
    obtain ⟨r, hrq, hr⟩ := (localData i branch).covered ⟨q, hqa⟩ x (U.persistent hqp hx) rfl
    refine ⟨r.val, (show r.val ≤ q from hrq).trans hqp,
      (localData i branch).endpoints, ?_, ?_⟩
    · exact ⟨branch, r.property, rfl⟩
    · rcases hr with hxS | ⟨y, hy, k, hk⟩
      · exact Or.inl hxS
      · refine Or.inr ⟨y, hy, k, ?_⟩
        exact (coverName_mix_iff (A i) (hAA i) (hAP i)
          (fun a => (localData i a).functionName) (L.into y k)
          branch r.val r.property x).mpr hk

end Erdos1172Part3NamedRowMixing
