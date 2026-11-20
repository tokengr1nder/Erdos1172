/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3PrescribedBaseFusion

@[expose] public section

/-!
# The coherent countable limit of the finite decision orders

A limit condition has one condition at each finite stage, with exact
agreement under the successor base projections. Order is pointwise.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3CountableHechlerLimit

open Erdos1172Part3FiniteHechlerStages (stage)
open Erdos1172Part3IteratedHechlerOrder (Condition emptyOver)

abbrev At (hGCH : GCH) (n : ℕ) : Type := (stage hGCH n).Carrier

structure Limit (hGCH : GCH) where
  point : ∀ n : ℕ, At hGCH n
  coherent : ∀ n : ℕ, (point (n + 1)).base = point n

variable {hGCH : GCH}

instance : Preorder (Limit hGCH) where
  le p q := ∀ n, p.point n ≤ q.point n
  le_refl _ _ := le_rfl
  le_trans _ _ _ hpq hqr n := (hpq n).trans (hqr n)

theorem limit_ext {p q : Limit hGCH} (h : p.point = q.point) : p = q := by
  cases p
  cases q
  cases h
  rfl

def atMap (n : ℕ) : Limit hGCH →o At hGCH n :=
  ⟨fun p => p.point n, fun _ _ h => h n⟩

/-- A dependent recursion with a fixed first coordinate. Each successor
is chosen with its base exactly equal to the preceding coordinate. -/
theorem exists_limit_starting_with (Good : ∀ n : ℕ, At hGCH n → Prop)
    (first : At hGCH 0) (hfirst : Good 0 first)
    (hstep : ∀ n (p : At hGCH n), Good n p →
      ∃ q : At hGCH (n + 1), q.base = p ∧ Good (n + 1) q) :
    ∃ q : Limit hGCH, q.point 0 = first ∧ ∀ n, Good n (q.point n) := by
  classical
  let Entry (n : ℕ) := {p : At hGCH n // Good n p}
  let next (n : ℕ) (p : Entry n) : Entry (n + 1) :=
    ⟨(hstep n p.val p.property).choose, (hstep n p.val p.property).choose_spec.2⟩
  let branch : ∀ n : ℕ, Entry n := fun n => Nat.rec (⟨first, hfirst⟩ : Entry 0) next n
  let q : Limit hGCH :=
    { point n := (branch n).val
      coherent n := (hstep n (branch n).val (branch n).property).choose_spec.1 }
  exact ⟨q, rfl, fun n => (branch n).property⟩

noncomputable def emptyLimit (hGCH : GCH) : Limit hGCH := by
  have h := exists_limit_starting_with (hGCH := hGCH) (fun _ _ => True)
    Erdos1172Part3HechlerOrder.emptyCondition trivial
    (fun _ p _ => ⟨emptyOver p, rfl, trivial⟩)
  exact h.choose

noncomputable instance : Inhabited (Limit hGCH) := ⟨emptyLimit hGCH⟩

end Erdos1172Part3CountableHechlerLimit
