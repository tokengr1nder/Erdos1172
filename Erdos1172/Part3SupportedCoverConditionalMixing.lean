/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FunctionNameMixing

@[expose] public section

/-!
# Guarded local-to-global mixing of cover names

Cone-local covering functions can be mixed along a predense antichain.
The resulting global function covers every actual source member whenever
the regular guard actually holds. On branches deciding the guard
negatively, a constant function suffices because the guarded obligation
is vacuous throughout that cone.

No closure, cardinality, monotonicity, or support hypothesis is needed:
the cover-name construction itself regularizes its finite certificates.
-/

open Set

namespace Erdos1172Part3SupportedCoverConditionalMixing

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (DenseBelow)
open Erdos1172Part3StationaryDecisions (exists_predense_antichain)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName exists_deciding_refinement)
open Erdos1172Part3FunctionNameMixing (mix coverName_mix_iff)
open Erdos1172Part3SupportedCoverRealization (coverName)

variable {P X : Type} [Preorder P]

/-- Mix a dense supply of cone-local guarded covers. The local function
may vary between cones; the conclusion uses one global function name. -/
theorem exists_guarded_cover_of_dense_local
    (guard : RegularName P Unit) (U : RegularName P X)
    (C : (W1 → W1) → Set X)
    (hlocal : ∀ p : P, ∃ q : P, q ≤ p ∧
      ∃ F : FunctionDecisions (Iic q) W1 W1,
        ∀ r : Iic q, ∀ x : X, guard.holds r.val () → U.holds r.val x → (coverName F C).holds r x) :
    ∃ H : FunctionDecisions P W1 W1,
      ∀ p : P, ∀ x : X, guard.holds p () → U.holds p x → (coverName H C).holds p x := by
  classical
  let D : Set P := {q | ∃ F : FunctionDecisions (Iic q) W1 W1,
    ∀ r : Iic q, ∀ x : X, guard.holds r.val () → U.holds r.val x → (coverName F C).holds r x}
  have hD : DenseBelow D := by
    intro p
    obtain ⟨q, hqp, F, hF⟩ := hlocal p
    exact ⟨q, ⟨F, hF⟩, hqp⟩
  obtain ⟨A, hAD, hA, hpredense⟩ := exists_predense_antichain D hD
  choose F hF using fun a : A => hAD a.property
  refine ⟨mix A hA hpredense F, ?_⟩
  intro p x hp hx
  apply (coverName (mix A hA hpredense F) C).of_dense p x
  intro q hqp
  obtain ⟨a, ha, r, hrq, hra⟩ := hpredense q
  refine ⟨r, hrq, ?_⟩
  apply (coverName_mix_iff A hA hpredense F C ⟨a, ha⟩ r hra x).mpr
  exact hF ⟨a, ha⟩ ⟨r, hra⟩ x
    (guard.persistent (hrq.trans hqp) hp) (U.persistent (hrq.trans hqp) hx)

/-- Local covers need only be provided below conditions where the guard
holds. Dense Boolean refinement supplies harmless negative branches,
and mixing produces one function name satisfying the guarded conclusion. -/
theorem exists_guarded_cover_of_local
    (guard : RegularName P Unit) (U : RegularName P X)
    (C : (W1 → W1) → Set X)
    (hlocal : ∀ p : P, guard.holds p () →
      ∃ q : P, q ≤ p ∧ ∃ F : FunctionDecisions (Iic q) W1 W1,
        ∀ r : Iic q, ∀ x : X, U.holds r.val x → (coverName F C).holds r x) :
    ∃ H : FunctionDecisions P W1 W1,
      ∀ p : P, ∀ x : X, guard.holds p () → U.holds p x → (coverName H C).holds p x := by
  apply exists_guarded_cover_of_dense_local guard U C
  intro p
  obtain ⟨q, hqp, hq⟩ := exists_deciding_refinement guard p ()
  rcases hq with hq | hq
  · obtain ⟨r, hrq, F, hF⟩ := hlocal q hq
    exact ⟨r, hrq.trans hqp, F, fun s x _hs hx => hF s x hx⟩
  · refine ⟨q, hqp, FunctionDecisions.ofFunction
      (fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩), ?_⟩
    intro r x hr _hx
    exact (hq r.val r.property hr).elim

end Erdos1172Part3SupportedCoverConditionalMixing
