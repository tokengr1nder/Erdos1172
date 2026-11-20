/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NiceFunctionNames

@[expose] public section

/-!
# Selecting coherent decisions from dense witnesses

A persistent relation with dense witnesses need not choose a unique value
at a condition. A predense antichain at each coordinate gives coherent
choices within the original types.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3DecisionSelection

open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3NiceFunctionNames (NiceFunctionName)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3ClosedDecisionSystem (DenseBelow)

variable {P I V : Type} [Preorder P]

/-- Local witnesses are chosen once on each antichain, so two compatible
decisions cannot subsequently choose different values. -/
theorem exists_function_decisions_of_dense (R : P → I → V → Prop)
    (hpersistent : ∀ {p q i v}, q ≤ p → R p i v → R q i v)
    (hdense : ∀ p i, ∃ q : P, q ≤ p ∧ ∃ v : V, R q i v) :
    ∃ F : FunctionDecisions P I V, ∀ p i v, F.decides p i v → R p i v := by
  classical
  let D (i : I) : Set P := {p | ∃ v : V, R p i v}
  have hD : ∀ i, DenseBelow (D i) := by
    intro i p
    obtain ⟨q, hqp, v, hv⟩ := hdense p i
    exact ⟨q, ⟨v, hv⟩, hqp⟩
  choose A hAD hAA hAP using fun i => exists_predense_antichain (D i) (hD i)
  have witnesses (i : I) (a : A i) : ∃ v : V, R a.val i v := hAD i a.property
  let value (i : I) (a : A i) : V := (witnesses i a).choose
  let F : FunctionDecisions P I V := {
    decides := fun p i v => ∃ a : A i, p ≤ a.val ∧ value i a = v
    dense := by
      intro p i
      obtain ⟨a, ha, q, hqp, hqa⟩ := hAP i p
      exact ⟨q, hqp, value i ⟨a, ha⟩, ⟨a, ha⟩, hqa, rfl⟩
    persistent := by
      rintro p q i v hqp ⟨a, hpa, hv⟩
      exact ⟨a, hqp.trans hpa, hv⟩
    unique := by
      rintro p i v w ⟨a, hpa, hv⟩ ⟨b, hpb, hw⟩
      have heq : a = b := by
        apply Subtype.ext
        by_contra hne
        exact hAA i a.val a.property b.val b.property hne ⟨p, hpa, hpb⟩
      subst b
      exact hv.symm.trans hw }
  refine ⟨F, ?_⟩
  rintro p i v ⟨a, hpa, hv⟩
  rw [← hv]
  exact hpersistent hpa (witnesses i a).choose_spec

/-- Under the chain condition the selected decisions also have a small
predense representation suitable for the next Hechler stage. -/
theorem exists_nice_name_of_dense (hcc : OmegaTwoCC P) (R : P → I → V → Prop)
    (hpersistent : ∀ {p q i v}, q ≤ p → R p i v → R q i v)
    (hdense : ∀ p i, ∃ q : P, q ≤ p ∧ ∃ v : V, R q i v) :
    ∃ N : NiceFunctionName P I V, ∀ p i v, N.toDecisions.decides p i v → R p i v := by
  obtain ⟨F, hF⟩ := exists_function_decisions_of_dense R hpersistent hdense
  obtain ⟨N, hN⟩ := Erdos1172Part3NiceFunctionNames.exists_nice_name hcc F
  exact ⟨N, fun p i v hv => hF p i v (hN p i v hv)⟩

def reindex {J : Type} (F : FunctionDecisions P I V) (f : J → I) :
    FunctionDecisions P J V where
  decides p j v := F.decides p (f j) v
  dense p j := F.dense p (f j)
  persistent := F.persistent
  unique := F.unique

end Erdos1172Part3DecisionSelection
