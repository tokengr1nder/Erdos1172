/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3SupportedCoverRealization

@[expose] public section

/-!
# Mixing cone-local function decisions

A predense antichain supports a single global function name whose decisions
agree exactly with each local name on its cone. Finite cover certificates,
and hence their actual regularized membership predicates, agree on each
branch as well. This construction uses neither closure nor a generic model.
-/

open Set

namespace Erdos1172Part3FunctionNameMixing

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (DenseBelow)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3SupportedCoverRealization

variable {P I V X : Type} [Preorder P]

/-- Distinct antichain branches cannot both be above one condition. -/
theorem branch_eq {A : Set P} (hA : IncompatibleFamily A)
    {a b : A} {p : P} (hpa : p ≤ a.val) (hpb : p ≤ b.val) : a = b := by
  apply Subtype.ext
  by_contra hne
  exact hA a.val a.property b.val b.property hne ⟨p, hpa, hpb⟩

/-- A local decision is a global decision exactly on its antichain cone. -/
def mix (A : Set P) (hA : IncompatibleFamily A)
    (hpredense : ∀ p : P, ∃ a ∈ A, Compatible p a)
    (F : ∀ a : A, FunctionDecisions (Iic a.val) I V) :
    FunctionDecisions P I V where
  decides p i v := ∃ a : A, ∃ hpa : p ≤ a.val, (F a).decides ⟨p, hpa⟩ i v
  dense p i := by
    obtain ⟨a, ha, q, hqp, hqa⟩ := hpredense p
    obtain ⟨r, hrq, v, hv⟩ := (F ⟨a, ha⟩).dense ⟨q, hqa⟩ i
    exact ⟨r.val, (show r.val ≤ q from hrq).trans hqp, v, ⟨a, ha⟩, r.property, hv⟩
  persistent := by
    rintro p q i v hqp ⟨a, hpa, hv⟩
    exact ⟨a, hqp.trans hpa, (F a).persistent hqp hv⟩
  unique := by
    rintro p i v w ⟨a, hpa, hv⟩ ⟨b, hpb, hw⟩
    have heq : a = b := branch_eq hA hpa hpb
    subst b
    exact (F a).unique hv hw

theorem mix_decides_iff (A : Set P) (hA : IncompatibleFamily A)
    (hpredense : ∀ p : P, ∃ a ∈ A, Compatible p a)
    (F : ∀ a : A, FunctionDecisions (Iic a.val) I V)
    (a : A) (p : P) (hpa : p ≤ a.val) (i : I) (v : V) :
    (mix A hA hpredense F).decides p i v ↔ (F a).decides ⟨p, hpa⟩ i v := by
  constructor
  · rintro ⟨b, hpb, hv⟩
    have heq : b = a := branch_eq hA hpb hpa
    subst b
    exact hv
  · intro hv
    exact ⟨a, hpa, hv⟩

/-- Mixing preserves each finite certificate exactly on a branch. -/
theorem certificate_mix_iff (A : Set P) (hA : IncompatibleFamily A)
    (hpredense : ∀ p : P, ∃ a ∈ A, Compatible p a)
    (F : ∀ a : A, FunctionDecisions (Iic a.val) W1 W1)
    (C : (W1 → W1) → Set X) (a : A) (p : P) (hpa : p ≤ a.val) (x : X) :
    Certificate (mix A hA hpredense F) C p x ↔
      Certificate (F a) C ⟨p, hpa⟩ x := by
  constructor
  · rintro ⟨f, support, hdec, hcover⟩
    exact ⟨f, support, fun i hi =>
      (mix_decides_iff A hA hpredense F a p hpa i (f i)).mp (hdec i hi), hcover⟩
  · rintro ⟨f, support, hdec, hcover⟩
    exact ⟨f, support, fun i hi =>
      (mix_decides_iff A hA hpredense F a p hpa i (f i)).mpr (hdec i hi), hcover⟩

/-- Actual supported-cover membership agrees on the entire branch cone.
The forward and backward directions compare all refinements, not merely
one compatible certificate. -/
theorem coverName_mix_iff (A : Set P) (hA : IncompatibleFamily A)
    (hpredense : ∀ p : P, ∃ a ∈ A, Compatible p a)
    (F : ∀ a : A, FunctionDecisions (Iic a.val) W1 W1)
    (C : (W1 → W1) → Set X) (a : A) (p : P) (hpa : p ≤ a.val) (x : X) :
    (coverName (mix A hA hpredense F) C).holds p x ↔
      (coverName (F a) C).holds ⟨p, hpa⟩ x := by
  constructor
  · intro hx q hqp
    obtain ⟨r, hrq, hr⟩ := hx q.val hqp
    exact ⟨⟨r, hrq.trans q.property⟩, hrq,
      (certificate_mix_iff A hA hpredense F C a r (hrq.trans q.property) x).mp hr⟩
  · intro hx q hqp
    obtain ⟨r, hrq, hr⟩ := hx ⟨q, hqp.trans hpa⟩ hqp
    exact ⟨r.val, hrq,
      (certificate_mix_iff A hA hpredense F C a r.val r.property x).mpr hr⟩

end Erdos1172Part3FunctionNameMixing
