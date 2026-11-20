/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NiceCliqueNames

@[expose] public section

/-!
# Mixing clique decisions along a predense antichain

Compatible decisions use the same branch. The construction preserves
the complete ordered clique, not just separate point names.
-/

open Set Order

namespace Erdos1172Part3NamedCliqueMixing

open Erdos1172Part3ClosedDecisionSystem (CliqueDecisions)
open Erdos1172Part3StationaryDecisions (Compatible IncompatibleFamily)

variable {P I V : Type} [Preorder P] [LinearOrder I] [LinearOrder V]
variable {G : SimpleGraph V} {A : Set P}

theorem branch_eq (hA : IncompatibleFamily A) (a b : A) (p : P)
    (hpa : p ≤ a.val) (hpb : p ≤ b.val) : a = b := by
  apply Subtype.ext
  by_contra hne
  exact hA a.val a.property b.val b.property hne ⟨p, hpa, hpb⟩

def mixedDecides (blocks : A → CliqueDecisions P I V G) (p : P) (i : I) (x : V) : Prop :=
  ∃ a : A, p ≤ a.val ∧ (blocks a).decides p i x

def mixCore (hA : IncompatibleFamily A)
    (hpredense : ∀ p : P, ∃ q ∈ A, Compatible p q)
    (blocks : A → CliqueDecisions P I V G) : CliqueDecisions P I V G where
  decides := mixedDecides blocks
  dense := by
    intro p i
    obtain ⟨a, ha, q, hqp, hqa⟩ := hpredense p
    obtain ⟨s, hsq, x, hx⟩ := (blocks ⟨a, ha⟩).dense q i
    exact ⟨s, hsq.trans hqp, x, ⟨a, ha⟩, hsq.trans hqa, hx⟩
  persistent := by
    rintro p q i x hqp ⟨a, hpa, hx⟩
    exact ⟨a, hqp.trans hpa, (blocks a).persistent hqp hx⟩
  unique := by
    rintro p i x y ⟨a, hpa, hx⟩ ⟨b, hpb, hy⟩
    have heq := branch_eq hA a b p hpa hpb
    subst b
    exact (blocks a).unique hx hy
  ordered := by
    rintro p i j x y hij ⟨a, hpa, hx⟩ ⟨b, hpb, hy⟩
    have heq := branch_eq hA a b p hpa hpb
    subst b
    exact (blocks a).ordered hij hx hy
  adjacent := by
    rintro p i j x y hij ⟨a, hpa, hx⟩ ⟨b, hpb, hy⟩
    have heq := branch_eq hA a b p hpa hpb
    subst b
    exact (blocks a).adjacent hij hx hy

theorem decides_on_branch (hA : IncompatibleFamily A)
    (blocks : A → CliqueDecisions P I V G) (a : A) (p : P) (hpa : p ≤ a.val)
    (i : I) (x : V) (hx : mixedDecides blocks p i x) : (blocks a).decides p i x := by
  obtain ⟨b, hpb, hb⟩ := hx
  have heq := branch_eq hA a b p hpa hpb
  subst b
  exact hb

end Erdos1172Part3NamedCliqueMixing
