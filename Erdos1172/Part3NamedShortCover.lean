/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedShortCofinalCover

@[expose] public section

/-!
# Actual short-profile covers of arbitrary regular names

The ground profile family is fixed before the condition order or regular
name is supplied. If a source is densely cofinal, its shorter enumeration
has a cofinal finite-power tail. Otherwise a strengthening bounds all its
later actual members by one ground cut. The same prefix-profile family
covers either case.

Absence of a full ordered decision embedding at the starting condition
is an explicit hypothesis. The conclusion supplies one strengthening;
it does not silently make this hypothesis hereditary on all sub-cones.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedShortCover

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3RegularGreedyEnumeration (HasOrderedEmbeddingBelow)
open Erdos1172Part3NamedOptionalCovers (OptionalNamedCofinalCovers)
open Erdos1172Part3NamedShortCofinalCover
open Erdos1172Part3CofinalCoverSupport (FinitelySupported)
open Erdos1172Part3SupportedCoverRealization (coverName)

variable {P V : Type} [Preorder P] [LinearOrder V] [WellFoundedLT V]

/-- The cofinal and bounded alternatives use exactly the same profile
family. The chosen profile is ground data, but its function remains a name. -/
theorem exists_profile_cover (L : ∀ n, OptionalNamedCofinalCovers n V)
    (hcard : #V ≤ ℵ_ 1) (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (U : RegularName P V) (p0 : P) (hclosed : CountablyClosed P)
    (hno : ¬HasOrderedEmbeddingBelow (I := V) U p0) :
    ∃ q : P, q ≤ p0 ∧ ∃ e : V × ℕ,
      ∃ F : FunctionDecisions (Set.Iic q) W1 W1,
        ∀ p : Set.Iic q, ∀ x : V, U.holds p.val x →
          (coverName F (profileFamily L e)).holds p x := by
  classical
  by_cases hcofinal : ∀ p : P, p ≤ p0 → ∀ cut : V,
      ∃ q : P, q ≤ p ∧ ∃ x : V, U.holds q x ∧ cut ≤ x
  · exact exists_cofinal_profile_cover L hcard htype U p0 hclosed hcofinal hno
  · obtain ⟨q, hq⟩ := not_forall.mp hcofinal
    have hqp0 : q ≤ p0 := by
      by_contra hnot
      exact hq (fun h => (hnot h).elim)
    have hcutExists : ¬∀ cut : V, ∃ r : P, r ≤ q ∧ ∃ x : V, U.holds r x ∧ cut ≤ x :=
      fun h => hq (fun _ => h)
    obtain ⟨cut, hcut⟩ := not_forall.mp hcutExists
    let F : FunctionDecisions (Set.Iic q) W1 W1 := FunctionDecisions.ofFunction
      (fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩)
    refine ⟨q, hqp0, (cut, 0), F, ?_⟩
    intro p x hx
    apply profileFamily_holds_of_lt L F (cut, 0) p x
    exact lt_of_not_ge (fun hcx => hcut ⟨p.val, p.property, x, hx, hcx⟩)

/-- Construct one small-profile, finitely supported family covering,
locally, every actual regular source without a full ordered decision
embedding. There is no seed, cofinality, or cover-name premise. -/
theorem exists_supported_named_short_covers
    (hcard : #V ≤ ℵ_ 1) (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) :
    ∃ C : (V × ℕ) → (W1 → W1) → Set V,
      (∀ e, Monotone (C e) ∧ FinitelySupported (C e) ∧
        ∀ f, typeLT (C e f) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1)) ∧
      ∀ (P : Type) [Preorder P], CountablyClosed P →
        ∀ (U : RegularName P V) (p0 : P),
          ¬HasOrderedEmbeddingBelow (I := V) U p0 →
            ∃ q : P, q ≤ p0 ∧ ∃ e : V × ℕ,
              ∃ F : FunctionDecisions (Set.Iic q) W1 W1,
                ∀ p : Set.Iic q, ∀ x : V, U.holds p.val x → (coverName F (C e)).holds p x := by
  classical
  let L (n : ℕ) : OptionalNamedCofinalCovers n V :=
    Classical.choice (Erdos1172Part3NamedOptionalCovers.exists_optionalNamedCofinalCovers hcard n)
  refine ⟨profileFamily L, ?_, ?_⟩
  · intro e
    exact ⟨profileFamily_mono L e, profileFamily_supported L e,
      profileFamily_type_lt L htype e⟩
  · intro P instP hclosed U p0 hno
    exact exists_profile_cover L hcard htype U p0 hclosed hno

end Erdos1172Part3NamedShortCover
