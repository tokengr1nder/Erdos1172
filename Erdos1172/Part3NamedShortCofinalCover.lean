/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedOptionalCovers
public import Erdos1172.Part3NamedFiniteTail

@[expose] public section

/-!
# Fixed bounded-prefix profiles cover short cofinal regular names

Choose the optional named finite-power families once, before considering
any condition order or source name. A cofinal source with no full
omega-successor ordered embedding has a named finite-power final tail.
Its covering name, together with one fixed cut for the discarded prefix,
covers the entire original source on a strengthening.

Every member of the fixed profile family has strictly short whole-set
order type and finite membership support. The theorem here covers
explicitly cofinal sources; no noncofinal covering claim is inferred.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedShortCofinalCover

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3NamedLocalRowCover (onConeDecisions)
open Erdos1172Part3NamedCofinalRowCovers
  (nestCone flattenDecisions coverName_flatten_iff)
open Erdos1172Part3SupportedCoverRealization (coverName)
open Erdos1172Part3CofinalCoverSupport (FinitelySupported)
open Erdos1172Part3BoundedPrefixCovers
  (withPrefix withPrefix_mono withPrefix_supported withPrefix_type_lt)
open Erdos1172Part3NamedOptionalCovers
  (OptionalNamedCofinalCovers coverName_withPrefix_of_or)

variable {P X : Type} [Preorder P]

/-- Restricting function decisions to a cone preserves actual cover
membership exactly, including all subsequent dense refinements. -/
theorem coverName_onCone_iff (q : P) (F : FunctionDecisions P W1 W1)
    (C : (W1 → W1) → Set X) (p : Set.Iic q) (x : X) :
    (coverName (onConeDecisions F q) C).holds p x ↔ (coverName F C).holds p.val x := by
  constructor
  · intro hx s hsp
    obtain ⟨t, hts, ht⟩ := hx ⟨s, hsp.trans p.property⟩ hsp
    exact ⟨t.val, hts, ht⟩
  · intro hx s hsp
    obtain ⟨t, hts, ht⟩ := hx s.val hsp
    exact ⟨⟨t, hts.trans s.property⟩, hts, ht⟩

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

/-- The cut and finite rank are ground profile parameters. The optional
named cover families are fixed before the condition order is chosen. -/
def profileFamily (L : ∀ n : ℕ, OptionalNamedCofinalCovers n V)
    (e : V × ℕ) : (W1 → W1) → Set V :=
  withPrefix (L e.2).toOptionalCofinalCovers e.1

theorem profileFamily_mono (L : ∀ n : ℕ, OptionalNamedCofinalCovers n V)
    (e : V × ℕ) : Monotone (profileFamily L e) :=
  withPrefix_mono _ _

theorem profileFamily_supported (L : ∀ n : ℕ, OptionalNamedCofinalCovers n V)
    (e : V × ℕ) : FinitelySupported (profileFamily L e) :=
  withPrefix_supported _ _

theorem profileFamily_type_lt (L : ∀ n : ℕ, OptionalNamedCofinalCovers n V)
    (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (e : V × ℕ) (f : W1 → W1) :
    typeLT (profileFamily L e f) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) :=
  withPrefix_type_lt _ _ htype f

/-- Bounded prefix members have an empty finite certificate for every
function name, a fact independent of named cofinality. -/
theorem profileFamily_holds_of_lt (L : ∀ n : ℕ, OptionalNamedCofinalCovers n V)
    (F : FunctionDecisions P W1 W1) (e : V × ℕ) (p : P) (x : V)
    (hx : x < e.1) : (coverName F (profileFamily L e)).holds p x :=
  coverName_withPrefix_of_or (L e.2).toOptionalCofinalCovers F e.1 (Or.inl hx)

/-- The same previously fixed profile family covers any short cofinal
regular name on a countably closed order, after one strengthening. -/
theorem exists_cofinal_profile_cover
    (L : ∀ n : ℕ, OptionalNamedCofinalCovers n V)
    (hcard : #V ≤ ℵ_ 1) (htype : typeLT V = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (U : RegularName P V) (p0 : P) (hclosed : CountablyClosed P)
    (hcofinal : ∀ p : P, p ≤ p0 → ∀ cut : V,
      ∃ q : P, q ≤ p ∧ ∃ x : V, U.holds q x ∧ cut ≤ x)
    (hno : ¬Erdos1172Part3RegularGreedyEnumeration.HasOrderedEmbeddingBelow
      (I := V) U p0) :
    ∃ r : P, r ≤ p0 ∧ ∃ e : V × ℕ,
      ∃ F : FunctionDecisions (Set.Iic r) W1 W1,
        ∀ p : Set.Iic r, ∀ x : V, U.holds p.val x →
          (coverName F (profileFamily L e)).holds p x := by
  have hVcof : Order.cof V = ℵ_ 1 := by
    rw [← Ordinal.cof_type V, htype]
    exact Erdos1172Part3FinalPowerTail.cof_omegaSuccessor
  obtain ⟨q, hqp0, n, E, T, hordered, hcofinalT, hcoverage, hmem, -, r, cut, -, hrest⟩ :=
    Erdos1172Part3NamedFiniteTail.exists_cofinal_finite_tail (I := V)
      U p0 hclosed hcard htype hVcof hcofinal hno
  obtain ⟨F, hF⟩ := (L n).named_covers (Set.Iic q)
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q)
    T E hordered hcofinalT hcoverage hmem
  let Fcone : FunctionDecisions (Set.Iic r) W1 W1 := onConeDecisions F r
  let H : FunctionDecisions (Set.Iic r.val) W1 W1 := flattenDecisions r Fcone
  refine ⟨r.val, r.property.trans hqp0, (cut, n), H, ?_⟩
  intro p x hx
  apply (coverName_flatten_iff r Fcone (profileFamily L (cut, n)) p x).mpr
  apply (coverName_onCone_iff r F (profileFamily L (cut, n)) (nestCone r p) x).mpr
  apply coverName_withPrefix_of_or (L n).toOptionalCofinalCovers F cut
  rcases hrest (nestCone r p).val (nestCone r p).property x hx with hprefix | htail
  · exact Or.inl hprefix
  · exact Or.inr (hF (nestCone r p).val x htail)

end Erdos1172Part3NamedShortCofinalCover
