/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularGreedyEnumeration
public import Erdos1172.Part3NamedCofinality
public import Erdos1172.Part3FinalPowerTail
public import Erdos1172.Part3ClosedDenseRequirements

@[expose] public section

/-!
# Short cofinal names have a fixed finite-power final domain

Absence of a full omega-successor embedding yields a complete shorter
enumeration on a strengthening. Named cofinality and countable closure
force the ground enumeration domain to have cofinality alephOne. Its
ordinal type therefore has a final finite-power summand.

This retains the actual ordered decision system and dense exact coverage;
it does not replace the name by a fixed-condition possible set.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedShortEnumeration

open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3RegularGreedyEnumeration
open Erdos1172Part3NamedCofinality
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)

variable {P I V : Type} [Preorder P] [LinearOrder I] [WellFoundedLT I]
  [LinearOrder V] [WellFoundedLT V]

theorem exists_shorter_cofinal_enumeration (U : RegularName P V) (p0 : P)
    (hclosed : CountablyClosed P) (hI : #I ≤ ℵ_ 1)
    (hItype : typeLT I = (ω_ 1 : Ordinal.{0}) ^ (ω + 1))
    (hVcof : Order.cof V = ℵ_ 1)
    (hcofinal : ∀ p : P, p ≤ p0 → ∀ cut : V, ∃ q : P, q ≤ p ∧ ∃ x : V, U.holds q x ∧ cut ≤ x)
    (hno : ¬HasOrderedEmbeddingBelow (I := I) U p0) :
    ∃ q : P, q ≤ p0 ∧ ∃ i : I,
      ∃ E : FunctionDecisions (Set.Iic q) (Set.Iio i) V,
        OrderedDecisions E ∧ CofinalDecisions E ∧
        (∀ p : Set.Iic q, ∀ j x, E.decides p j x → U.holds p.val x) ∧
        (∀ p : Set.Iic q, ∀ x : V, U.holds p.val x →
          ∃ r : Set.Iic q, r ≤ p ∧ ∃ j : Set.Iio i, E.decides r j x) ∧
        ∃ ζ : Ordinal.{0}, ∃ n : ℕ,
          typeLT (Set.Iio i) = ζ + (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
  obtain ⟨q, hqp0, i, E, horder, hactual, hcover⟩ := exists_shorter_enumeration U p0 hno
  have hord : OrderedDecisions E := fun {p j k x y} hjk hx hy => horder p j k x y hjk hx hy
  have hcof : CofinalDecisions E := by
    intro p cut
    obtain ⟨s, hsp, x, hx, hcut⟩ := hcofinal p.val (p.property.trans hqp0) cut
    obtain ⟨t, hts, j, ht⟩ := hcover ⟨s, hsp.trans p.property⟩ x hx
    exact ⟨t, hts.trans hsp, j, x, ht, hcut⟩
  have hdomain : (typeLT (Set.Iio i)).cof = ℵ_ 1 :=
    cof_typeLT_domain_eq_alephOne E
      (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q)
      ⟨q, le_rfl⟩ hord hcof ((Cardinal.mk_set_le (Set.Iio i)).trans hI) hVcof
  have hsmall : typeLT (Set.Iio i) < (ω_ 1 : Ordinal.{0}) ^ (ω + 1) := by
    rw [Ordinal.type_Iio_lt]
    exact (Ordinal.typein_lt_type _ i).trans_eq hItype
  exact ⟨q, hqp0, i, E, hord, hcof, hactual, hcover,
    Erdos1172Part3FinalPowerTail.exists_final_power_tail hsmall hdomain⟩

end Erdos1172Part3NamedShortEnumeration
