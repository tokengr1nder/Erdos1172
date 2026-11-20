/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedCofinalEndpoint
public import Erdos1172.Part3DecisionSelection
public import Erdos1172.Part3FunctionDecisions

@[expose] public section

/-!
# Coherent endpoint decisions for bounded regular names

Every selected endpoint retains its fixed ground bound, its strict upper
bound property, and dense cofinality of actual members below it. This is
a persistent dense relation, so coherent decision selection applies.
Countable closure is used only when simultaneously deciding a countable
family of endpoints. The resulting ground map retains all three properties
at every later condition.

No nonemptiness or limit-endpoint premise is imposed. Empty names force an
endpoint with no predecessors. A singleton name has its unique member as
the greatest point strictly below its endpoint.
-/

open Cardinal Set

namespace Erdos1172Part3NamedEndpointSelection

open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3NamedCofinalEndpoint
  (Upper CofinalBelow upper_persistent cofinalBelow_persistent exists_cofinal_endpoint)

variable {P J V : Type} [Preorder P] [LinearOrder V]

/-- A selected endpoint is bounded, strictly bounds every future actual
member, and has actual members densely cofinal below it. -/
def EndpointAt (U : J → RegularName P V) (bound : J → V)
    (p : P) (j : J) (y : V) : Prop :=
  y ≤ bound j ∧ Upper (U j) p y ∧ CofinalBelow (U j) p y

theorem endpointAt_persistent {U : J → RegularName P V} {bound : J → V}
    {p q : P} {j : J} {y : V} (hqp : q ≤ p) (h : EndpointAt U bound p j y) :
    EndpointAt U bound q j y :=
  ⟨h.1, upper_persistent hqp h.2.1, cofinalBelow_persistent hqp h.2.2⟩

/-- The endpoint of an everywhere empty name has no point strictly below
it; no nonempty-source assumption is hidden in endpoint selection. -/
theorem endpointAt_empty {U : J → RegularName P V} {bound : J → V}
    {p : P} {j : J} {y : V} (h : EndpointAt U bound p j y)
    (hempty : ∀ q : P, ∀ x : V, ¬(U j).holds q x) : ∀ z : V, y ≤ z := by
  intro z
  apply le_of_not_gt
  intro hzy
  obtain ⟨s, -, x, hx, -, -⟩ := h.2.2 p le_rfl z hzy
  exact hempty s x hx

/-- Singleton names retain their actual last member. The cofinality
witness below a successor endpoint is non-strict at the test point. -/
theorem endpointAt_singleton {U : J → RegularName P V} {bound : J → V}
    {p : P} {j : J} {y a : V} (h : EndpointAt U bound p j y)
    (hsingle : ∀ q : P, ∀ x : V, (U j).holds q x ↔ x = a) :
    a < y ∧ ∀ z : V, z < y → z ≤ a := by
  refine ⟨h.2.1 p le_rfl a ((hsingle p a).mpr rfl), ?_⟩
  intro z hzy
  obtain ⟨s, -, x, hx, hzx, -⟩ := h.2.2 p le_rfl z hzy
  exact (hsingle s x).mp hx ▸ hzx

variable [WellFoundedLT V]

theorem endpointAt_dense (U : J → RegularName P V) (bound : J → V)
    (hbound : ∀ j : J, ∀ p : P, Upper (U j) p (bound j)) :
    ∀ p : P, ∀ j : J, ∃ q : P, q ≤ p ∧ ∃ y : V, EndpointAt U bound q j y := by
  intro p j
  obtain ⟨q, hqp, y, hybound, hyupper, hycofinal⟩ :=
    exists_cofinal_endpoint (U j) p (bound j) (hbound j p)
  exact ⟨q, hqp, y, hybound, hyupper, hycofinal⟩

/-- Coherent endpoint decisions are constructed from the proved dense
relation, not supplied as an endpoint-name assumption. -/
theorem exists_endpoint_decisions (U : J → RegularName P V) (bound : J → V)
    (hbound : ∀ j : J, ∀ p : P, Upper (U j) p (bound j)) :
    ∃ D : FunctionDecisions P J V,
      ∀ p : P, ∀ j : J, ∀ y : V, D.decides p j y → EndpointAt U bound p j y :=
  Erdos1172Part3DecisionSelection.exists_function_decisions_of_dense (EndpointAt U bound)
    (fun {_ _ _ _} hqp h => endpointAt_persistent hqp h)
    (endpointAt_dense U bound hbound)

/-- A countable family of endpoints is decided simultaneously. The
ground endpoint map has its full endpoint properties at the chosen
condition and every strengthening, including for an empty index family. -/
theorem exists_countable_endpoints (U : J → RegularName P V) (bound : J → V)
    (hbound : ∀ j : J, ∀ p : P, Upper (U j) p (bound j))
    (hclosed : CountablyClosed P) (hJ : #J ≤ ℵ₀) (p0 : P) :
    ∃ q : P, q ≤ p0 ∧ ∃ endpoint : J → V,
      (∀ j : J, EndpointAt U bound q j (endpoint j)) ∧
      ∀ r : P, r ≤ q → ∀ j : J, EndpointAt U bound r j (endpoint j) := by
  classical
  obtain ⟨D, hD⟩ := exists_endpoint_decisions U bound hbound
  obtain ⟨q, hqp0, hvalues⟩ := D.exists_simultaneous hclosed p0 hJ
  choose endpoint hdec using hvalues
  have hendpoint (j : J) : EndpointAt U bound q j (endpoint j) :=
    hD q j (endpoint j) (hdec j)
  exact ⟨q, hqp0, endpoint, hendpoint,
    fun r hrq j => endpointAt_persistent hrq (hendpoint j)⟩

end Erdos1172Part3NamedEndpointSelection
