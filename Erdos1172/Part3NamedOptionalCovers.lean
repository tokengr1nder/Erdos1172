/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3BoundedPrefixCovers
public import Erdos1172.Part3NamedCofinalPowerCovers
public import Erdos1172.Part3NamedCofinalRealization
public import Erdos1172.Part3SupportedCoverRealization

@[expose] public section

/-!
# Optional cofinal covers with actual named completeness

The empty fallback is legitimate for names as well as ground sets: an
ordered cofinal enumeration on a countably closed condition order yields
a ground cofinal set of the same type below any given condition. Thus a
missing ground seed also precludes the corresponding named enumeration.

Adding a fixed bounded prefix preserves actual cover membership with
the very same function name. The prefix uses the empty certificate; a
certificate for the original family also certifies the enlarged family.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedOptionalCovers

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FiniteTraceSchemes (Index typeLT_index mk_index_le)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName)
open Erdos1172Part3NamedCofinality (OrderedDecisions CofinalDecisions)
open Erdos1172Part3NamedFinalTail (DenseCoverage)
open Erdos1172Part3SupportedCoverRealization (coverName holds_of_certificate)
open Erdos1172Part3BoundedPrefixCovers (OptionalCofinalCovers withPrefix)

/-- An optional ground cofinal family together with actual named
completeness for precisely the same family. -/
structure OptionalNamedCofinalCovers (n : ℕ) (V : Type)
    [LinearOrder V] [WellFoundedLT V] extends OptionalCofinalCovers n V where
  named_covers : ∀ (P : Type) [Preorder P] (hclosed : CountablyClosed P)
    (U : RegularName P V) (E : FunctionDecisions P (Index n) V),
    OrderedDecisions E → CofinalDecisions E → DenseCoverage E U →
    (∀ p j x, E.decides p j x → U.holds p x) →
      ∃ F : FunctionDecisions P W1 W1,
        ∀ p x, U.holds p x → (coverName F family).holds p x

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

/-- Optional named cofinal families exist at every finite rank, without
a ground seed assumption on the ambient well-order. -/
theorem exists_optionalNamedCofinalCovers (hV : #V ≤ ℵ_ 1) (n : ℕ) :
    Nonempty (OptionalNamedCofinalCovers n V) := by
  classical
  by_cases hseed : ∃ A : Set V, IsCofinal A ∧
      typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)
  · obtain ⟨C⟩ :=
      Erdos1172Part3NamedCofinalPowerCovers.exists_namedCofinalCovers n V hV hseed
    exact ⟨{
      family := C.family
      mono := C.mono
      supported := C.supported
      type_le := fun f => (C.orderType f).le
      covers := C.covers
      named_covers := C.named_covers }⟩
  · refine ⟨{
      family := fun _ => ∅
      mono := fun _ _ _ => Set.Subset.rfl
      supported := Erdos1172Part3CofinalCoverSupport.constant_supported ∅
      type_le := ?_
      covers := ?_
      named_covers := ?_ }⟩
    · intro f
      rw [Ordinal.type_eq_zero_of_empty]
      exact zero_le
    · intro A hA htype
      exact (hseed ⟨A, hA, htype⟩).elim
    · intro P instP hclosed U E hordered hcofinal _hcoverage _hmem
      refine ⟨FunctionDecisions.ofFunction
        (fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩), ?_⟩
      intro p x _hx
      obtain ⟨A, hA, hAtype⟩ :=
        Erdos1172Part3NamedCofinalRealization.exists_ground_cofinal_set E hclosed p
          (mk_index_le n) hV hordered hcofinal
      exact (hseed ⟨A, hA, hAtype.trans (typeLT_index n)⟩).elim

/-- All optional finite-rank families may be chosen before considering
any particular regular name or condition order. -/
theorem exists_optionalNamedCofinalFamily (hV : #V ≤ ℵ_ 1) :
    Nonempty (∀ n : ℕ, OptionalNamedCofinalCovers n V) :=
  ⟨fun n => Classical.choice (exists_optionalNamedCofinalCovers hV n)⟩

variable {P : Type} [Preorder P] {n : ℕ}

/-- A ground point of the prefix has an empty membership certificate,
independently of the values of the function name. -/
theorem coverName_withPrefix_of_lt (C : OptionalCofinalCovers n V)
    (F : FunctionDecisions P W1 W1) (cut : V) {p : P} {x : V}
    (hx : x < cut) : (coverName F (withPrefix C cut)).holds p x := by
  apply holds_of_certificate
  refine ⟨(fun _ => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩), ∅, by simp, ?_⟩
  intro g _hg
  exact Or.inl hx

/-- Actual family membership transfers to the enlarged family without
changing either the condition or the function name. -/
theorem coverName_withPrefix_of_family (C : OptionalCofinalCovers n V)
    (F : FunctionDecisions P W1 W1) (cut : V) {p : P} {x : V}
    (hx : (coverName F C.family).holds p x) :
    (coverName F (withPrefix C cut)).holds p x := by
  intro q hqp
  obtain ⟨r, hrq, f, support, hdec, hcover⟩ := hx q hqp
  exact ⟨r, hrq, f, support, hdec, fun g hg => Or.inr (hcover g hg)⟩

/-- Ground prefix membership or actual membership in the original
family suffices for actual membership in its bounded-prefix extension. -/
theorem coverName_withPrefix_of_or (C : OptionalCofinalCovers n V)
    (F : FunctionDecisions P W1 W1) (cut : V) {p : P} {x : V}
    (hx : x < cut ∨ (coverName F C.family).holds p x) :
    (coverName F (withPrefix C cut)).holds p x := by
  rcases hx with hx | hx
  · exact coverName_withPrefix_of_lt C F cut hx
  · exact coverName_withPrefix_of_family C F cut hx

end Erdos1172Part3NamedOptionalCovers
