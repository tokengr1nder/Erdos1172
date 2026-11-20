/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCohenCountableUnion
public import Erdos1172.Part4InternalNameSequence
public import Erdos1172.Part4CohenReadingExtension

@[expose] public section

/-!
# Same-condition countable decision fusion

Starting from a locally valid internal Cohen graph, actual mixed extensions
successively decide a prescribed countable family of completed Boolean
values. Every step is valid at the original first-stage Boolean condition.
The actual internal set of these graphs is countable and an inclusion chain,
so its union is again a condition. Readings persist under this strengthening.

The decisions remain Boolean disjunctions. No external choice of a binary
branch, external closure of the iteration preorder, generic filter, or
cardinal-preservation conclusion is asserted.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172CohenIteration

open bSet

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- One actual mixed extension simultaneously reads every member of a
countable family, with no loss of the original Boolean condition. -/
theorem exists_countable_deciding_extension {K q : bSet B} {Γ : B}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hq : Γ ≤ ErdosCohen.condition K q) (c : ℕ → Algebra K) :
    ∃ r : bSet B, Γ ≤ ErdosCohen.condition K r ∧ Γ ≤ q ⊆ᴮ r ∧
      ∀ n : ℕ, Γ ≤ reads (c n) r ⊔ reads (c n)ᶜ r := by
  classical
  let State := {r : bSet B // Γ ≤ ErdosCohen.condition K r}
  have Hextend (n : ℕ) (s : State) :
      ∃ t : State, Γ ≤ s.val ⊆ᴮ t.val ∧
        Γ ≤ reads (c n) t.val ⊔ reads (c n)ᶜ t.val := by
    obtain ⟨r, Hr, Hsub, Hread⟩ := exists_deciding_condition_extension s.property (c n)
    exact ⟨⟨r, Hr⟩, Hsub, Hread⟩
  choose next hnext using Hextend
  let states : ℕ → State := Nat.rec ⟨q, Hq⟩ next
  let s : ℕ → bSet B := fun n => (states n).val
  have Hstep (n : ℕ) : Γ ≤ s n ⊆ᴮ s (n + 1) ∧
      Γ ≤ reads (c n) (s (n + 1)) ⊔ reads (c n)ᶜ (s (n + 1)) :=
    hnext n (states n)
  have Hmono : ∀ n m : ℕ, m ≤ n → Γ ≤ s m ⊆ᴮ s n := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have heq : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      exact subset_self
    | succ n ih =>
      intro m hm
      rcases Nat.eq_or_lt_of_le hm with heq | hlt
      · subst m
        exact subset_self
      · exact subset_trans' (ih m (by omega)) (Hstep n).1
  let r : bSet B := bv_union (ErdosNameSequence.family s)
  have Hr : Γ ≤ ErdosCohen.condition K r :=
    ErdosCohen.condition_union_of_countable_chain HK
      (ErdosNameSequence.family_subset
        (fun n => ErdosCohen.mem_conditions_iff.mpr (states n).property))
      (ErdosNameSequence.family_inclusionChain (fun m n Hmn => Hmono n m Hmn))
      (ErdosNameSequence.family_countable s)
  refine ⟨r, Hr, ErdosNameSequence.term_subset_union s 0, ?_⟩
  intro n
  exact reads_decision_of_extension (ErdosNameSequence.term_subset_union s (n + 1))
    (ErdosCohen.mem_conditions_iff.mpr Hr) (Hstep n).2

end Erdos1172CohenIteration
