/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Flypitch4.Bfol

@[expose] public section

/-!
# Syntactic consistency from a nonzero local Boolean model

Boolean soundness applies below the value of the entire theory, not only
when that value is top. A supplied nonzero condition which forces every
sentence therefore suffices for consistency. The condition is neither
inferred to be nonzero nor replaced by top, and the structure is not
restricted or transported. This generic bridge constructs no Boolean
algebra, ideal, or model of an additional set-theoretic axiom.
-/

set_option autoImplicit false

universe u v

namespace Fol.ErdosLocalConsistency

open scoped Fol

variable {L : Language.{u}} {β : Type v} [CompleteBooleanAlgebra β]
variable {S : bStructure L β} [Nonempty S]
variable {T : SentTheory L} {Γ : β}

/-- Every syntactic consequence remains forced at the original local
condition. This is a direct composition with Boolean soundness. -/
theorem forces_consequence_of_forces_theory {A : sentence L}
    (Htheory : Γ ⊩ₜ[S] T) (Hproof : T ⊢ₛ' A) : Γ ⊩[S] A := by
  have Hsound : (⨅ f ∈ T, ⟦f⟧[S]) ≤ ⟦A⟧[S] :=
    boolean_soundness (β := β) Hproof (inferInstance : Nonempty S)
  exact le_trans Htheory Hsound

/-- A nonzero condition forcing the whole theory rules out a syntactic
proof of falsum. No separate nontriviality instance or top-forcing
hypothesis is needed: nonzeroness is supplied explicitly. -/
theorem consistent_of_nonzero_forces_theory
    (Hnonzero : Γ ≠ (⊥ : β)) (Htheory : Γ ⊩ₜ[S] T) : T.is_consistent := by
  intro Hcontradiction
  have Hfalse : Γ ⊩[S] (bd_falsum : sentence L) :=
    forces_consequence_of_forces_theory Htheory
      (show T ⊢ₛ' (bd_falsum : sentence L) from Hcontradiction)
  change Γ ≤ (⊥ : β) at Hfalse
  exact Hnonzero (le_antisymm Hfalse bot_le)

/-- Pointwise local forcing is sufficient, with the same condition for
all axioms. In particular no coherent choice of models per sentence is
used or permitted by this hypothesis. -/
theorem consistent_of_nonzero_forces_each
    (Hnonzero : Γ ≠ (⊥ : β))
    (Hsentences : ∀ f ∈ T, Γ ⊩[S] f) : T.is_consistent := by
  apply consistent_of_nonzero_forces_theory (S := S) Hnonzero
  show Γ ≤ ⨅ f ∈ T, ⟦f⟧[S]
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  exact Hsentences f hf

end Fol.ErdosLocalConsistency
