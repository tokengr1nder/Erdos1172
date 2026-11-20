/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanQuotientFactorEquivalence
public import Erdos1172.Part4PosetRetractionCompletion

@[expose] public section

/-! # Factoring a complete Boolean embedding through its quotient name

The evaluation of an iteration condition is a positive value in the
target algebra. Its canonical section gives a regular completion
isomorphism. Under this isomorphism the first-stage map is the given
complete homomorphism.
-/

set_option autoImplicit false

noncomputable section

namespace Erdos1172BooleanFactor

variable {B C : Type*} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

/-- The adjoint preserves a meet with an element from the embedded algebra. -/
theorem lowerProjection_inf_image (e : CompleteLatticeHom B C) (c : C) (b : B) :
    lowerProjection e (c ⊓ e b) = lowerProjection e c ⊓ b := by
  apply le_antisymm
  · exact le_inf (lowerProjection_mono e inf_le_left) (lowerProjection_le e inf_le_right)
  · have hc : c ≤ e (lowerProjection e (c ⊓ e b) ⊔ bᶜ) := by
      rw [map_sup, map_compl']
      calc
        c = (c ⊓ e b) ⊔ (c ⊓ (e b)ᶜ) := by
          rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
        _ ≤ e (lowerProjection e (c ⊓ e b)) ⊔ (e b)ᶜ :=
          sup_le_sup (le_image_lowerProjection e _) inf_le_right
    have hp := inf_le_inf_right b (lowerProjection_le e hc)
    rw [inf_sup_right, compl_inf_eq_bot, sup_bot_eq] at hp
    exact hp.trans inf_le_left

theorem lowerProjection_evaluation (e : CompleteLatticeHom B C) (p : FactorCondition e) :
    lowerProjection e (evaluation e p).val = p.source := by
  change lowerProjection e (e p.source ⊓ p.target) = p.source
  rw [inf_comm, lowerProjection_inf_image, inf_eq_right.mpr p.compatible]

end Erdos1172BooleanFactor

namespace Erdos1172BooleanQuotient

open Erdos1172BooleanFactor Erdos1172BooleanNameIteration Erdos1172PositiveBoolean
open Erdos1172PosetProjection Erdos1172PosetCompletion

universe u
variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

def iterationEvaluation (e : CompleteLatticeHom B C) :
    Condition (quotientName e) →o Positive C :=
  (evaluation e).comp ⟨factorOrderIso e, (factorOrderIso e).monotone⟩

def iterationSection (e : CompleteLatticeHom B C) :
    Positive C →o Condition (quotientName e) :=
  (⟨(factorOrderIso e).symm, (factorOrderIso e).symm.monotone⟩ :
    FactorCondition e →o Condition (quotientName e)).comp (canonicalSection e)

theorem iterationEvaluation_section (e : CompleteLatticeHom B C) (c : Positive C) :
    iterationEvaluation e (iterationSection e c) = c :=
  evaluation_section e c

theorem iterationSection_evaluation_le (e : CompleteLatticeHom B C)
    (p : Condition (quotientName e)) :
    iterationSection e (iterationEvaluation e p) ≤ p :=
  (factorOrderIso e).le_iff_le.mp (section_evaluation_le e (factorOrderIso e p))

theorem iterationEvaluation_lifts (e : CompleteLatticeHom B C) :
    ExactLifts (iterationEvaluation e) := by
  intro p c hc
  exact ⟨iterationSection e c,
    ((iterationSection e).monotone hc).trans (iterationSection_evaluation_le e p),
    iterationEvaluation_section e c⟩

/-- The target algebra is the regular completion of the actual name iteration. -/
def factorization (e : CompleteLatticeHom B C) : C ≃o Algebra (quotientName e) :=
  Erdos1172PositiveBoolean.completionOrderIso.trans
    (retractionCompletionOrderIso (iterationEvaluation e) (iterationEvaluation_lifts e)
      (iterationSection e) (iterationEvaluation_section e) (iterationSection_evaluation_le e))

def firstStage (e : CompleteLatticeHom B C) : CompleteLatticeHom B (Algebra (quotientName e)) :=
  (firstStageHom (quotientName e)).comp Erdos1172PositiveBoolean.completionHom

/-- A canonical section value supplies an actual condition for this completion. -/
instance quotientAlgebraNontrivial (e : CompleteLatticeHom B C) :
    NontrivialCompleteBooleanAlgebra (Algebra (quotientName e)) := by
  letI : Nonempty (Condition (quotientName e)) := ⟨iterationSection e (topLabel C)⟩
  exact { toCompleteBooleanAlgebra := inferInstance, bot_lt_top := bot_lt_top }

/-- The canonical first-stage embedding of the name iteration is the given map
after identifying the ambient forcing with the completion of the iteration. -/
theorem factorization_image (e : CompleteLatticeHom B C) (b : B) :
    factorization e (e b) = firstStage e b := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  change (evaluation e (factorOrderIso e p)).val ≤ e b ↔ (toFactor e p).source ≤ b
  rw [← lowerProjection_le_iff, lowerProjection_evaluation]
  rfl

end Erdos1172BooleanQuotient
