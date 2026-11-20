/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerNormality

@[expose] public section

/-! # Bounded evaluation of named rows at the critical seed -/

set_option autoImplicit false
noncomputable section
universe u
open Filter bSet Lattice
open scoped Flypitch
namespace Erdos1172BooleanUltrapower
variable {I B : Type u} [NontrivialCompleteBooleanAlgebra B] (U : Ultrafilter I)
variable [CountableInterFilter (U : Filter I)]
local notation "V" => Algebra U B

/-- A bounded existential over the lifted set ranges over all target names.
Its value is computed by Łoś when the predicate is extensional and is
already known to commute on represented elements. -/
theorem hereditary_bounded_evaluation (F : I → bSet B) (P : I → bSet B → B) (Q : bSet V → V)
    (pExt : ∀ i, B_ext (P i)) (qExt : B_ext Q)
    (commutes : ∀ X : I → bSet B, value U (fun i => P i (X i)) = Q (hereditary U X)) :
    value U (fun i => ⨆ x : bSet B, (x ∈ᴮ F i) ⊓ P i x) =
      ⨆ z : bSet V, (z ∈ᴮ hereditary U F) ⊓ Q z := by
  have source (i : I) : (⨆ x : bSet B, (x ∈ᴮ F i) ⊓ P i x) =
      ⨆ k : (F i).type, (F i).bval k ⊓ P i ((F i).func k) :=
    (bounded_exists (h_congr := pExt i)).symm
  have target : (⨆ z : bSet V, (z ∈ᴮ hereditary U F) ⊓ Q z) =
      ⨆ a : Children U F, value U (weight U F a) ⊓ Q (hereditary U (child U F a)) := by
    apply (bounded_exists (v := hereditary U F) (h_congr := qExt)).symm.trans
    conv_lhs => rw [show hereditary U F = _ from liftName_eq U _ F]
    rfl
  rw [target]
  calc
    _ = _ := congrArg (value U) (funext source)
    _ = _ := value_bounded_exists U F P
    _ = _ := iSup_congr fun a => congrArg (value U (weight U F a) ⊓ ·) (commutes (child U F a))

end Erdos1172BooleanUltrapower
