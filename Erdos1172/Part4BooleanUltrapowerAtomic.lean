/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerNames

@[expose] public section

/-! # Boolean truth values in the hereditary ultrapower of forcing names

Bounded quantifiers range over sections defined on ultrafilter-large sets.
Applying their truth-value formulas recursively computes equality and
membership for arbitrary families of forcing names.
-/

set_option autoImplicit false
noncomputable section
open Filter bSet
open scoped Flypitch
universe u

namespace Erdos1172BooleanUltrapower

variable {I B : Type u} [NontrivialCompleteBooleanAlgebra B] (U : Ultrafilter I)

theorem value_imp (f g : I → B) :
    value U (fun i => f i ⟹ g i) = (value U f ⟹ value U g) := by
  unfold imp
  rw [value_sup, value_compl]

theorem value_bounded_exists (X : I → bSet B) (P : I → bSet B → B) :
    value U (fun i => ⨆ k, (X i).bval k ⊓ P i ((X i).func k)) =
      ⨆ a : Children U X, value U (weight U X a) ⊓ value U (fun i => P i (child U X a i)) := by
  classical
  rw [value_iSup U (fun i => (X i).type) (fun i k => (X i).bval k ⊓ P i ((X i).func k))]
  apply iSup_congr
  intro a
  rw [← value_inf]
  apply value_eq_of_eventuallyEq
  filter_upwards [a.large] with i hi
  simp only [weight, selected, child, dif_pos hi]

theorem value_bounded_forall (X : I → bSet B) (P : I → bSet B → B) :
    value U (fun i => ⨅ k, (X i).bval k ⟹ P i ((X i).func k)) =
      ⨅ a : Children U X, value U (weight U X a) ⟹ value U (fun i => P i (child U X a i)) := by
  classical
  rw [value_iInf U (fun i => (X i).type) (fun i k => (X i).bval k ⟹ P i ((X i).func k))]
  apply iInf_congr
  intro a
  rw [← value_imp]
  apply value_eq_of_eventuallyEq
  filter_upwards [a.large] with i hi
  simp only [weight, selectedTop, selected, child, dif_pos hi]

def half {A : Type u} [NontrivialCompleteBooleanAlgebra A]
    (x y : bSet A) (r : bSet A → bSet A → A) : A :=
  ⨅ k, x.bval k ⟹ ⨆ l, y.bval l ⊓ r (x.func k) (y.func l)

private theorem equality_halves {A : Type u} [NontrivialCompleteBooleanAlgebra A]
    (x y : bSet A) :
    (x =ᴮ y) = half x y bv_eq ⊓ half y x (fun v w => w =ᴮ v) := by
  cases x
  cases y
  rfl

private theorem value_half (X Y : I → bSet B) (r : bSet B → bSet B → B) :
    value U (fun i => half (X i) (Y i) r) =
      ⨅ a : Children U X, value U (weight U X a) ⟹
        ⨆ b : Children U Y, value U (weight U Y b) ⊓
          value U (fun i => r (child U X a i) (child U Y b i)) := by
  unfold half
  rw [value_bounded_forall U X (fun i x => ⨆ l, (Y i).bval l ⊓ r x ((Y i).func l))]
  apply iInf_congr
  intro a
  rw [value_bounded_exists U Y (fun i y => r (child U X a i) y)]

variable [CountableInterFilter (U : Filter I)]

abbrev hereditary (X : I → bSet B) : bSet (Algebra U B) := liftName U (value U) X

private theorem hereditary_half (X Y : I → bSet B)
    (r : bSet (Algebra U B) → bSet (Algebra U B) → Algebra U B) :
    half (hereditary U X) (hereditary U Y) r =
      ⨅ a : Children U X, value U (weight U X a) ⟹
        ⨆ b : Children U Y, value U (weight U Y b) ⊓
          r (hereditary U (child U X a)) (hereditary U (child U Y b)) := by
  unfold hereditary
  conv_lhs => rw [liftName_eq U _ X, liftName_eq U _ Y]
  rfl

theorem value_name_eq (X Y : I → bSet B) :
    value U (fun i => X i =ᴮ Y i) = (hereditary U X =ᴮ hereditary U Y) := by
  induction X using (familyChild_wf U).induction generalizing Y with
  | h X ih =>
    simp only [equality_halves (X _) (Y _), value_inf, value_half,
      equality_halves (hereditary U X) (hereditary U Y), hereditary_half]
    apply congrArg₂ (· ⊓ ·)
    · apply iInf_congr
      intro a
      apply congrArg (imp _)
      apply iSup_congr
      intro b
      exact congrArg (_ ⊓ ·) (ih _ (child_lt U X a) (child U Y b))
    · apply iInf_congr
      intro b
      apply congrArg (imp _)
      apply iSup_congr
      intro a
      exact congrArg (_ ⊓ ·) (ih _ (child_lt U X a) (child U Y b))

theorem value_name_mem (X Y : I → bSet B) :
    value U (fun i => X i ∈ᴮ Y i) = (hereditary U X ∈ᴮ hereditary U Y) := by
  simp only [mem_unfold]
  rw [value_bounded_exists U Y (fun i y => X i =ᴮ y)]
  conv_rhs => rw [show hereditary U Y = _ from liftName_eq U _ Y]
  apply iSup_congr
  intro b
  exact congrArg (_ ⊓ ·) (value_name_eq U X (child U Y b))

theorem value_name_subset (X Y : I → bSet B) :
    value U (fun i => X i ⊆ᴮ Y i) = (hereditary U X ⊆ᴮ hereditary U Y) := by
  simp only [subset_unfold]
  rw [value_bounded_forall U X (fun i x => x ∈ᴮ Y i)]
  conv_rhs => rw [show hereditary U X = _ from liftName_eq U _ X]
  apply iInf_congr
  intro a
  exact congrArg (imp _) (value_name_mem U (child U X a) Y)

end Erdos1172BooleanUltrapower
