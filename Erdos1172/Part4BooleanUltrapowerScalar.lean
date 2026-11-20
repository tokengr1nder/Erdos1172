/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerAtomic
public import Erdos1172.Part4BooleanQuotientFactorization
public import Erdos1172.Part4BooleanNameTransport

@[expose] public section

/-! # Scalar extension on the complete Boolean ultrapower -/

set_option autoImplicit false
noncomputable section
universe u
open Filter Erdos1172PositiveBoolean Erdos1172BooleanFactor Erdos1172PosetProjection
namespace Erdos1172BooleanUltrapower
variable {I B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable (U : Ultrafilter I) (e : CompleteLatticeHom B C)
local notation "gB" => Germ (U : Filter I) B
local notation "gC" => Germ (U : Filter I) C
local notation "π" => Germ.map (l := (U : Filter I)) (lowerProjection e)
local notation "ι" => Germ.map (l := (U : Filter I)) (fun b => e b)

theorem germ_lower_adjunction (x : gC) (y : gB) : π x ≤ y ↔ x ≤ ι y := by
  induction x, y using Germ.inductionOn₂ with | h f g =>
    change (∀ᶠ i in U, lowerProjection e (f i) ≤ g i) ↔ ∀ᶠ i in U, f i ≤ e (g i)
    simp only [lowerProjection_le_iff]

private theorem lower_bot : π (⊥ : gC) = (⊥ : gB) := Germ.coe_eq.mpr (Eventually.of_forall fun _ =>
  bot_unique (lowerProjection_le e bot_le))

theorem germLower_ne {x : gC} (hx : x ≠ ⊥) : π x ≠ ⊥ := by
  intro h
  apply hx
  have b := (germ_lower_adjunction U e x ⊥).mp h.le
  have bot : ι (⊥ : gB) = (⊥ : gC) := Germ.coe_eq.mpr (Eventually.of_forall fun _ => map_bot e)
  exact bot_unique (b.trans_eq bot)

include e in
def germLowerProjection : Positive gC →o Positive gB where
  toFun p := ⟨π p.val,germLower_ne U e p.property⟩
  monotone' := fun p q h => (germ_lower_adjunction U e p.val (π q.val)).mpr
    ((show p.val ≤ q.val from h).trans ((germ_lower_adjunction U e q.val (π q.val)).mp le_rfl))

theorem germLower_exact : ExactLifts (germLowerProjection U e) := by
  intro p q h
  have split (x : gC) (y : gB) : π (x ⊓ ι y) = π x ⊓ y := by
    induction x, y using Germ.inductionOn₂ with | h f g =>
      exact Germ.coe_eq.mpr (Eventually.of_forall fun i => lowerProjection_inf_image e (f i) (g i))
  have eq : π (p.val ⊓ ι q.val) = q.val := (split _ _).trans (inf_eq_right.mpr h)
  have pos : p.val ⊓ ι q.val ≠ ⊥ := fun hn => q.property (eq.symm.trans ((congrArg (π) hn).trans (lower_bot U e)))
  exact ⟨⟨_,pos⟩,show p.val ⊓ ι q.val ≤ p.val from inf_le_left,Subtype.ext eq⟩

include e in
/-- A complete scalar hom induces a complete hom on the regular completions
of Boolean germs. The lower projection has exact lifts on positive germs. -/
def scalarHom : CompleteLatticeHom (Algebra U B) (Algebra U C) :=
  Erdos1172PosetProjection.completionHom (germLowerProjection U e) (germLower_exact U e)

theorem scalarHom_value (f : I → B) :
    scalarHom U e (value U f) = value U (fun i => e (f i)) := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  exact germ_lower_adjunction U e p.val (Germ.ofFun f)

open bSet ErdosNameTransport
open scoped Flypitch
variable [CountableInterFilter (U : Filter I)]

theorem scalarHom_hereditary_mem (X Y : I → bSet B) :
    scalarHom U e (hereditary U X ∈ᴮ hereditary U Y) =
      (hereditary U (fun i => mapNames e (X i)) ∈ᴮ hereditary U (fun i => mapNames e (Y i))) := by
  rw [← value_name_mem,scalarHom_value,← value_name_mem]
  exact congrArg (value U) (_root_.funext fun i => map_mem e (X i) (Y i))

theorem scalarHom_hereditary_eq (X Y : I → bSet B) :
    scalarHom U e (hereditary U X =ᴮ hereditary U Y) =
      (hereditary U (fun i => mapNames e (X i)) =ᴮ hereditary U (fun i => mapNames e (Y i))) := by
  rw [← value_name_eq,scalarHom_value,← value_name_eq]
  exact congrArg (value U) (_root_.funext fun i => map_bv_eq e (X i) (Y i))

end Erdos1172BooleanUltrapower
