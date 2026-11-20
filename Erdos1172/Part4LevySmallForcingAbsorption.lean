/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaDenseCoverIso

@[expose] public section

/-! # Absorption of a small forcing by one countable Lévy collapse -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion Erdos1172PositiveBoolean Erdos1172Collapse Cardinal
universe u
namespace Erdos1172LevyCollapse.Absorption

variable {B X : Type u} [CompleteBooleanAlgebra B] (d : X → Positive B)
local notation "Tree" => Erdos1172Collapse.Condition X
local notation "Target" => Positive B × Erdos1172Collapse.Condition X

def piece (p : Positive B) (x : X × Bool) : B :=
  p.val ⊓ (if x.2 then (d x.1).val else (d x.1).valᶜ)

def Live (p : Positive B) := {x : X × Bool // piece d p x ≠ ⊥}

theorem one_piece (p : Positive B) (x : X) : ∃ b, piece d p (x,b) ≠ ⊥ := by
  classical
  by_cases h : p.val ⊓ (d x).val = ⊥
  · refine ⟨false,?_⟩
    have le := le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h)
    simpa only [piece,Bool.false_eq_true,if_false,inf_eq_left.mpr le] using p.property
  · exact ⟨true,h⟩

def alphabet (hX : ℵ₀ ≤ #X) (p : Positive B) : X ≃ Live d p := by
  let liftLetter (x : X) : Live d p := ⟨(x,(one_piece d p x).choose),(one_piece d p x).choose_spec⟩
  have inj : Function.Injective liftLetter := fun _ _ h => congrArg (fun z : Live d p => z.val.1) h
  apply Classical.choice
  apply Cardinal.eq.mp
  apply le_antisymm (Cardinal.mk_le_of_injective inj)
  apply (Cardinal.mk_le_of_injective (f := (Subtype.val : Live d p → X × Bool)) Subtype.val_injective).trans
  rw [Cardinal.mk_prod]
  simpa using (mul_le_mul' (le_refl (#X)) ((Cardinal.natCast_le_aleph0 (n := 2)).trans hX)).trans_eq
    (Cardinal.mul_eq_self hX)

variable (hX : ℵ₀ ≤ #X)

def child (s : Target) (x : X) : Target :=
  let v := alphabet d hX s.1 x
  (⟨piece d s.1 v.val,v.property⟩,extend s.2 [v.val.1])

end Erdos1172LevyCollapse.Absorption
