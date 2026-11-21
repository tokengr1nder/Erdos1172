/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCoverPreservation

@[expose] public section

/-! # The two-step forcing with bounded Boolean binary strings

A positive condition in the first algebra supports a binary function name
of prescribed ground length below θ. The second string extends the first
on the stronger condition's positive Boolean value.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion Erdos1172PositiveBoolean
universe u
namespace Erdos1172Shioya.CohenCover

structure Condition (θ : Cardinal.{u}) (B : Type u) [NontrivialCompleteBooleanAlgebra B] where
  value : B
  positive : value ≠ ⊥
  length : θ.ord.ToType
  bits : length.toOrd.val.ToType → B

variable {θ : Cardinal.{u}} {B : Type u} [NontrivialCompleteBooleanAlgebra B]

namespace Condition

def name (p : Condition θ B) := StringName.ofBits p.length.toOrd.val p.bits

def Refines (q p : Condition θ B) : Prop :=
  q.value ≤ p.value ∧ q.value ≤ extensionValue (CompleteLatticeHom.id B) p.name q.name

instance : Preorder (Condition θ B) where
  le := Refines
  le_refl p := ⟨le_rfl, le_top.trans (extensionValue_refl p.name)⟩
  le_trans q p r h₁ h₂ := ⟨h₁.1.trans h₂.1, extensionValue_trans (CompleteLatticeHom.id B)
    (CompleteLatticeHom.id B) r.name p.name q.name h₁.1 h₂.2 h₁.2⟩

theorem le_iff_extension (q p : Condition θ B) : q ≤ p ↔ q.value ≤ p.value ∧
    q.value ≤ extensionValue (CompleteLatticeHom.id B) p.name q.name := Iff.rfl

theorem le_iff (q p : Condition θ B) : q ≤ p ↔ q.value ≤ p.value ∧
    ∃ h : p.length.toOrd.val ≤ q.length.toOrd.val, ∀ i, q.value ⊓ p.bits i =
      q.value ⊓ q.bits (StringName.includeIndex h i) := by
  rw [le_iff_extension, extensionValue_iff_bits _ _ _ q.positive]
  simp only [name, StringName.bits_ofBits, CompleteLatticeHom.id_apply]

def withValue (p : Condition θ B) (b : B) (hb : b ≠ ⊥) : Condition θ B :=
  { p with value := b, positive := hb }

theorem withValue_le (p : Condition θ B) (b : B) (hb : b ≠ ⊥) (hbp : b ≤ p.value) :
    p.withValue b hb ≤ p := ⟨hbp, le_top.trans (extensionValue_refl p.name)⟩

def empty (hθ : 0 < θ) (b : B) (hb : b ≠ ⊥) : Condition θ B where
  value := b
  positive := hb
  length := Ordinal.ToType.mk ⟨0,Cardinal.ord_pos.mpr hθ⟩
  bits _ := ⊥

end Condition

end Erdos1172Shioya.CohenCover
