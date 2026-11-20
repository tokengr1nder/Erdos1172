/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BoundedUltrapowerSequenceClosure
public import Erdos1172.Part4PosetProjectionCompletion
public import Mathlib.SetTheory.Cardinal.Ordinal

@[expose] public section

/-! # Bounded ultrapowers of stage posets

On every bounded interval of the fine seed, the fibers have size below the
critical cardinal. Normality transfers the comparisons of an external short
chain to simultaneous comparisons on these fibers. Thus their pointwise
infima form a bounded target point.
-/

set_option autoImplicit false
noncomputable section
open Filter Erdos1172GroundUltrapower
universe u
namespace Erdos1172Shioya.UltrapowerStage

variable {I : Type u} (U : Ultrafilter I) {κ θ : Cardinal.{u}} (a : I → Set θ.ord.ToType)

abbrev Point (P : Type u) := {x : Germ (U : Filter I) P //
  ∃ η : θ.ord.ToType, ∃ f : Set θ.ord.ToType → P,
    Germ.ofFun (fun i => f (boundedFiber θ a η i)) = x}

def represent {P : Type u} (η : θ.ord.ToType) (f : Set θ.ord.ToType → P) : Point U a P :=
  ⟨_,η,f,rfl⟩

def diagonal [Nonempty θ.ord.ToType] {P : Type u} [PartialOrder P] : P ↪o Point U a P where
  toFun x := represent U a (Classical.choice inferInstance) (fun _ => x)
  inj' _ _ h := Germ.const_inj.mp (congrArg Subtype.val h)
  map_rel_iff' := Germ.const_le_iff

def map {P Q : Type u} (f : P → Q) (p : Point U a P) : Point U a Q := by
  refine ⟨Germ.map f p.val, ?_⟩
  obtain ⟨η,g,hg⟩ := p.property
  exact ⟨η,f ∘ g,congrArg (Germ.map f) hg⟩

@[simp] theorem map_id {P : Type u} (p : Point U a P) : map U a id p = p := by
  apply Subtype.ext
  exact congrFun Germ.map_id p.val

end Erdos1172Shioya.UltrapowerStage
