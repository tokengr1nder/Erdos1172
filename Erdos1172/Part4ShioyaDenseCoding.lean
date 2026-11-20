/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaFreezing
public import Erdos1172.Part4ShioyaStringCoding

@[expose] public section

/-! # Dense coding conditions

At an inaccessible bound the full regular completion of a presentation fits
in one additional interval of the string. Thus even a coding that assigns
a separate bit to every Boolean value is available below each condition.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya.Condition

variable {κ θ : Cardinal.{u}}

theorem algebra_cardinal_lt (p : Condition κ θ) (hθ : θ.IsInaccessible) :
    Cardinal.mk p.Algebra < θ := by
  let f (b : p.Algebra) : Set p.Poset := b.val
  have hf : Function.Injective f :=
    fun _ _ h => Heyting.Regular.coe_injective (SetLike.coe_injective h)
  apply (Cardinal.mk_le_of_injective hf).trans_lt
  rw [Cardinal.mk_set]
  exact hθ.isStrongPrelimit p.presentation.cardinal_lt

theorem exists_full_coding (p : Condition κ θ) (hθ : θ.IsInaccessible) :
    ∃ w : Condition κ θ, Refines w p ∧ Function.Surjective w.bits := by
  let slots := tailSlots p.length hθ.aleph0_lt.le (p.algebra_cardinal_lt hθ)
  let w := p.append slots id
  refine ⟨w, p.append_refines slots id, ?_⟩
  intro b
  exact ⟨slots.slot b, p.append_at slots id b⟩

theorem exists_coding_refinement (p : Condition κ θ) (hθ : θ.IsInaccessible) :
    ∃ w : Condition κ θ, Refines w p ∧ Codes w := by
  obtain ⟨w, hw, hbits⟩ := p.exists_full_coding hθ
  exact ⟨w, hw, fun q => hbits (condition q)⟩

end Erdos1172Shioya.Condition
