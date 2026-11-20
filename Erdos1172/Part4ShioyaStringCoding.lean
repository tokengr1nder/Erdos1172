/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaProductRefinement

@[expose] public section

/-! # Coding arbitrary Boolean coefficients after a Shioya string

A family of fewer than θ truth values fits in a new interval after any
condition's old string. The witnesses include the exact coefficients
at the new positions and the projection witnessing refinement.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya

variable {κ θ : Cardinal.{u}} {T : Type u}

structure TailSlots (old : θ.ord.ToType) (T : Type u) where
  length : θ.ord.ToType
  extendsLength : old.toOrd.val ≤ length.toOrd.val
  slot : T ↪ length.toOrd.val.ToType
  fresh : ∀ t, old.toOrd.val ≤ (slot t).toOrd.val

def tailSlots (old : θ.ord.ToType) (hθ : Cardinal.aleph0 ≤ θ) (hT : Cardinal.mk T < θ) :
    TailSlots old T := by
  let δ := (Cardinal.mk T).ord
  let η := old.toOrd.val + δ
  have hη : η < θ.ord :=
    Ordinal.isPrincipal_add_ord hθ old.toOrd.property (Cardinal.ord_lt_ord.mpr hT)
  let l : θ.ord.ToType := Ordinal.ToType.mk ⟨η,hη⟩
  have hl : l.toOrd.val = η := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  let e : T ≃ δ.ToType := (Cardinal.eq.mp (Cardinal.mk_ord_toType (Cardinal.mk T)).symm).some
  let f (t : T) : l.toOrd.val.ToType := Ordinal.ToType.mk
    ⟨old.toOrd.val + (e t).toOrd.val, by
      change old.toOrd.val + (e t).toOrd.val < l.toOrd.val
      rw [hl]
      exact add_lt_add_right (show (e t).toOrd.val < δ from (e t).toOrd.property) old.toOrd.val⟩
  have hf (t : T) : (f t).toOrd.val = old.toOrd.val + (e t).toOrd.val :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  refine ⟨l, hl ▸ le_self_add, ⟨f, ?_⟩, fun t => (hf t).symm ▸ le_self_add⟩
  intro s t h
  have he := congrArg (fun j : l.toOrd.val.ToType => j.toOrd.val) h
  change (f s).toOrd.val = (f t).toOrd.val at he
  rw [hf, hf] at he
  exact e.injective (Ordinal.ToType.mk.symm.injective (Subtype.ext (add_left_cancel he)))

namespace Condition

def appendBits (p : Condition κ θ) (slots : TailSlots p.length T) (payload : T → p.Algebra)
    (j : slots.length.toOrd.val.ToType) : p.Algebra := by
  classical
  exact if h : ∃ t, slots.slot t = j then payload h.choose else StringName.padBits slots.extendsLength p.bits j

def append (p : Condition κ θ) (slots : TailSlots p.length T) (payload : T → p.Algebra) : Condition κ θ :=
  { p with length := slots.length, bits := appendBits p slots payload }

theorem append_at (p : Condition κ θ) (slots : TailSlots p.length T) (payload : T → p.Algebra) (t : T) :
    (append p slots payload).bits (slots.slot t) = payload t := by
  classical
  change (if h : ∃ s, slots.slot s = slots.slot t then payload h.choose else _) = _
  have ht : ∃ s, slots.slot s = slots.slot t := ⟨t,rfl⟩
  rw [dif_pos ht, slots.slot.injective ht.choose_spec]

theorem append_refines (p : Condition κ θ) (slots : TailSlots p.length T) (payload : T → p.Algebra) :
    Refines (append p slots payload) p := by
  classical
  refine ⟨PartialProjection.identity (κ := κ) (P := p.Poset), ?_, ?_⟩
  · change condition p.point ≤ (PartialProjection.identity (κ := κ) (P := p.Poset)).booleanHom _
    rw [PartialProjection.booleanHom_id]
    exact le_rfl
  · change condition p.point ≤ extensionValue (PartialProjection.identity (κ := κ) (P := p.Poset)).booleanHom
      p.name (StringName.ofBits (B := p.Algebra) slots.length.toOrd.val (appendBits p slots payload))
    rw [PartialProjection.booleanHom_id]
    apply extensionValue_of_bits (CompleteLatticeHom.id p.Algebra) p.name
      (StringName.ofBits (B := p.Algebra) slots.length.toOrd.val (appendBits p slots payload)) slots.extendsLength
    intro i
    simp only [name, StringName.bits_ofBits, CompleteLatticeHom.id_apply]
    have hn : ¬∃ t, slots.slot t = StringName.includeIndex slots.extendsLength i := by
      rintro ⟨t, ht⟩
      have h := slots.fresh t
      rw [ht, StringName.includeIndex_toOrd] at h
      exact i.toOrd.property.not_ge h
    change _ = _ ⊓ (if h : ∃ t, slots.slot t = StringName.includeIndex slots.extendsLength i
      then payload h.choose else _)
    rw [dif_neg hn, StringName.padBits_includeIndex]
    rfl

end Condition
end Erdos1172Shioya
