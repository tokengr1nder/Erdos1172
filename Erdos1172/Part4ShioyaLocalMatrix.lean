/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaGenericString

@[expose] public section

/-! # Local matrices in the generic Shioya string

Complete projection maps preserve the joins of the bits of a presentation.
A stronger condition identifies the transported bits on its point, so a
local covering row and an incompatible pair remain so in the generic string
below the original condition.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u v
namespace Erdos1172Shioya

variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)]

def ambientSlot (w : Condition κ θ) (i : w.length.toOrd.val.ToType) : θ.ord.ToType :=
  StringName.includeIndex w.length.toOrd.property.le i

omit [Fact (Cardinal.aleph0 < κ)] in
theorem ambientSlot_toOrd (w : Condition κ θ) (i : w.length.toOrd.val.ToType) :
    (ambientSlot w i).toOrd.val = i.toOrd.val :=
  StringName.includeIndex_toOrd _ i

private theorem exists_cone_below {P : Type u} [Preorder P] (p : P) {b : Completion P}
    (h : condition p ⊓ b ≠ ⊥) : ∃ q ≤ p, condition q ≤ b := by
  obtain ⟨r, hr⟩ := exists_condition_le h
  obtain ⟨q, hqr, hqp⟩ :=
    (mem_condition_iff p r).mp (condition_le_iff.mp (hr.trans inf_le_left)) r le_rfl
  exact ⟨q, hqp, (condition_mono hqr).trans (hr.trans inf_le_right)⟩

private theorem cone_le_of_dense_below {P : Type u} [Preorder P] (w : P) {b : Completion P}
    (h : ∀ p ≤ w, ∃ q ≤ p, condition q ≤ b) : condition w ≤ b := by
  classical
  by_contra hn
  obtain ⟨p,hp,hb⟩ := exists_cone_below w (b := bᶜ)
    (fun he => hn (disjoint_compl_right_iff.mp (disjoint_iff.mpr he)))
  obtain ⟨q,hq,hd⟩ := h p hp
  exact condition_ne_bot q (bot_unique ((le_inf hd ((condition_mono hq).trans hb)).trans inf_compl_eq_bot.le))

theorem condition_le_iSup_genericBit_of_local_cover (w : Condition κ θ) {A : Type v}
    (slot : A → w.length.toOrd.val.ToType) (h : condition w.point ≤ ⨆ t, w.bits (slot t)) :
    condition w ≤ ⨆ t, genericBit κ θ (ambientSlot w (slot t)) := by
  apply cone_le_of_dense_below
  intro p hp
  obtain ⟨π, hpoint, hext⟩ := hp
  obtain ⟨hlen, hagree⟩ := (extensionValue_iff_bits π.booleanHom w.name p.name (condition_ne_bot p.point)).mp hext
  simp only [Condition.name, StringName.bits_ofBits] at hagree
  have hjoin := hpoint.trans (OrderHomClass.mono π.booleanHom h)
  rw [map_iSup] at hjoin
  obtain ⟨t, ht⟩ : ∃ t, condition p.point ⊓ π.booleanHom (w.bits (slot t)) ≠ ⊥ := by
    by_contra! hz
    apply condition_ne_bot p.point
    rw [← inf_eq_left.mpr hjoin, inf_iSup_eq]
    exact iSup_eq_bot.mpr hz
  obtain ⟨r, hr, hbit⟩ := exists_cone_below p.point ht
  let q := p.withPoint r
  refine ⟨q, p.withPoint_le hr, le_iSup_of_le t (condition_le_decisionValue κ θ ?_)⟩
  refine ⟨StringName.includeIndex hlen (slot t),
    (StringName.includeIndex_toOrd hlen (slot t)).trans (ambientSlot_toOrd w (slot t)).symm, ?_⟩
  exact (le_inf (condition_mono hr) hbit).trans ((hagree (slot t)).le.trans inf_le_right)

private theorem image_inf_three_eq_bot {B C : Type u} [CompleteLattice B] [CompleteLattice C]
    (e : CompleteLatticeHom B C) (x y z : B) (h : x ⊓ (y ⊓ z) = ⊥) :
    e x ⊓ (e y ⊓ e z) = ⊥ := by
  rw [← map_inf, ← map_inf, h, map_bot]

theorem condition_inf_genericBits_eq_bot_of_local_disjoint (w : Condition κ θ)
    (i j : w.length.toOrd.val.ToType) (h : condition w.point ⊓ (w.bits i ⊓ w.bits j) = ⊥) :
    condition w ⊓ (genericBit κ θ (ambientSlot w i) ⊓ genericBit κ θ (ambientSlot w j)) = ⊥ := by
  classical
  by_contra hn
  obtain ⟨p, hp, hb⟩ := exists_cone_below w hn
  obtain ⟨π, hpoint, hext⟩ := hp
  obtain ⟨hlen, hagree⟩ := (extensionValue_iff_bits π.booleanHom w.name p.name (condition_ne_bot p.point)).mp hext
  simp only [Condition.name, StringName.bits_ofBits] at hagree
  have decide (k : w.length.toOrd.val.ToType) (hk : condition p ≤ genericBit κ θ (ambientSlot w k)) :
      condition p.point ≤ π.booleanHom (w.bits k) := by
    have hv := (condition_le_genericBit_iff κ θ p (StringName.includeIndex hlen k) (ambientSlot w k)
      ((StringName.includeIndex_toOrd hlen k).trans (ambientSlot_toOrd w k).symm)).mp hk
    exact (le_inf le_rfl hv).trans ((hagree k).ge.trans inf_le_right)
  have hzero := image_inf_three_eq_bot π.booleanHom _ _ _ h
  exact condition_ne_bot p.point (bot_unique ((le_inf hpoint (le_inf (decide i (hb.trans inf_le_left))
    (decide j (hb.trans inf_le_right)))).trans_eq hzero))

end Erdos1172Shioya
