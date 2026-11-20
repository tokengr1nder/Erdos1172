/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.SetTheory.Cardinal.Ordinal
public import Erdos1172.Part4ShioyaStringTransport
public import Mathlib.Order.Bounds.OrderIso
public import Erdos1172.Part4BooleanWeightedDenseBasis
public import Erdos1172.Part4LevyAnonymousCH

@[expose] public section

/-! # Descent of cardinal bounds through a forcing cover

A cover with density at most θ preserves the ground gap between θ and θ⁺.
An injected copy of the ground θ⁺ inside the smaller model's powerset
would remain too large in the cover. This descends the cover's powerset bound
without descending its enumerating function.
-/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open bSet ErdosNameTransport Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya

namespace ForcingCover
open Erdos1172PosetProjection

variable {S T : Type u} [Preorder S] [Preorder T] (π : T →o S)

def Lifts : Prop := ∀ t s, s ≤ π t → ∃ r ≤ t, π r ≤ s

theorem preimage_compl (hl : Lifts π) (A : LowerSet S) : pullback π Aᶜ = (pullback π A)ᶜ := by
  apply SetLike.ext
  intro t
  rw [mem_pullback, mem_pseudocompl_iff, mem_pseudocompl_iff]
  constructor
  · exact fun h r hr => h (π r) (π.monotone hr)
  · intro h s hs ha
    obtain ⟨r, hr, hπ⟩ := hl t s hs
    exact h r hr (A.lower hπ ha)

def preimage (hl : Lifts π) (b : Completion S) : Completion T :=
  ⟨pullback π b.val, by
    change (pullback π b.val)ᶜᶜ = pullback π b.val
    rw [← preimage_compl π hl, ← preimage_compl π hl, b.prop.eq]⟩

def booleanHom (hl : Lifts π) : CompleteLatticeHom (Completion S) (Completion T) := by
  let f := preimage π hl
  have hcompl (b : Completion S) : f bᶜ = (f b)ᶜ :=
    Heyting.Regular.coe_injective (preimage_compl π hl b.val)
  have hinf (A : Set (Completion S)) : f (sInf A) = sInf (f '' A) := by
    apply Heyting.Regular.coe_injective
    apply SetLike.ext
    intro p
    change π p ∈ (sInf A).val ↔ p ∈ (sInf (f '' A)).val
    simp only [mem_sInf_completion, Set.forall_mem_image]
    rfl
  refine { toFun := f, map_sInf' := hinf, map_sSup' := fun A => ?_ }
  apply compl_injective
  rw [← hcompl, compl_sSup', hinf, compl_sSup', Set.image_image, Set.image_image]
  simp only [hcompl]

theorem booleanHom_injective (hl : Lifts π) (hd : ∀ p, ∃ t, π t ≤ p) : Function.Injective (booleanHom π hl) := by
  have ref {b c : Completion S} (h : booleanHom π hl b ≤ booleanHom π hl c) : b ≤ c := by
    apply le_of_dense_conditions_le (Set.range π) (fun p => by
      obtain ⟨t,ht⟩ := hd p
      exact ⟨π t, Set.mem_range_self t, ht⟩)
    rintro ⟨_, t, rfl⟩ hb
    apply condition_le_iff.mpr
    have hmem : π t ∈ b.val := condition_le_iff.mp hb
    exact h (show t ∈ (booleanHom π hl b).val from hmem)
  intro b c h
  exact le_antisymm (ref h.le) (ref h.ge)

end ForcingCover

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

section Poset

variable {T : Type u} [Preorder T] [Nonempty T]
local instance : NontrivialCompleteBooleanAlgebra (Completion T) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

theorem successor_gap_of_dense_cover (θ : Cardinal.{u}) (hinf : Cardinal.aleph0 ≤ θ)
    (D : Set T) (hd : ∀ p : T, ∃ d ∈ D, d ≤ p) (hD : Cardinal.mk D ≤ θ) :
    (injects_into (check (PSet.ordinalMk (Order.succ θ).ord)) (check (PSet.ordinalMk θ.ord)) :
      Completion T) = ⊥ := by
  let μ := Order.succ θ
  have hμ : μ.IsRegular := Cardinal.isRegular_succ hinf
  have hs := ErdosCardinalPreservation.surjects_onto_eq_bot (B := Completion T) hμ
    (fun w hp hj => ((disjoint_family_cardinal_le_dense D hd w hp hj).trans hD).trans_lt (Order.lt_succ θ))
    (PSet.ordinalMk θ.ord) (PSet.ordinalMk μ.ord)
    (by simpa only [PSet.ordinalMk_type, Cardinal.mk_ord_toType] using Order.lt_succ θ)
    (by simp only [PSet.ordinalMk_type, Cardinal.mk_ord_toType, le_refl]) (PSet.ordinalMk_inj _)
  obtain ⟨x,hx⟩ := PSet.exists_mem_of_nonzero hμ.ord_pos
  have hm : (⊤ : Completion T) ≤ exists_mem (check (PSet.ordinalMk μ.ord)) :=
    le_iSup_of_le (check x) (check_mem hx)
  exact bot_unique ((surjects_onto_of_injects_into' le_rfl (le_top.trans hm)).trans_eq hs)

end Poset
end Erdos1172Shioya
