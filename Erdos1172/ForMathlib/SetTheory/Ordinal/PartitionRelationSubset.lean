/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Ordinal.PartitionRelationAPI

@[expose] public section

open Ordinal Set

universe u

namespace OrdinalRamsey

/-- Apply an ordinal partition relation inside any subset of an arbitrary
well-ordered ambient type whose order type contains the source ordinal. -/
theorem on_set
    {V : Type u} [LinearOrder V] [WellFoundedLT V]
    {α β γ : Ordinal.{u}}
    (h : OrdinalRamsey α β γ)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (r : Set V) (hr : α ≤ typeLT r) :
    (∃ t : Set V, t ⊆ r ∧ red.IsClique t ∧ typeLT t = β) ∨
      ∃ t : Set V, t ⊆ r ∧ blue.IsClique t ∧ typeLT t = γ := by
  classical
  have htype : typeLT α.ToType ≤ typeLT r := by
    simpa only [Ordinal.type_toType] using hr
  let f := Classical.choice (Ordinal.type_le_iff.mp htype)
  let e : α.ToType ↪o V := f.toOrderEmbedding.trans (OrderEmbedding.subtype fun x ↦ x ∈ r)
  obtain ⟨s, hs, hstype⟩ | ⟨s, hs, hstype⟩ := h (red.comap e) ((red.comap e)ᶜ) isCompl_compl
  · refine Or.inl ⟨e '' s, ?_, ?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact (f x).property
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact hs hx hy fun hxy' ↦ hxy (congrArg e hxy')
    · have heq : typeLT s = typeLT (e '' s) :=
        ((e.strictMono.strictMonoOn s).orderIso e s).ordinalType_congr
      exact heq.symm.trans hstype
  · refine Or.inr ⟨e '' s, ?_, ?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact (f x).property
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      have hedge := hs hx hy fun hxy' ↦ hxy (congrArg e hxy')
      rw [SimpleGraph.compl_adj] at hedge
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      exact ⟨hxy, hedge.2⟩
    · have heq : typeLT s = typeLT (e '' s) :=
        ((e.strictMono.strictMonoOn s).orderIso e s).ordinalType_congr
      exact heq.symm.trans hstype

/-- Exact-source-order-type specialization of `OrdinalRamsey.on_set`. -/
theorem on_set_of_type
    {V : Type u} [LinearOrder V] [WellFoundedLT V]
    {α β γ : Ordinal.{u}} (h : OrdinalRamsey α β γ)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (s : Set V) (hstype : typeLT s = α) :
    (∃ t : Set V, t ⊆ s ∧ red.IsClique t ∧ typeLT t = β) ∨
      ∃ t : Set V, t ⊆ s ∧ blue.IsClique t ∧ typeLT t = γ :=
  h.on_set red blue hcompl s hstype.ge

end OrdinalRamsey
