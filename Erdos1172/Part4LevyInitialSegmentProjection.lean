/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyCoordinateProjection

@[expose] public section

/-! # Restricting the Levy collapse between two cardinals

For κ ≤ θ, the coordinates of the smaller collapse form an initial segment
of those of the larger collapse. Their alphabets are equivalent initial
segments as well. Restriction along these maps lifts every strengthening
exactly, retaining all coordinates outside the strengthened finite support.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172LevyCollapse

open Erdos1172PosetCompletion Erdos1172PosetProjection
open scoped Erdos1172LevyCollapse

def mapEntries {X Y : Type u} (f : X → Y) :
    Erdos1172Collapse.Condition X →o Erdos1172Collapse.Condition Y where
  toFun p := ⟨p.entries.map f⟩
  monotone' := by
    intro p q h
    obtain ⟨tail, ht⟩ := h
    exact ⟨tail.map f, by simp only [← ht, List.map_append]⟩

private theorem mapEntries_inverse {X Y : Type u} (f : X ≃ Y)
    (p : Erdos1172Collapse.Condition X) : mapEntries f.symm (mapEntries f p) = p := by
  apply Erdos1172Collapse.Condition.ext
  change (p.entries.map f).map f.symm = p.entries
  simp

variable {κ θ : Cardinal.{u}}

def initialCoordinate (h : κ ≤ θ) : κ.ord.ToType ≤i θ.ord.ToType := by
  apply Classical.choice (Ordinal.type_le_iff.mp _)
  rw [Ordinal.type_toType, Ordinal.type_toType]
  exact Cardinal.ord_le_ord.mpr h

def initialAlphabet (h : κ ≤ θ) (i : κ.ord.ToType) :
    Set.Iio i ≃ Set.Iio (initialCoordinate h i) :=
  Equiv.ofBijective
    (fun x => ⟨initialCoordinate h x.val, (initialCoordinate h).strictMono x.property⟩)
    ⟨fun _ _ hx => Subtype.ext ((initialCoordinate h).injective (congrArg Subtype.val hx)), by
      intro y
      obtain ⟨k, hk, he⟩ := (initialCoordinate h).lt_apply_iff.mp y.property
      exact ⟨⟨k, hk⟩, Subtype.ext he⟩⟩

def initialProjection (h : κ ≤ θ) : BelowCondition θ →o BelowCondition κ where
  toFun p := DFinsupp.mapRange
    (fun i => mapEntries (initialAlphabet h i).symm) (fun _ => rfl)
    (DFinsupp.comapDomain (initialCoordinate h) (initialCoordinate h).injective p)
  monotone' := fun _ _ hp i => (mapEntries (initialAlphabet h i).symm).monotone (hp _)

theorem initialProjection_entries (h : κ ≤ θ) (p : BelowCondition θ) (i : κ.ord.ToType) :
    ((initialProjection h p) i).entries =
      (p (initialCoordinate h i)).entries.map (initialAlphabet h i).symm := rfl

private theorem exists_override {I J : Type u} {A : J → Type u} (j : I ↪ J)
    (f : ∀ i, Erdos1172Collapse.Condition (A (j i))) (p : ProductCondition A) (s : Finset I) :
    ∃ r : ProductCondition A, (∀ i ∈ s, r (j i) = f i) ∧
      ∀ k, (∀ i ∈ s, j i ≠ k) → r k = p k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨p, by simp, fun _ _ => rfl⟩
  | @insert i s hi ih =>
    obtain ⟨r, hr, hout⟩ := ih
    refine ⟨r.update (j i) (f i), ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · simp only [DFinsupp.coe_update, Function.update_self]
      · have hne : j a ≠ j i := fun he => hi (j.injective he ▸ ha)
        simpa only [DFinsupp.coe_update, Function.update_of_ne hne] using hr a ha
    · intro k hk
      rw [DFinsupp.coe_update, Function.update_of_ne (hk i (Finset.mem_insert_self _ _)).symm]
      exact hout k (fun a ha => hk a (Finset.mem_insert_of_mem ha))

theorem initialProjection_exactLifts (h : κ ≤ θ) : ExactLifts (initialProjection h) := by
  classical
  intro p q hq
  let j := (initialCoordinate h).toRelEmbedding.toEmbedding
  let f := fun i => mapEntries (initialAlphabet h i) (q i)
  obtain ⟨r, hr, hout⟩ := exists_override (A := fun i : θ.ord.ToType => Set.Iio i) j f p q.support
  have hf (i : κ.ord.ToType) : f i ≤ p (j i) := by
    have hle := (mapEntries (initialAlphabet h i)).monotone (hq i)
    change f i ≤ mapEntries (initialAlphabet h i)
      (mapEntries (initialAlphabet h i).symm (p (j i))) at hle
    exact hle.trans_eq (mapEntries_inverse (initialAlphabet h i).symm _)
  refine ⟨r, ?_, ?_⟩
  · intro k
    by_cases hk : ∃ i ∈ q.support, j i = k
    · obtain ⟨i, hi, rfl⟩ := hk
      exact (hr i hi).le.trans (hf i)
    · exact (hout k (fun i hi he => hk ⟨i, hi, he⟩)).le
  · apply DFinsupp.ext
    intro i
    change mapEntries (initialAlphabet h i).symm (r (j i)) = q i
    by_cases hi : i ∈ q.support
    · rw [hr i hi]
      exact mapEntries_inverse (initialAlphabet h i) _
    · have he : q i = ⊤ := DFinsupp.notMem_support_iff.mp hi
      have hrp := hout (j i) (fun a ha heq => hi (j.injective heq ▸ ha))
      rw [hrp]
      exact le_antisymm (he ▸ le_top) (hq i)

theorem initialProjection_surjective (h : κ ≤ θ) : Function.Surjective (initialProjection h) := by
  intro q
  have ht : initialProjection h (⊤ : BelowCondition θ) = ⊤ := by
    apply DFinsupp.ext
    intro i
    rfl
  obtain ⟨r, _, hr⟩ := initialProjection_exactLifts h (⊤ : BelowCondition θ) q
    (ht.symm ▸ le_top)
  exact ⟨r, hr⟩

def initialCollapseHom (h : κ ≤ θ) :
    CompleteLatticeHom (Completion (BelowCondition κ)) (Completion (BelowCondition θ)) :=
  completionHom (initialProjection h) (initialProjection_exactLifts h)

theorem initialCollapseHom_injective (h : κ ≤ θ) : Function.Injective (initialCollapseHom h) :=
  completionHom_injective _ _ (initialProjection_surjective h)

end Erdos1172LevyCollapse
