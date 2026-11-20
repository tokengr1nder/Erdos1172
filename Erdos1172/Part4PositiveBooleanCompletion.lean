/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4PosetProjectionCompletion

@[expose] public section

/-!
# Recovering a complete Boolean algebra from its positive conditions

The regular lower set associated to `b` consists of the nonzero elements
below `b`. Its complement is computed using actual nonzero intersections.
This yields a complete Boolean embedding and an explicit inverse by taking
the supremum of the members of a regular lower set. No representation or
forcing equivalence is supplied as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Erdos1172PositiveBoolean

open Erdos1172PosetCompletion

/-- Positive Boolean conditions, with the inherited order. -/
abbrev Positive (B : Type u) [Bot B] := {b : B // b ≠ ⊥}

variable {B : Type u} [CompleteBooleanAlgebra B]

instance positiveNonempty [Nontrivial B] : Nonempty (Positive B) :=
  ⟨⟨⊤, top_ne_bot⟩⟩

/-- The lower set of positive conditions below a Boolean element. -/
def elementLowerSet (b : B) : LowerSet (Positive B) :=
  ⟨{p | p.val ≤ b}, fun p q hpq hq =>
    (show q.val ≤ p.val from hpq).trans hq⟩

@[simp] theorem mem_elementLowerSet (b : B) (p : Positive B) :
    p ∈ elementLowerSet b ↔ p.val ≤ b := Iff.rfl

/-- Pseudocomplementation of lower sets agrees with Boolean complement.
If a positive condition is not disjoint from `b`, its intersection with `b`
is the explicit positive strengthening witnessing failure. -/
theorem elementLowerSet_compl (b : B) :
    elementLowerSet bᶜ = (elementLowerSet b)ᶜ := by
  classical
  apply SetLike.ext
  intro p
  change p.val ≤ bᶜ ↔ p ∈ (elementLowerSet b)ᶜ
  rw [mem_pseudocompl_iff]
  constructor
  · intro hp q hqp hq
    have hqb : q.val ≤ b := hq
    have hqc : q.val ≤ bᶜ := (show q.val ≤ p.val from hqp).trans hp
    exact q.property (bot_unique
      ((le_inf hqb hqc).trans inf_compl_eq_bot.le))
  · intro hp
    apply le_compl_iff_disjoint_right.mpr
    rw [disjoint_iff_inf_le]
    by_contra h
    have hpos : p.val ⊓ b ≠ ⊥ := fun he => h he.le
    exact hp ⟨p.val ⊓ b, hpos⟩ inf_le_left inf_le_right

theorem elementLowerSet_regular (b : B) :
    Heyting.IsRegular (elementLowerSet b) := by
  change (elementLowerSet b)ᶜᶜ = elementLowerSet b
  rw [← elementLowerSet_compl, ← elementLowerSet_compl, compl_compl]

/-- The concrete regular lower set representing a Boolean element. -/
def element (b : B) : Completion (Positive B) :=
  ⟨elementLowerSet b, elementLowerSet_regular b⟩

@[simp] theorem mem_element (b : B) (p : Positive B) :
    p ∈ (element b).val ↔ p.val ≤ b := Iff.rfl

theorem element_compl (b : B) : element bᶜ = (element b)ᶜ :=
  Heyting.Regular.coe_injective (elementLowerSet_compl b)

theorem element_le_element_iff {b c : B} :
    element b ≤ element c ↔ b ≤ c := by
  classical
  constructor
  · intro h
    by_cases hb : b = ⊥
    · rw [hb]
      exact bot_le
    · exact h (show (⟨b, hb⟩ : Positive B) ∈ (element b).val from le_rfl)
  · intro h p hp
    exact hp.trans h

theorem element_injective : Function.Injective (element (B := B)) := by
  intro b c h
  exact le_antisymm (element_le_element_iff.mp h.le)
    (element_le_element_iff.mp h.ge)

theorem element_sInf (S : Set B) :
    element (sInf S) = sInf (element '' S) := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  simp only [mem_element, Erdos1172PosetProjection.mem_sInf_completion,
    Set.forall_mem_image, le_sInf_iff]

theorem element_sSup (S : Set B) :
    element (sSup S) = sSup (element '' S) := by
  apply compl_injective
  rw [← element_compl, compl_sSup', element_sInf, compl_sSup',
    Set.image_image, Set.image_image]
  simp only [element_compl]

/-- The complete embedding is built from the explicit lower-set map. -/
def completionHom : CompleteLatticeHom B (Completion (Positive B)) where
  toFun := element
  map_sSup' := element_sSup
  map_sInf' := element_sInf

@[simp] theorem completionHom_apply (b : B) : completionHom b = element b := rfl

theorem completionHom_injective : Function.Injective (completionHom (B := B)) :=
  element_injective

theorem completionHom_compl (b : B) :
    completionHom bᶜ = (completionHom b)ᶜ := element_compl b

/-- A positive Boolean element represents exactly its principal forcing
condition, not merely a weaker regular lower set. -/
theorem element_condition (p : Positive B) : element p.val = condition p := by
  apply Heyting.Regular.coe_injective
  have hcone : LowerSet.Iic p = elementLowerSet p.val := by
    apply SetLike.ext
    intro q
    rfl
  change elementLowerSet p.val = (LowerSet.Iic p)ᶜᶜ
  rw [hcone, (elementLowerSet_regular p.val).eq]

theorem completionHom_condition (p : Positive B) :
    completionHom p.val = condition p := element_condition p

/-- The proposed inverse takes the actual supremum of all positive members. -/
def joinMembers (a : Completion (Positive B)) : B :=
  sSup (Subtype.val '' (a.val : Set (Positive B)))

theorem element_joinMembers (a : Completion (Positive B)) :
    element (joinMembers a) = a := by
  apply le_antisymm
  · unfold joinMembers
    rw [element_sSup]
    apply sSup_le
    rintro _ ⟨b, ⟨p, hp, rfl⟩, rfl⟩
    rw [element_condition]
    exact condition_le_iff.mpr hp
  · change a.val ≤ (element (joinMembers a)).val
    intro p hp
    exact le_sSup ⟨p, hp, rfl⟩

theorem joinMembers_element (b : B) : joinMembers (element b) = b :=
  element_injective (element_joinMembers (element b))

theorem element_surjective : Function.Surjective (element (B := B)) :=
  fun a => ⟨joinMembers a, element_joinMembers a⟩

/-- Every complete Boolean algebra is explicitly order-isomorphic to the
regular completion of its positive poset, including the trivial case. -/
def completionOrderIso : B ≃o Completion (Positive B) where
  toFun := element
  invFun := joinMembers
  left_inv := joinMembers_element
  right_inv := element_joinMembers
  map_rel_iff' := element_le_element_iff

@[simp] theorem completionOrderIso_apply (b : B) :
    completionOrderIso b = element b := rfl

@[simp] theorem completionOrderIso_symm_apply (a : Completion (Positive B)) :
    completionOrderIso.symm a = joinMembers a := rfl

end Erdos1172PositiveBoolean
