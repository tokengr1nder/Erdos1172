/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Flypitch4.Bvm
public import Erdos1172.Part4PosetProjectionCompletion

@[expose] public section

/-!
# A small canonical-label iteration for an internal family of partial graphs

A condition consists of a positive first-stage Boolean value and one child
of an actual Boolean name `Q`, with the value below that child's coefficient.
The second-stage order is actual reverse Boolean inclusion of the children.
The condition type remains in the universe of the Boolean algebra.

An arbitrary mixed member of `Q` is represented after a nonzero strengthening.
No unchanged-condition choice of a child is asserted. Projection has exact
strengthening lifts without any nonemptiness assumption. Surjectivity is
proved under an explicit coefficient-one label; Boolean nonemptiness alone
instead gives a dense projection image.

This constructs the iteration preorder and its regular completion. It does
not yet construct a Cohen-condition name, a second-stage generic subset,
or any cardinal preservation or ideal theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch

universe u

namespace Erdos1172BooleanNameIteration

open bSet Erdos1172PosetCompletion Erdos1172PosetProjection

variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- Canonical labels keep the actual iteration condition type in `Type u`. -/
structure Condition (Q : bSet B) : Type u where
  value : B
  nonzero : value ≠ ⊥
  index : Q.type
  valid : value ≤ Q.bval index

def name {Q : bSet B} (p : Condition Q) : bSet B := Q.func p.index

instance conditionPreorder (Q : bSet B) : Preorder (Condition Q) where
  le p q := p.value ≤ q.value ∧ p.value ≤ name q ⊆ᴮ name p
  le_refl _ := ⟨le_rfl, subset_self⟩
  le_trans _ _ _ hpq hqr :=
    ⟨hpq.1.trans hqr.1, subset_trans' (hpq.1.trans hqr.2) hpq.2⟩

theorem le_iff {Q : bSet B} (p q : Condition Q) :
    p ≤ q ↔ p.value ≤ q.value ∧ p.value ≤ name q ⊆ᴮ name p := Iff.rfl

theorem name_mem {Q : bSet B} (p : Condition Q) : p.value ≤ name p ∈ᴮ Q := by
  rw [mem_unfold]
  apply le_iSup_of_le p.index
  exact le_inf p.valid (by simp only [name, bv_eq_refl]; exact le_top)

/-- Shrinking the first-stage value preserves the same canonical label. -/
def shrink {Q : bSet B} (p : Condition Q) (b : B) (hb : b ≠ ⊥)
    (hbp : b ≤ p.value) : Condition Q :=
  ⟨b, hb, p.index, hbp.trans p.valid⟩

theorem shrink_le {Q : bSet B} (p : Condition Q) (b : B) (hb : b ≠ ⊥)
    (hbp : b ≤ p.value) : shrink p b hb hbp ≤ p :=
  ⟨hbp, subset_self⟩

def projection (Q : bSet B) : Condition Q →o {b : B // b ≠ ⊥} where
  toFun p := ⟨p.value, p.nonzero⟩
  monotone' := fun _ _ hpq => hpq.1

theorem projection_exactLifts (Q : bSet B) : ExactLifts (projection Q) := by
  intro p b hbp
  refine ⟨shrink p b.val b.property hbp, shrink_le p b.val b.property hbp, ?_⟩
  exact Subtype.ext rfl

/-- Exact projection surjectivity needs labels covering whole Boolean values. -/
theorem projection_surjective_iff (Q : bSet B) :
    Function.Surjective (projection Q) ↔ ∀ b : B, b ≠ ⊥ → ∃ i : Q.type, b ≤ Q.bval i := by
  constructor
  · intro H b hb
    obtain ⟨p, hp⟩ := H ⟨b, hb⟩
    have hpv : p.value = b := congrArg Subtype.val hp
    exact ⟨p.index, hpv ▸ p.valid⟩
  · intro H b
    obtain ⟨i, hi⟩ := H b.val b.property
    exact ⟨⟨b.val, b.property, i, hi⟩, Subtype.ext rfl⟩

theorem projection_surjective_of_top_label {Q : bSet B}
    (i : Q.type) (hi : Q.bval i = ⊤) :
    Function.Surjective (projection Q) := by
  apply (projection_surjective_iff Q).mpr
  intro b _
  exact ⟨i, hi.symm ▸ le_top⟩

/-- Membership is a Boolean cover by canonical-label equality pieces. -/
theorem membership_pieces {Q q : bSet B} {b : B} (hq : b ≤ q ∈ᴮ Q) :
    b = ⨆ i : Q.type, b ⊓ (Q.bval i ⊓ q =ᴮ Q.func i) := by
  calc
    b = b ⊓ q ∈ᴮ Q := (inf_eq_left.mpr hq).symm
    _ = ⨆ i : Q.type, b ⊓ (Q.bval i ⊓ q =ᴮ Q.func i) := by
      rw [mem_unfold, inf_iSup_eq]

/-- A mixed name has a canonical representative after a positive refinement. -/
theorem exists_canonical_refinement {Q q : bSet B} {b : B}
    (hb : b ≠ ⊥) (hq : b ≤ q ∈ᴮ Q) :
    ∃ p : Condition Q, p.value ≤ b ∧ p.value ≤ q =ᴮ name p := by
  classical
  have hex : ∃ i : Q.type, b ⊓ (Q.bval i ⊓ q =ᴮ Q.func i) ≠ ⊥ := by
    by_contra h
    have hbot : (⨆ i : Q.type, b ⊓ (Q.bval i ⊓ q =ᴮ Q.func i)) = ⊥ := by
      apply iSup_eq_bot.mpr
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    exact hb ((membership_pieces hq).trans hbot)
  obtain ⟨i, hi⟩ := hex
  refine ⟨⟨b ⊓ (Q.bval i ⊓ q =ᴮ Q.func i), hi, i, inf_le_right.trans inf_le_left⟩, inf_le_left, ?_⟩
  exact inf_le_right.trans inf_le_right

/-- Any locally valid mixed graph extension refines to an actual condition. -/
theorem exists_extension_refinement {Q q : bSet B} (p : Condition Q)
    {b : B} (hb : b ≠ ⊥) (hbp : b ≤ p.value)
    (hq : b ≤ q ∈ᴮ Q) (hsub : b ≤ name p ⊆ᴮ q) :
    ∃ r : Condition Q, r ≤ p ∧ r.value ≤ b ∧ r.value ≤ q =ᴮ name r := by
  obtain ⟨r, hrb, hreq⟩ := exists_canonical_refinement hb hq
  refine ⟨r, ⟨hrb.trans hbp, ?_⟩, hrb, hreq⟩
  exact subset_trans' (hrb.trans hsub) (subset_of_eq hreq)

/-- Boolean nonemptiness yields dense projection image, not exact surjectivity. -/
theorem projection_dense_of_mem {Q q : bSet B} (hq : (⊤ : B) ≤ q ∈ᴮ Q) :
    ∀ b : {b : B // b ≠ ⊥}, ∃ p : Condition Q, projection Q p ≤ b := by
  intro b
  obtain ⟨p, hp, _⟩ := exists_canonical_refinement b.property (le_top.trans hq)
  exact ⟨p, hp⟩

theorem condition_nonempty_of_mem {Q q : bSet B} (hq : (⊤ : B) ≤ q ∈ᴮ Q) :
    Nonempty (Condition Q) := by
  obtain ⟨p, _⟩ := projection_dense_of_mem hq ⟨⊤, top_ne_bot⟩
  exact ⟨p⟩

/-- The regular completion of the canonical-label iteration. -/
abbrev Algebra (Q : bSet B) := Completion (Condition Q)

def firstStageHom (Q : bSet B) :
    CompleteLatticeHom (Completion {b : B // b ≠ ⊥}) (Algebra Q) :=
  completionHom (projection Q) (projection_exactLifts Q)

theorem firstStageHom_injective_of_top_label {Q : bSet B}
    (i : Q.type) (hi : Q.bval i = ⊤) : Function.Injective (firstStageHom Q) :=
  completionHom_injective _ _ (projection_surjective_of_top_label i hi)

theorem condition_le_firstStageHom_iff (Q : bSet B) (p : Condition Q)
    (b : Completion {b : B // b ≠ ⊥}) :
    condition p ≤ firstStageHom Q b ↔ condition (projection Q p) ≤ b :=
  condition_le_completionHom_iff _ _ _ _

end Erdos1172BooleanNameIteration
