/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.UpperLower.Principal

@[expose] public section

/-!
# An actual Boolean completion of a forcing preorder

Regular lower sets give a complete Boolean algebra, with a positive dense
family indexed by the original conditions. This constructs the algebra;
it assumes neither an ideal nor a Boolean representation of a powerset.
It does not construct the normal ideal or the GCH-preserving model.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Erdos1172PosetCompletion

variable {P : Type u} [Preorder P]

/-- Boolean truth values are double-negation-stable lower sets. -/
abbrev Completion (P : Type u) [Preorder P] := Heyting.Regular (LowerSet P)

instance completionCompleteBooleanAlgebra : CompleteBooleanAlgebra (Completion P) :=
  let c := (Heyting.Regular.gi (α := LowerSet P)).liftCompleteLattice
  { (inferInstance : BooleanAlgebra (Heyting.Regular (LowerSet P))) with
    sSup := c.sSup
    sInf := c.sInf
    isLUB_sSup := c.isLUB_sSup
    isGLB_sInf := c.isGLB_sInf }

/-- The regularization of the principal cone below a condition. -/
def condition (p : P) : Completion P :=
  Heyting.Regular.toRegular (LowerSet.Iic p)

theorem condition_le_iff {p : P} {b : Completion P} :
    condition p ≤ b ↔ p ∈ (b.val : LowerSet P) :=
  Heyting.Regular.gi.gc _ _ |>.trans LowerSet.Iic_le

theorem condition_mono : Monotone (condition (P := P)) := by
  intro p q hpq
  apply Heyting.Regular.toRegular.monotone
  intro r hr
  exact hr.trans hpq

theorem mem_condition_self (p : P) :
    p ∈ ((condition p).val : LowerSet P) :=
  condition_le_iff.mp le_rfl

theorem condition_ne_bot (p : P) : condition p ≠ ⊥ := by
  intro h
  have hp := mem_condition_self p
  rw [h] at hp
  exact hp

instance completionNontrivial [Nonempty P] : Nontrivial (Completion P) := by
  obtain ⟨p⟩ := ‹Nonempty P›
  exact ⟨⟨condition p, ⊥, condition_ne_bot p⟩⟩

theorem exists_condition_le {b : Completion P} (hb : b ≠ ⊥) :
    ∃ p : P, condition p ≤ b := by
  have hv : b.val ≠ (⊥ : LowerSet P) := by
    intro h
    exact hb (Heyting.Regular.coe_injective h)
  obtain ⟨p, hp⟩ := LowerSet.coe_nonempty.mpr hv
  exact ⟨p, condition_le_iff.mpr hp⟩

theorem mem_pseudocompl_iff (A : LowerSet P) (p : P) :
    p ∈ (Aᶜ : LowerSet P) ↔ ∀ q, q ≤ p → q ∉ A := by
  rw [← LowerSet.Iic_le, le_compl_iff_disjoint_right, disjoint_iff_inf_le]
  constructor
  · intro h q hqp hq
    exact h ⟨hqp, hq⟩
  · intro h q hq
    exact h q hq.1 hq.2

theorem mem_regularization_iff (A : LowerSet P) (p : P) :
    p ∈ (Aᶜᶜ : LowerSet P) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ r ∈ A := by
  classical
  simp only [mem_pseudocompl_iff, not_forall, not_not, exists_prop]

/-- This membership test records compatibility below every strengthening. -/
theorem mem_condition_iff (p q : P) :
    q ∈ ((condition p).val : LowerSet P) ↔
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ s ≤ p :=
  mem_regularization_iff (LowerSet.Iic p) q

/-- The completion preserves exactly incompatibility of conditions. -/
theorem condition_inf_ne_bot_iff (p q : P) :
    condition p ⊓ condition q ≠ ⊥ ↔ ∃ r, r ≤ p ∧ r ≤ q := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := exists_condition_le h
    have hrp := condition_le_iff.mp (hr.trans inf_le_left)
    have hrq := condition_le_iff.mp (hr.trans inf_le_right)
    obtain ⟨s, hsr, hsp⟩ := (mem_condition_iff p r).mp hrp r le_rfl
    obtain ⟨t, hts, htq⟩ := (mem_condition_iff q r).mp hrq s hsr
    exact ⟨t, hts.trans hsp, htq⟩
  · rintro ⟨r, hrp, hrq⟩ h
    have hr : condition r ≤ condition p ⊓ condition q :=
      le_inf (condition_mono hrp) (condition_mono hrq)
    exact condition_ne_bot r (bot_unique (hr.trans_eq h))

/-- Every dense set of conditions has Boolean supremum top. -/
theorem iSup_condition_eq_top_of_dense (D : Set P)
    (hD : ∀ p : P, ∃ q ∈ D, q ≤ p) :
    (⨆ q : D, condition q.val) = ⊤ := by
  classical
  apply eq_top_iff.mpr
  by_contra h
  have hn : (⨆ q : D, condition q.val) ≠ ⊤ :=
    fun he => h he.ge
  have hc : (⨆ q : D, condition q.val)ᶜ ≠ ⊥ := by
    intro he
    apply hn
    have hh := congrArg compl he
    simpa only [compl_compl, compl_bot] using hh
  obtain ⟨p, hp⟩ := exists_condition_le hc
  obtain ⟨q, hqD, hqp⟩ := hD p
  have hqleft : condition q ≤ ⨆ r : D, condition r.val :=
    le_iSup (fun r : D => condition r.val) ⟨q, hqD⟩
  have hqright : condition q ≤ (⨆ r : D, condition r.val)ᶜ :=
    (condition_mono hqp).trans hp
  exact condition_ne_bot q
    (bot_unique ((le_inf hqleft hqright).trans inf_compl_eq_bot.le))

end Erdos1172PosetCompletion
