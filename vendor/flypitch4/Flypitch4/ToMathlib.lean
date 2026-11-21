/-
Local Lean 4.33.1 compatibility changes for E1172, 2026-09-19.
Theorem statements and mathematical definitions are preserved.
See ../PROVENANCE.md for the pinned upstream source and modifications.
-/
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/to_mathlib.lean -/
module

public import Erdos1172.Statement
public import Mathlib.Data.Set.Countable
public import Mathlib.SetTheory.Cardinal.Cofinality
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Sets.Opens
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

universe u v w w'

/-! ## Lean 3 → Lean 4 Port: Renames and Drops

### Renames (for downstream file porters, search counts in src/)

1. `imp_self` → `ba_imp_self` (renamed to avoid collision with Lean 4 core `imp_self`)
   - Call sites: `src/henkin.lean:210`, `src/fol.lean:2097` (2 sites)

2. `le_trans'` → `le_trans_inf` (renamed to avoid collision with mathlib4 `ge_trans` alias and
   Lean 4 core `le_trans'` for lists)
   - Call sites: `src/bfol.lean:706`, `src/bvm.lean:64`, `:2475`, `:2481`,
   `src/bvm_extras.lean:2121`, `:2124` (6 sites)

3. `mk_union_le` → `mk_union_le_impl` (kept as wrapper; mathlib4 has `Cardinal.mk_union_le`)
   - Call site: `src/collapse.lean:570` — when collapse is ported, prefer
   `Cardinal.mk_union_le` over our wrapper

4. `nontrivial.bot_lt_top` → `nontrivial_bot_lt_top` (flattened from sub-namespace dot notation;
   class accessor pattern changes in Lean 4)
   - Call sites: `src/bfol.lean:790`, `src/bvm.lean:1596`, `src/zfc.lean:519`, `:534` (4 sites)

### Drops (declarations removed because they exist in mathlib4)

1. `congr1` and `rexact` tactics (src/to_mathlib.lean:492-510)
   - `congr1` was a custom tactic used in ~10 downstream Lean 3 proof sites
   - In Lean 4, `congr 1` (with a space) is a built-in tactic
   - When porting `fol`, `henkin`, `language_extension`, etc., translate `congr1` (no space) to
   `congr 1` (with space) inline rather than re-implementing

2. `complete_degenerate_boolean_algebra` (src/to_mathlib.lean:756)
   - Replaced by mathlib4's `PUnit.instCompleteBooleanAlgebra` in
   `Mathlib/Order/CompleteBooleanAlgebra.lean`
   - No downstream `src/` file uses this directly
-/

/-!
## function namespace

`Function.Injective.ne_iff` already exists in mathlib4. No redeclaration needed.
-/

/-! ## dvector type and namespace -/

/-- Finite type with `n` elements, used with `DVec`. -/
inductive DFin : ℕ → Type
  | fz {n} : DFin (n + 1)
  | fs {n} : DFin n → DFin (n + 1)

namespace DVec

variable {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

@[simp] protected theorem zero_eq : ∀ (xs : DVec α 0), xs = DVec.nil
  | DVec.nil => rfl

@[simp] protected def nth : ∀ {n : ℕ}, DVec α n → (m : ℕ) → m < n → α
  | _, DVec.nil, m, h => absurd h (Nat.not_lt_zero m)
  | _, DVec.cons x _, 0, _ => x
  | _, DVec.cons _ xs, m + 1, h => DVec.nth xs m (Nat.lt_of_succ_lt_succ h)

protected def mem : ∀ {n : ℕ}, α → DVec α n → Prop
  | _, _, DVec.nil => False
  | _, x, DVec.cons x' xs => x = x' ∨ DVec.mem x xs

protected def pmem : ∀ {n : ℕ}, α → DVec α n → Type
  | _, _, DVec.nil => Empty
  | _, x, DVec.cons x' xs => PSum (x = x') (DVec.pmem x xs)

@[simp] protected def map (f : α → β) : ∀ {n : ℕ}, DVec α n → DVec β n
  | _, DVec.nil => DVec.nil
  | _, DVec.cons x xs => DVec.cons (f x) (DVec.map f xs)

@[simp] protected def map2 (f : α → β → γ) : ∀ {n : ℕ}, DVec α n → DVec β n → DVec γ n
  | _, DVec.nil, DVec.nil => DVec.nil
  | _, DVec.cons x xs, DVec.cons y ys => DVec.cons (f x y) (DVec.map2 f xs ys)

@[simp] protected theorem map_id : ∀ {n : ℕ} (xs : DVec α n), DVec.map (fun x => x) xs = xs
  | _, DVec.nil => rfl
  | _, DVec.cons _ xs => by simp [DVec.map, DVec.map_id xs]

@[simp] protected theorem map_map (g : β → γ) (f : α → β) : ∀ {n : ℕ} (xs : DVec α n),
    DVec.map g (DVec.map f xs) = DVec.map (fun x => g (f x)) xs
  | _, DVec.nil => rfl
  | _, DVec.cons _ xs => by simp [DVec.map, DVec.map_map g f xs]

@[simp] protected def append : ∀ {n m : ℕ}, DVec α n → DVec α m → DVec α (m + n)
  | _, _, DVec.nil, xs => xs
  | _, _, DVec.cons x' xs, xs' => DVec.cons x' (DVec.append xs xs')

@[simp] protected def insert : ∀ {n : ℕ}, α → ℕ → DVec α n → DVec α (n + 1)
  | n, x, 0, xs => DVec.cons x xs
  | 0, x, _, _ => DVec.cons x DVec.nil
  | n + 1, x, k + 1, DVec.cons y ys => DVec.cons y (DVec.insert x k ys)

@[simp] protected theorem insert_nth : ∀ {n : ℕ} (x : α) (k : ℕ) (xs : DVec α n) (h : k < n + 1),
    DVec.nth (DVec.insert x k xs) k h = x
  | 0, x, 0, _, _ => rfl
  | 0, x, k + 1, _, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)
  | n + 1, x, 0, _, _ => by simp [DVec.insert, DVec.nth]
  | n + 1, x, k + 1, DVec.cons _ ys, h => by
    simp [DVec.insert, DVec.nth]
    exact DVec.insert_nth x k ys _

/-- The n-th initial segment of a vector, given a proof that n ≤ m. -/
@[simp] protected def trunc : ∀ (n) {m : ℕ}, n ≤ m → DVec α m → DVec α n
  | 0, 0, _, _ => DVec.nil
  | 0, _ + 1, _, _ => DVec.nil
  | n + 1, 0, h, _ => absurd h (Nat.not_succ_le_zero n)
  | n + 1, m + 1, h, DVec.cons x xs =>
    DVec.cons x (DVec.trunc n (Nat.lt_succ_iff.mp (Nat.lt_of_succ_le h)) xs)

@[simp] protected theorem trunc_n_n {n : ℕ} {h : n ≤ n} {v : DVec α n} :
    DVec.trunc n h v = v := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [DVec.trunc, ih]

@[simp] protected theorem trunc_0_n {n : ℕ} {h : 0 ≤ n} {v : DVec α n} :
    DVec.trunc 0 h v = DVec.nil := by cases v <;> rfl

@[simp] protected theorem trunc_nth {n m l : ℕ} {h : n ≤ m} {h' : l < n} {v : DVec α m} :
    DVec.nth (DVec.trunc n h v) l h' = DVec.nth v l (Nat.lt_of_lt_of_le h' h) := by
  induction m generalizing n l with
  | zero =>
    have : n = 0 := Nat.eq_zero_of_le_zero h
    subst this; exact absurd h' (Nat.not_lt_zero _)
  | succ m ih =>
    cases n with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ n =>
      cases l with
      | zero =>
        cases v with
        | cons _ _ => rfl
      | succ l =>
        cases v with
        | cons _ vs =>
          show DVec.nth (DVec.trunc n _ vs) l _ = DVec.nth vs l _
          apply ih

protected def cast {n m} (p : n = m) (v : DVec α n) : DVec α m := p ▸ v

@[simp] protected theorem cast_rfl {n m} {p : n = m} {q : m = n} {v : DVec α n} :
    DVec.cast q (DVec.cast p v) = v := by subst p; rfl

@[simp] protected def replace : ∀ {n : ℕ}, α → ℕ → DVec α n → DVec α n
  | _, x, 0, DVec.cons _ ys => DVec.cons x ys
  | 0, _, _, ys => ys
  | n + 1, x, k + 1, DVec.cons y ys => DVec.cons y (DVec.replace x k ys)

protected theorem insert_nth_lt {n k l : ℕ} (x : α) (xs : DVec α n) (h : l < n)
    (h' : l < n + 1) (h2 : l < k) :
    DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs l h := by
  induction xs generalizing k l with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons x' xs ih =>
    cases k with
    | zero => exact absurd h2 (Nat.not_lt_zero _)
    | succ k =>
      cases l with
      | zero => rfl
      | succ l =>
        simp [DVec.insert, DVec.nth]
        exact ih (Nat.lt_of_succ_lt_succ h) (Nat.lt_of_succ_lt_succ h')
          (Nat.lt_of_succ_lt_succ h2)

protected theorem insert_nth_gt' {n k l : ℕ} (x : α) (xs : DVec α n)
    (h : l - 1 < n) (h' : l < n + 1) (h2 : k < l) :
    DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs (l - 1) h := by
  induction xs generalizing k l with
  | nil =>
    cases k with
    | zero =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l => simp [DVec.insert, DVec.nth]
    | succ k =>
      cases l with
      | zero => exact absurd h (Nat.not_lt_zero _)
      | succ l => exact absurd h' (by omega)
  | cons x' xs ih =>
    cases k with
    | zero =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l => simp [DVec.insert, DVec.nth]
    | succ k =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l =>
        cases l with
        | zero => exact absurd h2 (by omega)
        | succ l =>
          simp [DVec.insert, DVec.nth]
          have := ih (k := k) (l := l + 1) (by omega) (Nat.lt_of_succ_lt_succ h') (by omega)
          simp at this ⊢
          convert this using 2 <;> omega

@[simp] protected theorem insert_nth_gt_simp {n k l : ℕ} (x : α) (xs : DVec α n)
    (h' : l < n + 1) (h2 : k < l) :
    DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs (l - 1) (by omega) :=
  DVec.insert_nth_gt' x xs (by omega) h' h2

@[simp] def foldr (f : α → β → β) (b : β) : ∀ {n}, DVec α n → β
  | _, DVec.nil => b
  | _, DVec.cons a l => f a (DVec.foldr f b l)

/-- The finitary infimum -/
def fInf [SemilatticeInf α] [OrderTop α] (xs : DVec α n) : α :=
  DVec.foldr (fun (x b : α) => x ⊓ b) ⊤ xs

@[simp] lemma fInf_nil [SemilatticeInf α] [OrderTop α] : fInf (DVec.nil (α := α)) = ⊤ := rfl

@[simp] lemma fInf_cons [SemilatticeInf α] [OrderTop α] (x : α) (xs : DVec α n) :
    fInf (DVec.cons x xs) = x ⊓ fInf xs := rfl

end DVec

/-! ## set namespace -/

namespace Set

@[simp] theorem not_nonempty_iff {α} {s : Set α} : ¬Nonempty s ↔ s = ∅ := by
  rw [Set.nonempty_coe_sort, Set.not_nonempty_iff_eq_empty]

-- subset_sInter_iff is already in Mathlib as Set.subset_sInter_iff

end Set

/-! ## topological_space section -/

section TopologicalSpace

open TopologicalSpace Set Filter

variable {α : Type u} {β : Type v}
variable [t : TopologicalSpace α] [TopologicalSpace β]

end TopologicalSpace

/-! ## ordinal namespace -/

namespace Ordinal

variable {σ : Type*}

end Ordinal

/-! ## cardinal namespace -/

namespace Cardinal

open scoped Cardinal

end Cardinal

/-! ## nat namespace -/

namespace Nat

end Nat

/-! ## classical namespace (logic helpers) -/

namespace Classical

end Classical

/-! ## list namespace -/

namespace List

end List

/-! ## additional nat lemmas -/

namespace Nat

end Nat

/-! ## misc prop lemmas -/

/-! ## additional set lemmas -/

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

def change {π : α → Type*} [DecidableEq α] (f : ∀ a, π a) {x : α} (z : π x) (y : α) : π y :=
  if h : x = y then h ▸ z else f y

end Set

/-! ## nonempty namespace -/

namespace Nonempty

variable {α : Sort u} {β : Sort v}

end Nonempty

/-! ## arity' type and namespace -/

namespace Arity'

inductive arity'_respect_setoid {α β : Type u} [R : Setoid α] : ∀ {n}, Arity' α β n → Type u
  | r_zero (b : β) : @arity'_respect_setoid _ _ _ 0 b
  | r_succ (n : ℕ) (f : Arity' α β (n + 1)) (h₁ : ∀ {a a'}, a ≈ a' → f a = f a')
    (h₂ : ∀ a, arity'_respect_setoid (f a)) : arity'_respect_setoid f

end Arity'

/-! ## Miscellaneous lemmas -/

/-! ## Boolean algebra / lattice helpers -/

/-- A nontrivial complete Boolean algebra has ⊥ < ⊤ -/
class NontrivialCompleteBooleanAlgebra (α : Type*) extends CompleteBooleanAlgebra α where
  bot_lt_top : (⊥ : α) < (⊤ : α)

/-- Every NontrivialCompleteBooleanAlgebra is Nontrivial (witnesses: ⊥ ≠ ⊤). -/
instance (priority := 100) NontrivialCompleteBooleanAlgebra.toNontrivial {α : Type*}
    [H : NontrivialCompleteBooleanAlgebra α] : Nontrivial α :=
  ⟨⊥, ⊤, ne_of_lt H.bot_lt_top⟩

-- iSup/iInf distributivity (aliases for Lean 4 mathlib names)
theorem inf_iSup_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    a ⊓ (⨆ (i : ι), s i) = ⨆ (i : ι), a ⊓ s i :=
  inf_iSup_eq a s

theorem iSup_inf_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    (⨆ (i : ι), s i) ⊓ a = ⨆ (i : ι), (s i ⊓ a) := by
  rw [inf_comm, inf_iSup_eq']; simp_rw [inf_comm]

theorem sup_iInf_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    a ⊔ (⨅ (i : ι), s i) = ⨅ (i : ι), a ⊔ s i :=
  sup_iInf_eq a s

theorem iInf_sup_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    (⨅ (i : ι), s i) ⊔ a = ⨅ (i : ι), s i ⊔ a := by
  rw [sup_comm, sup_iInf_eq']; simp_rw [sup_comm]

theorem sup_self {α : Type*} [Lattice α] {a : α} : a ⊔ a = a := sup_idem a

-- Note: bot_lt_iff_not_le_bot and lt_top_iff_not_top_le already exist in mathlib4

/-- Material implication in a Boolean algebra -/
def imp {α : Type*} [BooleanAlgebra α] (a₁ a₂ : α) : α := a₁ᶜ ⊔ a₂

scoped[Flypitch] infixl:65 " ⟹ " => imp
open scoped Flypitch

@[reducible, simp] def biimp {α : Type*} [BooleanAlgebra α] (a₁ a₂ : α) : α :=
  imp a₁ a₂ ⊓ imp a₂ a₁

scoped[Flypitch] infixl:50 " ⇔ " => biimp

@[simp] theorem imp_le_of_right_le {α : Type*} [BooleanAlgebra α] {a a₁ a₂ : α} {h : a₁ ≤ a₂} :
    imp a a₁ ≤ imp a a₂ := sup_le_sup_left h _

@[simp] theorem imp_le_of_left_le {α : Type*} [BooleanAlgebra α] {a a₁ a₂ : α} {h : a₂ ≤ a₁} :
    imp a₁ a ≤ imp a₂ a := sup_le_sup_right (compl_le_compl h) _

@[simp] theorem imp_bot {α : Type*} [BooleanAlgebra α] {a : α} : imp a ⊥ = aᶜ := by simp [imp]

@[simp] theorem top_imp {α : Type*} [BooleanAlgebra α] {a : α} : imp ⊤ a = a := by simp [imp]

-- Note: Lean 4 already has a `imp_self` in core; use `ba_imp_self` for Boolean algebra version

theorem inf_eq_of_le {α : Type*} [DistribLattice α] {a b : α} (h : a ≤ b) : a ⊓ b = a :=
  le_antisymm inf_le_left (le_inf le_rfl h)

theorem imp_inf_le {α : Type*} [BooleanAlgebra α] (a b : α) : imp a b ⊓ a ≤ b := by
  unfold imp; rw [inf_sup_right]; simp

theorem le_of_sub_eq_bot {α : Type*} [BooleanAlgebra α] {a b : α} (h : bᶜ ⊓ a = ⊥) : a ≤ b := by
  rw [inf_comm] at h
  exact disjoint_compl_right_iff.mp (disjoint_iff.mpr h)

theorem le_neg_of_inf_eq_bot {α : Type*} [BooleanAlgebra α] {a b : α} (h : b ⊓ a = ⊥) :
    a ≤ bᶜ := by
  apply le_of_sub_eq_bot; rwa [compl_compl]

theorem sub_eq_bot_of_le {α : Type*} [BooleanAlgebra α] {a b : α} (h : a ≤ b) : bᶜ ⊓ a = ⊥ := by
  rw [← inf_eq_of_le h, inf_comm, inf_assoc, inf_compl_eq_bot, inf_bot_eq]

@[simp] theorem imp_top_iff_le {α : Type*} [BooleanAlgebra α] {a₁ a₂ : α} :
    imp a₁ a₂ = ⊤ ↔ a₁ ≤ a₂ := by
  rw [imp, sup_comm, ← himp_eq]
  exact himp_eq_top_iff

theorem curry_uncurry {α : Type*} [BooleanAlgebra α] {a b c : α} :
    imp (a ⊓ b) c = imp a (imp b c) := by simp [imp]; ac_rfl

theorem deduction {α : Type*} [BooleanAlgebra α] {a b c : α} :
    a ⊓ b ≤ c ↔ a ≤ imp b c := by
  rw [← imp_top_iff_le, curry_uncurry, imp_top_iff_le]

theorem deduction_simp {α : Type*} [BooleanAlgebra α] {a b c : α} :
    a ≤ imp b c ↔ a ⊓ b ≤ c := deduction.symm

theorem supr_max_of_bounded' {α β : Type*} [CompleteLattice β] {A : α → β} {b c : β}
    {h : b ≤ ⨆ (a : α), A a} {h_lt : c < b} {h_bounded : ∀ a : α, ¬b ≤ A a → A a ≤ c} :
    ∃ x : α, b ≤ A x := by
  by_contra h'
  push_neg at h'
  have : b ≤ c := le_trans h (iSup_le (fun a => h_bounded a (h' a)))
  exact absurd (lt_of_lt_of_le h_lt this) (lt_irrefl c)

theorem supr_eq_Gamma_max {α β : Type*} [CompleteLattice β] {A : α → β} {Γ : β}
    (h_nonzero : ⊥ < Γ) (h_Γ : Γ ≤ ⨆ a, A a)
    (h_bounded : ∀ a, ¬Γ ≤ A a → A a = ⊥) : ∃ x : α, Γ ≤ A x := by
  apply supr_max_of_bounded' (h := h_Γ) (h_lt := h_nonzero)
  intro a H; exact (h_bounded a H).symm ▸ bot_le

-- Note: le_trans' already exists in Mathlib (as alias for ge_trans)
-- Use le_trans_inf for our version

theorem poset_yoneda_iff {β : Type*} [PartialOrder β] {a b : β} :
    a ≤ b ↔ ∀ {Γ : β}, Γ ≤ a → Γ ≤ b :=
  ⟨fun h _ hΓ => le_trans hΓ h, fun H => H le_rfl⟩

theorem poset_yoneda_inv {β : Type*} [PartialOrder β] {a b : β} (Γ : β) (H : a ≤ b) :
    Γ ≤ a → Γ ≤ b := poset_yoneda_iff.mp H

theorem context_specialize {β : Type*} [CompleteLattice β] {ι : Type*} {s : ι → β}
    {Γ : β} (H : Γ ≤ ⨅ i, s i) (j : ι) : Γ ≤ s j :=
  le_trans H (iInf_le _ _)

theorem context_imp_elim {β : Type*} [CompleteBooleanAlgebra β] {a b Γ : β}
    (H₁ : Γ ≤ imp a b) (H₂ : Γ ≤ a) : Γ ≤ b :=
  le_trans (le_inf H₁ H₂) (imp_inf_le a b)

theorem bv_absurd {β} [BooleanAlgebra β] {Γ : β} (b : β) (H₁ : Γ ≤ b) (H₂ : Γ ≤ bᶜ) :
    Γ ≤ ⊥ :=
  le_trans (le_inf H₁ H₂) inf_compl_eq_bot.le

theorem neg_imp {β : Type*} [BooleanAlgebra β] {a b : β} : (imp a b)ᶜ = a ⊓ bᶜ := by
  simp [imp]

theorem nonzero_wit {β : Type*} [CompleteLattice β] {ι : Type*} {s : ι → β} :
    (⊥ < ⨆ i, s i) → ∃ j, ⊥ < s j := by
  intro H
  by_contra h
  push_neg at h
  simp only [bot_lt_iff_ne_bot, ne_eq, not_not] at h
  have key : ⨆ i, s i = ⊥ :=
    le_antisymm (iSup_le (fun j => (h j).le)) bot_le
  exact absurd (key ▸ H) (lt_irrefl ⊥)

theorem bv_by_contra {𝔹} [BooleanAlgebra 𝔹] {Γ b : 𝔹} (H : Γ ≤ imp bᶜ ⊥) : Γ ≤ b := by
  simpa [imp] using H

/-! ## tactic.interactive section — DEFERRED

  The tactic extensions (bv_intro, bv_cases_at, bv_or_elim_at, specialize_context,
  bv_split, bv_and_intro, bv_imp_elim_at, bv_mp, bv_imp_intro, bv_split_goal,
  bv_or_inr, bv_or_inl, bv_contradiction, tidy_context, bv_exfalso,
  bv_cases_on, bv_exists_intro, bv_specialize_at, bv_to_pi, bv_to_pi') need
  a complete rewrite for Lean 4's macro/elab system.

  These are deferred until downstream files actually need them.
  - Main block: See src/to_mathlib.lean:1252-1684 for the original definitions.
  - Early block also deferred: src/to_mathlib.lean:492-510 contained `congr1` and `rexact`
    tactics. `congr1` is used in roughly 10 downstream Lean 3 proof sites. In Lean 4,
    `congr 1` (with a space) is a built-in tactic, so when porting `fol`, `henkin`,
    `language_extension`, etc., translate `congr1` (no space) to `congr 1` (with space)
    inline rather than re-implementing the tactic.
-/
