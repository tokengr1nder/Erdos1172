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
/- Lean 4 port of src/fol.lean (lines 23-508): Language, preterm, term-level material. -/
module

public import Erdos1172.Statement
public import Flypitch4.ToMathlib

@[expose] public section

universe u v

namespace Fol

/-! ## Valuation helpers (subst_realize) -/

@[simp] lemma subst_realize_lt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : k < n) :
    Fol.subst_realize v x n k = v k := by
  simp only [subst_realize, H, if_true]

@[simp] lemma subst_realize_gt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : n < k) :
    Fol.subst_realize v x n k = v (k - 1) := by
  have h : ¬(k < n) := Nat.lt_asymm H
  simp only [subst_realize, h, if_false, H, if_true]

@[simp] lemma subst_realize_var_eq {S : Type u} (v : ℕ → S) (x : S) (n : ℕ) :
    Fol.subst_realize v x n n = x := by
  simp only [subst_realize, lt_irrefl, if_false]

lemma subst_realize_congr {S : Type u} {v v' : ℕ → S} (hv : ∀ k, v k = v' k) (x : S)
    (n k : ℕ) : Fol.subst_realize v x n k = Fol.subst_realize v' x n k := by
  rcases Nat.lt_trichotomy k n with h | h | h
  · simp [subst_realize, h, hv k]
  · subst h; simp [subst_realize]
  · simp [subst_realize, Nat.lt_asymm h, h, hv (k - 1)]

lemma subst_realize2 {S : Type u} (v : ℕ → S) (x x' : S) (n₁ n₂ k : ℕ) :
    Fol.subst_realize (Fol.subst_realize v x' (n₁ + n₂)) x n₁ k =
    Fol.subst_realize (Fol.subst_realize v x n₁) x' (n₁ + n₂ + 1) k := by
  simp only [subst_realize]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp_all [subst_realize] <;> omega

lemma subst_realize2_0 {S : Type u} (v : ℕ → S) (x x' : S) (n k : ℕ) :
    Fol.subst_realize (Fol.subst_realize v x' n) x 0 k =
    Fol.subst_realize (Fol.subst_realize v x 0) x' (n + 1) k := by
  have h := subst_realize2 v x x' 0 n k
  simp only [Nat.zero_add] at h
  exact h

lemma subst_realize_irrel {S : Type u} {v₁ v₂ : ℕ → S} {n : ℕ} (hv : ∀ k, k < n → v₁ k = v₂ k)
    (x : S) {k : ℕ} (hk : k < n + 1) :
    Fol.subst_realize v₁ x 0 k = Fol.subst_realize v₂ x 0 k := by
  cases k with
  | zero => rfl
  | succ k =>
    have h : 0 < k + 1 := Nat.succ_pos _
    simp [subst_realize, h, hv k (Nat.lt_of_succ_lt_succ hk)]

/-! ## Language -/

variable (L : Language.{u})

/-! ## preterm and term -/

variable {L}

@[simp] def apps : ∀ {l}, preterm L l → DVec (term L) l → term L
  | _, t, DVec.nil => t
  | _, t, DVec.cons t' ts => apps (preterm.app t t') ts

namespace preterm

end preterm

-- term.rec: custom recursion principle via structural recursion
def term.rec {C : term L → Sort v}
    (hvar : ∀ (k : ℕ), C (&k))
    (hfunc : ∀ {l} (f : L.functions l) (ts : DVec (term L) l)
      (ih_ts : ∀ t, DVec.pmem t ts → C t), C (apps (preterm.func f) ts)) :
    ∀ (t : term L), C t :=
  let rec go : ∀ {l} (t : preterm L l) (ts : DVec (term L) l)
      (ih_ts : ∀ s, DVec.pmem s ts → C s), C (apps t ts)
    | _, preterm.var k, ts, _ => by rw [DVec.zero_eq ts]; exact hvar k
    | _, preterm.func f, ts, ih_ts => hfunc f ts ih_ts
    | _, preterm.app t₁ t₂, ts, ih_ts =>
        go t₁ (DVec.cons t₂ ts) fun t ht => by
          cases ht with
          | inl h => exact h ▸ go t₂ DVec.nil (fun s hs => hs.elim)
          | inr h => exact ih_ts t h
  fun t => go t DVec.nil (fun s hs => hs.elim)

def term.elim' {C : Type v}
    (hvar : ∀ (k : ℕ), C)
    (hfunc : ∀ {{l}} (f : L.functions l) (ts : DVec (term L) l) (ih_ts : DVec C l), C) :
    ∀ {l} (t : preterm L l) (ts : DVec (term L) l) (ih_ts : DVec C l), C
  | _, preterm.var k, _, _ => hvar k
  | _, preterm.func f, ts, ih_ts => hfunc f ts ih_ts
  | _, preterm.app t s, ts, ih_ts =>
      term.elim' hvar hfunc t (DVec.cons s ts)
        (DVec.cons (term.elim' hvar hfunc s DVec.nil DVec.nil) ih_ts)

def term.elim {C : Type v}
    (hvar : ∀ (k : ℕ), C)
    (hfunc : ∀ {{l}} (f : L.functions l) (ts : DVec (term L) l) (ih_ts : DVec C l), C) :
    ∀ (t : term L), C :=
  fun t => term.elim' hvar hfunc t DVec.nil DVec.nil

/-! ## lift_term_at — lifting variables -/

@[simp] lemma lift_term_def {l} (t : preterm L l) (n : ℕ) : lift_term_at t n 0 = lift_term t n :=
  rfl

@[simp] lemma lift_term_at_zero : ∀ {l} (t : preterm L l) (m : ℕ), lift_term_at t 0 m = t
  | _, preterm.var k, _ => by simp [lift_term_at]
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, m => by
      simp only [lift_term_at, lift_term_at_zero t₁ m, lift_term_at_zero t₂ m]

@[simp] lemma lift_term_zero {l} (t : preterm L l) : lift_term t 0 = t := lift_term_at_zero t 0

/-- Iterated lifts: smaller new position -/
lemma lift_term_at2_small : ∀ {l} (t : preterm L l) (n n') {m m'}, m' ≤ m →
    lift_term_at (lift_term_at t n m) n' m' = lift_term_at (lift_term_at t n' m') n (m + n')
  | _, preterm.var k, n, n', m, m', H => by
      simp only [lift_term_at]
      split_ifs <;> simp_all [lift_term_at] <;> omega
  | _, preterm.func _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, n, n', m, m', H => by
      simp only [lift_term_at, lift_term_at2_small t₁ n n' H, lift_term_at2_small t₂ n n' H]

lemma lift_term_at2_medium : ∀ {l} (t : preterm L l) {n} (n') {m m'}, m ≤ m' → m' ≤ m + n →
    lift_term_at (lift_term_at t n m) n' m' = lift_term_at t (n + n') m
  | _, preterm.var k, n, n', m, m', H₁, H₂ => by
      simp only [lift_term_at]
      split_ifs <;> simp_all [lift_term_at] <;> omega
  | _, preterm.func _, _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, n, n', m, m', H₁, H₂ => by
      simp only [lift_term_at, lift_term_at2_medium t₁ n' H₁ H₂, lift_term_at2_medium t₂ n' H₁ H₂]

lemma lift_term2_medium {l} (t : preterm L l) {n} (n') {m'} (h : m' ≤ n) :
    lift_term_at (lift_term t n) n' m' = lift_term t (n + n') :=
  lift_term_at2_medium t n' (Nat.zero_le _) (by omega)

lemma lift_term2 {l} (t : preterm L l) (n n') :
    lift_term (lift_term t n) n' = lift_term t (n + n') :=
  lift_term2_medium t n' (Nat.zero_le _)

lemma lift_term_at2_large {l} (t : preterm L l) {n} (n') {m m'} (H : m + n ≤ m') :
    lift_term_at (lift_term_at t n m) n' m' =
    lift_term_at (lift_term_at t n' (m' - n)) n m := by
  have H₁ : n ≤ m' := Nat.le_trans (Nat.le_add_left _ _) H
  have H₂ : m ≤ m' - n := by omega
  rw [lift_term_at2_small t n' n H₂, Nat.sub_add_cancel H₁]

/-! ## subst_term — substitution -/

@[simp] lemma subst_term_var_lt (s : term L) {k n : ℕ} (H : k < n) :
    subst_term (preterm.var k) s n = &k := by
  simp only [subst_term, subst_realize, H, if_true]

@[simp] lemma subst_term_var_gt (s : term L) {k n : ℕ} (H : n < k) :
    subst_term (preterm.var k) s n = &(k - 1) := by
  have h : ¬(k < n) := Nat.lt_asymm H
  simp only [subst_term, subst_realize, h, if_false, H, if_true]

@[simp] lemma subst_term_var_eq (s : term L) (n : ℕ) :
    subst_term (preterm.var n) s n = lift_term_at s n 0 := by
  simp [subst_term, subst_realize]

/-! ## preformula and formula -/

variable (L)

-- formula: formula L is the type of first-order formulas over language L.
variable {L}

def and' (f₁ f₂ : formula L) : formula L := not' (preformula.imp f₁ (not' f₂))
scoped infixr:69 " ⊓' " => Fol.and'
def or' (f₁ f₂ : formula L) : formula L := preformula.imp (not' f₁) f₂
scoped infixr:68 " ⊔' " => Fol.or'
def biimp (f₁ f₂ : formula L) : formula L :=
  and' (preformula.imp f₁ f₂) (preformula.imp f₂ f₁)
scoped infix:61 " ⇔ " => Fol.biimp
def ex' (f : formula L) : formula L := not' (preformula.all (not' f))
scoped prefix:110 "∃'" => Fol.ex'

@[simp] def apps_rel : ∀ {l}, @preformula L l → DVec (term L) l → formula L
  | _, f, DVec.nil => f
  | _, f, DVec.cons t ts => apps_rel (preformula.apprel f t) ts

@[simp] lemma apps_rel_zero (f : formula L) (ts : DVec (term L) 0) :
    apps_rel f ts = f := by
  cases ts; rfl

@[elab_as_elim] def formula.rec' {C : formula L → Sort v}
    (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l), C (apps_rel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (ih : C f), C (∀' f)) :
    ∀ {l} (f : @preformula L l) (ts : DVec (term L) l), C (apps_rel f ts)
  | _, preformula.falsum, ts => by cases ts; exact hfalsum
  | _, preformula.equal t₁ t₂, ts => by cases ts; exact hequal t₁ t₂
  | _, preformula.rel R, ts => hrel R ts
  | _, preformula.apprel f t, ts => formula.rec' hfalsum hequal hrel himp hall f (DVec.cons t ts)
  | _, preformula.imp f₁ f₂, ts => by
      cases ts
      exact himp (formula.rec' hfalsum hequal hrel himp hall f₁ DVec.nil)
                 (formula.rec' hfalsum hequal hrel himp hall f₂ DVec.nil)
  | _, preformula.all f, ts => by
      cases ts
      exact hall (formula.rec' hfalsum hequal hrel himp hall f DVec.nil)

@[elab_as_elim] def formula.rec {C : formula L → Sort v}
    (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l), C (apps_rel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (ih : C f), C (∀' f)) :
    ∀ f, C f :=
  fun f =>
    have h := @formula.rec' L C hfalsum hequal hrel himp hall 0 f DVec.nil
    apps_rel_zero f DVec.nil ▸ h

/-! ## lift_formula_at — lifting variables in formulas -/

lemma lift_formula_at2_medium : ∀ {l} (f : @preformula L l) (n n') {m m'}, m ≤ m' → m' ≤ m + n →
    lift_formula_at (lift_formula_at f n m) n' m' = lift_formula_at f (n + n') m
  | _, preformula.falsum, _, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, n, n', m, m', H₁, H₂ => by
      simp [lift_formula_at, lift_term_at2_medium, H₁, H₂]
  | _, preformula.rel R, _, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at, lift_term_at2_medium t n' H₁ H₂]
      exact congrArg₂ preformula.apprel (lift_formula_at2_medium f n n' H₁ H₂) rfl
  | _, preformula.imp f₁ f₂, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at]
      exact congrArg₂ preformula.imp
        (lift_formula_at2_medium f₁ n n' H₁ H₂)
        (lift_formula_at2_medium f₂ n n' H₁ H₂)
  | _, preformula.all f, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at]
      exact congrArg preformula.all
        (lift_formula_at2_medium f n n' (Nat.add_le_add_right H₁ 1)
          (by omega))

/-! ## subst_formula — substitution into formulas -/

/-! ## count_quantifiers and quantifier_free -/

/-! ## prf — the proof system (src/fol.lean lines 816-824) -/

def axm1 {Γ : Set (formula L)} {A : formula L} : insert A Γ ⊢ A :=
  prf.axm (Set.mem_insert A Γ)

noncomputable def weakening {Γ Δ : Set (formula L)} {f : formula L} (H₁ : Γ ⊆ Δ) (H₂ : Γ ⊢ f) : Δ ⊢ f := by
  induction H₂ generalizing Δ with
  | axm h => exact prf.axm (H₁ h)
  | impI _ ih => exact prf.impI (ih (Set.insert_subset_insert H₁))
  | impE A _ _ ih₁ ih₂ => exact prf.impE A (ih₁ H₁) (ih₂ H₁)
  | falsumE _ ih => exact prf.falsumE (ih (Set.insert_subset_insert H₁))
  | allI _ ih => exact prf.allI (ih (Set.image_mono H₁))
  | allE₂ A t _ ih => exact prf.allE₂ A t (ih H₁)
  | ref => exact prf.ref _ _
  | subst₂ s t f _ _ ih₁ ih₂ => exact prf.subst₂ s t f (ih₁ H₁) (ih₂ H₁)

noncomputable def weakening1 {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢ f₂) : insert f₁ Γ ⊢ f₂ :=
  weakening (Set.subset_insert f₁ Γ) H

noncomputable def deduction {Γ : Set (formula L)} {A B : formula L} (H : Γ ⊢ A ⟹ B) : insert A Γ ⊢ B :=
  prf.impE A (weakening1 H) axm1

noncomputable def exfalso {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢ ⊥') : Γ ⊢ A :=
  prf.falsumE (weakening1 H)

/-! ## Theory and consistency (src/fol.lean lines 1105-) -/

def Theory (L : Language.{u}) := Set (formula L)

def is_consistent (T : Theory L) := ¬(T ⊢' ⊥')

/-! ## Structure — L-structures (src/fol.lean line 1109) -/

variable (L)

structure Structure : Type (u + 1) where
  carrier : Type u
  fun_map : ∀ {n}, L.functions n → DVec carrier n → carrier
  rel_map : ∀ {n}, L.relations n → DVec carrier n → Prop

variable {L}

instance : CoeSort (Structure L) (Type u) where
  coe S := S.carrier

/-! ## realize_term — realization of terms in a structure -/

@[simp] def realize_term {S : Structure L} (v : ℕ → S) :
    ∀ {l} (t : preterm L l) (xs : DVec S l), S.carrier
  | _, preterm.var k, _ => v k
  | _, preterm.func f, xs => S.fun_map f xs
  | _, preterm.app t₁ t₂, xs => realize_term v t₁ (DVec.cons (realize_term v t₂ DVec.nil) xs)

lemma realize_term_congr {S : Structure L} {v v' : ℕ → S} (h : ∀ n, v n = v' n) :
    ∀ {l} (t : preterm L l) (xs : DVec S l),
    realize_term v t xs = realize_term v' t xs
  | _, preterm.var k, _ => h k
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
      simp only [realize_term]
      rw [realize_term_congr h t₁, realize_term_congr h t₂]

lemma realize_term_subst {S : Structure L} (v : ℕ → S) :
    ∀ {l} (n : ℕ) (t : preterm L l) (s : term L) (xs : DVec S l),
    realize_term (subst_realize v (realize_term v (lift_term s n) DVec.nil) n) t xs =
    realize_term v (subst_term t s n) xs
  | _, n, preterm.var k, s, DVec.nil => by
      rcases Nat.lt_trichotomy k n with h | h | h
      · simp only [realize_term, subst_realize_lt _ _ h, subst_term_var_lt _ h]
      · subst h
        simp only [realize_term, subst_term_var_eq, subst_realize_var_eq, lift_term]
      · simp only [realize_term, subst_realize_gt _ _ h, subst_term_var_gt _ h]
  | _, _, preterm.func _, _, _ => rfl
  | _, n, preterm.app t₁ t₂, s, xs => by
      simp only [realize_term, subst_term]
      rw [realize_term_subst v n t₂ s DVec.nil]
      rw [realize_term_subst v n t₁ s]

lemma realize_term_subst_lift {S : Structure L} (v : ℕ → S) (x : S) (m : ℕ) :
    ∀ {l} (t : preterm L l) (xs : DVec S l),
    realize_term (subst_realize v x m) (lift_term_at t 1 m) xs = realize_term v t xs
  | _, preterm.var k, DVec.nil => by
      simp only [realize_term, lift_term_at]
      by_cases h : m ≤ k
      · -- lift gives k+1, subst_realize gives v k
        have hmk1 : m < k + 1 := Nat.lt_succ_of_le h
        simp only [if_pos h, subst_realize_gt _ _ hmk1, Nat.add_sub_cancel]
      · -- lift gives k, subst_realize gives v k (since k < m)
        have hkm : k < m := Nat.lt_of_not_le h
        simp only [if_neg h, realize_term, subst_realize_lt _ _ hkm]
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
      simp only [realize_term, lift_term_at]
      rw [realize_term_subst_lift v x m t₂ DVec.nil]
      rw [realize_term_subst_lift v x m t₁]

/-! ## realize_formula — satisfaction relation -/

@[simp] def realize_formula {S : Structure L} :
    ∀ {l}, (ℕ → S) → @preformula L l → DVec S l → Prop
  | _, v, preformula.falsum, _ => False
  | _, v, preformula.equal t₁ t₂, _ =>
      realize_term v t₁ DVec.nil = realize_term v t₂ DVec.nil
  | _, _, preformula.rel R, xs => S.rel_map R xs
  | _, v, preformula.apprel f t, xs =>
      realize_formula v f (DVec.cons (realize_term v t DVec.nil) xs)
  | _, v, preformula.imp f₁ f₂, xs =>
      realize_formula v f₁ xs → realize_formula v f₂ xs
  | _, v, preformula.all f, _ =>
      ∀ x : S, realize_formula (subst_realize v x 0) f DVec.nil

lemma realize_formula_congr {S : Structure L} :
    ∀ {l} {v v' : ℕ → S} (h : ∀ n, v n = v' n) (f : @preformula L l) (xs : DVec S l),
    realize_formula v f xs ↔ realize_formula v' f xs
  | _, _, _, _, preformula.falsum, _ => Iff.rfl
  | _, _, _, h, preformula.equal t₁ t₂, _ => by
      simp [realize_formula, realize_term_congr h]
  | _, _, _, _, preformula.rel _, _ => Iff.rfl
  | _, _, _, h, preformula.apprel f t, xs => by
      simp only [realize_formula, realize_term_congr h]
      exact realize_formula_congr h f _
  | _, _, _, h, preformula.imp f₁ f₂, xs => by
      simp only [realize_formula]
      exact Iff.imp (realize_formula_congr h f₁ xs) (realize_formula_congr h f₂ xs)
  | _, _, _, h, preformula.all f, _ => by
      simp only [realize_formula]
      apply forall_congr'
      intro x
      exact realize_formula_congr (subst_realize_congr h x 0) f DVec.nil

lemma realize_formula_subst {S : Structure L} :
    ∀ {l} (v : ℕ → S) (n : ℕ) (f : @preformula L l) (s : term L) (xs : DVec S l),
    realize_formula (subst_realize v (realize_term v (lift_term s n) DVec.nil) n) f xs ↔
    realize_formula v (subst_formula f s n) xs
  | _, _, _, preformula.falsum, _, _ => Iff.rfl
  | _, v, n, preformula.equal t₁ t₂, s, _ => by
      simp [realize_formula, realize_term_subst]
  | _, _, _, preformula.rel _, _, _ => Iff.rfl
  | _, v, n, preformula.apprel f t, s, xs => by
      simp only [realize_formula, subst_formula, realize_term_subst]
      exact realize_formula_subst v n f s _
  | _, v, n, preformula.imp f₁ f₂, s, xs => by
      simp only [realize_formula, subst_formula]
      exact Iff.imp (realize_formula_subst v n f₁ s xs) (realize_formula_subst v n f₂ s xs)
  | _, v, n, preformula.all f, s, _ => by
      simp only [realize_formula, subst_formula]
      apply forall_congr'
      intro x
      -- goal: realize_formula (subst_realize (subst_realize v ...) x 0) f [] ↔ realize_formula v (f[s//n+1]) []
      -- use: IH at n+1, then congr on valuation
      rw [← realize_formula_subst (subst_realize v x 0) (n + 1) f s DVec.nil]
      apply realize_formula_congr
      intro k
      -- Use subst_realize2_0 to swap the two substitutions:
      -- subst_realize (subst_realize v (realize_term v (lift_term s n) []) n) x 0 k
      -- = subst_realize (subst_realize v x 0) (realize_term v (lift_term s n) []) (n+1) k (by subst_realize2_0)
      -- And realize_term v (lift_term s n) [] = realize_term (subst_realize v x 0) (lift_term_at s 1 0 ↑ n) []
      --   since s ↑ n+1 applied then subst at 0 cancels the lift-at-0.
      -- Port from src/fol.lean:1178-1181:
      -- rw [subst_realize2_0, ←realize_term_subst_lift v x 0, lift_term_def, lift_term2]
      rw [subst_realize2_0]
      congr 1
      -- Goal: realize_term v (lift_term s n) [] = realize_term (subst_realize v x 0) (lift_term s (n+1)) []
      rw [← realize_term_subst_lift v x 0 (lift_term s n) DVec.nil]
      simp only [lift_term_def]
      rw [← lift_term2 s n 1]

lemma realize_formula_subst0 {S : Structure L} {l} (v : ℕ → S) (f : @preformula L l)
    (s : term L) (xs : DVec S l) :
    realize_formula (subst_realize v (realize_term v s DVec.nil) 0) f xs ↔
    realize_formula v (subst_formula f s 0) xs := by
  have h := realize_formula_subst v 0 f s
  simp only [lift_term_zero] at h
  exact h xs

lemma realize_formula_subst_lift {S : Structure L} :
    ∀ {l} (v : ℕ → S) (x : S) (m : ℕ) (f : @preformula L l) (xs : DVec S l),
    realize_formula (subst_realize v x m) (lift_formula_at f 1 m) xs = realize_formula v f xs
  | _, _, _, _, preformula.falsum, _ => rfl
  | _, v, x, m, preformula.equal t₁ t₂, _ => by
      simp [realize_formula, realize_term_subst_lift]
  | _, _, _, _, preformula.rel _, _ => rfl
  | _, v, x, m, preformula.apprel f t, xs => by
      simp only [realize_formula, lift_formula_at, realize_term_subst_lift]
      exact realize_formula_subst_lift v x m f _
  | _, v, x, m, preformula.imp f₁ f₂, xs => by
      simp only [realize_formula, lift_formula_at]
      exact propext (Iff.imp
        (Iff.of_eq (realize_formula_subst_lift v x m f₁ xs))
        (Iff.of_eq (realize_formula_subst_lift v x m f₂ xs)))
  | _, v, x, m, preformula.all f, _ => by
      simp only [realize_formula, lift_formula_at]
      apply propext
      apply forall_congr'
      intro x'
      rw [propext (realize_formula_congr (fun k => subst_realize2_0 v x' x m k) (lift_formula_at f 1 (m + 1)) DVec.nil)]
      exact Iff.of_eq (realize_formula_subst_lift (subst_realize v x' 0) x (m + 1) f DVec.nil)

/-! ## Semantic notions — satisfaction and models -/

def satisfied_in (S : Structure L) (f : formula L) : Prop :=
  ∀ v : ℕ → S, realize_formula v f DVec.nil

scoped infix:51 " ⊨ₛ " => Fol.satisfied_in

def satisfied (T : Set (formula L)) (f : formula L) : Prop :=
  ∀ (S : Structure L) (v : ℕ → S),
    (∀ f' ∈ T, realize_formula v (f' : formula L) DVec.nil) →
    realize_formula v f DVec.nil

scoped infix:51 " ⊨ " => Fol.satisfied

/-! ## Soundness (src/fol.lean lines 1247-1261) -/

lemma formula_soundness {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢ A) : Γ ⊨ A := by
  intro S
  induction H with
  | axm h => intro v hΓ; exact hΓ _ h
  | impI _ ih =>
    intro v hΓ ha
    apply ih
    intro f hf
    rcases hf with rfl | hf
    · exact ha
    · exact hΓ f hf
  | impE A _ _ ih₁ ih₂ => intro v hΓ; exact ih₁ v hΓ (ih₂ v hΓ)
  | falsumE _ ih =>
    intro v hΓ
    by_contra ha
    apply ih v
    intro f hf
    rcases hf with rfl | hf
    · exact ha
    · exact hΓ f hf
  | allI _ ih =>
    intro v hΓ x
    apply ih
    intro f hf
    rcases hf with ⟨f', hf', rfl⟩
    rw [realize_formula_subst_lift v x 0 f']
    exact hΓ f' hf'
  | allE₂ A t _ ih =>
    intro v hΓ
    rw [← realize_formula_subst0]
    exact ih v hΓ (realize_term v t DVec.nil)
  | ref => intro v _; simp [realize_formula]
  | subst₂ s t f _ _ ih₁ ih₂ =>
    intro v hΓ
    have h' := ih₁ v hΓ
    simp only [realize_formula] at h'
    rw [← realize_formula_subst0, ← h', realize_formula_subst0]
    exact ih₂ v hΓ

/-! ## bounded_preterm, bounded_term, closed_preterm (src/fol.lean lines 1265-1660) -/

-- Bring L back to explicit so that bounded_preterm's constructors can refer to the
-- inductive type unambiguously (same pattern as Structure and formula above).
variable (L)

variable {L}

namespace bounded_preterm

/-- Equality of bounded preterms is determined by their underlying preterms. -/
@[ext] protected theorem eq {n} : ∀ {l} {t₁ t₂ : bounded_preterm L n l},
    t₁.fst = t₂.fst → t₁ = t₂
  | _, bd_var k, bd_var k', h => by
      simp [bounded_preterm.fst] at h
      congr 1; exact Fin.ext h
  | _, bd_var _, bd_func _, h => by simp [bounded_preterm.fst] at h
  | _, bd_var _, bd_app _ _, h => by simp [bounded_preterm.fst] at h
  | _, bd_func _, bd_var _, h => by simp [bounded_preterm.fst] at h
  | _, bd_func f, bd_func f', h => by
      simp [bounded_preterm.fst] at h; exact congrArg bd_func h
  | _, bd_func _, bd_app _ _, h => by simp [bounded_preterm.fst] at h
  | _, bd_app _ _, bd_var _, h => by simp [bounded_preterm.fst] at h
  | _, bd_app _ _, bd_func _, h => by simp [bounded_preterm.fst] at h
  | _, bd_app t₁ t₂, bd_app t₁' t₂', h => by
      simp only [bounded_preterm.fst, preterm.app.injEq] at h
      exact congrArg₂ bd_app (bounded_preterm.eq h.1) (bounded_preterm.eq h.2)

@[simp] lemma cast_rfl {n} {h : n ≤ n} : ∀ {l} (t : bounded_preterm L n l), t.cast h = t := by
  intros l t; induction t with
  | bd_var k => simp [bounded_preterm.cast, Fin.ext_iff]
  | bd_func => rfl
  | bd_app _ _ iht ihs => simp [bounded_preterm.cast, iht, ihs]

protected def cast_eq {n m l} (h : n = m) (t : bounded_preterm L n l) : bounded_preterm L m l :=
  t.cast (Nat.le_of_eq h)

@[simp] lemma cast_fst {n m} (h : n ≤ m) : ∀ {l} (t : bounded_preterm L n l),
    (t.cast h).fst = t.fst
  | _, bd_var k => rfl
  | _, bd_func f => rfl
  | _, bd_app t s => by simp [bounded_preterm.cast, cast_fst h t, cast_fst h s]

@[simp] lemma cast_eq_fst {n m l} (h : n = m) (t : bounded_preterm L n l) :
    (t.cast_eq h).fst = t.fst := cast_fst _ t

end bounded_preterm

namespace closed_preterm

end closed_preterm

/-! ### bounded_term.rec — custom recursion principle -/

/-- Custom recursion principle for bounded terms, analogous to `term.rec`. -/
def bounded_term.rec {n} {C : bounded_term L n → Sort v}
    (hvar : ∀ (k : Fin n), C (bd_var k))
    (hfunc : ∀ {l} (f : L.functions l) (ts : DVec (bounded_term L n) l)
      (ih_ts : ∀ t, DVec.pmem t ts → C t), C (bd_apps (bd_func f) ts)) :
    ∀ (t : bounded_term L n), C t :=
  let rec go : ∀ {l} (t : bounded_preterm L n l) (ts : DVec (bounded_term L n) l)
      (ih_ts : ∀ s, DVec.pmem s ts → C s), C (bd_apps t ts)
    | _, bd_var k, ts, _ => by rw [DVec.zero_eq ts]; exact hvar k
    | _, bd_func f, ts, ih_ts => hfunc f ts ih_ts
    | _, bd_app t₁ t₂, ts, ih_ts =>
        go t₁ (DVec.cons t₂ ts) fun t ht => by
          cases ht with
          | inl h => exact h ▸ go t₂ DVec.nil (fun s hs => hs.elim)
          | inr h => exact ih_ts t h
  fun t => go t DVec.nil (fun s hs => hs.elim)

/-! ### Lift and substitution — irrel lemmas -/

/-! ### realize_bounded_term -/

/-- Realize a bounded preterm given a valuation vector `v : DVec S n` and extra args `xs : DVec S l`. -/
@[simp] def realize_bounded_term {S : Structure L} {n} (v : DVec S n) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l), S.carrier
  | _, bd_var k, _ => v.nth k.1 k.2
  | _, bd_func f, xs => S.fun_map f xs
  | _, bd_app t₁ t₂, xs =>
      realize_bounded_term v t₁ (DVec.cons (realize_bounded_term v t₂ DVec.nil) xs)

/-- Notation for realizing a bounded term with an empty extra argument list. -/
notation:0 S "[" t " ;;; " v "]" => @realize_bounded_term _ S _ v 0 t DVec.nil

notation:0 S "[" t " ;;; " v " ;;; " xs "]" => @realize_bounded_term _ S _ v _ t xs

lemma realize_bounded_term_eq {S : Structure L} {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l),
    realize_bounded_term v₁ t xs = realize_term v₂ t.fst xs
  | _, bd_var k, _ => hv k.1 k.2
  | _, bd_func f, xs => rfl
  | _, bd_app t₁ t₂, xs => by
      simp only [realize_bounded_term, bounded_preterm.fst, realize_term]
      rw [realize_bounded_term_eq hv t₂ DVec.nil, realize_bounded_term_eq hv t₁]

/-! ### lift_bounded_term_at — lifting bounded terms -/

@[simp] lemma lift_bounded_term_fst {n} : ∀ {l} (t : bounded_preterm L n l) (n' m : ℕ),
    (lift_bounded_term_at t n' m).fst = t.fst ↑' n' # m
  | _, bd_var k, n', m => by
      simp only [lift_bounded_term_at, bounded_preterm.fst, lift_term_at]
      split_ifs with h <;> simp [h]
  | _, bd_func _, _, _ => rfl
  | _, bd_app t₁ t₂, n', m => by
      simp [lift_bounded_term_fst t₁ n' m, lift_bounded_term_fst t₂ n' m]

/-! ### subst_bounded_term — substitution in bounded terms -/

notation:0 t "[" s " /// " n "]" => @subst_bounded_term _ n _ _ t s

@[simp] lemma subst_bounded_term_var_eq {n n'} (s : bounded_term L n') (k : Fin (n + n' + 1))
    (h : k.1 = n) : (subst_bounded_term (bd_var k) s).fst = s.fst ↑' n # 0 := by
  have h₂ : ¬(k.1 < n) := by omega
  have h₃ : ¬(n < k.1) := by omega
  simp only [subst_bounded_term, h₂, h₃, dite_false, if_false]
  exact (bounded_preterm.cast_fst _ (s ↑ᵇ n)).trans (lift_bounded_term_fst s n 0)

@[simp] lemma subst_bounded_term_fst {n n'} : ∀ {l} (t : bounded_preterm L (n + n' + 1) l)
    (s : bounded_term L n'), (subst_bounded_term t s).fst = subst_term t.fst s.fst n
  | _, bd_var k, s => by
      rcases Nat.lt_trichotomy k.1 n with h | h | h
      · simp [h, subst_bounded_term]
      · rw [subst_bounded_term_var_eq s k h]
        simp [subst_term, subst_realize, h]
      · simp [subst_bounded_term, h, Nat.not_lt.mpr (Nat.le_of_lt h), subst_term, subst_realize,
              Nat.lt_asymm h]
  | _, bd_func f, _ => rfl
  | _, bd_app t₁ t₂, s => by
      exact congrArg₂ preterm.app (subst_bounded_term_fst t₁ s)
        (subst_bounded_term_fst t₂ s)

/-! ## bounded_preformula, bounded_formula, presentence, sentence (src/fol.lean lines 1660-2200) -/

variable (L)

variable {L}

/-! ### bounded_preformula notations -/

-- Note: ≃ and ⟹ and ∀' are already declared for preformula/preterm above (scoped).
-- We overload them here for bounded_preformula. Since these are scoped notations,
-- we extend existing ones in the Fol namespace.

-- bd_falsum notation conflicts with preformula.falsum ⊥'; we use bd_falsum directly.
-- The bounded equality and implication will reuse the same notation symbols.

scoped prefix:max "∼ᵇ" => Fol.bd_not

scoped infixr:69 " ⊓ᵇ " => Fol.bd_and

scoped infixr:68 " ⊔ᵇ " => Fol.bd_or

scoped infix:61 " ⇔ᵇ " => Fol.bd_biimp

scoped prefix:110 "∃ᵇ" => Fol.bd_ex

/-! ### bd_apps_rel -/

@[simp] lemma bd_apps_rel_zero {n} (f : bounded_formula L n)
    (ts : DVec (bounded_term L n) 0) : bd_apps_rel f ts = f := by
  cases ts; rfl

/-! ### namespace bounded_preformula -/

namespace bounded_preformula

/-- Equality of bounded_preformulas is determined by their underlying preformulas. -/
@[ext] protected theorem eq : ∀ {n l} {f₁ f₂ : bounded_preformula L n l},
    f₁.fst = f₂.fst → f₁ = f₂
  | _, _, bd_falsum, bd_falsum, _ => rfl
  | _, _, bd_equal t₁ t₂, bd_equal t₁' t₂', h => by
      simp only [bounded_preformula.fst, preformula.equal.injEq] at h
      exact congrArg₂ bd_equal (bounded_preterm.eq h.1) (bounded_preterm.eq h.2)
  | _, _, bd_rel R, bd_rel R', h => by
      simp only [bounded_preformula.fst, preformula.rel.injEq] at h
      exact congrArg bd_rel h
  | _, _, bd_apprel f t, bd_apprel f' t', h => by
      simp only [bounded_preformula.fst, preformula.apprel.injEq] at h
      exact congrArg₂ bd_apprel (bounded_preformula.eq h.1) (bounded_preterm.eq h.2)
  | _, _, bd_imp f₁ f₂, bd_imp f₁' f₂', h => by
      simp only [bounded_preformula.fst, preformula.imp.injEq] at h
      exact congrArg₂ bd_imp (bounded_preformula.eq h.1) (bounded_preformula.eq h.2)
  | _, _, bd_all f, bd_all f', h => by
      simp only [bounded_preformula.fst, preformula.all.injEq] at h
      exact congrArg bd_all (bounded_preformula.eq h)
  -- cross-constructor cases: fst is in different constructors
  | _, _, bd_falsum, bd_equal _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_falsum, bd_rel _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_falsum, bd_imp _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_falsum, bd_all _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_equal _ _, bd_falsum, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_equal _ _, bd_imp _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_equal _ _, bd_all _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_rel _, bd_apprel _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_apprel _ _, bd_rel _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_imp _ _, bd_falsum, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_imp _ _, bd_equal _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_imp _ _, bd_all _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_all _, bd_falsum, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_all _, bd_equal _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_all _, bd_imp _ _, h => by simp [bounded_preformula.fst] at h

@[simp] lemma cast_rfl {n} {h : n ≤ n} : ∀ {l} (f : bounded_preformula L n l), f.cast h = f
  | _, bd_falsum => rfl
  | _, bd_equal t₁ t₂ => by
      exact congrArg₂ bd_equal (bounded_preterm.cast_rfl t₁) (bounded_preterm.cast_rfl t₂)
  | _, bd_rel _ => rfl
  | _, bd_apprel f t => by
      exact congrArg₂ bd_apprel (cast_rfl f) (bounded_preterm.cast_rfl t)
  | _, bd_imp f₁ f₂ => by simp [bounded_preformula.cast, cast_rfl f₁, cast_rfl f₂]
  | _, bd_all f => by simp [bounded_preformula.cast, cast_rfl f]

@[simp] lemma cast_fst : ∀ {l n m} (h : n ≤ m) (f : bounded_preformula L n l),
    (f.cast h).fst = f.fst
  | _, _, _, _, bd_falsum => rfl
  | _, _, _, h, bd_equal t₁ t₂ => by
      exact congrArg₂ preformula.equal (bounded_preterm.cast_fst h t₁)
        (bounded_preterm.cast_fst h t₂)
  | _, _, _, _, bd_rel _ => rfl
  | _, _, _, h, bd_apprel f t => by
      exact congrArg₂ preformula.apprel (cast_fst h f) (bounded_preterm.cast_fst h t)
  | _, _, _, h, bd_imp f₁ f₂ => by simp [bounded_preformula.cast, cast_fst h f₁, cast_fst h f₂]
  | _, _, _, h, bd_all f => by simp [bounded_preformula.cast, cast_fst (Nat.succ_le_succ h) f]

@[simp] lemma cast_eq_fst {l n m} (h : n = m) (f : bounded_preformula L n l) :
    (f.cast_eq h).fst = f.fst := cast_fst _ f

end bounded_preformula

/-! ### namespace presentence -/

namespace presentence

end presentence

/-! ### Irrel lemmas for bounded formulas -/

/-! ### realize_bounded_formula -/

@[simp] def realize_bounded_formula {S : Structure L} :
    ∀ {n l} (v : DVec S n) (f : bounded_preformula L n l) (xs : DVec S l), Prop
  | _, _, v, bd_falsum, _ => False
  | _, _, v, bd_equal t₁ t₂, _ =>
      realize_bounded_term v t₁ DVec.nil = realize_bounded_term v t₂ DVec.nil
  | _, _, _, bd_rel R, xs => S.rel_map R xs
  | _, _, v, bd_apprel f t, xs =>
      realize_bounded_formula v f (DVec.cons (realize_bounded_term v t DVec.nil) xs)
  | _, _, v, bd_imp f₁ f₂, xs =>
      realize_bounded_formula v f₁ xs → realize_bounded_formula v f₂ xs
  | _, _, v, bd_all f, xs =>
      ∀ x : S, realize_bounded_formula (DVec.cons x v) f xs

@[reducible] def realize_sentence (S : Structure L) (f : sentence L) : Prop :=
  realize_bounded_formula (DVec.nil : DVec S 0) f DVec.nil

scoped infix:51 " ⊨ₘ " => Fol.realize_sentence

/-! ### realize_bounded_formula lemmas -/

-- Helper for realize_bounded_formula_iff: structural recursion over f
def realize_bounded_formula_iff_aux {S : Structure L} :
    ∀ {n l} (f : bounded_preformula L n l) (v₁ : DVec S n) (v₂ : ℕ → S)
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) (xs : DVec S l),
    realize_bounded_formula v₁ f xs ↔ realize_formula v₂ f.fst xs
  | _, _, bd_falsum, _, _, _, _ => Iff.rfl
  | _, _, bd_equal t₁ t₂, v₁, v₂, hv, _ => by
      change (realize_bounded_term v₁ t₁ DVec.nil = realize_bounded_term v₁ t₂ DVec.nil) ↔
        (realize_term v₂ t₁.fst DVec.nil = realize_term v₂ t₂.fst DVec.nil)
      rw [realize_bounded_term_eq hv t₁ DVec.nil, realize_bounded_term_eq hv t₂ DVec.nil]
  | _, _, bd_rel _, _, _, _, _ => Iff.rfl
  | _, _, bd_apprel f t, v₁, v₂, hv, xs => by
      change realize_bounded_formula v₁ f (DVec.cons (realize_bounded_term v₁ t DVec.nil) xs) ↔
        realize_formula v₂ f.fst (DVec.cons (realize_term v₂ t.fst DVec.nil) xs)
      rw [realize_bounded_term_eq hv t DVec.nil]
      exact realize_bounded_formula_iff_aux f v₁ v₂ hv _
  | _, _, bd_imp f₁ f₂, v₁, v₂, hv, xs => by
      simp only [realize_bounded_formula, bounded_preformula.fst, realize_formula]
      exact Iff.imp (realize_bounded_formula_iff_aux f₁ v₁ v₂ hv xs)
                    (realize_bounded_formula_iff_aux f₂ v₁ v₂ hv xs)
  | n, _, bd_all f, v₁, v₂, hv, _ => by
      simp only [realize_bounded_formula, bounded_preformula.fst, realize_formula]
      apply forall_congr'
      intro x
      have hv' : ∀ k (hk : k < n + 1), (DVec.cons x v₁).nth k hk = subst_realize v₂ x 0 k := by
        intro k hk
        cases k with
        | zero => simp [DVec.nth, subst_realize]
        | succ k =>
          have hk' : k < n := Nat.lt_of_succ_lt_succ hk
          simp only [DVec.nth, subst_realize, Nat.zero_lt_succ, ↓reduceIte, Nat.succ_ne_zero,
                     if_false, Nat.add_sub_cancel]
          exact hv k hk'
      -- f : bounded_preformula L (n+1) 0; DVec.cons x v₁ : DVec S (n+1)
      -- goal: realize_bounded_formula (DVec.cons x v₁) f x✝ ↔ realize_formula (subst_realize v₂ x 0) f.fst DVec.nil
      -- x✝ : DVec S 0, so x✝ = DVec.nil
      simp only [DVec.zero_eq]
      exact realize_bounded_formula_iff_aux f (DVec.cons x v₁) (subst_realize v₂ x 0) hv' DVec.nil

lemma realize_bounded_formula_iff {S : Structure L} {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k)
    {l} (f : bounded_preformula L n l) (xs : DVec S l) :
    realize_bounded_formula v₁ f xs ↔ realize_formula v₂ f.fst xs :=
  realize_bounded_formula_iff_aux f v₁ v₂ hv xs

/-! ### bounded_formula_of_relation -/

/-- Recursor for bounded_formula at any n. -/
def bounded_formula.rec {C : ∀ n, bounded_formula L n → Sort v}
    (hfalsum : ∀ {n}, C n bd_falsum)
    (hequal : ∀ {n} (t₁ t₂ : bounded_term L n), C n (bd_equal t₁ t₂))
    (hrel : ∀ {n l : ℕ} (R : L.relations l) (ts : DVec (bounded_term L n) l),
            C n (bd_apps_rel (bd_rel R) ts))
    (himp : ∀ {n} {f₁ f₂ : bounded_formula L n} (ih₁ : C n f₁) (ih₂ : C n f₂),
            C n (bd_imp f₁ f₂))
    (hall : ∀ {n} {f : bounded_formula L (n + 1)} (ih : C (n + 1) f), C n (bd_all f)) :
    ∀ {{n : ℕ}} (f : bounded_formula L n), C n f :=
  let rec go : ∀ {n l} (f : bounded_preformula L n l)
               (ts : DVec (bounded_term L n) l), C n (bd_apps_rel f ts)
    | _, _, bd_falsum, ts => by simp only [DVec.zero_eq ts]; exact hfalsum
    | _, _, bd_equal t₁ t₂, ts => by simp only [DVec.zero_eq ts]; exact hequal t₁ t₂
    | _, _, bd_rel R, ts => hrel R ts
    | _, _, bd_apprel f t, ts => go f (DVec.cons t ts)
    | _, _, bd_imp f₁ f₂, ts => by
        simp only [DVec.zero_eq ts]
        exact himp (go f₁ DVec.nil) (go f₂ DVec.nil)
    | _, _, bd_all f, ts => by
        simp only [DVec.zero_eq ts]
        exact hall (go f DVec.nil)
  fun {{n}} f => bd_apps_rel_zero f DVec.nil ▸ go f DVec.nil

/-! ### substmax_bounded_formula — substitute the max (last) variable -/

@[simp] lemma subst_bounded_formula_fst : ∀ {n n' n'' l} (f : bounded_preformula L n'' l)
    (s : bounded_term L n') (h : n + n' + 1 = n''),
    (subst_bounded_formula f s h).fst = subst_formula f.fst s.fst n
  | _, _, _, _, bd_falsum, _, _ => rfl
  | _, _, _, _, bd_equal t₁ t₂, s, rfl => by
      exact congrArg₂ preformula.equal (subst_bounded_term_fst t₁ s)
        (subst_bounded_term_fst t₂ s)
  | _, _, _, _, bd_rel _, _, _ => rfl
  | _, _, _, _, bd_apprel f t, s, rfl => by
      exact congrArg₂ preformula.apprel (subst_bounded_formula_fst f s rfl)
        (subst_bounded_term_fst t s)
  | _, _, _, _, bd_imp f₁ f₂, s, rfl => by
      simp [subst_bounded_formula, subst_bounded_formula_fst f₁ s rfl,
            subst_bounded_formula_fst f₂ s rfl]
  | n, n', _, _, bd_all f, s, rfl => by
      simp only [subst_bounded_formula, bounded_preformula.fst, bounded_preformula.cast_eq_fst]
      rw [subst_bounded_formula_fst f s (by omega : (n + 1) + n' + 1 = n + n' + 1 + 1)]
      simp [subst_formula]

@[simp] lemma subst0_bounded_formula_fst {n l} (f : bounded_preformula L (n + 1) l)
    (s : bounded_term L n) : (subst0_bounded_formula f s).fst = subst_formula f.fst s.fst 0 := by
  simp only [subst0_bounded_formula, bounded_preformula.cast_eq_fst]
  rw [subst_bounded_formula_fst f s (by omega : 0 + n + 1 = n + 1)]

/-! ### realize_sentence lemmas -/

lemma realize_sentence_iff {S : Structure L} (v : ℕ → S) (f : sentence L) :
    realize_sentence S f ↔ realize_formula v f.fst DVec.nil := by
  apply realize_bounded_formula_iff
  intro k hk
  exact absurd hk (Nat.not_lt_zero k)

/-! ### lift_bounded_formula_at — lift bounded formulas -/

@[reducible] def lift_bounded_formula {n l} (f : bounded_preformula L n l) (n' : ℕ) :
    bounded_preformula L (n + n') l := lift_bounded_formula_at f n' 0

infixl:100 " ↑ᶠᵇ " => Fol.lift_bounded_formula

@[simp] lemma lift_bounded_formula_fst : ∀ {n l} (f : bounded_preformula L n l) (n' m : ℕ),
    (lift_bounded_formula_at f n' m).fst = lift_formula_at f.fst n' m
  | _, _, bd_falsum, _, _ => rfl
  | _, _, bd_equal t₁ t₂, n', m => by
      exact congrArg₂ preformula.equal (lift_bounded_term_fst t₁ n' m)
        (lift_bounded_term_fst t₂ n' m)
  | _, _, bd_rel _, _, _ => rfl
  | _, _, bd_apprel f t, n', m => by
      exact congrArg₂ preformula.apprel (lift_bounded_formula_fst f n' m)
        (lift_bounded_term_fst t n' m)
  | _, _, bd_imp f₁ f₂, n', m => by
      simp [lift_bounded_formula_fst f₁ n' m, lift_bounded_formula_fst f₂ n' m]
  | n, _, bd_all f, n', m => by
      simp only [lift_bounded_formula_at, bounded_preformula.fst, bounded_preformula.cast_eq_fst,
                 lift_bounded_formula_fst f n' (m + 1)]
      rfl

/-! ## Sentence theories (src/fol.lean lines 2233-2759) -/

/-- Derivability for sentence theories: T.fst ⊢ f.fst -/
def SentTheory.sprf (T : SentTheory L) (f : sentence L) : Type u := T.fst ⊢ f.fst

/-- Provability (nonempty-wrapped) for sentence theories -/
def SentTheory.sprovable (T : SentTheory L) (f : sentence L) : Prop := T.fst ⊢' f.fst

scoped notation:51 T " ⊢ₛ " f => Fol.SentTheory.sprf T f
scoped notation:51 T " ⊢ₛ' " f => Fol.SentTheory.sprovable T f

/-! ### All-realize-sentence — a structure models a sentence theory -/

/-- A structure S realizes all sentences in T -/
def all_realize_sentence (S : Structure L) (T : SentTheory L) : Prop :=
  ∀ ⦃f⦄, f ∈ T → S ⊨ₘ f

-- Use ⊨ₜ for "structure realizes a sentence theory" (distinct from existing ⊨ₛ)
scoped notation:51 S " ⊨ₜ " T => Fol.all_realize_sentence S T

/-! ### ssatisfied — semantic consequence for sentence theories -/

-- Note: ⊨ₛ is already taken by satisfied_in; use ssatisfied directly.

/-! ### Connection between ssatisfied and satisfied -/

/-! ## Model — bundled structure satisfying a sentence theory -/

/-- A model of T is a structure satisfying T.
    Lean 3 `Σ' (S : Structure L), S ⊨ T` → Lean 4 `{S : Structure L // all_realize_sentence S T}` -/
def Model (T : SentTheory L) : Type (u + 1) :=
  {S : Structure L // all_realize_sentence S T}

namespace Model

variable {T : SentTheory L}

end Model

/-! ### Soundness at sentence level -/

/-! ### Sentence-level is_consistent -/

/-! ### eliminates_quantifiers -/

/-! ### L_empty, T_empty, T_equality -/

/-! ## Section bd_alls (src/fol.lean lines 2706-2757) -/

end Fol
