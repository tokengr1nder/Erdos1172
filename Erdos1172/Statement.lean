/-
Copyright 2019 The Flypitch Project; 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Filter.CardinalInter
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Ordinal.Exponential

@[expose] public section

/-!
# Statement Definitions for Erdős Problem 1172

This self-contained Mathlib-only module defines every object appearing in the formal
statements of Parts (ii)–(iv) of [Erdős Problem 1172](https://www.erdosproblems.com/1172) and
the countable-color partial step `ω₃ → (ω₂ + 1)²_ω` toward the open original Part (i)
(`ω₃ → (ω₂ + 2)²_ω` under `GCH`), assembled from Baumgartner–Hajnal–Todorčević
(`[BHT93, p. 2]`, `arXiv:math/9311207`), the 1999 Budapest conference problem booklet
(`[Va99, 7.87]`, p. 13), and Erdős–Hajnal (`[ErHa74, p. 272]`):

1. First-order logic with equality (`Fol.Language`, de Bruijn terms/formulas, the classical
   natural-deduction calculus `Fol.prf`, and syntactic consistency `Fol.SentTheory.is_consistent`)
   and the first-order theory `ZFC` over `L_ZFC = {∅, pair, ω, P, ⋃, ∈}`, reproduced verbatim
   from Han–van Doorn's Flypitch foundation (`Flypitch4`).
2. The closed parameter-free `L_ZFC`-sentences `fullGCHSentence` (`∀ κ ≥ ω, 2^|κ| = |κ|⁺`),
   `part4Sentence` (`ω₂ → (ω₁ + ω, ω₁ + ω)²`), and `gchPart4Theory := ZFC ∪ {fullGCHSentence, part4Sentence}`.
3. Kanamori's canonical `[θ]^{ot = κ}` huge-cardinal predicates `IsHugeWithTarget` and `IsHugeCardinal`.
4. `Cardinal.CH`, `Cardinal.GCH`, `OrdinalRamsey`, `OrdinalCountableRamsey`, and the target
   abbreviations `Erdos1172.Part1CountableStep`, `Part2`, `Part3`.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

universe u v

inductive DVec (α : Type u) : ℕ → Type u
  | nil  : DVec α 0
  | cons : ∀ {n} (x : α) (xs : DVec α n), DVec α (n + 1)

def Arity' (α β : Type u) : ℕ → Type u
  | 0 => β
  | n + 1 => α → Arity' α β n

namespace Arity'
@[simp] def of_dvector_map {α β : Type u} : ∀ {l} (f : DVec α l → β), Arity' α β l
  | 0, f => f DVec.nil
  | l + 1, f => fun x => of_dvector_map (fun xs => f (DVec.cons x xs))
end Arity'

namespace Fol

def subst_realize {S : Type u} (v : ℕ → S) (x : S) (n k : ℕ) : S :=
  if k < n then v k else if n < k then v (k - 1) else x

structure Language : Type (u + 1) where
  functions : ℕ → Type u
  relations : ℕ → Type u

def Language.constants (L : Language.{u}) := L.functions 0

variable (L : Language.{u})

inductive preterm : ℕ → Type u
  | var : ∀ (k : ℕ), preterm 0
  | func : ∀ {l : ℕ} (f : L.functions l), preterm l
  | app : ∀ {l : ℕ} (t : preterm (l + 1)) (s : preterm 0), preterm l

@[reducible] def term := preterm L 0

variable {L}

prefix:max "&" => Fol.preterm.var

@[simp] def lift_term_at : ∀ {l}, preterm L l → ℕ → ℕ → preterm L l
  | _, preterm.var k, n, m => &(if m ≤ k then k + n else k)
  | _, preterm.func f, _, _ => preterm.func f
  | _, preterm.app t₁ t₂, n, m => preterm.app (lift_term_at t₁ n m) (lift_term_at t₂ n m)

notation:90 t " ↑' " n " # " m => Fol.lift_term_at t n m

@[reducible] def lift_term {l} (t : preterm L l) (n : ℕ) : preterm L l := lift_term_at t n 0

infixl:100 " ↑ " => Fol.lift_term

@[reducible, simp] def lift_term1 {l} (t : preterm L l) : preterm L l := lift_term t 1

def subst_term : ∀ {l}, preterm L l → term L → ℕ → preterm L l
  | _, preterm.var k, s, n => Fol.subst_realize preterm.var (lift_term s n) n k
  | _, preterm.func f, _, _ => preterm.func f
  | _, preterm.app t₁ t₂, s, n => preterm.app (subst_term t₁ s n) (subst_term t₂ s n)

inductive preformula : ℕ → Type u
  | falsum : preformula 0
  | equal (t₁ t₂ : term L) : preformula 0
  | rel {l : ℕ} (R : L.relations l) : preformula l
  | apprel {l : ℕ} (f : preformula (l + 1)) (t : term L) : preformula l
  | imp (f₁ f₂ : preformula 0) : preformula 0
  | all (f : preformula 0) : preformula 0

variable (L)
@[reducible] def formula (L : Language.{u}) : Type u := @preformula L 0
variable {L}

notation "⊥'" => Fol.preformula.falsum
scoped infix:88 " ≃ " => Fol.preformula.equal
scoped infixr:62 " ⟹ " => Fol.preformula.imp
scoped prefix:110 "∀'" => Fol.preformula.all

def not' (f : formula L) : formula L := preformula.imp f preformula.falsum
scoped prefix:max "∼" => Fol.not'

@[simp] def lift_formula_at : ∀ {l}, @preformula L l → ℕ → ℕ → @preformula L l
  | _, preformula.falsum, _, _ => preformula.falsum
  | _, preformula.equal t₁ t₂, n, m => preformula.equal (lift_term_at t₁ n m) (lift_term_at t₂ n m)
  | _, preformula.rel R, _, _ => preformula.rel R
  | _, preformula.apprel f t, n, m => preformula.apprel (lift_formula_at f n m) (lift_term_at t n m)
  | _, preformula.imp f₁ f₂, n, m => preformula.imp (lift_formula_at f₁ n m) (lift_formula_at f₂ n m)
  | _, preformula.all f, n, m => preformula.all (lift_formula_at f n (m + 1))

notation:90 f " ↑f' " n " # " m => Fol.lift_formula_at f n m

@[reducible] def lift_formula {l} (f : @preformula L l) (n : ℕ) : @preformula L l :=
  lift_formula_at f n 0

infixl:100 " ↑f " => Fol.lift_formula

@[reducible, simp] def lift_formula1 {l} (f : @preformula L l) : @preformula L l := lift_formula f 1

@[simp] def subst_formula : ∀ {l}, @preformula L l → term L → ℕ → @preformula L l
  | _, preformula.falsum, _, _ => preformula.falsum
  | _, preformula.equal t₁ t₂, s, n => preformula.equal (subst_term t₁ s n) (subst_term t₂ s n)
  | _, preformula.rel R, _, _ => preformula.rel R
  | _, preformula.apprel f t, s, n => preformula.apprel (subst_formula f s n) (subst_term t s n)
  | _, preformula.imp f₁ f₂, s, n => preformula.imp (subst_formula f₁ s n) (subst_formula f₂ s n)
  | _, preformula.all f, s, n => preformula.all (subst_formula f s (n + 1))

notation:95 f " [" s " // " n "]f" => Fol.subst_formula f s n

/-- Classical natural-deduction proof trees for first-order logic with equality (`Γ ⊢ A`). -/
inductive prf : Set (formula L) → formula L → Type u
  | axm     {Γ A}   (h : A ∈ Γ) : prf Γ A
  | impI    {Γ : Set (formula L)} {A B} (h : prf (insert A Γ) B) : prf Γ (A ⟹ B)
  | impE    {Γ}     (A) {B} (h₁ : prf Γ (A ⟹ B)) (h₂ : prf Γ A) : prf Γ B
  | falsumE {Γ : Set (formula L)} {A} (h : prf (insert (∼A) Γ) ⊥') : prf Γ A
  | allI    {Γ A}   (h : prf (lift_formula1 '' Γ) A) : prf Γ (∀' A)
  | allE₂   {Γ}     (A) (t : term L) (h : prf Γ (∀' A)) : prf Γ (A [t // 0]f)
  | ref     (Γ)     (t : term L) : prf Γ (t ≃ t)
  | subst₂  {Γ}     (s t : term L) (f : formula L)
                    (h₁ : prf Γ (s ≃ t)) (h₂ : prf Γ (f [s // 0]f)) : prf Γ (f [t // 0]f)

scoped infix:51 " ⊢ " => Fol.prf
def provable (T : Set (formula L)) (f : formula L) := Nonempty (T ⊢ f)
scoped infix:51 " ⊢' " => Fol.provable

variable (L)

inductive bounded_preterm (L : Language.{u}) (n : ℕ) : ℕ → Type u
  | bd_var : ∀ (k : Fin n), bounded_preterm L n 0
  | bd_func : ∀ {l : ℕ} (f : L.functions l), bounded_preterm L n l
  | bd_app : ∀ {l : ℕ} (t : bounded_preterm L n (l + 1)) (s : bounded_preterm L n 0),
      bounded_preterm L n l

export bounded_preterm (bd_var bd_func bd_app)

def bounded_term (n : ℕ) := bounded_preterm L n 0
def closed_preterm (l : ℕ) := bounded_preterm L 0 l
def closed_term := closed_preterm L 0

variable {L}

prefix:max "&ᵇ" => @bd_var _ _

def bd_const {n} (c : L.constants) : bounded_term L n := bd_func c

@[simp] def bd_apps {n} : ∀ {l}, bounded_preterm L n l → DVec (bounded_term L n) l →
    bounded_term L n
  | _, t, DVec.nil => t
  | _, t, DVec.cons t' ts => bd_apps (bd_app t t') ts

namespace bounded_preterm
@[simp] protected def fst {n} : ∀ {l}, bounded_preterm L n l → preterm L l
  | _, bd_var k => &k.1
  | _, bd_func f => preterm.func f
  | _, bd_app t s => preterm.app (bounded_preterm.fst t) (bounded_preterm.fst s)

@[simp] protected def cast {n m} (h : n ≤ m) : ∀ {l}, bounded_preterm L n l →
    bounded_preterm L m l
  | _, bd_var k => bd_var ⟨k.1, Nat.lt_of_lt_of_le k.2 h⟩
  | _, bd_func f => bd_func f
  | _, bd_app t s => bd_app (t.cast h) (s.cast h)
end bounded_preterm

@[simp] def lift_bounded_term_at {n} : ∀ {l} (t : bounded_preterm L n l) (n' m : ℕ),
    bounded_preterm L (n + n') l
  | _, bd_var k, n', m =>
      if m ≤ k.1 then bd_var ⟨k.1 + n', Nat.add_lt_add_right k.2 n'⟩
      else bd_var ⟨k.1, Nat.lt_of_lt_of_le k.2 (Nat.le_add_right n n')⟩
  | _, bd_func f, _, _ => bd_func f
  | _, bd_app t₁ t₂, n', m => bd_app (lift_bounded_term_at t₁ n' m) (lift_bounded_term_at t₂ n' m)

notation:90 t " ↑ᵇ' " n " # " m => Fol.lift_bounded_term_at t n m

@[reducible] def lift_bounded_term {n l} (t : bounded_preterm L n l) (n' : ℕ) :
    bounded_preterm L (n + n') l := lift_bounded_term_at t n' 0

infixl:100 " ↑ᵇ " => Fol.lift_bounded_term

def subst_bounded_term {n n'} : ∀ {l} (t : bounded_preterm L (n + n' + 1) l)
    (s : bounded_term L n'), bounded_preterm L (n + n') l
  | _, bd_var k, s =>
      if h : k.1 < n then bd_var ⟨k.1, Nat.lt_of_lt_of_le h (Nat.le_add_right n n')⟩
      else if h' : n < k.1 then bd_var ⟨k.1 - 1, Nat.sub_lt_right_of_lt_add (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le n) h')) k.2⟩
      else (s ↑ᵇ n).cast (Nat.le_of_eq (Nat.add_comm n' n))
  | _, bd_func f, _ => bd_func f
  | _, bd_app t₁ t₂, s => bd_app (subst_bounded_term t₁ s) (subst_bounded_term t₂ s)

def bounded_term_of_function {l n} (f : L.functions l) :
    Arity' (bounded_term L n) (bounded_term L n) l :=
  Arity'.of_dvector_map (bd_apps (bd_func f))

variable (L)

inductive bounded_preformula (L : Language.{u}) : ℕ → ℕ → Type u
  | bd_falsum : ∀ {n}, bounded_preformula L n 0
  | bd_equal : ∀ {n} (t₁ t₂ : bounded_term L n), bounded_preformula L n 0
  | bd_rel : ∀ {n l : ℕ} (R : L.relations l), bounded_preformula L n l
  | bd_apprel : ∀ {n l} (f : bounded_preformula L n (l + 1)) (t : bounded_term L n),
      bounded_preformula L n l
  | bd_imp : ∀ {n} (f₁ f₂ : bounded_preformula L n 0), bounded_preformula L n 0
  | bd_all : ∀ {n} (f : bounded_preformula L (n + 1) 0), bounded_preformula L n 0

export bounded_preformula (bd_falsum bd_equal bd_rel bd_apprel bd_imp bd_all)

@[reducible] def bounded_formula (n : ℕ) := bounded_preformula L n 0
@[reducible] def presentence (l : ℕ) := bounded_preformula L 0 l
@[reducible] def sentence := presentence L 0

variable {L}

def bd_not {n} (f : bounded_formula L n) : bounded_formula L n := bd_imp f bd_falsum
def bd_and {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n := bd_not (bd_imp f₁ (bd_not f₂))
def bd_or {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n := bd_imp (bd_not f₁) f₂
def bd_biimp {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_and (bd_imp f₁ f₂) (bd_imp f₂ f₁)
def bd_ex {n} (f : bounded_formula L (n + 1)) : bounded_formula L n := bd_not (bd_all (bd_not f))

@[simp] def bd_apps_rel {n} : ∀ {l} (f : bounded_preformula L n l)
    (ts : DVec (bounded_term L n) l), bounded_formula L n
  | _, f, DVec.nil => f
  | _, f, DVec.cons t ts => bd_apps_rel (bd_apprel f t) ts

namespace bounded_preformula
@[simp] protected def fst : ∀ {n l}, bounded_preformula L n l → @preformula L l
  | _, _, bd_falsum => preformula.falsum
  | _, _, bd_equal t₁ t₂ => preformula.equal t₁.fst t₂.fst
  | _, _, bd_rel R => preformula.rel R
  | _, _, bd_apprel f t => preformula.apprel f.fst t.fst
  | _, _, bd_imp f₁ f₂ => preformula.imp f₁.fst f₂.fst
  | _, _, bd_all f => preformula.all f.fst

@[simp] protected def cast {n m} (h : n ≤ m) : ∀ {l}, bounded_preformula L n l →
    bounded_preformula L m l
  | _, bd_falsum => bd_falsum
  | _, bd_equal t₁ t₂ => bd_equal (t₁.cast h) (t₂.cast h)
  | _, bd_rel R => bd_rel R
  | _, bd_apprel f t => bd_apprel (f.cast h) (t.cast h)
  | _, bd_imp f₁ f₂ => bd_imp (f₁.cast h) (f₂.cast h)
  | _, bd_all f => bd_all (f.cast (Nat.succ_le_succ h))

protected def cast_eq {n m l} (h : n = m) (f : bounded_preformula L n l) :
    bounded_preformula L m l := f.cast (Nat.le_of_eq h)
end bounded_preformula

def bounded_formula_of_relation {l n} (R : L.relations l) :
    Arity' (bounded_term L n) (bounded_formula L n) l :=
  Arity'.of_dvector_map (bd_apps_rel (bd_rel R))

@[simp] def subst_bounded_formula : ∀ {n n' n'' l} (f : bounded_preformula L n'' l)
    (s : bounded_term L n') (_ : n + n' + 1 = n''), bounded_preformula L (n + n') l
  | _, _, _, _, bd_falsum, _, _ => bd_falsum
  | _, _, _, _, bd_equal t₁ t₂, s, rfl => bd_equal (subst_bounded_term t₁ s) (subst_bounded_term t₂ s)
  | _, _, _, _, bd_rel R, _, _ => bd_rel R
  | _, _, _, _, bd_apprel f t, s, rfl =>
      bd_apprel (subst_bounded_formula f s rfl) (subst_bounded_term t s)
  | _, _, _, _, bd_imp f₁ f₂, s, rfl =>
      bd_imp (subst_bounded_formula f₁ s rfl) (subst_bounded_formula f₂ s rfl)
  | n, n', _, _, bd_all f, s, rfl =>
      bd_all ((subst_bounded_formula f s (congrArg Nat.succ (Nat.succ_add n n'))).cast_eq
        (Nat.succ_add n n'))

def subst0_bounded_formula {n l} (f : bounded_preformula L (n + 1) l)
    (s : bounded_term L n) : bounded_preformula L n l :=
  (subst_bounded_formula f s (congrArg Nat.succ (Nat.zero_add n))).cast_eq (Nat.zero_add n)

@[simp] def lift_bounded_formula_at : ∀ {n l} (f : bounded_preformula L n l) (n' m : ℕ),
    bounded_preformula L (n + n') l
  | _, _, bd_falsum, _, _ => bd_falsum
  | _, _, bd_equal t₁ t₂, n', m => bd_equal (t₁ ↑ᵇ' n' # m) (t₂ ↑ᵇ' n' # m)
  | _, _, bd_rel R, _, _ => bd_rel R
  | _, _, bd_apprel f t, n', m => bd_apprel (lift_bounded_formula_at f n' m) (t ↑ᵇ' n' # m)
  | _, _, bd_imp f₁ f₂, n', m =>
      bd_imp (lift_bounded_formula_at f₁ n' m) (lift_bounded_formula_at f₂ n' m)
  | n, _, bd_all f, n', m =>
      bd_all ((lift_bounded_formula_at f n' (m + 1)).cast_eq (Nat.succ_add n n'))

notation:90 f " ↑ᶠᵇ' " n " # " m => Fol.lift_bounded_formula_at f n m

abbrev SentTheory (L : Language.{u}) := Set (sentence L)

@[reducible] def SentTheory.fst (T : SentTheory L) : Set (formula L) :=
  bounded_preformula.fst '' T

/-- Syntactic consistency of a first-order theory `T`: `⊥'` is not derivable from `T` in `Fol.prf`. -/
def SentTheory.is_consistent (T : SentTheory L) : Prop := ¬(T.fst ⊢' ⊥')

@[simp] def bd_alls : ∀ (n : ℕ), bounded_formula L n → sentence L
  | 0,     f => f
  | n + 1, f => bd_alls n (bd_all f)

end Fol

open Fol

inductive ZFC_rel : ℕ → Type 1
  | ε : ZFC_rel 2

inductive ZFC_func : ℕ → Type 1
  | emptyset : ZFC_func 0
  | pr       : ZFC_func 2
  | ω        : ZFC_func 0
  | P        : ZFC_func 1
  | Union    : ZFC_func 1

/-- First-order signature `L_ZFC = {∅, pair, ω, P, ⋃, ∈}` of Zermelo–Fraenkel set theory. -/
def L_ZFC : Language.{1} := { functions := ZFC_func, relations := ZFC_rel }

def emptyset' {n} : bounded_term L_ZFC n := bd_const ZFC_func.emptyset
notation "∅'" => emptyset'
def omega' {n} : bounded_term L_ZFC n := bd_const ZFC_func.ω
notation "ω'" => omega'
def Powerset {n} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n := bd_app (bd_func ZFC_func.P) t
notation "P'" => Powerset
def mem' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  @bounded_formula_of_relation L_ZFC 2 n ZFC_rel.ε t₁ t₂
def pair' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  @bounded_term_of_function L_ZFC 2 n ZFC_func.pr t₁ t₂
def union' {n} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n := bd_app (bd_func ZFC_func.Union) t
notation "⋃'" => union'

def subset'' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_all (bd_imp
    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (t₁ ↑ᵇ' 1 # 0))
    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (t₂ ↑ᵇ' 1 # 0)))

def is_transitive_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
                 (subset'' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)))

def epsilon_trichotomy_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
    (bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
      (bd_or
        (bd_or (bd_equal (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩))
               (mem' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))
        (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))))))

def epsilon_well_founded_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (subset'' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
    (bd_imp (bd_not (bd_equal (bd_var ⟨0, Nat.zero_lt_succ _⟩) ∅'))
      (bd_ex (bd_and (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
          (bd_not (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)))))))))

def ewo_f : bounded_formula L_ZFC 1 := bd_and epsilon_trichotomy_f epsilon_well_founded_f
def Ord_f : bounded_formula L_ZFC 1 := bd_and ewo_f is_transitive_f

def axiom_of_emptyset : sentence L_ZFC := bd_all (bd_not (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) ∅'))

def axiom_of_ordered_pairs : sentence L_ZFC :=
  bd_all (bd_all (bd_all (bd_all
    (bd_biimp
      (bd_equal (pair' (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
                (pair' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))
      (bd_and
        (bd_equal (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
        (bd_equal (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))))))

def axiom_of_extensionality : sentence L_ZFC :=
  bd_all (bd_all
    (bd_imp
      (bd_all (bd_biimp
        (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
        (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))))
      (bd_equal (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩))))

def axiom_of_collection {n} (ϕ : bounded_formula L_ZFC (n + 2)) : sentence L_ZFC :=
  bd_alls (n + 1) $
    bd_imp
      (bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
        (bd_ex (ϕ ↑ᶠᵇ' 1 # 2))))
      (bd_ex
        (bd_and
          (bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
            (bd_ex (bd_and
              (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
              (ϕ ↑ᶠᵇ' 2 # 2)))))
          (bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
            (bd_ex (bd_and
              (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩))
              (subst0_bounded_formula (ϕ ↑ᶠᵇ' 3 # 2) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))))))))

def axiom_of_union : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp
      (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (union' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)))
      (bd_ex (bd_and
        (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
        (mem' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩))))))

def axiom_of_powerset : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp
      (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (Powerset (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)))
      (bd_all (bd_imp
        (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
        (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))))))

def axiom_of_infinity : sentence L_ZFC :=
  bd_and
    (bd_and
      (bd_and
        (mem' ∅' ω')
        (bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) ω')
          (bd_ex (bd_and
            (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) ω')
            (mem' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))))))
      (bd_ex (bd_and Ord_f (bd_equal ω' (bd_var ⟨0, Nat.zero_lt_succ _⟩)))))
    (bd_all (bd_imp Ord_f (bd_imp
      (bd_and (mem' ∅' (bd_var ⟨0, Nat.zero_lt_succ _⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
          (bd_ex (bd_and
            (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
            (mem' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))))))
      (subset'' ω' (bd_var ⟨0, Nat.zero_lt_succ _⟩)))))

def axiom_of_regularity : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal (bd_var ⟨0, Nat.zero_lt_succ _⟩) ∅'))
    (bd_ex (bd_and (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
      (bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
        (bd_not (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))))))))

def zorns_lemma : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal (bd_var ⟨0, Nat.zero_lt_succ _⟩) ∅'))
    (bd_imp
      (bd_all (bd_imp
        (bd_and (subset'' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
          (bd_all (bd_all (bd_imp
            (bd_and (mem' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
                    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩)))
            (bd_or (subset'' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩))
                   (subset'' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)))))))
        (mem' (union' (bd_var ⟨0, Nat.zero_lt_succ _⟩)) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))))
      (bd_ex (bd_and (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
          (bd_imp (subset'' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩))
            (bd_equal (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))))))))

/-- First-order `ZFC` over `L_ZFC`: empty set, ordered pairs, extensionality, union, powerset,
infinity (as least limit ordinal `ω'`), regularity, Zorn's lemma, and the full unrestricted
strong collection schema. -/
def ZFC : SentTheory L_ZFC :=
  {axiom_of_emptyset, axiom_of_ordered_pairs, axiom_of_extensionality, axiom_of_union,
   axiom_of_powerset, axiom_of_infinity, axiom_of_regularity, zorns_lemma} ∪
  ⋃ (n : ℕ), axiom_of_collection '' (Set.univ : Set (bounded_formula L_ZFC (n + 2)))

def is_func_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (mem' (pair' (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)) (bd_var ⟨4, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))))⟩))
        (mem' (pair' (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)) (bd_var ⟨4, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))))⟩)))
      (bd_imp (bd_equal (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
              (bd_equal (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))))))

def is_total'_f : bounded_formula L_ZFC 3 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩))
    (bd_ex (bd_and
      (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩))
      (mem' (pair' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩)))))

def is_func'_f : bounded_formula L_ZFC 3 := bd_and (is_func_f.cast (Nat.succ_le_succ (Nat.zero_le 2))) is_total'_f

def is_inj_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (bd_and
          (mem' (pair' (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)) (bd_var ⟨4, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))))⟩))
          (mem' (pair' (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)) (bd_var ⟨4, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))))⟩)))
        (bd_equal (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))
      (bd_equal (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))))))

def injects_into_f : bounded_formula L_ZFC 2 := bd_ex (bd_and is_func'_f (is_inj_f.cast (Nat.succ_le_succ (Nat.zero_le 2))))

namespace Erdos1172Part4InternalCardinalLanguage
/-- Internal Hartogs relation `Hartogs(κ, α)`: `α` is the least ordinal not injecting into `κ`. -/
def least_noninjecting_ordinal_f : bounded_formula L_ZFC 2 :=
  bd_and (Ord_f ↑ᶠᵇ' 1 # 0)
    (bd_and (bd_not injects_into_f)
      (bd_all (bd_imp
        (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
        (subst0_bounded_formula
          (injects_into_f.cast (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 2))) : bounded_formula L_ZFC 4)
          (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)))))
end Erdos1172Part4InternalCardinalLanguage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true

open Fol

namespace Erdos1172Part4InternalPartitionLanguage
variable {n : ℕ}

def liftTerm (t : bounded_term L_ZFC n) : (k : ℕ) → bounded_term L_ZFC (n + k)
  | 0 => t
  | k + 1 => (liftTerm t k) ↑ᵇ 1

def singleValuedFormula (f : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (mem' (pair' (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)) (liftTerm f 4))
        (mem' (pair' (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)) (liftTerm f 4)))
      (bd_imp (bd_equal (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩))
        (bd_equal (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))))))

def totalOnFormula (A κ f : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_all (bd_imp (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (liftTerm A 1))
    (bd_ex (bd_and
      (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (liftTerm κ 2))
      (mem' (pair' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)) (liftTerm f 2)))))

def functionOnFormula (A κ f : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_and (singleValuedFormula f) (totalOnFormula A κ f)

def rangeMemFormula (A f x : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_ex (bd_and
    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (liftTerm A 1))
    (mem' (pair' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (liftTerm x 1)) (liftTerm f 1)))

def increasingFormula (A f : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (bd_and
          (bd_and
            (mem' (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (liftTerm A 4))
            (mem' (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩) (liftTerm A 4)))
          (mem' (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩)))
        (bd_and
          (mem' (pair' (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)) (liftTerm f 4))
          (mem' (pair' (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)) (liftTerm f 4))))
      (mem' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩))))))

def separatedFormula (A B f g : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (bd_and
          (mem' (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (liftTerm A 4))
          (mem' (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩) (liftTerm B 4)))
        (bd_and
          (mem' (pair' (bd_var ⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)) (liftTerm f 4))
          (mem' (pair' (bd_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)) (liftTerm g 4))))
      (mem' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩))))))

def homogeneousFormula (color : Bool) (R A B f g : bounded_term L_ZFC n) :
    bounded_formula L_ZFC n :=
  bd_all (bd_all (bd_imp
    (bd_and
      (bd_and
        (bd_or
          (rangeMemFormula (liftTerm A 2) (liftTerm f 2) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩))
          (rangeMemFormula (liftTerm B 2) (liftTerm g 2) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)))
        (bd_or
          (rangeMemFormula (liftTerm A 2) (liftTerm f 2) (bd_var ⟨0, Nat.zero_lt_succ _⟩))
          (rangeMemFormula (liftTerm B 2) (liftTerm g 2) (bd_var ⟨0, Nat.zero_lt_succ _⟩))))
      (mem' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))
    (if color then
      mem' (pair' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)) (liftTerm R 2)
    else bd_not (mem' (pair' (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)) (liftTerm R 2)))))

def twoBlockWitnessFormula (color : Bool) (R A B κ f g : bounded_term L_ZFC n) :
    bounded_formula L_ZFC n :=
  bd_and (bd_and (functionOnFormula A κ f) (functionOnFormula B κ g))
    (bd_and (bd_and (increasingFormula A f) (increasingFormula B g))
      (bd_and (separatedFormula A B f g) (homogeneousFormula color R A B f g)))

def hasTwoBlockFormula (color : Bool) (R A B κ : bounded_term L_ZFC n) :
    bounded_formula L_ZFC n :=
  bd_ex (bd_ex (twoBlockWitnessFormula color
    (liftTerm R 2) (liftTerm A 2) (liftTerm B 2) (liftTerm κ 2)
    (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))

def partitionFormula (κ A B : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_all (bd_or
    (hasTwoBlockFormula false (bd_var ⟨0, Nat.zero_lt_succ _⟩) (liftTerm A 1) (liftTerm B 1) (liftTerm κ 1))
    (hasTwoBlockFormula true (bd_var ⟨0, Nat.zero_lt_succ _⟩) (liftTerm A 1) (liftTerm B 1) (liftTerm κ 1)))
end Erdos1172Part4InternalPartitionLanguage

namespace Erdos1172Part4InternalBinaryTermInstantiation
open Erdos1172Part4InternalPartitionLanguage Erdos1172Part4InternalCardinalLanguage
variable {n : ℕ}

def binaryTermFormula (f : bounded_formula L_ZFC 2)
    (first second : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  subst0_bounded_formula
    (subst0_bounded_formula
      (f.cast (Nat.le_add_left 2 n) : bounded_formula L_ZFC (n + 2)) (liftTerm first 1)) second

def injectionFormula (source target : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  binaryTermFormula injects_into_f target source

def hartogsFormula (base ordinal : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  binaryTermFormula least_noninjecting_ordinal_f base ordinal
end Erdos1172Part4InternalBinaryTermInstantiation

namespace Erdos1172Part4InternalFullGCHSentence
open Erdos1172Part4InternalPartitionLanguage Erdos1172Part4InternalBinaryTermInstantiation
variable {n : ℕ}

def gchAtFormula (κ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_ex (bd_and
    (hartogsFormula (liftTerm κ 1) (bd_var ⟨0, Nat.zero_lt_succ _⟩))
    (injectionFormula (Powerset (liftTerm κ 1)) (bd_var ⟨0, Nat.zero_lt_succ _⟩)))

/-- Parameter-free closed `L_ZFC`-sentence stating the Generalized Continuum Hypothesis:
for every infinite set `κ` (`ω' ↪ κ`), `𝒫(κ)` injects into the Hartogs successor ordinal of `κ`. -/
def fullGCHSentence : sentence L_ZFC :=
  bd_all (bd_imp
    (injectionFormula omega' (bd_var ⟨0, Nat.zero_lt_succ _⟩))
    (gchAtFormula (bd_var ⟨0, Nat.zero_lt_succ _⟩)))
end Erdos1172Part4InternalFullGCHSentence

namespace Erdos1172Part4InternalPartitionSentence
open Erdos1172Part4InternalCardinalLanguage Erdos1172Part4InternalPartitionLanguage

def firstHartogsFormula : bounded_formula L_ZFC 2 :=
  (subst0_bounded_formula least_noninjecting_ordinal_f
    (omega' : bounded_term L_ZFC 1)) ↑ᶠᵇ' 1 # 0

def secondHartogsFormula : bounded_formula L_ZFC 2 :=
  subst0_bounded_formula
    (least_noninjecting_ordinal_f.cast (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))) : bounded_formula L_ZFC 3)
    (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)

def partitionBody : bounded_formula L_ZFC 2 :=
  partitionFormula (bd_var ⟨0, Nat.zero_lt_succ _⟩) (bd_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) omega'

/-- Parameter-free closed `L_ZFC`-sentence stating `ω₂ → (ω₁ + ω, ω₁ + ω)²`:
for `α = ω₁` (`Hartogs(ω', α)`) and `δ = ω₂` (`Hartogs(α, δ)`), every binary relation `R`
admits strictly increasing maps `f : α → δ` and `g : ω' → δ` with `ran(f) < ran(g)` whose
union `ran(f) ∪ ran(g)` (order type `ω₁ + ω`) is monochromatic for `R`. -/
def part4Sentence : sentence L_ZFC :=
  bd_ex (bd_ex (bd_and firstHartogsFormula (bd_and secondHartogsFormula partitionBody)))
end Erdos1172Part4InternalPartitionSentence

namespace Erdos1172Part4InternalGCHTheory
open Erdos1172Part4InternalFullGCHSentence Erdos1172Part4InternalPartitionSentence

/-- First-order theory `ZFC ∪ {fullGCHSentence, part4Sentence}` (`ZFC + GCH + ω₂ → (ω₁ + ω)₂²`). -/
def gchPart4Theory : SentTheory L_ZFC := ZFC ∪ {fullGCHSentence, part4Sentence}
end Erdos1172Part4InternalGCHTheory

open Cardinal Ordinal Filter

namespace Erdos1172GroundUltrapower
variable {I J : Type u}

/-- Fineness of an ultrafilter `U` with respect to an indexed family of subsets `a i ⊆ J`. -/
def FineOn (U : Ultrafilter I) (a : I → Set J) : Prop := ∀ ξ, ∀ᶠ i in U, ξ ∈ a i

/-- Normality of an ultrafilter `U` with respect to `a i ⊆ J`: regressive choice functions are `U`-almost constant. -/
def NormalOn (U : Ultrafilter I) (a : I → Set J) : Prop :=
  ∀ f : I → J, (∀ᶠ i in U, f i ∈ a i) → ∃ ξ, ∀ᶠ i in U, f i = ξ

/-- Kanamori's canonical index space `[θ]^{ot = κ}` of subsets of `θ` of order type `κ`. -/
abbrev HugeFiberSpace (κ θ : Cardinal.{u}) : Type u :=
  {s : Set θ.ord.ToType // Nonempty (κ.ord.ToType ≃o s)}

/-- `κ` is huge with target `θ` (Kanamori, *The Higher Infinite*, Theorem 24.8):
`ℵ₀ < κ < θ` and `[θ]^{ot = κ}` carries a `κ`-complete, fine, normal ultrafilter. -/
def IsHugeWithTarget (κ θ : Cardinal.{u}) : Prop :=
  ℵ₀ < κ ∧ κ < θ ∧
    ∃ U : Ultrafilter (HugeFiberSpace κ θ),
      CardinalInterFilter (U : Filter (HugeFiberSpace κ θ)) κ ∧
      FineOn U Subtype.val ∧
      NormalOn U Subtype.val

/-- `κ` is a huge cardinal if it is huge with some target cardinal `θ > κ`. -/
def IsHugeCardinal (κ : Cardinal.{u}) : Prop :=
  ∃ θ : Cardinal.{u}, IsHugeWithTarget κ θ
end Erdos1172GroundUltrapower

namespace Cardinal
/-- The Continuum Hypothesis (`2^ℵ₀ = ℵ₁`) at universe `0`. -/
def CH : Prop := (𝔠 : Cardinal.{0}) = ℵ_ 1
/-- The Generalized Continuum Hypothesis (`∀ o, 2^(ℵ_ o) = ℵ_(o + 1)`) at universe `0`. -/
def GCH : Prop := ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ ℵ_ o = ℵ_ (Order.succ o)
end Cardinal

section PartitionRelation
/-- Binary ordinary ordinal partition relation `α → (β, γ)²`: for every complementary pair of
simple graphs `(red, blue)` on `α.ToType`, either `red` has a clique of order type `β` or
`blue` has a clique of order type `γ`. -/
def OrdinalRamsey (α β γ : Ordinal.{u}) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
    (∃ s, blue.IsClique s ∧ typeLT s = γ)

/-- Countable-color balanced ordinary ordinal partition relation `α → (β)²_ω`: for every
coloring `col : Sym2 α.ToType → ℕ` of unordered pairs from `α.ToType` with `ℕ`-many colors,
there exist a color `n : ℕ` and a subset `s : Set α.ToType` of order type `typeLT s = β`
all of whose distinct pairs receive color `n`. -/
def OrdinalCountableRamsey (α β : Ordinal.{u}) : Prop :=
  ∀ col : Sym2 α.ToType → ℕ,
    ∃ (n : ℕ) (s : Set α.ToType),
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → col s(x, y) = n) ∧
      typeLT s = β
end PartitionRelation

namespace Erdos1172
/-- Countable-color partial-step target `ω₃ → (ω₂ + 1)²_ω` toward the open original
`[BHT93, p. 2]` / `[Va99, 7.87]` Part (i) question `ω₃ → (ω₂ + 2)²_ω` under `GCH` (also
entailed under `GCH` by Erdős–Rado / `[BHT93, Theorem 2.1]`). -/
abbrev Part1CountableStep : Prop := OrdinalCountableRamsey (ω_ 3 : Ordinal.{u}) (ω_ 2 + 1)
/-- Part (ii) target `ω₃ → (ω₂ + ω₁, ω₂ + ω)²` (`[BHT93, p. 2]`, `[Va99, 7.87]`). -/
abbrev Part2 : Prop := OrdinalRamsey (ω_ 3 : Ordinal.{u}) (ω_ 2 + ω_ 1) (ω_ 2 + ω)
/-- Part (iii) target `ω₂ → (ω₁^(ω + 2) + 2, ω₁ + 2)²` (`[BHT93, p. 2]`, `[Va99, 7.87]`). -/
abbrev Part3 : Prop := OrdinalRamsey (ω_ 2 : Ordinal.{u}) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2)
end Erdos1172
