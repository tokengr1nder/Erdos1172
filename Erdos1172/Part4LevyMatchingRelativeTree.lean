/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingRelativeChildren

@[expose] public section

/-! # Recognizing the collapse over a prescribed complete subalgebra -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172PositiveBoolean Erdos1172BooleanFactor Erdos1172PosetCompletion Erdos1172Collapse
open Erdos1172Shioya.ForcingCover
namespace Erdos1172LevyCollapse.Matching

variable {A B X : Type u} [CompleteBooleanAlgebra A] [CompleteBooleanAlgebra B]
variable (e : CompleteLatticeHom A B)
local notation "π" => lowerProjection e

structure Tree (M : CollapseMatrix X B) (d : X → Positive B) where
  child : ℕ → B → X → B
  below : ∀ n p x, child n p x ≤ p
  support : ∀ n p x, π (child n p x) = π p
  sep : ∀ n p i j, i ≠ j → Disjoint (child n p i) (child n p j)
  cover : ∀ n p, (⨆ x, child n p x) = p
  resolves : ∀ n p x, ∃ k, child n p k ⊓ e (π ((p ⊓ M.value n x) ⊓ (d x).val)) ≤ (p ⊓ M.value n x) ⊓ (d x).val

def makeTree (M : CollapseMatrix X B) (d : X → Positive B) (hX : ℵ₀ ≤ #X)
    (split : ∀ p : B, ∃ v : X → B, (∀ x, v x ≤ p) ∧ (∀ x, π (v x) = π p) ∧
      ∀ x y, x ≠ y → v x ⊓ v y = ⊥) : Tree e M d := by
  let c (n : ℕ) (p : B) (x : X) := (p ⊓ M.value n x) ⊓ (d x).val
  have dis (n p) (x y : X) (hne : x ≠ y) : Disjoint (c n p x) (c n p y) :=
    (disjoint_iff.mpr (M.disjoint n x y hne)).mono (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right)
  choose v sub proj sep cover res using fun n p =>
    exists_relative_children e hX split p (c n p) (fun _ => inf_le_left.trans inf_le_left) (dis n p)
  exact ⟨v,sub,proj,sep,cover,res⟩

variable {e} {M : CollapseMatrix X B} {d : X → Positive B} (T : Tree e M d)

def eval (n : ℕ) (p : B) : List X → B
  | [] => p
  | x :: xs => eval (n+1) (T.child n p x) xs

theorem eval_le (n : ℕ) (p : B) (xs : List X) : eval T n p xs ≤ p := by
  induction xs generalizing n p with
  | nil => exact le_rfl
  | cons i xs ih => exact (ih (n+1) _).trans (T.below n p i)

theorem eval_support (n : ℕ) (p : B) (xs : List X) : π (eval T n p xs) = π p := by
  induction xs generalizing n p with
  | nil => rfl
  | cons i xs ih => exact (ih (n+1) _).trans (T.support n p i)

theorem eval_append (n : ℕ) (p : B) (xs ys : List X) :
    eval T n p (xs ++ ys) = eval T (n+xs.length) (eval T n p xs) ys := by
  induction xs generalizing n p with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.cons_append,eval,List.length_cons,Nat.succ_add,Nat.add_succ] using ih (n+1) (T.child n p x)

private theorem eval_comparable (n : ℕ) (p : B) (xs ys : List X) (z : Positive B)
    (hx : z.val ≤ eval T n p xs) (hy : z.val ≤ eval T n p ys) : xs <+: ys ∨ ys <+: xs := by
  induction xs generalizing n p ys with
  | nil => exact Or.inl List.nil_prefix
  | cons x xs ih =>
    cases ys with
    | nil => exact Or.inr List.nil_prefix
    | cons y ys =>
      have he : x = y := by
        by_contra hn
        exact z.property (bot_unique ((le_inf (hx.trans (eval_le T (n+1) _ xs))
          (hy.trans (eval_le T (n+1) _ ys))).trans (disjoint_iff_inf_le.mp (T.sep n p x y hn))))
      subst y
      exact (ih (n+1) _ ys hx hy).imp (fun ⟨w,h⟩ => ⟨w,congrArg (List.cons x) h⟩)
        (fun ⟨w,h⟩ => ⟨w,congrArg (List.cons x) h⟩)

private theorem eval_reach (n l : ℕ) (p : B) (b : Positive B) (h : b.val ≤ p) :
    ∃ xs : List X, xs.length = l ∧ ∃ w : Positive B, w ≤ b ∧ w.val ≤ eval T n p xs := by
  induction l generalizing n p b with
  | zero => exact ⟨[],rfl,b,le_rfl,h⟩
  | succ l ih =>
    have hit : ∃ x, b.val ⊓ T.child n p x ≠ ⊥ := by
      by_contra! bad
      exact b.property ((inf_eq_left.mpr h).symm.trans (by rw [← T.cover n p,inf_iSup_eq,iSup_eq_bot]; exact bad))
    obtain ⟨x,hx⟩ := hit
    let v : Positive B := ⟨b.val ⊓ T.child n p x,hx⟩
    obtain ⟨xs,hlen,w,hw,hws⟩ := ih (n+1) (T.child n p x) v inf_le_right
    exact ⟨x :: xs,congrArg Nat.succ hlen,w,hw.trans (show v ≤ b from inf_le_left),hws⟩

variable (he : Function.Injective e)
local notation "S" => Positive A × Condition X
include he in
theorem top_support : lowerProjection e ⊤ = ⊤ := by
  apply he
  rw [map_top]
  exact top_unique (le_image_lowerProjection e ⊤)

def productTreeMap : S →o Positive B where
  toFun z := ⟨e z.1.val ⊓ eval T 0 ⊤ z.2.entries,inf_image_lowerProjection_ne_bot e z.1.property
    (by rw [eval_support,top_support he]; exact le_top)⟩
  monotone' := by
    intro z w hw
    apply inf_le_inf (OrderHomClass.mono e hw.1)
    obtain ⟨xs,hxs⟩ := le_iff_prefix.mp hw.2
    rw [← hxs,eval_append]
    exact eval_le T _ _ _

private theorem productTreeSupport (s : S) : π (productTreeMap T he s).val = s.1.val := by
  change π (e s.1.val ⊓ eval T 0 ⊤ s.2.entries) = _
  rw [inf_comm,lowerProjection_inf_image,eval_support,top_support he,top_inf_eq]

private theorem productTreeDense (dense : ∀ b, ∃ x, d x ≤ b) (b : Positive B) :
    ∃ s, productTreeMap T he s ≤ b := by
  obtain ⟨x,hxb⟩ := dense b
  obtain ⟨n,hn⟩ := exists_compatible_piece (d x).property (fun n => M.value n x) (M.onto x)
  let z : Positive B := ⟨(d x).val ⊓ M.value n x,hn⟩
  obtain ⟨xs,hlen,w,hw,hwp⟩ := eval_reach T 0 n ⊤ z le_top
  let p := eval T 0 ⊤ xs
  let c := (p ⊓ M.value n x) ⊓ (d x).val
  have hwz : w.val ≤ (d x).val ⊓ M.value n x := hw
  have pos : c ≠ ⊥ := fun hz => w.property (bot_unique
    ((le_inf (le_inf hwp (hwz.trans inf_le_right)) (hwz.trans inf_le_left)).trans_eq hz))
  obtain ⟨k,hk⟩ := T.resolves n p x
  refine ⟨(⟨π c,lowerProjection_ne_bot e pos⟩,⟨xs ++ [k]⟩),?_⟩
  change e (π c) ⊓ eval T 0 ⊤ (xs ++ [k]) ≤ b.val
  rw [eval_append,Nat.zero_add,hlen,inf_comm]
  exact hk.trans (inf_le_right.trans (show (d x).val ≤ b.val from hxb))

private theorem image_le_components {s t : S} (h : productTreeMap T he s ≤ productTreeMap T he t) :
    s.1 ≤ t.1 ∧ (s.2 ≤ t.2 ∨ t.2 ≤ s.2) := by
  refine ⟨(productTreeSupport T he s).symm.trans_le ((lowerProjection_mono e h).trans_eq
    (productTreeSupport T he t)),?_⟩
  apply Or.symm
  exact eval_comparable T 0 ⊤ s.2.entries t.2.entries (productTreeMap T he s) inf_le_right
    ((show (productTreeMap T he s).val ≤ (productTreeMap T he t).val from h).trans inf_le_right)

variable (e) in
/-- The pointwise embedding of the old algebra into the completion of the
product. Membership depends only on the old coordinate. -/
def oldFactor (X : Type u) (a : A) : Completion (Positive A × Condition X) :=
  Erdos1172PosetProjection.completionHom (⟨Prod.fst,fun _ _ h => h.1⟩ : Positive A × Condition X →o Positive A)
    (fun p q h => ⟨(q,p.2),⟨h,le_rfl⟩,rfl⟩) (element a)

variable (e) in
/-- A regular uncountable collapse algebra is the product of its small
complete subalgebra with the ordinary one-coordinate collapse. The
isomorphism commutes on the nose with every old Boolean value. -/
theorem exists_relative_collapse_iso {K : Type u} (he : Function.Injective e)
    (M : CollapseMatrix X B) (hX : ℵ₀ < #X) (reg : (#X).IsRegular)
    (g : K → Positive A) (small : #K < #X) (gDense : ∀ a, ∃ k, g k ≤ a)
    (d : X → Positive B) (dDense : ∀ b, ∃ x, d x ≤ b) :
    ∃ φ : B ≃o Completion (Positive A × Condition X), ∀ a, φ (e a) = oldFactor X a := by
  let T := makeTree e M d hX.le (exists_full_support_antichain e M hX reg g small gDense)
  let f := productTreeMap T he
  have lifts : Lifts f := by
    intro s b hb
    obtain ⟨q,hq⟩ := productTreeDense T he dDense b
    obtain ⟨ha,ht | ht⟩ := image_le_components T he (hq.trans hb)
    · exact ⟨q,⟨ha,ht⟩,hq⟩
    · exact ⟨(q.1,s.2),⟨ha,le_rfl⟩,(f.monotone (show (q.1,s.2) ≤ q from ⟨le_rfl,ht⟩)).trans hq⟩
  have compatible (s t : S) (h : f s ≤ f t) : ∃ z ≤ s, z ≤ t := by
    obtain ⟨ha,ht | ht⟩ := image_le_components T he h
    · exact ⟨s,le_rfl,ha,ht⟩
    · exact ⟨(s.1,t.2),⟨le_rfl,ht⟩,ha,le_rfl⟩
  let φ := completionOrderIso.trans (completionIso f lifts compatible (productTreeDense T he dDense))
  refine ⟨φ,fun a => ?_⟩
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro s
  change (f s).val ≤ e a ↔ s.1.val ≤ a
  rw [← lowerProjection_le_iff e,productTreeSupport]

end Erdos1172LevyCollapse.Matching
