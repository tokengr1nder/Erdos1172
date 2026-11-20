/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingPartitions

@[expose] public section

/-! # Recognizing the Lévy collapse by a dense family and a collapse matrix -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172PositiveBoolean Erdos1172PosetCompletion Erdos1172Collapse
namespace Erdos1172LevyCollapse.Matching

variable {X B : Type u} [CompleteBooleanAlgebra B]
variable (M : CollapseMatrix X B) (hX : ℵ₀ < #X) (reg : (#X).IsRegular) (d : X → Positive B)
local notation "children" => fun (n : ℕ) (p : Positive B) =>
  Exists.choose (CollapseMatrix.exists_resolving_partition M hX reg d p n)
local notation "laws" => fun (n : ℕ) (p : Positive B) =>
  Exists.choose_spec (CollapseMatrix.exists_resolving_partition M hX reg d p n)

def walk (n : ℕ) (p : Positive B) : List X → Positive B
  | [] => p
  | x :: xs => walk (n + 1) (children n p x) xs

theorem walk_le (n : ℕ) (p : Positive B) (xs : List X) : walk M hX reg d n p xs ≤ p := by
  induction xs generalizing n p with
  | nil => exact le_rfl
  | cons x xs ih => exact (ih (n+1) (children n p x)).trans ((laws n p).1 x)

theorem walk_append (n : ℕ) (p : Positive B) (xs ys : List X) :
    walk M hX reg d n p (xs ++ ys) = walk M hX reg d (n + xs.length) (walk M hX reg d n p xs) ys := by
  induction xs generalizing n p with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.cons_append,walk,List.length_cons,Nat.succ_add,Nat.add_succ] using
      ih (n+1) (children n p x)

private theorem comparable (n : ℕ) (p : Positive B) (xs ys : List X) (z : Positive B)
    (hx : z ≤ walk M hX reg d n p xs) (hy : z ≤ walk M hX reg d n p ys) : xs <+: ys ∨ ys <+: xs := by
  induction xs generalizing n p ys with
  | nil => exact Or.inl List.nil_prefix
  | cons x xs ih =>
    cases ys with
    | nil => exact Or.inr List.nil_prefix
    | cons y ys =>
      have h₁ : z ≤ children n p x := hx.trans (walk_le M hX reg d (n+1) _ xs)
      have h₂ : z ≤ children n p y := hy.trans (walk_le M hX reg d (n+1) _ ys)
      have he : x = y := by
        by_contra hn
        exact z.property (bot_unique ((le_inf (show z.val ≤ _ from h₁) (show z.val ≤ _ from h₂)).trans_eq
          ((laws n p).2.2.1 x y hn)))
      subst y
      exact (ih (n+1) _ ys hx hy).imp (fun ⟨w,hw⟩ => ⟨w,congrArg (List.cons x) hw⟩)
        (fun ⟨w,hw⟩ => ⟨w,congrArg (List.cons x) hw⟩)

private theorem next_compatible (n : ℕ) (p b : Positive B) (h : b ≤ p) :
    ∃ x, ∃ w : Positive B, w ≤ b ∧ w ≤ children n p x := by
  by_contra! bad
  apply b.property
  calc b.val = b.val ⊓ ⨆ x, (children n p x).val := by rw [(laws n p).2.1,inf_eq_left.mpr h]
       _ = ⊥ := by
        rw [inf_iSup_eq,iSup_eq_bot]
        intro x
        by_contra hn
        exact bad x ⟨_,hn⟩ inf_le_left inf_le_right

private theorem reach (n l : ℕ) (p b : Positive B) (h : b ≤ p) :
    ∃ xs : List X, xs.length = l ∧ ∃ w : Positive B, w ≤ b ∧ w ≤ walk M hX reg d n p xs := by
  induction l generalizing n p b with
  | zero => exact ⟨[],rfl,b,le_rfl,h⟩
  | succ l ih =>
    obtain ⟨x,w,hwb,hw⟩ := next_compatible M hX reg d n p b h
    obtain ⟨xs,hlen,z,hzw,hz⟩ := ih (n+1) _ w hw
    exact ⟨x :: xs,congrArg Nat.succ hlen,z,hzw.trans hwb,hz⟩

variable [Nontrivial B]
def treeRoot : Positive B := ⟨⊤,top_ne_bot⟩

/-- The tree labels are actual positive Boolean values. -/
def collapseTreeMap : Condition X →o Positive B where
  toFun t := walk M hX reg d 0 treeRoot t.entries
  monotone' := by
    intro t s h
    obtain ⟨tail,ht⟩ := le_iff_prefix.mp h
    change walk M hX reg d 0 treeRoot t.entries ≤ walk M hX reg d 0 treeRoot s.entries
    rw [← ht,walk_append]
    exact walk_le _ _ _ _ _ _ _

include M hX reg in
theorem collapseTreeMap_dense (dense : ∀ b, ∃ x, d x ≤ b) (b : Positive B) :
    ∃ t, collapseTreeMap M hX reg d t ≤ b := by
  obtain ⟨x,hx⟩ := dense b
  obtain ⟨n,hn⟩ := exists_compatible_piece (d x).property (fun n => M.value n x) (M.onto x)
  let z : Positive B := ⟨(d x).val ⊓ M.value n x,hn⟩
  obtain ⟨xs,hlen,w,hwz,hws⟩ := reach M hX reg d 0 n treeRoot z (show z.val ≤ ⊤ from le_top)
  let s := walk M hX reg d 0 treeRoot xs
  obtain ⟨k,v,hvw,hvk⟩ := next_compatible M hX reg d n s w hws
  have hvz : v.val ≤ (d x).val ⊓ M.value n x := (show v ≤ z from hvw.trans hwz)
  have hd : v.val ≤ (d x).val := hvz.trans inf_le_left
  have hr : v.val ≤ M.value n x := hvz.trans inf_le_right
  have hpos : (children n s k).val ⊓ M.value n x ≠ ⊥ :=
    fun he => v.property (bot_unique ((le_inf (show v.val ≤ _ from hvk) hr).trans_eq he))
  have hc : children n s k ≤ d x := ((laws n s).2.2.2 k x hpos).resolve_right
    (fun hg => v.property (bot_unique ((le_inf hd ((show v.val ≤ _ from hvk).trans hg)).trans inf_compl_eq_bot.le)))
  refine ⟨⟨xs ++ [k]⟩,?_⟩
  change walk M hX reg d 0 treeRoot (xs ++ [k]) ≤ b
  rw [walk_append,Nat.zero_add,hlen]
  exact hc.trans hx

include M hX reg in
theorem compatible_of_image (p q : Condition X) (z : Positive B)
    (hp : z ≤ collapseTreeMap M hX reg d p) (hq : z ≤ collapseTreeMap M hX reg d q) : p ≤ q ∨ q ≤ p :=
  (comparable M hX reg d 0 treeRoot p.entries q.entries z hp hq).symm

/-- A complete Boolean algebra of density at most |X| which forces the
regular uncountable X to be countable is the completion of the finite-list
collapse on X. The dense map is constructed from the given enumeration. -/
def collapseOrderIso (dense : ∀ b, ∃ x, d x ≤ b) : B ≃o Completion (Condition X) := by
  let g := collapseTreeMap M hX reg d
  have lifts : Erdos1172Shioya.ForcingCover.Lifts g := by
    intro p b hb
    obtain ⟨q,hq⟩ := collapseTreeMap_dense M hX reg d dense b
    rcases compatible_of_image M hX reg d q p (g q) le_rfl (hq.trans hb) with h | h
    · exact ⟨q,h,hq⟩
    · exact ⟨p,le_rfl,(g.monotone h).trans hq⟩
  have comp (p q : Condition X) (h : g p ≤ g q) : ∃ z ≤ p, z ≤ q :=
    compatible_iff_comparable.mpr (compatible_of_image M hX reg d p q (g p) le_rfl h)
  exact completionOrderIso.trans (Erdos1172Shioya.ForcingCover.completionIso g lifts comp
    (collapseTreeMap_dense M hX reg d dense))

end Erdos1172LevyCollapse.Matching
