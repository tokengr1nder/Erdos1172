/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaDenseCoverIso
public import Erdos1172.Part4PositiveBooleanCompletion
public import Erdos1172.Part4CollapseConditions
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

/-! # Absorption of a small forcing by one countable Lévy collapse -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion Erdos1172PositiveBoolean Erdos1172Collapse Cardinal
universe u
namespace Erdos1172LevyCollapse.Absorption

variable {B X : Type u} [CompleteBooleanAlgebra B] (d : X → Positive B)
local notation "Tree" => Erdos1172Collapse.Condition X
local notation "Target" => Positive B × Erdos1172Collapse.Condition X

def piece (p : Positive B) (x : X × Bool) : B :=
  p.val ⊓ (if x.2 then (d x.1).val else (d x.1).valᶜ)

def Live (p : Positive B) := {x : X × Bool // piece d p x ≠ ⊥}

theorem one_piece (p : Positive B) (x : X) : ∃ b, piece d p (x,b) ≠ ⊥ := by
  classical
  by_cases h : p.val ⊓ (d x).val = ⊥
  · refine ⟨false,?_⟩
    have le := le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h)
    simpa only [piece,Bool.false_eq_true,if_false,inf_eq_left.mpr le] using p.property
  · exact ⟨true,h⟩

def alphabet (hX : ℵ₀ ≤ #X) (p : Positive B) : X ≃ Live d p := by
  let liftLetter (x : X) : Live d p := ⟨(x,(one_piece d p x).choose),(one_piece d p x).choose_spec⟩
  have inj : Function.Injective liftLetter := fun _ _ h => congrArg (fun z : Live d p => z.val.1) h
  apply Classical.choice
  apply Cardinal.eq.mp
  apply le_antisymm (Cardinal.mk_le_of_injective inj)
  apply (Cardinal.mk_le_of_injective (f := (Subtype.val : Live d p → X × Bool)) Subtype.val_injective).trans
  rw [Cardinal.mk_prod]
  simpa using (mul_le_mul' (le_refl (#X)) ((Cardinal.natCast_le_aleph0 (n := 2)).trans hX)).trans_eq
    (Cardinal.mul_eq_self hX)

variable (hX : ℵ₀ ≤ #X)

def child (s : Target) (x : X) : Target :=
  let v := alphabet d hX s.1 x
  (⟨piece d s.1 v.val,v.property⟩,extend s.2 [v.val.1])

private theorem child_le (s : Target) (x : X) : child d hX s x ≤ s :=
  ⟨inf_le_left,extend_le _ _⟩

private theorem child_inj (s : Target) (i j : X) (z : Target)
    (hi : z ≤ child d hX s i) (hj : z ≤ child d hX s j) : i = j := by
  let u := alphabet d hX s.1 i
  let v := alphabet d hX s.1 j
  have ha : s.2.entries ++ [u.val.1] <+: z.2.entries := hi.2
  have hb : s.2.entries ++ [v.val.1] <+: z.2.entries := hj.2
  have hl : s.2.entries ++ [u.val.1] = s.2.entries ++ [v.val.1] := by
    rcases List.prefix_or_prefix_of_prefix ha hb with h | h
    · exact h.eq_of_length (by simp)
    · exact (h.eq_of_length (by simp)).symm
  have same : u.val.1 = v.val.1 := by simpa using hl
  have left : z.1.val ≤ (if u.val.2 then (d u.val.1).val else (d u.val.1).valᶜ) :=
    (show z.1.val ≤ piece d s.1 u.val from hi.1).trans inf_le_right
  have right : z.1.val ≤ (if v.val.2 then (d u.val.1).val else (d u.val.1).valᶜ) := by
    rw [same]
    exact (show z.1.val ≤ piece d s.1 v.val from hj.1).trans inf_le_right
  have bits : u.val.2 = v.val.2 := by
    cases hu : u.val.2 <;> cases hv : v.val.2 <;> first | rfl | skip
    · simp only [hu,hv,Bool.false_eq_true,if_false,if_true] at left right
      exact (z.1.property (bot_unique ((le_inf right left).trans inf_compl_eq_bot.le))).elim
    · simp only [hu,hv,Bool.false_eq_true,if_false,if_true] at left right
      exact (z.1.property (bot_unique ((le_inf left right).trans inf_compl_eq_bot.le))).elim
  exact (alphabet d hX s.1).injective (Subtype.ext (Prod.ext same bits))

def walk (s : Target) (p : List X) : Target := p.foldl (child d hX) s

theorem below (s : Target) (p : List X) : walk d hX s p ≤ s := by
  induction p generalizing s with
  | nil => exact le_rfl
  | cons x p ih => exact (ih (child d hX s x)).trans (child_le d hX s x)

private theorem comparable (s : Target) (p q : List X) (z : Target)
    (hp : z ≤ walk d hX s p) (hq : z ≤ walk d hX s q) : p <+: q ∨ q <+: p := by
  induction p generalizing s q with
  | nil => exact Or.inl List.nil_prefix
  | cons i p ih =>
    cases q with
    | nil => exact Or.inr List.nil_prefix
    | cons j q =>
      have he := child_inj d hX s i j z (hp.trans (below d hX _ p)) (hq.trans (below d hX _ q))
      subst j
      exact (ih _ _ hp hq).imp (fun ⟨w,hw⟩ => ⟨w,congrArg (List.cons i) hw⟩)
        (fun ⟨w,hw⟩ => ⟨w,congrArg (List.cons i) hw⟩)

variable [Nontrivial B]

def root : Target := (⟨⊤,top_ne_bot⟩,⊤)

def treeMap : Tree →o Target where
  toFun p := walk d hX root p.entries
  monotone' := by
    intro p q hp
    change walk d hX root p.entries ≤ walk d hX root q.entries
    obtain ⟨tail,he⟩ := (le_iff_prefix.mp hp)
    rw [← he]
    exact (show walk d hX root (q.entries ++ tail) ≤ _ by
      simpa only [walk,List.foldl_append] using below d hX (walk d hX root q.entries) tail)

omit [Nontrivial B] in
private theorem follow (s : Target) (tail : List X) (b : Positive B) (hb : b ≤ s.1) :
    ∃ p : List X, (walk d hX s p).2 = extend s.2 tail ∧
      ∃ c : Positive B, c ≤ b ∧ c ≤ (walk d hX s p).1 := by
  induction tail generalizing s b with
  | nil => exact ⟨[],by apply Condition.ext; simp [walk,extend],b,le_rfl,hb⟩
  | cons x tail ih =>
    obtain ⟨bit,hbit⟩ := one_piece d b x
    have mono : piece d b (x,bit) ≤ piece d s.1 (x,bit) := inf_le_inf_right _ hb
    let live : Live d s.1 := ⟨(x,bit),fun ht => hbit (bot_unique (mono.trans ht.le))⟩
    let i := (alphabet d hX s.1).symm live
    have selected : alphabet d hX s.1 i = live := Equiv.apply_symm_apply _ _
    let c : Positive B := ⟨_,hbit⟩
    have c_le : c ≤ (child d hX s i).1 := by
      change piece d b (x,bit) ≤ piece d s.1 (alphabet d hX s.1 i).val
      rw [selected]
      exact mono
    obtain ⟨p,hp,z,hzc,hz⟩ := ih (child d hX s i) c c_le
    refine ⟨i :: p,?_,z,hzc.trans (show c ≤ b from inf_le_left),hz⟩
    change (walk d hX (child d hX s i) p).2 = _
    rw [hp]
    change extend (extend s.2 [(alphabet d hX s.1 i).val.1]) tail = _
    rw [selected,extend_append]
    rfl

variable (dense : ∀ b : Positive B, ∃ x, d x ≤ b)

include dense in
theorem treeMap_lifts : Erdos1172Shioya.ForcingCover.Lifts (treeMap d hX) := by
  intro p t ht
  let s := treeMap d hX p
  obtain ⟨tail,he⟩ := le_iff_exists_extend.mp ht.2
  obtain ⟨l,hl,b,hbt,hbs⟩ := follow d hX s tail t.1 ht.1
  let w := walk d hX s l
  obtain ⟨x,hx⟩ := dense b
  have lew : d x ≤ w.1 := hx.trans hbs
  have eqp : piece d w.1 (x,true) = (d x).val := inf_eq_right.mpr lew
  let v : Live d w.1 := ⟨(x,true),fun h => (d x).property (eqp.symm.trans h)⟩
  let i := (alphabet d hX w.1).symm v
  have chosen : alphabet d hX w.1 i = v := Equiv.apply_symm_apply _ _
  refine ⟨extend p (l ++ [i]),extend_le _ _,?_⟩
  have eqwalk : treeMap d hX (extend p (l ++ [i])) = child d hX w i := by
    simp only [treeMap,OrderHom.coe_mk,extend_entries,walk,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rfl
  rw [eqwalk]
  constructor
  · change piece d w.1 (alphabet d hX w.1 i).val ≤ t.1.val
    rw [chosen]
    exact eqp.trans_le (hx.trans hbt)
  · exact (extend_le _ _).trans (show w.2 ≤ t.2 from (hl.trans he.symm).le)

theorem treeMap_compatible (p q : Tree) (hpq : treeMap d hX p ≤ treeMap d hX q) :
    ∃ z ≤ p, z ≤ q := compatible_iff_prefix_comparable.mpr
      (comparable d hX root p.entries q.entries _ le_rfl hpq)

/-- The collapse on X absorbs the product with a Boolean forcing admitting
an X-indexed dense family. This is an isomorphism of Boolean completions. -/
def collapseAbsorbs : Completion Target ≃o Completion Tree :=
  Erdos1172Shioya.ForcingCover.completionIso (treeMap d hX) (treeMap_lifts d hX dense)
    (treeMap_compatible d hX)
    (fun t => by
      have top : t ≤ treeMap d hX (⊤ : Tree) := ⟨show t.1.val ≤ ⊤ from le_top,show t.2 ≤ ⊤ from le_top⟩
      obtain ⟨p,_,hp⟩ := treeMap_lifts d hX dense _ _ top
      exact ⟨p,hp⟩)

end Erdos1172LevyCollapse.Absorption
