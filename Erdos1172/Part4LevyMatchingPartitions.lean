/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevySmallForcingAbsorption
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-! # Maximal partitions below conditions in a regular-cardinal collapse -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172PositiveBoolean
namespace Erdos1172LevyCollapse.Matching

variable {X B : Type u} [CompleteBooleanAlgebra B]

/-- Boolean truth values of a surjection from ω onto the ground alphabet. -/
structure CollapseMatrix (X B : Type u) [CompleteBooleanAlgebra B] where
  value : ℕ → X → B
  row : ∀ n, (⨆ i, value n i) = ⊤
  disjoint : ∀ n i j, i ≠ j → value n i ⊓ value n j = ⊥
  onto : ∀ i, (⨆ n, value n i) = ⊤

theorem exists_compatible_piece {T : Type*} {p : B} (hp : p ≠ ⊥) (v : T → B)
    (hv : (⨆ t, v t) = ⊤) : ∃ t, p ⊓ v t ≠ ⊥ := by
  by_contra! h
  apply hp
  calc p = p ⊓ ⨆ t, v t := by rw [hv,inf_top_eq]
       _ = ⊥ := by rw [inf_iSup_eq,iSup_eq_bot]; exact h

/-- Any positive condition in a forcing that collapses a regular uncountable
alphabet splits into a maximal partition of that alphabet's cardinality. -/
theorem CollapseMatrix.exists_partition (M : CollapseMatrix X B) (hX : ℵ₀ < #X)
    (reg : (#X).IsRegular) (p : Positive B) :
    ∃ v : X → Positive B, (∀ x, v x ≤ p) ∧ (⨆ x, (v x).val) = p.val ∧
      ∀ x y, x ≠ y → (v x).val ⊓ (v y).val = ⊥ := by
  classical
  let S (n : ULift.{u} ℕ) : Set X := {x | p.val ⊓ M.value n.down x ≠ ⊥}
  have all : (⋃ n, S n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n,hn⟩ := exists_compatible_piece p.property (fun n => M.value n x) (M.onto x)
    exact Set.mem_iUnion.mpr ⟨⟨n⟩,hn⟩
  have large : ∃ n, #(S n) = #X := by
    by_contra! h
    have hs : Cardinal.mk (ULift.{u} ℕ) < #X := by simpa using hX
    have bad := (Cardinal.card_iUnion_lt_iff_forall_of_isRegular reg hs).mpr
      (fun n => (Cardinal.mk_set_le (S n)).lt_of_ne (h n))
    simp only [all,Cardinal.mk_univ,lt_self_iff_false] at bad
  obtain ⟨n,hn⟩ := large
  let e : X ≃ S n := Classical.choice (Cardinal.eq.mp hn.symm)
  let v (x : X) : Positive B := ⟨p.val ⊓ M.value n.down (e x).val,(e x).property⟩
  refine ⟨v,fun _ => inf_le_left,le_antisymm (iSup_le fun _ => inf_le_left) ?_,?_⟩
  · calc p.val = ⨆ x, p.val ⊓ M.value n.down x := by rw [← inf_iSup_eq,M.row,inf_top_eq]
         _ ≤ ⨆ x, (v x).val := by
          apply iSup_le
          intro i
          by_cases hi : i ∈ S n
          · let x := e.symm ⟨i,hi⟩
            have he : (e x).val = i := congrArg Subtype.val (e.apply_symm_apply _)
            exact le_iSup_of_le x (show p.val ⊓ M.value n.down i ≤ p.val ⊓ M.value n.down (e x).val
              from he.symm ▸ le_rfl)
          · have hz : p.val ⊓ M.value n.down i = ⊥ := by_contra hi
            exact hz.trans_le bot_le
  · intro x y hxy
    apply bot_unique
    exact (inf_le_inf (show (v x).val ≤ M.value n.down (e x).val from inf_le_right)
      (show (v y).val ≤ M.value n.down (e y).val from inf_le_right)).trans_eq
      (M.disjoint _ _ _ (fun he => hxy (e.injective (Subtype.ext he))))

/-- The children of a tree node resolve the dense condition indexed by the
next value of the collapsing enumeration. They still form a full-sized
maximal partition below their parent. -/
theorem CollapseMatrix.exists_resolving_partition (M : CollapseMatrix X B) (hX : ℵ₀ < #X)
    (reg : (#X).IsRegular) (d : X → Positive B) (p : Positive B) (n : ℕ) :
    ∃ v : X → Positive B, (∀ x, v x ≤ p) ∧ (⨆ x, (v x).val) = p.val ∧
      (∀ x y, x ≠ y → (v x).val ⊓ (v y).val = ⊥) ∧
      ∀ k x, (v k).val ⊓ M.value n x ≠ ⊥ → v k ≤ d x ∨ (v k).val ≤ (d x).valᶜ := by
  classical
  let sign (x : X) (b : Bool) := if b then (d x).val else (d x).valᶜ
  let piece (z : X × Bool) := (p.val ⊓ M.value n z.1) ⊓ sign z.1 z.2
  have split (x : X) : piece (x,true) ⊔ piece (x,false) = p.val ⊓ M.value n x := by
    simp only [piece,sign,if_true,Bool.false_eq_true,if_false,← inf_sup_left,sup_compl_eq_top,inf_top_eq]
  have sep (z w : X × Bool) (hne : z ≠ w) : piece z ⊓ piece w = ⊥ := by
    apply bot_unique
    by_cases he : z.1 = w.1
    · have hz : z.2 ≠ w.2 := fun hb => hne (Prod.ext he hb)
      have h : sign z.1 z.2 ⊓ sign w.1 w.2 = ⊥ := by
        rw [he]
        cases hb : z.2 <;> cases hc : w.2 <;> simp_all [sign]
      exact (inf_le_inf (show piece z ≤ sign z.1 z.2 from inf_le_right)
        (show piece w ≤ sign w.1 w.2 from inf_le_right)).trans_eq h
    · exact (inf_le_inf (show piece z ≤ M.value n z.1 from inf_le_left.trans inf_le_right)
        (show piece w ≤ M.value n w.1 from inf_le_left.trans inf_le_right)).trans_eq (M.disjoint n _ _ he)
  let C := {z : X × Bool // piece z ≠ ⊥}
  have cover : p.val ≤ ⨆ c : C, piece c.val := by
    calc p.val = ⨆ x, p.val ⊓ M.value n x := by rw [← inf_iSup_eq,M.row,inf_top_eq]
         _ ≤ ⨆ c : C, piece c.val := by
          apply iSup_le
          intro x
          have add (z : X × Bool) : piece z ≤ ⨆ c : C, piece c.val := by
            by_cases hz : piece z = ⊥
            · exact hz.trans_le bot_le
            · exact le_iSup (fun c : C => piece c.val) ⟨z,hz⟩
          rw [← split x]
          exact sup_le (add _) (add _)
  have nonempty : Nonempty C := by
    by_contra h
    have emp : IsEmpty C := not_nonempty_iff.mp h
    exact p.property (bot_unique (cover.trans (iSup_le fun c => (emp.false c).elim)))
  choose parts below total dis using fun c : C => M.exists_partition hX reg ⟨piece c.val,c.property⟩
  let idx : X ≃ C × X := Classical.choice (Cardinal.eq.mp (le_antisymm
    (Cardinal.mk_le_of_injective (f := fun x : X => (Classical.choice nonempty,x))
      (fun _ _ h => congrArg Prod.snd h)) (by
        have hc : #C ≤ #X := (Cardinal.mk_le_of_injective (f := (Subtype.val : C → X × Bool))
          Subtype.val_injective).trans (by
            rw [Cardinal.mk_prod]
            simpa using (mul_le_mul' (le_refl (#X)) ((Cardinal.natCast_le_aleph0 (n := 2)).trans hX.le)).trans_eq
              (Cardinal.mul_eq_self hX.le))
        rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id]
        exact (mul_le_mul' hc (le_refl _)).trans_eq (Cardinal.mul_eq_self hX.le))))
  let v (x : X) := parts (idx x).1 (idx x).2
  have sub (x) : (v x).val ≤ piece (idx x).1.val := below _ _
  refine ⟨v,fun x => (sub x).trans (inf_le_left.trans inf_le_left),
    le_antisymm (iSup_le fun x => (sub x).trans (inf_le_left.trans inf_le_left)) ?_,?_,?_⟩
  · apply cover.trans
    apply iSup_le
    intro c
    apply (total c).symm.trans_le
    apply iSup_le
    intro x
    apply le_iSup_of_le (idx.symm (c,x))
    simp only [v,idx.apply_symm_apply,le_refl]
  · intro x y hxy
    by_cases he : (idx x).1 = (idx y).1
    · have hn : (idx x).2 ≠ (idx y).2 := fun h => hxy (idx.injective (Prod.ext he h))
      dsimp only [v]
      rw [he]
      exact dis _ _ _ hn
    · exact bot_unique ((inf_le_inf (sub x) (sub y)).trans_eq (sep _ _ (fun h => he (Subtype.ext h))))
  · intro k x hk
    let c := (idx k).1.val
    have he : c.1 = x := by
      by_contra hn
      exact hk (bot_unique ((inf_le_inf ((sub k).trans (inf_le_left.trans inf_le_right)) le_rfl).trans_eq
        (M.disjoint n c.1 x hn)))
    have hs : (v k).val ≤ sign x c.2 := he ▸ (sub k).trans inf_le_right
    cases hb : c.2 with
    | false => exact Or.inr (by simpa only [sign,hb,Bool.false_eq_true,if_false] using hs)
    | true =>
      apply Or.inl
      change (v k).val ≤ (d x).val
      simpa only [sign,hb,if_true] using hs

end Erdos1172LevyCollapse.Matching
