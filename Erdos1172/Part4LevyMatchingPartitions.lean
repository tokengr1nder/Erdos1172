/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevySmallForcingAbsorption

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

end Erdos1172LevyCollapse.Matching
