/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyAnonymousCheckedSequenceReading
public import Erdos1172.Part4BooleanQuotientFactorization

@[expose] public section

/-!
# Countable intersections of weighted dense opens in the anonymous quotient

Membership of a target label in an open set carries a source Boolean value.
The separative comparison of labels `q` and `p` excludes the lower
projection of `q ⊓ pᶜ`. Disjoint refinements and simultaneous anonymous
reading yield one condition locally belonging to every dense open.
-/

set_option autoImplicit false
noncomputable section

universe u v

namespace Erdos1172LevyCohen

open Erdos1172PositiveBoolean Erdos1172BooleanFactor Erdos1172CompleteSubalgebra

theorem disjoint_cover_refinement {C I : Type u} [CompleteBooleanAlgebra C]
    (a : I → C) :
    ∃ w : I → C, (∀ i, w i ≤ a i) ∧ (∀ i j, i ≠ j → w i ⊓ w j = ⊥) ∧ (⨆ i, w i) = ⨆ i, a i := by
  classical
  obtain ⟨_lo, wf⟩ := exists_wellFoundedLT I
  letI := _lo
  haveI : WellFoundedLT (I) := wf
  let past := fun i : I => ⨆ j : {j : I // j < i}, a j.val
  let w := fun i => a i ⊓ (past i)ᶜ
  have hd {i j : I} (h : i < j) : w i ⊓ w j = ⊥ := by
    have hl : w i ≤ past j := inf_le_left.trans (le_iSup (fun k : {k : I // k < j} => a k.val) ⟨i, h⟩)
    exact bot_unique ((inf_le_inf hl (show w j ≤ (past j)ᶜ from inf_le_right)).trans
      inf_compl_eq_bot.le)
  refine ⟨w, fun _ => inf_le_left, ?_, le_antisymm (iSup_mono (fun _ => inf_le_left)) ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hd h
    · exact (inf_comm _ _).trans (hd h)
  · apply iSup_le
    intro i
    apply wf.induction i
    intro j ih
    calc
      a j = a j ⊓ past j ⊔ w j := by
        change a j = a j ⊓ past j ⊔ a j ⊓ (past j)ᶜ
        rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
      _ ≤ ⨆ k, w k := sup_le
        (inf_le_right.trans (iSup_le fun k : {k : I // k < j} => ih k.val k.property))
        (le_iSup w j)

end Erdos1172LevyCohen
