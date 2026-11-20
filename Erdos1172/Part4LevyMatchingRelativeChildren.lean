/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingRelativeSplit

@[expose] public section

/-! # A resolving partition that retains the whole old-stage support -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal Erdos1172BooleanFactor
namespace Erdos1172LevyCollapse.Matching

variable {A B X : Type u} [CompleteBooleanAlgebra A] [CompleteBooleanAlgebra B]
variable (e : CompleteLatticeHom A B)
local notation "π" => lowerProjection e

private theorem lowerProjection_sup (u v : B) : π (u ⊔ v) = π u ⊔ π v := by
  apply le_antisymm ((lowerProjection_le_iff e).mpr (sup_le ((lowerProjection_le_iff e).mp le_sup_left)
    ((lowerProjection_le_iff e).mp le_sup_right)))
  exact sup_le (lowerProjection_mono e le_sup_left) (lowerProjection_mono e le_sup_right)

/-- For each requested piece cᵢ, one child restricts below cᵢ on precisely
its old-stage support. All children, including this one, have the parent's
full support and together exhaust it. -/
theorem exists_relative_children (hX : ℵ₀ ≤ #X)
    (split : ∀ p : B, ∃ v : X → B, (∀ x, v x ≤ p) ∧ (∀ x, π (v x) = π p) ∧
      ∀ x y, x ≠ y → v x ⊓ v y = ⊥)
    (p : B) (c : X → B) (sub : ∀ x, c x ≤ p) (sep : ∀ x y, x ≠ y → Disjoint (c x) (c y)) :
    ∃ v : X → B, (∀ x, v x ≤ p) ∧ (∀ x, π (v x) = π p) ∧
      (∀ x y, x ≠ y → Disjoint (v x) (v y)) ∧ (⨆ x, v x) = p ∧
      ∀ x, ∃ k, v k ⊓ e (π (c x)) ≤ c x := by
  classical
  let _ : Infinite X := Cardinal.infinite_iff.mpr hX
  obtain ⟨i,j,hij⟩ := exists_pair_ne X
  let idx : Option X ≃ X := Classical.choice (Cardinal.eq.mp (Cardinal.mk_option.trans (Cardinal.add_one_eq hX)))
  choose a asub aproj asep using fun x => split (c x)
  let t (x : X) := a x i
  let r := p ⊓ (⨆ x, t x)ᶜ
  have trem (x : X) : a x j ≤ r := by
    refine le_inf ((asub x j).trans (sub x)) (le_compl_iff_disjoint_right.mpr ?_)
    apply disjoint_iSup_iff.mpr
    intro y
    by_cases xy : x = y
    · subst y
      exact disjoint_iff.mpr (asep x j i hij.symm)
    · exact (sep x y xy).mono (asub x j) (asub y i)
  have projR : π r = π p := by
    apply le_antisymm (lowerProjection_mono e inf_le_left)
    have old (x) : π (t x) ≤ π r := (aproj x i).trans_le ((aproj x j).symm.trans_le (lowerProjection_mono e (trem x)))
    have h : p ≤ r ⊔ ⨆ x, t x := by
      change p ≤ (p ⊓ (⨆ x, t x)ᶜ) ⊔ ⨆ x, t x
      rw [sup_inf_right,compl_sup_eq_top,inf_top_eq]
      exact le_sup_left
    exact (lowerProjection_mono e h).trans ((lowerProjection_sup e _ _).trans_le
      (sup_le le_rfl ((lowerProjection_iSup e t).trans_le (iSup_le old))))
  obtain ⟨w,wsub,wproj,wsep⟩ := split r
  let fill (x : X) := w (idx (some x)) ⊓ e (π (c x))ᶜ
  let s (x : X) := t x ⊔ fill x
  have ft (x y : X) : Disjoint (fill x) (t y) := by
    apply disjoint_compl_left.mono
    · exact (show fill x ≤ r from inf_le_left.trans (wsub _)).trans inf_le_right
    · exact le_iSup t y
  have ssep (x y : X) (xy : x ≠ y) : Disjoint (s x) (s y) := by
    apply disjoint_sup_left.mpr
    refine ⟨disjoint_sup_right.mpr ⟨(sep x y xy).mono (asub x i) (asub y i),(ft y x).symm⟩,
      disjoint_sup_right.mpr ⟨ft x y,?_⟩⟩
    exact (disjoint_iff.mpr (wsep _ _ (fun he => xy (Option.some.inj (idx.injective he))))).mono
      inf_le_left inf_le_left
  have ssub (x) : s x ≤ p := sup_le ((asub x i).trans (sub x)) (inf_le_left.trans ((wsub _).trans inf_le_left))
  have sproj (x) : π (s x) = π p := by
    change π (t x ⊔ (w (idx (some x)) ⊓ e (π (c x))ᶜ)) = _
    change π (a x i ⊔ (w (idx (some x)) ⊓ e ((π (c x))ᶜ))) = _
    rw [lowerProjection_sup,lowerProjection_inf_image,aproj,wproj,projR,sup_inf_left,
      sup_compl_eq_top,inf_top_eq,sup_eq_right.mpr (lowerProjection_mono e (sub x))]
  let rest := p ⊓ (⨆ x, s x)ᶜ
  have unused : w (idx none) ≤ rest := by
    refine le_inf ((wsub _).trans inf_le_left) (le_compl_iff_disjoint_right.mpr (disjoint_iSup_iff.mpr ?_))
    intro x
    refine disjoint_sup_right.mpr ⟨disjoint_compl_left.mono ((wsub _).trans inf_le_right) (le_iSup t x),?_⟩
    exact (disjoint_iff.mpr (wsep (idx none) (idx (some x))
      (fun h => by cases idx.injective h))).mono le_rfl inf_le_left
  let v : Option X → B := fun k => k.elim rest s
  have vsub (k) : v k ≤ p := by cases k <;> first | exact inf_le_left | exact ssub _
  have vproj (k) : π (v k) = π p := by
    cases k with
    | none =>
      exact le_antisymm (lowerProjection_mono e (vsub none))
        (projR.symm.trans_le ((wproj _).symm.trans_le (lowerProjection_mono e unused)))
    | some x => exact sproj x
  refine ⟨fun x => v (idx.symm x),fun x => vsub _,fun x => vproj _,?_,
    le_antisymm (iSup_le fun x => vsub _) ?_,?_⟩
  · intro x y hxy
    change Disjoint (v (idx.symm x)) (v (idx.symm y))
    have hn : idx.symm x ≠ idx.symm y := fun he => hxy (idx.symm.injective he)
    have rest_dis (k : X) : Disjoint rest (s k) := disjoint_compl_left.mono inf_le_right (le_iSup s k)
    cases hx : idx.symm x <;> cases hy : idx.symm y
    · exact (hn (hx.trans hy.symm)).elim
    · exact rest_dis _
    · exact (rest_dis _).symm
    · exact ssep _ _ (fun h => hn (hx.trans ((congrArg some h).trans hy.symm)))
  · let all := ⨆ x, v (idx.symm x)
    have each (k : Option X) : v k ≤ all := by
      have h := le_iSup (fun x => v (idx.symm x)) (idx k)
      simpa only [idx.symm_apply_apply] using h
    have bound : rest ⊔ (⨆ x, s x) ≤ all := sup_le (each none) (iSup_le fun x => each (some x))
    apply le_trans _ bound
    change p ≤ (p ⊓ (⨆ x, s x)ᶜ) ⊔ ⨆ x, s x
    rw [sup_inf_right,compl_sup_eq_top,inf_top_eq]
    exact le_sup_left
  · intro x
    refine ⟨idx (some x),?_⟩
    change v (idx.symm (idx (some x))) ⊓ e (π (c x)) ≤ c x
    rw [idx.symm_apply_apply]
    change (t x ⊔ fill x) ⊓ e (π (c x)) ≤ c x
    rw [inf_sup_right]
    apply sup_le (inf_le_left.trans (asub x i))
    have hfill : fill x ≤ (e (π (c x)))ᶜ := (show fill x ≤ e ((π (c x))ᶜ) from inf_le_right).trans_eq
      (map_compl' e _)
    exact ((inf_le_inf hfill le_rfl).trans compl_inf_eq_bot.le).trans bot_le

end Erdos1172LevyCollapse.Matching
