/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaLevyCardinalBounds
public import Erdos1172.Part4ShioyaCohenCoverReading
public import Erdos1172.Part4BooleanCheckedIndicatorAgreement

@[expose] public section

/-! # Cardinal bounds after the bounded Cohen strings

Reading a short sequence of rows over the first Boolean algebra bounds
each row by fewer than θ labels. Hence a function with fewer than θ ground
inputs cannot cover θ distinct checked labels. Reading binary rows also
recovers an arbitrary subset of a checked short domain from first-stage
Boolean coefficients.
-/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion bSet Lattice ErdosCheckedIndicator
open scoped Flypitch
universe u

namespace Erdos1172Shioya.CohenCover

variable {θ : Cardinal.{u}} {B : Type u} [NontrivialCompleteBooleanAlgebra B]

instance completionNontrivial [Nonempty (Condition θ B)] :
    NontrivialCompleteBooleanAlgebra (Completion (Condition θ B)) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

abbrev ChainCondition (θ : Cardinal.{u}) (B : Type u) [NontrivialCompleteBooleanAlgebra B] :=
  ∀ {I : Type u} (v : I → B), (∀ i, v i ≠ ⊥) →
    (∀ i j, i ≠ j → v i ⊓ v j = ⊥) → Cardinal.mk I < θ

private theorem small_subcover (hcc : ChainCondition θ B) {J : Type u} (a : J → B) :
    ∃ S : Set J, Cardinal.mk S < θ ∧ (⨆ j, a j) ≤ ⨆ j : S, a j.val := by
  obtain ⟨w, hw, hd, he⟩ := disjoint_cover a
  let S := {j : J | w j ≠ ⊥}
  refine ⟨S, hcc (fun j : S => w j.val) (fun j => j.property)
    (fun i j hij => hd _ _ (fun h => hij (Subtype.ext h))), ?_⟩
  rw [← he]
  apply iSup_le
  intro j
  by_cases h : w j = ⊥
  · exact h.le.trans bot_le
  · exact (hw j).trans (le_iSup (fun z : S => a z.val) ⟨j,h⟩)

variable (hθ : θ.IsRegular) (hcc : ChainCondition θ B)

include hθ hcc in
theorem exists_small_row_covers {I J : Type u} (hI : Cardinal.mk I < θ)
    (p : Condition θ B) (c : I → J → Completion (Condition θ B))
    (hc : ∀ i, condition p ≤ ⨆ j, c i j) :
    ∃ q ≤ p, ∃ S : I → Set J, (∀ i, Cardinal.mk (S i) < θ) ∧
      ∀ i, condition q ≤ ⨆ j : S i, c i j.val := by
  classical
  obtain ⟨_lo, wf⟩ := exists_wellFoundedLT I
  letI := _lo
  haveI : WellFoundedLT (I) := wf
  obtain ⟨q, hqp, hv, hq⟩ := exists_short_row_reading hθ hcc hI p c hc
  choose S hS hcov using fun i => small_subcover hcc (fun j => q.read (c i j))
  refine ⟨q, hqp, S, hS, fun i => ?_⟩
  have h := (condition_le_firstStageHom_iff q _).mpr (hv.le.trans ((hq i).trans (hcov i)))
  apply (le_inf le_rfl h).trans
  rw [map_iSup, inf_iSup_eq]
  exact iSup_mono fun j => q.inf_firstStageHom_read (c i j.val)

private theorem pair_row {C : Type u} [NontrivialCompleteBooleanAlgebra C]
    (X Y : PSet.{u}) {f : bSet C} {Γ : C} (ht : Γ ≤ is_total (check X) (check Y) f) (i : X.Type) :
    Γ ≤ ⨆ j : Y.Type, pair (check (X.Func i)) (check (Y.Func j)) ∈ᴮ f := by
  have h : Γ ≤ ⨆ y : bSet C, y ∈ᴮ check Y ⊓ pair (check (X.Func i)) y ∈ᴮ f :=
    (le_inf (ht.trans (iInf_le _ (check (X.Func i)))) mem_check_of_mem).trans bv_imp_elim
  rw [← @bounded_exists C _ (check Y) (fun y => pair (check (X.Func i)) y ∈ᴮ f)
    (h_congr := B_ext_pair_mem_right)] at h
  cases Y
  exact h.trans (iSup_mono (fun _ => inf_le_right))

private theorem pair_column {C : Type u} [NontrivialCompleteBooleanAlgebra C]
    (X Y : PSet.{u}) {f : bSet C} {Γ : C} (hs : Γ ≤ is_surj (check X) (check Y) f) (j : Y.Type) :
    Γ ≤ ⨆ i : X.Type, pair (check (X.Func i)) (check (Y.Func j)) ∈ᴮ f := by
  have h : Γ ≤ ⨆ x : bSet C, x ∈ᴮ check X ⊓ pair x (check (Y.Func j)) ∈ᴮ f :=
    (le_inf (hs.trans (iInf_le _ (check (Y.Func j)))) mem_check_of_mem).trans bv_imp_elim
  rw [← @bounded_exists C _ (check X) (fun x => pair x (check (Y.Func j)) ∈ᴮ f)
    (h_congr := B_ext_pair_mem_left)] at h
  cases X
  exact h.trans (iSup_mono (fun _ => inf_le_right))

variable [Nonempty (Condition θ B)]

include hθ hcc in
theorem small_surjection_eq_bot (X Y : PSet.{u}) (hX : Cardinal.mk X.Type < θ)
    (hY : θ ≤ Cardinal.mk Y.Type) (hsep : ∀ i j : Y.Type, i ≠ j → ¬ PSet.Equiv (Y.Func i) (Y.Func j)) :
    (surjects_onto (check X) (check Y) : Completion (Condition θ B)) = ⊥ := by
  classical
  apply bot_unique
  apply iSup_le
  intro f
  by_contra h
  obtain ⟨p,hp⟩ := exists_condition_le (fun he => h he.le)
  let c (i : X.Type) (j : Y.Type) : Completion (Condition θ B) := pair (check (X.Func i)) (check (Y.Func j)) ∈ᴮ f
  obtain ⟨q,hqp,S,hS,hq⟩ := exists_small_row_covers hθ hcc hX p c
    (pair_row X Y (hp.trans (inf_le_left.trans inf_le_right)))
  let D := ⋃ i, S i
  have hD : Cardinal.mk D < θ := (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hθ hX).mpr hS
  obtain ⟨j,hj⟩ : ∃ j : Y.Type, j ∉ D := by
    by_contra! hall
    have he : D = Set.univ := Set.eq_univ_of_forall hall
    exact hY.not_gt (by simpa only [he, Cardinal.mk_univ] using hD)
  have hf := (condition_mono hqp).trans hp
  have hc : condition q ≤ ⨆ i, c i j := pair_column X Y (hf.trans inf_le_right) j
  apply condition_ne_bot q
  apply bot_unique
  apply (le_inf le_rfl hc).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply (le_inf le_rfl (inf_le_left.trans (hq i))).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro k
  have he : (condition q ⊓ c i j) ⊓ c i k.val ≤ check (Y.Func j) =ᴮ check (Y.Func k.val) :=
    eq_of_is_func_of_eq (inf_le_left.trans (inf_le_left.trans (hf.trans (inf_le_left.trans inf_le_left))))
      bv_refl (inf_le_left.trans inf_le_right) inf_le_right
  exact he.trans_eq (check_bv_eq_bot_of_not_equiv (hsep j k.val (fun h =>
    hj (Set.mem_iUnion.mpr ⟨i, h ▸ k.property⟩))))

private theorem binary_forward {C : Type u} [CompleteBooleanAlgebra C] {d x yes no : C}
    (cover : d ≤ yes ⊔ no) (hno : d ⊓ no ≤ xᶜ) : d ⊓ x ≤ yes := by
  apply (le_inf le_rfl (inf_le_left.trans cover)).trans
  rw [inf_sup_left]
  apply sup_le inf_le_right
  have hx : (d ⊓ x) ⊓ no ≤ x := inf_le_left.trans inf_le_right
  have hn : (d ⊓ x) ⊓ no ≤ xᶜ := (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hno
  exact ((le_inf hx hn).trans inf_compl_eq_bot.le).trans bot_le

include hθ hcc in
theorem exists_first_stage_subset_reading (A : PSet.{u}) (hA : Cardinal.mk A.Type < θ)
    (x : bSet (Completion (Condition θ B))) (p : Condition θ B) (hx : condition p ≤ x ⊆ᴮ check A) :
    ∃ q ≤ p, ∃ b : A.Type → B,
      condition q ≤ x =ᴮ checkedIndicator A (fun i => firstStageHom θ B (b i)) := by
  classical
  let χ (i : A.Type) : Completion (Condition θ B) := check (A.Func i) ∈ᴮ x
  let c (i : A.Type) (j : ULift.{u} Bool) := if j.down = true then χ i else (χ i)ᶜ
  have hc (i : A.Type) : condition p ≤ ⨆ j, c i j := by
    have h₁ : χ i ≤ ⨆ j, c i j := le_iSup_of_le (ULift.up true) le_rfl
    have h₀ : (χ i)ᶜ ≤ ⨆ j, c i j := le_iSup_of_le (ULift.up false) le_rfl
    exact le_top.trans (sup_compl_eq_top.ge.trans (sup_le h₁ h₀))
  obtain ⟨_lo, wf⟩ := exists_wellFoundedLT A.Type
  letI := _lo
  haveI : WellFoundedLT (A.Type) := wf
  obtain ⟨q, hqp, hv, hq⟩ := exists_short_row_reading hθ hcc hA p c hc
  let e := firstStageHom θ B
  let b (i : A.Type) := q.read (χ i)
  have heq : condition q ≤ x =ᴮ checkedIndicator A χ := by
    rw [checkedIndicator_membership_eq]
    exact eq_membership_indicator_of_subset ((condition_mono hqp).trans hx)
  refine ⟨q, hqp, b, bv_trans heq (subset_ext (checkedIndicator_subset_of_coefficients A ?_)
    (checkedIndicator_subset_of_coefficients A ?_))⟩
  · intro i
    have hsup : (⨆ j, q.read (c i j)) ≤ q.read (χ i) ⊔ q.read ((χ i)ᶜ) := by
      apply iSup_le
      rintro ⟨j⟩
      cases j
      · exact le_sup_right
      · exact le_sup_left
    have hc' := (condition_le_firstStageHom_iff q _).mpr ((hv.le.trans (hq i)).trans hsup)
    rw [map_sup] at hc'
    exact binary_forward hc' (q.inf_firstStageHom_read ((χ i)ᶜ))
  · intro i
    exact q.inf_firstStageHom_read (χ i)

include hθ hcc in
theorem powerset_injects_checked_of_short_coefficients (A : PSet.{u}) (hA : Cardinal.mk A.Type < θ)
    (hcodes : Cardinal.mk (A.Type → B) ≤ θ) :
    (⊤ : Completion (Condition θ B)) ≤ injects_into (bv_powerset (check A)) (check (PSet.ordinalMk θ.ord)) := by
  let label (b : A.Type → B) := checkedIndicator A (fun i => firstStageHom θ B (b i))
  let Y : bSet (Completion (Condition θ B)) := .mk (A.Type → B) label (fun _ => ⊤)
  have hs : (⊤ : Completion (Condition θ B)) ≤ bv_powerset (check A) ⊆ᴮ Y := by
    rw [subset_unfold]
    apply le_iInf
    intro χ
    rw [← deduction]
    let x := (bv_powerset (check A : bSet (Completion (Condition θ B)))).func χ
    let D : Set (Condition θ B) := {p | condition p ≤ x ∈ᴮ Y}
    apply le_of_dense_conditions_le D _ (fun p _ => p.property)
    intro p
    obtain ⟨q,hq,b,he⟩ := exists_first_stage_subset_reading hθ hcc A hA x p check_set_of_indicator_subset
    refine ⟨q, ?_, hq⟩
    change condition q ≤ x ∈ᴮ Y
    rw [mem_unfold]
    exact le_iSup_of_le b (le_inf le_top he)
  exact injects_into_trans (injects_into_of_subset hs)
    (ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le θ Y hcodes)

section Levy

abbrev LevyCondition (κ θ : Cardinal.{u}) [Nonempty (LevyProduct.Full κ θ)] :=
  Condition θ (Completion (LevyProduct.Full κ θ))

variable {κ : Cardinal.{u}} [Nonempty (LevyProduct.Full κ θ)]
variable [Nonempty (LevyCondition κ θ)]

theorem levy_checked_powerset_injects_upper (hθ : θ.IsInaccessible) (hκθ : κ < θ)
    (hκ : Cardinal.aleph0 ≤ κ) (μ : Cardinal.{u}) (hμ : μ < θ) :
    (⊤ : Completion (LevyCondition κ θ)) ≤ injects_into (bv_powerset (check (PSet.ordinalMk μ.ord)))
      (check (PSet.ordinalMk θ.ord)) := by
  have hs : Cardinal.mk (PSet.ordinalMk μ.ord).Type < θ := by
    simpa only [PSet.ordinalMk_card, Cardinal.card_ord] using hμ
  exact powerset_injects_checked_of_short_coefficients hθ.isRegular
    (fun w hp hd => LevyProduct.full_completion_disjoint_family_cardinal_lt hθ hκθ hκ w hp hd)
    (PSet.ordinalMk μ.ord) hs (LevyProduct.full_short_coefficients_cardinal_le hθ hκθ hκ hs)

theorem levy_upper_injects_predecessor_eq_bot (hθ : θ.IsInaccessible) (hκθ : κ < θ)
    (hκ : Cardinal.aleph0 ≤ κ) (γ : Ordinal.{u}) (hγ : γ < θ.ord) :
    (injects_into (check (PSet.ordinalMk θ.ord)) (check (PSet.ordinalMk γ)) :
      Completion (LevyCondition κ θ)) = ⊥ := by
  have hs := small_surjection_eq_bot (B := Completion (LevyProduct.Full κ θ)) hθ.isRegular
    (fun w hp hd => LevyProduct.full_completion_disjoint_family_cardinal_lt hθ hκθ hκ w hp hd)
    (PSet.ordinalMk γ) (PSet.ordinalMk θ.ord)
    (by simpa only [PSet.ordinalMk_card] using Cardinal.lt_ord.mp hγ)
    (by simp only [PSet.ordinalMk_card, Cardinal.card_ord, le_refl]) (PSet.ordinalMk_inj _)
  obtain ⟨z,hz⟩ := PSet.exists_mem_of_nonzero (Cardinal.ord_pos.mpr hθ.pos)
  have hm : (⊤ : Completion (LevyCondition κ θ)) ≤ exists_mem (check (PSet.ordinalMk θ.ord)) :=
    le_iSup_of_le (check z) (check_mem hz)
  exact bot_unique ((surjects_onto_of_injects_into' le_rfl (le_top.trans hm)).trans_eq hs)

end Levy

end Erdos1172Shioya.CohenCover
