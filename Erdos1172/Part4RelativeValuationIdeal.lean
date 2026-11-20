/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4RelativeNormalValuation
public import Erdos1172.Part4BooleanWeightedDenseBasis

@[expose] public section

/-! # The ideal and dense family as names in the source forcing -/

set_option autoImplicit false
noncomputable section
open bSet ErdosIdeal ErdosWeightedDenseBasis ErdosOmegaTwo ErdosDenseBasis
open Erdos1172BooleanFactor Erdos1172SeedQuotient
open scoped Flypitch
universe u
namespace Erdos1172RelativeValuation
variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable (κ : Cardinal.{u}) (e : CompleteLatticeHom B C) (μ : BoundedLatticeHom (κ.ord.ToType → B) C)
variable (scalar : ∀ b : B, μ (fun _ => b) = e b)
local notation "K" => (check (PSet.ordinalMk κ.ord) : bSet B)

def coeff (X : bSet B) (i : κ.ord.ToType) : B := label κ i ∈ᴮ X

theorem coeff_domain (a : κ.ord.ToType → B) : coeff κ (domain κ a) = a := by
  funext i
  apply le_antisymm _ (label_mem κ a i)
  rw [mem_unfold]
  apply iSup_le
  intro j
  by_cases h : i = j
  · subst j
    exact inf_le_left
  · have hn : ¬PSet.Equiv (PSet.ordinalMk i.toOrd.val) (PSet.ordinalMk j.toOrd.val) :=
      fun eq => h (Ordinal.ToType.mk.symm.injective (Subtype.ext (PSet.eq_of_mk_equiv eq)))
    exact (inf_le_right.trans_eq (check_bv_eq_bot_of_not_equiv hn)).trans bot_le

def null (X : bSet B) : B := (lowerProjection e (μ (coeff κ X)))ᶜ

theorem le_null_iff (X : bSet B) (b : B) : b ≤ null κ e μ X ↔ e b ⊓ μ (coeff κ X) = ⊥ := by
  rw [null,le_compl_comm,lowerProjection_le_iff,map_compl',le_compl_iff_disjoint_left,disjoint_iff]

include scalar in
theorem localized_subset {X Y : bSet B} {b : B} (h : b ≤ X ⊆ᴮ Y) :
    e b ⊓ μ (coeff κ X) ≤ μ (coeff κ Y) := by
  rw [localized e μ scalar]
  exact OrderHomClass.mono μ (fun i => mem_of_mem_subset (inf_le_left.trans h) inf_le_right)

include scalar in
theorem null_ext : B_ext (null κ e μ) := by
  intro X Y
  let b := (X =ᴮ Y) ⊓ null κ e μ X
  apply (le_null_iff κ e μ Y b).mpr
  have le : e b ⊓ μ (coeff κ Y) ≤ μ (coeff κ X) :=
    localized_subset κ e μ scalar (subset_of_eq (bv_symm (show b ≤ X =ᴮ Y from inf_le_left)))
  exact bot_unique ((le_inf inf_le_left le).trans_eq ((le_null_iff κ e μ X b).mp inf_le_right))

def idealName : bSet B := comprehend (null κ e μ) (bv_powerset K)

include scalar in
theorem mem_ideal_iff {X : bSet B} {b : B} : b ≤ X ∈ᴮ idealName κ e μ ↔
    b ≤ X ⊆ᴮ K ∧ e b ⊓ μ (coeff κ X) = ⊥ := by
  rw [idealName,ErdosRelationGraph.mem_comprehend_and (null_ext κ e μ scalar),mem_powerset_iff,le_null_iff]

include scalar in
theorem positive_value (X : bSet B) :
    positive K (idealName κ e μ) X = (X ⊆ᴮ K) ⊓ lowerProjection e (μ (coeff κ X)) := by
  have hm : X ∈ᴮ idealName κ e μ = (X ⊆ᴮ K) ⊓ null κ e μ X := by
    apply eq_of_forall_le_iff
    intro b
    rw [mem_ideal_iff κ e μ scalar,le_inf_iff,le_null_iff]
  rw [positive,hm,null,compl_inf,compl_compl,inf_sup_left,inf_compl_eq_bot,bot_sup_eq]

theorem coeff_difference (X Y : bSet B) :
    coeff κ (difference X Y) = coeff κ X ⊓ (coeff κ Y)ᶜ := by
  funext i
  exact mem_difference X Y _

include scalar in
theorem loss_value (X Y : bSet B) (sub : (⊤ : B) ≤ X ⊆ᴮ K) :
    (difference X Y ∈ᴮ idealName κ e μ) =
      (lowerProjection e (μ (coeff κ X) ⊓ (μ (coeff κ Y))ᶜ))ᶜ := by
  have h : difference X Y ∈ᴮ idealName κ e μ = null κ e μ (difference X Y) := by
    apply eq_of_forall_le_iff
    intro b
    rw [mem_ideal_iff κ e μ scalar,le_null_iff]
    exact and_iff_right (subset_trans' difference_subset (le_top.trans sub))
  rw [h,null,coeff_difference,map_inf,map_compl']

include scalar in
theorem idealName_proper (he : Function.Injective e) : (⊤ : B) ≤ properIdeal K (idealName κ e μ) := by
  have hm {X : bSet B} {b : B} := @mem_ideal_iff B C _ _ κ e μ scalar X b
  apply le_inf
  · refine le_inf (comprehend_subset (ϕ := null κ e μ) (bv_powerset K)) (le_inf ?_ (le_inf ?_ ?_))
    · apply hm.mpr
      refine ⟨empty_subset,?_⟩
      have hz : coeff κ (∅ : bSet B) = ⊥ := funext fun _ => bot_unique (bot_of_mem_empty le_rfl)
      rw [hz,map_bot,inf_bot_eq]
    · apply le_iInf; intro X; apply le_iInf; intro Y
      rw [← deduction,top_inf_eq]
      let b := (X ⊆ᴮ Y) ⊓ (Y ∈ᴮ idealName κ e μ)
      have hy := hm.mp (show b ≤ Y ∈ᴮ idealName κ e μ from inf_le_right)
      exact hm.mpr ⟨subset_trans' inf_le_left hy.1,bot_unique ((le_inf inf_le_left
        (localized_subset κ e μ scalar (show b ≤ X ⊆ᴮ Y from inf_le_left))).trans_eq hy.2)⟩
    · apply le_iInf; intro X; apply le_iInf; intro Y
      rw [← deduction,top_inf_eq]
      let b := (X ∈ᴮ idealName κ e μ) ⊓ (Y ∈ᴮ idealName κ e μ)
      have hx := hm.mp (show b ≤ X ∈ᴮ idealName κ e μ from inf_le_left)
      have hy := hm.mp (show b ≤ Y ∈ᴮ idealName κ e μ from inf_le_right)
      apply hm.mpr
      refine ⟨ErdosSmallPoolOperations.binary_union_subset hx.1 hy.1,?_⟩
      have hu : coeff κ (binary_union X Y) = coeff κ X ⊔ coeff κ Y := funext (fun _ => mem_binary_union X Y _)
      change e b ⊓ μ _ = ⊥
      rw [hu,map_sup,inf_sup_left,hx.2,hy.2,sup_idem]
  · apply le_compl_iff_disjoint_right.mpr
    rw [disjoint_iff,top_inf_eq]
    have hK : coeff κ K = ⊤ := funext fun i => top_unique (check_mem (PSet.mk_mem_mk_of_lt i.toOrd.property))
    have h := (hm.mp (show (K ∈ᴮ idealName κ e μ) ≤ K ∈ᴮ idealName κ e μ from le_rfl)).2
    rw [hK,map_top,inf_top_eq] at h
    exact he (h.trans (map_bot e).symm)

include scalar in
/-- All four internal basis fields use the actual residual forcing's
density. Each chosen value is represented by a subset name in the source. -/
theorem exists_internal_basis (δ : Cardinal.{u}) (d : δ.ord.ToType → C) (dense : denseOver e d)
    (normal : ∀ F : δ.ord.ToType → κ.ord.ToType → B, ∃ X, μ X = ⨆ i, μ (F i))
    {Γ : B} (hδ : Γ ≤ check (PSet.ordinalMk δ.ord) =ᴮ omegaOne) :
    ∃ I D : bSet B, Γ ≤ is_function I (bv_powerset K) D ∧
      Γ ≤ positiveValues K (idealName κ e μ) I D ∧ Γ ≤ denseValues K (idealName κ e μ) I D ∧
      Γ ≤ injects_into I omegaOne := by
  obtain ⟨X,cover⟩ := exists_quotient_basis e μ scalar d dense normal
  let Y (i : δ.ord.ToType) := domain κ (X i)
  let w (i : δ.ord.ToType) := positive K (idealName κ e μ) (Y i)
  have good (i : δ.ord.ToType) : (⊤ : B) ≤ Y i ⊆ᴮ K := domain_subset_checked κ (X i)
  refine ⟨domain δ w, graph δ w Y, basis_fields δ w Y K (idealName κ e μ) hδ (fun _ => le_rfl) ?_⟩
  intro A
  apply inf_le_right.trans
  rw [positive_value κ e μ scalar]
  apply inf_le_right.trans ((cover (coeff κ A)).trans (iSup_mono ?_))
  intro i
  dsimp only [w]
  rw [positive_value κ e μ scalar,top_unique (good i),top_inf_eq,loss_value κ e μ scalar _ _ (good i)]
  simp only [Y,coeff_domain,le_rfl]

end Erdos1172RelativeValuation
