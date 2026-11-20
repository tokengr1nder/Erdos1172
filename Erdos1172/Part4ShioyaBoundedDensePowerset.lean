/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4DenseCompletionCardinality
public import Erdos1172.Part4BooleanCheckedIndicatorAgreement
public import Erdos1172.Part4GroundIndexNameBound

@[expose] public section

/-! # Powerset names read below a bounded initial segment of a dense enumeration -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open bSet Lattice Erdos1172PosetCompletion bSet.ErdosCheckedIndicator
universe u
namespace Erdos1172Shioya.BoundedDensePowerset
variable {P : Type u} [Preorder P] [Nonempty P]
local instance : NontrivialCompleteBooleanAlgebra (Completion P) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top
variable {θ : Cardinal.{u}} (D : Set P) (e : D ↪ θ.ord.ToType)
local notation "B" => Completion P

def label (j : θ.ord.ToType) : bSet B := check (PSet.ordinalMk j.toOrd.val)

def positives (b : B) (x : bSet B) : B :=
  ⨆ d : {d : D // condition d.val ≤ b}, condition d.val.val ⊓ (x =ᴮ label (e d.val))

private theorem positive_witness (hd : ∀ p : P, ∃ d ∈ D, d ≤ p) (z : θ.ord.ToType) (b : B) :
    ∃ x : bSet B, (⊤ : B) ≤ x ∈ᴮ check (PSet.ordinalMk θ.ord) ∧ b ≤ positives D e b x := by
  let pred (x : bSet B) := (x ∈ᴮ check (PSet.ordinalMk θ.ord)) ⊓ (bᶜ ⊔ positives D e b x)
  obtain ⟨x,hx⟩ := maximum_principle pred (B_ext_inf B_ext_mem_left (B_ext_sup (h₁ := B_ext_const)
    (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_bv_eq_left))))
  have hm (i : θ.ord.ToType) : (⊤ : B) ≤ label i ∈ᴮ check (PSet.ordinalMk θ.ord) :=
    check_mem (PSet.mk_mem_mk_of_lt i.toOrd.property)
  have hneg : bᶜ ≤ pred x := (le_iSup_of_le (label z) (le_inf (le_top.trans (hm z)) le_sup_left)).trans_eq hx
  have hpos : b ≤ pred x := by
    apply le_of_dense_conditions_le D hd
    intro d h
    apply (le_iSup_of_le (label (e d)) _).trans_eq hx
    apply le_inf (le_top.trans (hm (e d)))
    apply le_sup_of_le_right
    exact le_iSup_of_le (⟨d,h⟩ : {d : D // condition d.val ≤ b}) (le_inf le_rfl bv_refl)
  have hall : (⊤ : B) ≤ pred x := (show b ⊔ bᶜ = ⊤ from sup_compl_eq_top).symm.le.trans (sup_le hpos hneg)
  refine ⟨x,hall.trans inf_le_left,?_⟩
  apply (le_inf (le_refl b) (hpos.trans inf_le_right)).trans
  rw [inf_sup_left,inf_compl_eq_bot,bot_sup_eq]
  exact inf_le_right

abbrev Initial (d : θ.ord.ToType) := {j : D // e j < d}
abbrev Code (A : PSet.{u}) := Σ d : θ.ord.ToType, Set (A.Type × Initial D e d)

omit [Preorder P] [Nonempty P] in
private theorem code_small (A : PSet.{u}) (hθ : θ.IsInaccessible) (hA : Cardinal.mk A.Type < θ) :
    Cardinal.mk (Code D e A) ≤ θ := by
  rw [Code,Cardinal.mk_sigma]
  apply (Cardinal.sum_le_sum _ (fun _ => θ) _).trans
  · rw [Cardinal.sum_const',Cardinal.mk_ord_toType,Cardinal.mul_eq_self hθ.aleph0_lt.le]
  · intro d
    let f (j : Initial D e d) : Set.Iio d := ⟨e j.val,j.property⟩
    have hf : Function.Injective f := fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h))
    have hl : Cardinal.mk (Set.Iio d) < θ := by simpa using Cardinal.mk_Iio_lt d (by simp)
    rw [Cardinal.mk_set,Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id]
    exact (hθ.isStrongLimit.isStrongPrelimit (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hA
      ((Cardinal.mk_le_of_injective hf).trans_lt hl))).le

def weight (A : PSet.{u}) (c : Code D e A) (i : A.Type) : B :=
  ⨆ j : {j : Initial D e c.1 // (i,j) ∈ c.2}, condition j.val.val.val

def records (A : PSet.{u}) : bSet B :=
  .mk (Code D e A) (fun c => checkedIndicator A (weight D e A c)) (fun _ => ⊤)

def record (A : PSet.{u}) (b : A.Type → B) (a : θ.ord.ToType) : Code D e A :=
  ⟨a,{z | condition z.2.val.val ≤ b z.1}⟩

omit [Nonempty P] in
private theorem record_weight_le (A : PSet.{u}) (b : A.Type → B) (a : θ.ord.ToType) (i : A.Type) :
    weight D e A (record D e A b a) i ≤ b i := iSup_le fun j => j.property

private theorem le_record_weight (A : PSet.{u}) (b : A.Type → B) (x : A.Type → bSet B)
    (hp : ∀ i, b i ≤ positives D e (b i) (x i)) (a : θ.ord.ToType) (i : A.Type) {Λ : B}
    (ha : Λ ≤ x i ∈ᴮ label a) : Λ ⊓ b i ≤ weight D e A (record D e A b a) i := by
  apply (le_inf (le_refl (Λ ⊓ b i)) (inf_le_right.trans (hp i))).trans
  unfold positives
  rw [inf_iSup_eq]
  apply iSup_le
  intro d
  let z := (Λ ⊓ b i) ⊓ (condition d.val.val ⊓ (x i =ᴮ label (e d.val)))
  by_cases h : e d.val < a
  · let j : Initial D e a := ⟨d.val,h⟩
    exact le_iSup_of_le (⟨j,d.property⟩ : {j : Initial D e a // (i,j) ∈ (record D e A b a).2})
      (inf_le_right.trans inf_le_left)
  · have he : z ≤ x i =ᴮ label (e d.val) := inf_le_right.trans inf_le_right
    have hxa : z ≤ x i ∈ᴮ label a := inf_le_left.trans (inf_le_left.trans ha)
    have hm : z ≤ label (e d.val) ∈ᴮ label a := mem_congr he bv_refl hxa
    apply (hm.trans_eq (not_check_mem_iff.mp ?_)).trans bot_le
    exact fun hmem => h (Ordinal.ToType.mk.symm.lt_iff_lt.mp (PSet.ordinalMk_lt_of_mem hmem))

include e in
/-- When each family of A-indexed choices in the checked θ is locally bounded
in θ, indicators for arbitrary subsets of checked A are coded on bounded parts
of the ground dense enumeration. -/
theorem powerset_injects_of_bounded_labels (hd : ∀ p : P, ∃ d ∈ D, d ≤ p) (A : PSet.{u})
    (hθ : θ.IsInaccessible) (hA : Cardinal.mk A.Type < θ) {Γ : B}
    (bounds : ∀ x : A.Type → bSet B, (∀ i, (⊤ : B) ≤ x i ∈ᴮ check (PSet.ordinalMk θ.ord)) →
      Γ ≤ ⨆ a : θ.ord.ToType, ⨅ i, x i ∈ᴮ check (PSet.ordinalMk a.toOrd.val)) :
    Γ ≤ injects_into (bv_powerset (check A)) (check (PSet.ordinalMk θ.ord)) := by
  have small := ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le θ
    (records D e A) (code_small D e A hθ hA)
  apply injects_into_trans (injects_into_of_subset ?_) (le_top.trans small)
  rw [subset_unfold']
  apply le_iInf
  intro y
  rw [← deduction]
  let b (i : A.Type) : B := check (A.Func i) ∈ᴮ y
  let z : θ.ord.ToType := Ordinal.ToType.mk ⟨0,Cardinal.ord_pos.mpr hθ.pos⟩
  choose x hmem hx using fun i : A.Type => positive_witness D e hd z (b i)
  let Δ := Γ ⊓ (y ∈ᴮ bv_powerset (check A))
  have hy : Δ ≤ y ⊆ᴮ check A := mem_powerset_iff.mp inf_le_right
  have hb := bounds x hmem
  apply (le_inf (le_refl Δ) (inf_le_left.trans hb)).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro a
  let Λ := Δ ⊓ ⨅ i, x i ∈ᴮ label a
  let c := record D e A b a
  have hrep : Λ ≤ y =ᴮ checkedIndicator A b := by
    rw [checkedIndicator_membership_eq]
    exact eq_membership_indicator_of_subset (inf_le_left.trans hy)
  have heq : Λ ≤ checkedIndicator A b =ᴮ checkedIndicator A (weight D e A c) := by
    apply (le_inf ?_ ?_).trans (eq_of_subset_subset _ _)
    · apply checkedIndicator_subset_of_coefficients
      exact fun i => le_record_weight D e A b x hx a i (inf_le_right.trans (iInf_le _ i))
    · apply checkedIndicator_subset_of_coefficients
      exact fun i => inf_le_right.trans (record_weight_le D e A b a i)
  rw [mem_unfold]
  exact le_iSup_of_le (c : (records D e A).type) (le_inf le_top (bv_trans hrep heq))

end Erdos1172Shioya.BoundedDensePowerset
