/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4RelativeValuationIdeal
public import Erdos1172.Part4BooleanUltrapowerCountableCover

@[expose] public section

/-! # Normality and countable completeness of the source-model ideal -/

set_option autoImplicit false
noncomputable section
open bSet ErdosIdeal ErdosWeightedDenseBasis ErdosOmegaTwo Erdos1172BooleanFactor Lattice
open scoped Flypitch
universe u
namespace Erdos1172RelativeValuation
variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable (κ : Cardinal.{u})
local notation "W" => κ.ord.ToType
local notation "K" => (check (PSet.ordinalMk κ.ord) : bSet B)

def initialValue (i : W) (x : W) : B := if x ≤ i then ⊤ else ⊥
def diagonal (F : W → W → B) (x : W) : B := ⨆ i : Set.Iio x, F i.val x
variable (e : CompleteLatticeHom B C) (μ : BoundedLatticeHom (κ.ord.ToType → B) C)
variable (scalar : ∀ b : B, μ (fun _ => b) = e b)
variable (initial : ∀ i : κ.ord.ToType, μ (initialValue κ i) = ⊥)
variable (normal : ∀ F : κ.ord.ToType → κ.ord.ToType → B, μ (diagonal κ F) ≤ ⨆ i, μ (F i))

include initial normal in
theorem diagonal_value (F : W → W → B) : μ (diagonal κ F) = ⨆ i, μ (F i) := by
  refine le_antisymm (normal F) (iSup_le fun i => ?_)
  have le : F i ≤ initialValue κ i ⊔ diagonal κ F := by
    intro x
    by_cases h : x ≤ i
    · exact (show F i x ≤ initialValue κ i x by simp [initialValue,h]).trans le_sup_left
    · exact (le_iSup (fun t : Set.Iio x => F t.val x) ⟨i,lt_of_not_ge h⟩).trans le_sup_right
  exact (OrderHomClass.mono μ le).trans_eq (by rw [map_sup,initial,bot_sup_eq])

include initial normal in
theorem bounded_union_value {J : Type u} (v : J ↪ W) {z : W} (bound : ∀ j, v j ≤ z)
    (F : J → W → B) : μ (fun x => ⨆ j, F j x) = ⨆ j, μ (F j) := by
  classical
  let A (i : W) : W → B := if h : ∃ j, v j = i then F h.choose else ⊥
  have atIndex (j : J) : A (v j) = F j := by
    have h : ∃ k, v k = v j := ⟨j,rfl⟩
    simp only [A,dif_pos h,v.injective h.choose_spec]
  have le : (fun x => ⨆ j, F j x) ≤ initialValue κ z ⊔ diagonal κ A := by
    intro x
    by_cases h : x ≤ z
    · exact (show (⨆ j, F j x) ≤ initialValue κ z x by simp [initialValue,h]).trans le_sup_left
    · apply iSup_le
      intro j
      have lt := (bound j).trans_lt (lt_of_not_ge h)
      exact (congrFun (atIndex j).symm x).trans_le
        ((le_iSup (fun t : Set.Iio x => A t.val x) ⟨v j,lt⟩).trans le_sup_right)
  apply le_antisymm
  · apply (OrderHomClass.mono μ le).trans
    rw [map_sup,initial,bot_sup_eq,diagonal_value κ μ initial normal]
    apply iSup_le
    intro i
    by_cases h : ∃ j, v j = i
    · obtain ⟨j,rfl⟩ := h
      rw [atIndex]
      exact le_iSup (fun k => μ (F k)) j
    · simp only [A,dif_neg h,map_bot,bot_le]
  · exact iSup_le (fun j => OrderHomClass.mono μ (fun x => le_iSup (fun k => F k x) j))

include initial normal in
theorem countable_union_value (hk : Cardinal.aleph0 < κ) (F : ULift.{u} ℕ → W → B) :
    μ (fun x => ⨆ j, F j x) = ⨆ j, μ (F j) := by
  let emb := (Ordinal.ToType.mk (o := κ.ord))
  have hω : Ordinal.omega0 < κ.ord := by simpa using Cardinal.ord_lt_ord.mpr hk
  let z := emb ⟨Ordinal.omega0,hω⟩
  let idx (n : ULift.{u} ℕ) := emb ⟨n.down,(Ordinal.natCast_lt_omega0 _).trans hω⟩
  have inj : Function.Injective idx := by
    intro n m eq
    exact ULift.down_injective (Nat.cast_injective (R := Ordinal.{u}) (congrArg Subtype.val (emb.injective eq)))
  apply bounded_union_value κ μ initial normal ⟨idx,inj⟩ (z := z) _ F
  intro n
  exact emb.monotone (show (n.down : Ordinal.{u}) ≤ Ordinal.omega0 from (Ordinal.natCast_lt_omega0 _).le)

theorem checked_member_cover (x : bSet B) :
    (x ∈ᴮ K) = ⨆ i : W, x =ᴮ label κ i := by
  rw [PSet.ordinalMk_eq_def κ.ord,check_unfold,mem_unfold]
  change (⨆ i : W, ⊤ ⊓ (x =ᴮ label κ i)) = _
  simp only [top_inf_eq]

private theorem checked_lt_of_mem (i j : W) (h : ¬i < j) :
    ((label κ i : bSet B) ∈ᴮ label κ j) = ⊥ := by
  apply not_check_mem_iff.mp
  exact fun hm => h (Ordinal.ToType.mk.symm.lt_iff_lt.mp (PSet.ordinalMk_lt_of_mem hm))

private theorem coeff_diagonal_le (R : bSet B) :
    coeff κ (diagonalUnion K R) ≤ diagonal κ (fun i => coeff κ (fiber K R (label κ i))) := by
  intro x
  rw [coeff,mem_diagonalUnion]
  apply inf_le_right.trans
  apply iSup_le
  intro z
  have split := checked_member_cover κ z
  rw [split,iSup_inf_eq,iSup_inf_eq]
  apply iSup_le
  intro i
  let b := ((z =ᴮ label κ i) ⊓ (z ∈ᴮ label κ x)) ⊓ (pair (label κ x) z ∈ᴮ R)
  have eq : b ≤ z =ᴮ label κ i := inf_le_left.trans inf_le_left
  by_cases h : i < x
  · have hf : b ≤ label κ x ∈ᴮ fiber K R (label κ i) := by
      rw [mem_fiber]
      exact le_inf (le_top.trans (check_mem (PSet.mk_mem_mk_of_lt x.toOrd.property)))
        (bv_rw'' eq (show b ≤ pair (label κ x) z ∈ᴮ R from inf_le_right) B_ext_pair_mem_right)
    exact hf.trans (le_iSup (fun t : Set.Iio x => coeff κ (fiber K R (label κ t.val)) x) ⟨i,h⟩)
  · have mem : b ≤ label κ i ∈ᴮ label κ x := subst_congr_mem_left' eq (inf_le_left.trans inf_le_right)
    exact (mem.trans_eq (checked_lt_of_mem κ i x h)).trans bot_le

include scalar normal in
theorem idealName_diagonalClosure : (⊤ : B) ≤ diagonalClosure K (idealName κ e μ) := by
  apply le_iInf
  intro R
  rw [← deduction,top_inf_eq]
  let b := ⨅ i : bSet B, _root_.imp (i ∈ᴮ K) (fiber K R i ∈ᴮ idealName κ e μ)
  apply (mem_ideal_iff κ e μ scalar).mpr
  refine ⟨?_,bot_unique ?_⟩
  · unfold diagonalUnion
    apply comprehend_subset
  have below := (OrderHomClass.mono μ (coeff_diagonal_le κ R)).trans (normal _)
  apply (inf_le_inf_left (e b) below).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  have member : (⊤ : B) ≤ label κ i ∈ᴮ K := check_mem (PSet.mk_mem_mk_of_lt i.toOrd.property)
  have hi : b ≤ fiber K R (label κ i) ∈ᴮ idealName κ e μ :=
    (le_inf (iInf_le _ (label κ i)) (le_top.trans member)).trans bv_imp_elim
  exact ((mem_ideal_iff κ e μ scalar).mp hi).2.le

private theorem labels_eq_bot {i j : W} (h : i ≠ j) :
    ((label κ i : bSet B) =ᴮ label κ j) = ⊥ :=
  check_bv_eq_bot_of_not_equiv (fun eq =>
    h (Ordinal.ToType.mk.symm.injective (Subtype.ext (PSet.eq_of_mk_equiv eq))))

include scalar initial in
/-- All singleton names have zero value, including mixed ordinal names. -/
theorem point_value (x : bSet B) : μ (fun i => (label κ i : bSet B) =ᴮ x) = ⊥ := by
  classical
  let w (i : W) := (label κ i : bSet B) =ᴮ x
  let atom (j i : W) : B := if j = i then ⊤ else ⊥
  have sep (i j : W) (hn : i ≠ j) : w i ⊓ w j = ⊥ := by
    exact bot_unique ((bv_trans (show w i ⊓ w j ≤ label κ i =ᴮ x from inf_le_left)
      (bv_symm (show w i ⊓ w j ≤ label κ j =ᴮ x from inf_le_right))).trans_eq (labels_eq_bot κ hn))
  have split : (fun i => ⨆ j, w j ⊓ atom j i) = w := by
    funext i
    apply le_antisymm
    · apply iSup_le
      intro j
      by_cases h : j = i
      · subst j; exact inf_le_left
      · simp [atom,h]
    · apply le_iSup_of_le i
      simp [atom]
  change μ w = ⊥
  rw [← split,value_mix e μ scalar w sep atom]
  apply iSup_eq_bot.mpr
  intro j
  have small : μ (atom j) = ⊥ := by
    apply bot_unique
    apply (OrderHomClass.mono μ (show atom j ≤ initialValue κ j from ?_)).trans_eq (initial j)
    intro i
    by_cases h : j = i
    · subst j; simp [atom,initialValue]
    · simp [atom,h]
  rw [small,inf_bot_eq]

include scalar initial normal in
theorem idealName_countableAbsorption (hk : Cardinal.aleph0 < κ) :
    (⊤ : B) ≤ countableAbsorption K (idealName κ e μ) := by
  apply le_iInf
  intro A
  rw [← deduction,top_inf_eq]
  let b := (A ⊆ᴮ K) ⊓ injects_into A omega
  obtain ⟨x,cover⟩ := Erdos1172BooleanUltrapower.exists_countable_member_cover A b inf_le_right
  apply (mem_ideal_iff κ e μ scalar).mpr
  refine ⟨inf_le_left,bot_unique ?_⟩
  rw [localized e μ scalar]
  let F (n : ULift.{u} ℕ) (i : W) := (label κ i : bSet B) =ᴮ x n
  apply (OrderHomClass.mono μ (show (fun i => b ⊓ coeff κ A i) ≤ (fun i => ⨆ n, F n i) from
    fun i => (cover _).trans (iSup_mono fun _ => inf_le_right))).trans
  rw [countable_union_value κ μ initial normal hk F]
  exact iSup_le fun n => (point_value κ e μ scalar initial (x n)).le

include scalar initial normal in
theorem idealName_countableClosure (hk : Cardinal.aleph0 < κ) :
    (⊤ : B) ≤ countableClosure (idealName κ e μ) := by
  apply le_iInf
  intro H
  rw [← deduction,top_inf_eq]
  let b := injects_into H omega ⊓ (H ⊆ᴮ idealName κ e μ)
  have small (y : bSet B) : b ⊓ (y ∈ᴮ H) ≤ y ∈ᴮ idealName κ e μ :=
    mem_of_mem_subset (inf_le_left.trans inf_le_right) inf_le_right
  obtain ⟨x,cover⟩ := Erdos1172BooleanUltrapower.exists_countable_member_cover H b inf_le_left
  let w (n : ULift.{u} ℕ) := b ⊓ (x n ∈ᴮ H)
  let F (n : ULift.{u} ℕ) (i : W) := w n ⊓ coeff κ (x n) i
  apply (mem_ideal_iff κ e μ scalar).mpr
  refine ⟨ErdosInitialSegments.union_subset_of_members_subset ?_,bot_unique ?_⟩
  · apply le_iInf
    intro z
    rw [← deduction]
    exact ((mem_ideal_iff κ e μ scalar).mp (small z)).1
  · rw [localized e μ scalar]
    have bound (i : W) : b ⊓ coeff κ (bv_union H) i ≤ ⨆ n, F n i := by
      have hu := (bv_union_spec_split H (label κ i)).mp (le_refl (coeff κ (bv_union H) i))
      apply (inf_le_inf_left b hu).trans
      rw [inf_iSup_eq]
      apply iSup_le
      intro z
      let p := b ⊓ ((z ∈ᴮ H) ⊓ (label κ i ∈ᴮ z))
      have hv : p ≤ ⨆ n, (x n ∈ᴮ H) ⊓ (z =ᴮ x n) :=
        (le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans (cover z)
      apply (le_inf (le_refl p) hv).trans
      rw [inf_iSup_eq]
      apply iSup_mono
      intro n
      exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
        (bv_rw'' (inf_le_right.trans inf_le_right) (inf_le_left.trans (inf_le_right.trans inf_le_right)) B_ext_mem_right)
    apply (OrderHomClass.mono μ bound).trans
    rw [countable_union_value κ μ initial normal hk F]
    apply iSup_le
    intro n
    change μ (fun i => w n ⊓ coeff κ (x n) i) ≤ ⊥
    rw [← localized e μ scalar]
    exact ((mem_ideal_iff κ e μ scalar).mp (small (x n))).2.le

end Erdos1172RelativeValuation
