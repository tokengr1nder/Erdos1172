/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationBoundedChecked
public import Erdos1172.Part4LevyPreparationCohenConditions
public import Erdos1172.Part4BoundedEmbeddingCriticalRank

@[expose] public section

/-! # Mixed Cohen conditions are fixed by the bounded preparation lift -/

set_option autoImplicit false
noncomputable section
open Filter bSet ErdosNameTransport ErdosCheckedIndicator Erdos1172GroundUltrapower Erdos1172BooleanUltrapower
open Erdos1172LevyCohen ErdosOmegaTwo ErdosPartialInjection
open scoped Flypitch
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]
variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
local notation "A" => FirstAlgebra κ
local notation "B" => FirstAlgebra θ
local notation "j" => boundedPreparedName U a hk hf hn ht
local notation "inc" => initialCollapseHom hk

include hκ in
theorem boundedPrepared_subset (X Y : bSet A) : (j X ⊆ᴮ j Y) = inc (X ⊆ᴮ Y) := by
  let φ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U A) B := collapseCompletionIso U a hk hf hn ht
  apply (map_subset φ _ _).symm.trans
  apply (congrArg (fun b => φ b) (boundedName_subset U a hk hf hn ht hκ (fun _ => X) (fun _ => Y)
    (Supported.const _) (Supported.const _)).symm).trans
  exact collapseCompletionIso_constant U a hk hf hn ht hκ.isRegular hκ.aleph0_lt _

include hκ in
theorem boundedPrepared_checked_fix_rank (S : PSet.{u}) (hs : S.rank < κ.ord) :
    (⊤ : B) ≤ j (check S) =ᴮ check S := by
  apply bv_trans (boundedPrepared_checked U a hk hf hn ht hκ S)
  apply check_bv_eq
  apply PSet.equiv_iff_eq.mpr
  exact (ZFSet.mk_out _).trans (boundedGroundEmbedding_fix_rank U κ θ a hκ (ZFSet.mk S) hs)

include hκ in
/-- This includes every mixed subset of a ground set of rank below κ, on
the exact Boolean value where the name is such a subset. -/
theorem boundedPrepared_fixed_rank_subset (S : PSet.{u}) (hs : S.rank < κ.ord) (X : bSet A) :
    inc (X ⊆ᴮ check S) ≤ j X =ᴮ mapNames inc X := by
  let d := inc (X ⊆ᴮ check S)
  have js := boundedPrepared_checked_fix_rank U a hk hf hn ht hκ S hs
  have child (k : S.Type) := boundedPrepared_checked_fix_rank U a hk hf hn ht hκ (S.Func k)
    ((PSet.rank_lt_of_mem (PSet.func_mem S k)).trans hs)
  have h₁ : d ≤ j X ⊆ᴮ check S :=
    bv_rw'' (le_top.trans js) (boundedPrepared_subset U a hk hf hn ht hκ X (check S)).ge B_ext_subset_right
  have h₂ : d ≤ mapNames inc X ⊆ᴮ check S := by
    simpa only [map_check] using (map_subset inc X (check S)).le
  have row (k : S.Type) : (check (S.Func k) ∈ᴮ j X) = (check (S.Func k) ∈ᴮ mapNames inc X) := by
    have he : (j (check (S.Func k)) ∈ᴮ j X) = (check (S.Func k) ∈ᴮ j X) := le_antisymm
      (subst_congr_mem_left' (le_top.trans (child k)) le_rfl)
      (subst_congr_mem_left' (bv_symm (le_top.trans (child k))) le_rfl)
    rw [← he,boundedPrepared_mem U a hk hf hn ht hκ, map_mem inc,map_check]
  have rep (Y : bSet B) (sub : d ≤ Y ⊆ᴮ check S) :
      d ≤ Y =ᴮ checkedIndicator S (fun k => check (S.Func k) ∈ᴮ Y) := by
    rw [checkedIndicator_membership_eq]
    exact eq_membership_indicator_of_subset sub
  have h := rep (j X) h₁
  simp_rw [row] at h
  exact bv_trans h (bv_symm (rep _ h₂))

private theorem binary_graph_rank (κ : Cardinal.{u}) (hκ : κ.IsInaccessible)
    (β : Ordinal.{u}) (hβ : β < κ.ord) :
    (PSet.pSet_prod (PSet.ordinalMk β) (PSet.ofNat 2)).rank < κ.ord := by
  let S := PSet.pSet_prod (PSet.ordinalMk β) (PSet.ofNat 2)
  have small : Cardinal.mk S.Type < κ := by
    rw [show S.Type = ((PSet.ordinalMk β).Type × (PSet.ofNat 2).Type) from rfl,Cardinal.mk_prod,
      Cardinal.lift_id,Cardinal.lift_id,PSet.ordinalMk_type,Cardinal.mk_toType]
    exact Cardinal.mul_lt_of_lt hκ.aleph0_lt.le (Cardinal.lt_ord.mp hβ)
      ((show Cardinal.mk (Option (Option PEmpty.{u+1})) < Cardinal.aleph0 from Cardinal.mk_lt_aleph0).trans hκ.aleph0_lt)
  have natCode (m : ℕ) : ZFSet.mk (PSet.ofNat m) = (m : Ordinal.{u}).toZFSet := by
    induction m with
    | zero => exact Ordinal.toZFSet_zero.symm
    | succ n ih => rw [Nat.cast_succ,Ordinal.toZFSet_add_one,← ih]; rfl
  have htwo : (PSet.ofNat 2 : PSet.{u}).rank < κ.ord := by
    rw [← ZFSet.rank_mk,natCode,Ordinal.rank_toZFSet]
    exact (Ordinal.natCast_lt_omega0 2).trans (by simpa only [← Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hκ.aleph0_lt)
  have ho : (PSet.ordinalMk β).rank < κ.ord := by
    change β.toZFSet.rank < κ.ord
    rwa [Ordinal.rank_toZFSet]
  let lim := Cardinal.isSuccLimit_ord hκ.aleph0_lt.le
  change (⨆ k : S.Type, (S.Func k).rank + 1) < κ.ord
  apply Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hκ.isRegular.cof_ord])
  rintro ⟨i,k⟩
  have hi := (PSet.rank_lt_of_mem (PSet.func_mem (PSet.ordinalMk β) i)).trans ho
  have hq := (PSet.rank_lt_of_mem (PSet.func_mem (PSet.ofNat 2) k)).trans htwo
  change (PSet.pSet_pair _ _).rank < _
  rw [PSet.pSet_pair,PSet.rank_pair,PSet.rank_singleton,PSet.rank_pair]
  exact max_lt (lim.succ_lt (lim.succ_lt hi)) (lim.succ_lt (max_lt (lim.succ_lt hi) (lim.succ_lt hq)))

include hκ in
theorem boundedPrepared_bounded_binary_graph (β : Ordinal.{u}) (hβ : β < κ.ord) (X : bSet A) :
    inc (X ⊆ᴮ prod (check (PSet.ordinalMk β)) two) ≤ j X =ᴮ mapNames inc X := by
  let S := PSet.pSet_prod (PSet.ordinalMk β) (PSet.ofNat 2)
  have sub : (X ⊆ᴮ prod (check (PSet.ordinalMk β)) two) ≤ X ⊆ᴮ check S :=
    subset_trans' le_rfl (subset_of_eq (bv_symm (check_pset_prod (x := PSet.ordinalMk β) (y := PSet.ofNat 2))))
  exact (OrderHomClass.mono inc sub).trans
    (boundedPrepared_fixed_rank_subset U a hk hf hn ht hκ S (binary_graph_rank κ hκ β hβ) X)

include hκ in
theorem boundedPrepared_cohen_condition (q : bSet A) :
    inc (ErdosCohen.condition omegaOne q) ≤ j q =ᴮ mapNames inc q := by
  let v := ErdosCohen.condition (omegaOne : bSet A) q
  let dom := graphDomain (omegaOne : bSet A) two q
  let bound (i : κ.ord.ToType) := dom ⊆ᴮ check (PSet.ordinalMk i.toOrd.val)
  have cov : v ≤ ⨆ i, bound i := firstStage_condition_domain_bound_cover κ hκ.isRegular hκ.aleph0_lt le_rfl
  have localize : v ≤ ⨆ i, v ⊓ bound i := (le_inf le_rfl cov).trans_eq (inf_iSup_eq _ _)
  apply (OrderHomClass.mono inc localize).trans
  rw [_root_.map_iSup]
  apply iSup_le
  intro i
  have sub : v ⊓ bound i ≤ q ⊆ᴮ prod (check (PSet.ordinalMk i.toOrd.val)) two :=
    subset_trans' (subset_prod_of_is_function (ErdosCohen.condition_function inf_le_left)) (prod_domain_mono inf_le_right)
  exact (OrderHomClass.mono inc sub).trans (boundedPrepared_bounded_binary_graph U a hk hf hn ht hκ _ i.toOrd.property q)

end Erdos1172LevyCollapse.Preparation
