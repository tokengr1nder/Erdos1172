/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4AnonymousInternalLevyReasonable
public import Erdos1172.Part4LevyAnonymousCountableSubsetReading

@[expose] public section

/-! # Small-support dense conditions, stage master graphs, and stage-local tests

For `R := AmbientInternalLevy κ θ` and each stage `α < θ.ord`:
1. `SmallLevyCondition κ α` (`#(tripleSupport α s) < κ`) is dense in `InternalLevyCondition κ α`
   via `checked_sequence_small_ground_capture_cover`.
2. `stageMasterGraph` is an explicit `< θ`-supported functional graph in `bSet R` built from
   `ambientLevyStageHom` applied to ground entry cones `levyEntry α idx`, satisfying exact
   coordinate-restriction compatibility `restrictLevy ... (stageMasterGraph α') =ᴮ stageMasterGraph α`
   and disjoint-coordinate chain amalgamation (`amalgamateChainWithMaster`).
3. `levyTruthOpen`, `levyRowRelation`, and `levyJoinTest` give stage-local open truth sets,
   row relations, and regressive normality tests inside `internalLevyPoset κ α`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Flypitch Ordinal
open Cardinal Filter bSet Lattice ErdosOmegaTwo ErdosNameTransport ErdosPartialInjection
open ErdosIdeal ErdosSmallPoolOperations ErdosRelationGraph
open Erdos1172LevyCohen Erdos1172CompleteSubalgebra Erdos1172BooleanNameIteration
open Erdos1172PosetCompletion Erdos1172PositiveBoolean Erdos1172RelativeValuation
open Erdos1172GroundUltrapower Erdos1172BooleanUltrapower Erdos1172LevyCollapse
open Erdos1172LevyCollapse.Matching bSet.ErdosShioyaInternal
open Erdos1172Shioya.UltrapowerStage (ordinalImage ordinalImage_code)
open Erdos1172Shioya (StringName)

universe u

namespace Erdos1172AnonymousInternalLevy

theorem completeHom_inf {X Y : Type u} [CompleteLattice X] [CompleteLattice Y]
    (f : CompleteLatticeHom X Y) (x y : X) : f (x ⊓ y) = f x ⊓ f y := by
  rw [← sInf_pair, map_sInf, Set.image_pair, sInf_pair]

theorem completeHom_sup {X Y : Type u} [CompleteLattice X] [CompleteLattice Y]
    (f : CompleteLatticeHom X Y) (x y : X) : f (x ⊔ y) = f x ⊔ f y := by
  rw [← sSup_pair, map_sSup, Set.image_pair, sSup_pair]

theorem completeHom_compl {X Y : Type u} [CompleteBooleanAlgebra X] [CompleteBooleanAlgebra Y]
    (f : CompleteLatticeHom X Y) (x : X) : f xᶜ = (f x)ᶜ :=
  _root_.map_compl' f x

section SmallSupportAndEntries
variable {κ : Cardinal.{u}}

/-- Stage-`α` conditions whose nonzero ground-triple support has cardinality strictly `< κ`. -/
def SmallLevyCondition (κ : Cardinal.{u}) (α : Ordinal.{u}) : Type u :=
  {s : InternalLevyCondition κ α // #(tripleSupport α s) < κ}

private theorem eq_image_of_surjection' {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {P X C f : bSet B} {Γ : B} (hX : Γ ≤ X ⊆ᴮ C)
    (hf : Γ ≤ is_function P X f) (hs : Γ ≤ is_surj P X f) :
    Γ ≤ X =ᴮ image P C f := by
  apply mem_ext
  · refine le_iInf fun z => deduction.mp ?_
    exact mem_image_iff.mpr ⟨mem_of_mem_subset (inf_le_left.trans hX) inf_le_right,
      (le_inf (inf_le_left.trans (hs.trans (iInf_le _ z))) inf_le_right).trans bv_imp_elim⟩
  · refine le_iInf fun z => deduction.mp ?_
    have h := (mem_image_iff.mp (show Γ ⊓ (z ∈ᴮ image P C f) ≤ z ∈ᴮ image P C f from inf_le_right)).2
    obtain ⟨w, hw⟩ := exists_convert h (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_right_of_prod_mem (mem_of_mem_subset
      (inf_le_left.trans (subset_prod_of_is_function hf)) (hw.trans inf_le_right))

/-- Every condition in `InternalLevyCondition κ α` refines to one with `#(tripleSupport α s) < κ`. -/
theorem exists_small_tripleSupport_refinement (hκ : κ.IsInaccessible) (α : Ordinal.{u})
    (p : InternalLevyCondition κ α) :
    ∃ s : SmallLevyCondition κ α, s.val ≤ p := by
  classical
  let A := anonymousAlgebra κ
  let P_α := levyTriplePSet κ α
  have hp_sub : p.value ≤ name p ⊆ᴮ check P_α :=
    subset_trans' (countableCollapse_mem.mp (mem_internalLevyCollapse.mp (name_mem p)).1).1
      (bSet.subset_of_eq (le_top.trans (prod_ordinalCarrier_eq_check_levyTriplePSet α)))
  have hp_cnt : p.value ≤ injects_into (name p) omega :=
    (countableCollapse_mem.mp (mem_internalLevyCollapse.mp (name_mem p)).1).2.2
  by_cases hemp : p.value ⊓ (name p =ᴮ (∅ : bSet A)) ≠ ⊥
  · obtain ⟨s, hsv, hseq⟩ := exists_canonical_refinement hemp
      (empty_mem_internalLevyCollapse (ordinalCarrier κ.ord) (ordinalCarrier α))
    have hs_p : s ≤ p :=
      ⟨hsv.trans inf_le_left,
       bSet.subset_of_eq (bv_trans ((hsv.trans inf_le_right)) hseq)⟩
    have hts_empty : tripleSupport α s = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨idx, w⟩ ⟨hw_ne, hw_eq⟩
      apply hw_ne
      apply le_bot_iff.mp
      rw [hw_eq]
      have hm_emp : s.value ⊓ (check (P_α.Func idx) ∈ᴮ name s) ≤
          check (P_α.Func idx) ∈ᴮ (∅ : bSet A) :=
        mem_congr bv_refl (bv_symm (inf_le_left.trans hseq)) inf_le_right
      exact bot_of_mem_empty hm_emp
    refine ⟨⟨s, ?_⟩, hs_p⟩
    have : IsEmpty (tripleSupport α s) := Set.isEmpty_coe_sort.mpr hts_empty
    rw [Cardinal.mk_eq_zero]
    exact Cardinal.aleph0_pos.trans hκ.aleph0_lt
  · have hnonemp : p.value ≤ (name p =ᴮ (∅ : bSet A))ᶜ :=
      le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr (not_ne_iff.mp hemp))
    have honto : p.value ≤ surjects_onto omega (name p) :=
      surjects_onto_of_injects_into' hp_cnt (exists_mem_of_nonempty (name p) hnonemp)
    have honto_pos : p.value ⊓ (⨆ f : bSet A, is_func' omega (name p) f ⊓ is_surj omega (name p) f) ≠ ⊥ := by
      erw [inf_of_le honto]
      exact p.nonzero
    obtain ⟨f, hf_ne⟩ := exists_mem_iSup_inf_ne_bot honto_pos
    let b := p.value ⊓ (is_func' omega (name p) f ⊓ is_surj omega (name p) f)
    have hweak : b ≤ is_func' omega (name p) f := inf_le_right.trans inf_le_left
    let g_fn := function_of_func' hweak
    have hfun : b ≤ is_function omega (name p) g_fn :=
      function_of_func'_is_function hweak
    have hrange : b ≤ name p =ᴮ image omega (check P_α) g_fn :=
      eq_image_of_surjection' (inf_le_left.trans hp_sub) hfun
        (function_of_func'_surj_of_surj hweak (inf_le_right.trans inf_le_right))
    have hfun_P : b ≤ is_function omega (check P_α) g_fn :=
      ErdosIndependentHomogeneous.is_function_codomain_mono (inf_le_left.trans hp_sub) hfun
    let inc := inclusion A
    have hinc_fun : inc b ≤ is_function omega (check P_α) (mapNames inc g_fn) := by
      simpa only [omega, map_check] using map_is_function_of inc hfun_P
    have hcap := checked_sequence_small_ground_capture_cover κ hκ.isRegular hκ.aleph0_lt
      P_α (fun _ _ hne => levyTriplePSet_inj α hne) hinc_fun
    have hinc_ne : inc b ≠ ⊥ :=
      fun h0 => hf_ne (inclusion_injective A (h0.trans (BotHomClass.map_bot inc).symm))
    obtain ⟨A₀, hA₀_ne⟩ := exists_mem_iSup_inf_ne_bot (c := inc b)
      (by erw [inf_of_le hcap]; exact hinc_ne)
    obtain ⟨g, hg_ne⟩ := exists_mem_iSup_inf_ne_bot hA₀_ne
    let c₀ := inc b ⊓ (Erdos1172LevyCohen.firstStageHom κ (is_function omega (check A₀.val) g) ⊓
      (mapNames inc g_fn =ᴮ mapNames (Erdos1172LevyCohen.firstStageHom κ) g))
    have hc₀_sub : c₀ ≤ inc (b ⊓ (name p ⊆ᴮ check A₀.val)) := by
      rw [completeHom_inf inc, map_subset, map_check]
      refine le_inf inf_le_left ?_
      have heq₁ : c₀ ≤ mapNames inc (name p) =ᴮ
          image omega (check P_α) (mapNames inc g_fn) := by
        have hm := OrderHomClass.mono inc hrange
        rw [map_bv_eq, map_bounded_image, show mapNames inc omega = omega from map_check _ _,
          map_check] at hm
        exact inf_le_left.trans hm
      have heq₂ : c₀ ≤ image omega (check P_α) (mapNames inc g_fn) =ᴮ
          image omega (check P_α) (mapNames (Erdos1172LevyCohen.firstStageHom κ) g) :=
        B_congr_image_right (inf_le_right.trans inf_le_right)
      have hg_fn : c₀ ≤ is_function omega (check A₀.val)
          (mapNames (Erdos1172LevyCohen.firstStageHom κ) g) := by
        have hm := map_is_function_of (Erdos1172LevyCohen.firstStageHom κ)
          (le_rfl : is_function omega (check A₀.val) g ≤ _)
        simp only [omega, map_check] at hm
        exact (inf_le_right.trans inf_le_left).trans hm
      have himg_sub : c₀ ≤ image omega (check P_α)
          (mapNames (Erdos1172LevyCohen.firstStageHom κ) g) ⊆ᴮ check A₀.val := by
        let img_g : bSet (Erdos1172LevyCohen.Algebra κ) :=
          image omega (check P_α) (mapNames (Erdos1172LevyCohen.firstStageHom κ) g)
        rw [subset_unfold']
        refine le_iInf fun z => deduction.mp ?_
        have himg : c₀ ⊓ (z ∈ᴮ img_g) ≤
            ⨆ w, w ∈ᴮ omega ⊓ pair w z ∈ᴮ mapNames (Erdos1172LevyCohen.firstStageHom κ) g :=
          (mem_image_iff.mp (inf_le_right : c₀ ⊓ (z ∈ᴮ img_g) ≤ z ∈ᴮ img_g)).2
        obtain ⟨w, hw⟩ := exists_convert himg (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
        exact mem_right_of_prod_mem (mem_of_mem_subset
          (inf_le_left.trans (subset_prod_of_is_function hg_fn)) (hw.trans inf_le_right))
      exact subset_trans' (bSet.subset_of_eq (bv_trans heq₁ heq₂)) himg_sub
    have hb'_ne : b ⊓ (name p ⊆ᴮ check A₀.val) ≠ ⊥ :=
      fun h0 => hg_ne (le_bot_iff.mp (hc₀_sub.trans_eq ((congrArg inc h0).trans (BotHomClass.map_bot inc))))
    let b' := (b ⊓ (name p ⊆ᴮ check A₀.val))
    let s := shrink p b' hb'_ne (inf_le_left.trans inf_le_left)
    have hs_p : s ≤ p := shrink_le p b' hb'_ne (inf_le_left.trans inf_le_left)
    have hs_sub : s.value ≤ name s ⊆ᴮ check A₀.val := inf_le_right
    have hts_lt : #(tripleSupport α s) < κ := by
      have hex_k (sw : tripleSupport α s) :
          ∃ k : A₀.val.Type, PSet.Equiv (P_α.Func sw.val.1) (A₀.val.Func k) := by
        have hw_ne := sw.property.1
        have hw_eq := sw.property.2
        have hle : sw.val.2 ≤ check (P_α.Func sw.val.1) ∈ᴮ check A₀.val := by
          rw [hw_eq]
          exact mem_of_mem_subset (inf_le_left.trans hs_sub) inf_le_right
        rw [mem_unfold] at hle
        obtain ⟨k, hk_ne⟩ := exists_mem_iSup_inf_ne_bot (c := sw.val.2)
          (by erw [inf_of_le hle]; exact hw_ne)
        by_contra hnone
        have hbot : (check (P_α.Func sw.val.1) =ᴮ (check (A₀.val.Func (check_cast k)) : bSet A)) = ⊥ :=
          check_bv_eq_bot_of_not_equiv (fun he => hnone ⟨check_cast k, he⟩)
        rw [check_func, check_bval_top, top_inf_eq, hbot, inf_bot_eq] at hk_ne
        exact hk_ne rfl
      choose fk hfk using hex_k
      have hfk_inj : Function.Injective fk := by
        intro sw₁ sw₂ heq
        have heqv : PSet.Equiv (P_α.Func sw₁.val.1) (P_α.Func sw₂.val.1) :=
          PSet.Equiv.trans (hfk sw₁) (heq ▸ PSet.Equiv.symm (hfk sw₂))
        have hidx : sw₁.val.1 = sw₂.val.1 := by
          by_contra hne
          exact levyTriplePSet_inj α hne heqv
        apply Subtype.ext
        apply Prod.ext hidx
        rw [sw₁.property.2, sw₂.property.2, hidx]
      exact (Cardinal.mk_le_of_injective hfk_inj).trans_lt A₀.property.1
    exact ⟨⟨s, hts_lt⟩, hs_p⟩

theorem smallLevyCondition_iSup_eq (hκ : κ.IsInaccessible) (α : Ordinal.{u})
    (b : InternalLevyStage κ α) :
    (⨆ s : {s : SmallLevyCondition κ α // condition s.val ≤ b}, condition s.val.val) = b := by
  apply le_antisymm (iSup_le fun s => s.property)
  apply le_of_dense_conditions_le
    (Set.range (fun s : SmallLevyCondition κ α => s.val))
    (fun p => let ⟨s, hs⟩ := exists_small_tripleSupport_refinement hκ α p; ⟨s.val, ⟨s, rfl⟩, hs⟩)
  rintro ⟨_, ⟨s, rfl⟩⟩ hs
  exact le_iSup (fun t : {t : SmallLevyCondition κ α // condition t.val ≤ b} => condition t.val.val) ⟨s, hs⟩

/-- Boolean cone in `InternalLevyStage κ α` asserting that the ground triple `idx` belongs to
the generic collapse function. -/
def levyEntry (α : Ordinal.{u}) (idx : (levyTriplePSet κ α).Type) : InternalLevyStage κ α :=
  ⨆ p : {p : InternalLevyCondition κ α //
      p.value ≤ check ((levyTriplePSet κ α).Func idx) ∈ᴮ name p},
    condition p.val

theorem condition_inf_sourceHom_le_levyEntry (α : Ordinal.{u})
    (s : InternalLevyCondition κ α) (idx : (levyTriplePSet κ α).Type) :
    condition s ⊓ sourceHom (internalLevyPoset κ α)
      (s.value ⊓ (check ((levyTriplePSet κ α).Func idx) ∈ᴮ name s)) ≤
      levyEntry α idx := by
  let w := s.value ⊓ (check ((levyTriplePSet κ α).Func idx) ∈ᴮ name s)
  change condition s ⊓ sourceHom (internalLevyPoset κ α) w ≤ levyEntry α idx
  by_cases hw : w = ⊥
  · rw [hw, BotHomClass.map_bot]
    erw [inf_bot_eq]
    exact bot_le
  · let r := shrink s w hw inf_le_left
    have hr_cone : condition s ⊓ sourceHom (internalLevyPoset κ α) w ≤ condition r := by
      intro t ht
      change t ∈ (condition s).val ∧ t ∈ (sourceHom _ w).val at ht
      have htw := (condition_le_source _ t w).mp (condition_le_iff.mpr ht.2)
      apply (mem_condition_iff r t).mpr
      intro v hvt
      obtain ⟨z, hzv, hzs⟩ := (mem_condition_iff s t).mp ht.1 v hvt
      exact ⟨z, hzv, (hzv.trans hvt).1.trans htw, hzs.2⟩
    exact hr_cone.trans (le_iSup (fun p : {p : InternalLevyCondition κ α //
      p.value ≤ check ((levyTriplePSet κ α).Func idx) ∈ᴮ name p} => condition p.val) ⟨r, inf_le_right⟩)

theorem levyEntry_disjoint (α : Ordinal.{u})
    {idx₁ idx₂ : (levyTriplePSet κ α).Type}
    (hdom : idx₁.1 = idx₂.1) (hne : idx₁.2 ≠ idx₂.2) :
    levyEntry α idx₁ ⊓ levyEntry α idx₂ = ⊥ := by
  unfold levyEntry
  erw [iSup_inf_eq]
  apply le_antisymm ?_ bot_le
  refine iSup_le fun ⟨q₁, hq₁⟩ => ?_
  erw [inf_iSup_eq]
  refine iSup_le fun ⟨q₂, hq₂⟩ => ?_
  by_contra hpos
  obtain ⟨r, hr₁, hr₂⟩ := (condition_inf_ne_bot_iff q₁ q₂).mp (fun h0 => hpos h0.le)
  have hm₁ : r.value ≤ pair
      (pair (check ((PSet.ordinalMk α).Func idx₁.1.1))
        (check ((PSet.ordinalMk κ.ord).Func idx₁.1.2)))
      (check ((PSet.ordinalMk α).Func idx₁.2)) ∈ᴮ name r :=
    mem_congr (check_levyTriplePSet_func α idx₁) bv_refl (mem_of_mem_subset hr₁.2 (hr₁.1.trans hq₁))
  have hm₂ : r.value ≤ pair
      (pair (check ((PSet.ordinalMk α).Func idx₁.1.1))
        (check ((PSet.ordinalMk κ.ord).Func idx₁.1.2)))
      (check ((PSet.ordinalMk α).Func idx₂.2)) ∈ᴮ name r := by
    have h0 := mem_congr (check_levyTriplePSet_func α idx₂) bv_refl
      (mem_of_mem_subset hr₂.2 (hr₂.1.trans hq₂))
    rwa [← hdom] at h0
  have hr_fn : r.value ≤ is_func (name r) :=
    (countableCollapse_mem.mp (mem_internalLevyCollapse.mp (name_mem r)).1).2.1
  have hy_eq : r.value ≤ check ((PSet.ordinalMk α).Func idx₁.2) =ᴮ
      check ((PSet.ordinalMk α).Func idx₂.2) :=
    eq_of_is_func_of_eq hr_fn bv_refl hm₁ hm₂
  rw [check_bv_eq_bot_of_not_equiv (PSet.ordinalMk_inj α _ _ hne)] at hy_eq
  exact r.nonzero (le_bot_iff.mp hy_eq)

/-- Canonical ordinal extraction from `i : (PSet.ordinalMk α).Type`. -/
def ordOfPSetIdx {α : Ordinal.{u}} (i : (PSet.ordinalMk α).Type) : Ordinal.{u} :=
  (PSet.mem_ordinalMk_iff.mp (PSet.func_mem (PSet.ordinalMk α) i)).choose

theorem ordOfPSetIdx_lt {α : Ordinal.{u}} (i : (PSet.ordinalMk α).Type) :
    ordOfPSetIdx i < α :=
  (PSet.mem_ordinalMk_iff.mp (PSet.func_mem (PSet.ordinalMk α) i)).choose_spec.1

theorem ordOfPSetIdx_equiv {α : Ordinal.{u}} (i : (PSet.ordinalMk α).Type) :
    PSet.Equiv ((PSet.ordinalMk α).Func i) (PSet.ordinalMk (ordOfPSetIdx i)) :=
  (PSet.mem_ordinalMk_iff.mp (PSet.func_mem (PSet.ordinalMk α) i)).choose_spec.2

theorem ordOfPSetIdx_inj {α : Ordinal.{u}} :
    Function.Injective (ordOfPSetIdx (α := α)) := by
  intro i₁ i₂ heq
  by_contra hne
  exact PSet.ordinalMk_inj α i₁ i₂ hne
    (PSet.Equiv.trans (ordOfPSetIdx_equiv i₁) (heq ▸ PSet.Equiv.symm (ordOfPSetIdx_equiv i₂)))

/-- Inclusion of `(PSet.ordinalMk α).Type` into `(PSet.ordinalMk α').Type` for `α ≤ α'`. -/
def includeOrdIdx {α α' : Ordinal.{u}} (h : α ≤ α') (i : (PSet.ordinalMk α).Type) :
    (PSet.ordinalMk α').Type :=
  (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt ((ordOfPSetIdx_lt i).trans_le h))).choose

theorem ordOfPSetIdx_includeOrdIdx {α α' : Ordinal.{u}} (h : α ≤ α')
    (i : (PSet.ordinalMk α).Type) :
    ordOfPSetIdx (includeOrdIdx h i) = ordOfPSetIdx i := by
  have heqv : PSet.Equiv ((PSet.ordinalMk α').Func (includeOrdIdx h i))
      (PSet.ordinalMk (ordOfPSetIdx i)) :=
    PSet.Equiv.symm (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt ((ordOfPSetIdx_lt i).trans_le h))).choose_spec
  have heqv₂ := ordOfPSetIdx_equiv (includeOrdIdx h i)
  exact Ordinal.toZFSet_injective (ZFSet.sound (PSet.Equiv.trans (PSet.Equiv.symm heqv₂) heqv))

theorem includeOrdIdx_equiv {α α' : Ordinal.{u}} (h : α ≤ α') (i : (PSet.ordinalMk α).Type) :
    PSet.Equiv ((PSet.ordinalMk α').Func (includeOrdIdx h i)) ((PSet.ordinalMk α).Func i) :=
  PSet.Equiv.trans (ordOfPSetIdx_equiv (includeOrdIdx h i))
    ((ordOfPSetIdx_includeOrdIdx h i) ▸ PSet.Equiv.symm (ordOfPSetIdx_equiv i))

/-- Inclusion of ground triple indices along `h : α ≤ α'`. -/
def includeTripleIdx {α α' : Ordinal.{u}} (h : α ≤ α') (idx : (levyTriplePSet κ α).Type) :
    (levyTriplePSet κ α').Type :=
  ((includeOrdIdx h idx.1.1, idx.1.2), includeOrdIdx h idx.2)

theorem includeTripleIdx_check_eq {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {α α' : Ordinal.{u}} (h : α ≤ α') (idx : (levyTriplePSet κ α).Type) {Γ : B} :
    Γ ≤ check ((levyTriplePSet κ α').Func (includeTripleIdx h idx)) =ᴮ
      check ((levyTriplePSet κ α).Func idx) := by
  refine bv_trans (check_levyTriplePSet_func α' (includeTripleIdx h idx)) ?_
  refine bv_trans ?_ (bv_symm (check_levyTriplePSet_func α idx))
  exact pair_congr (pair_congr (check_bv_eq (includeOrdIdx_equiv h idx.1.1)) bv_refl)
    (check_bv_eq (includeOrdIdx_equiv h idx.2))

theorem stageStepHom_levyEntry {α α' : Ordinal.{u}} (h : α ≤ α')
    (idx : (levyTriplePSet κ α).Type)
    (hvalid : ordOfPSetIdx idx.2 < ordOfPSetIdx idx.1.1) :
    stageStepHom (κ := κ) h (levyEntry α idx) = levyEntry α' (includeTripleIdx h idx) := by
  apply le_antisymm
  · rw [levyEntry, _root_.map_iSup]
    refine iSup_le fun ⟨p, hp⟩ => ?_
    rw [stageStepHom_condition]
    refine iSup_le fun ⟨q, hqv, hqsub⟩ => ?_
    have hq_mem : q.value ≤ check ((levyTriplePSet κ α').Func (includeTripleIdx h idx)) ∈ᴮ name q :=
      mem_congr (bv_symm (includeTripleIdx_check_eq h idx)) bv_refl
        (mem_of_mem_subset hqsub (hqv.trans hp))
    exact le_iSup (fun r : {r : InternalLevyCondition κ α' //
      r.value ≤ check ((levyTriplePSet κ α').Func (includeTripleIdx h idx)) ∈ᴮ name r} =>
        condition r.val) ⟨q, hq_mem⟩
  · refine iSup_le fun ⟨q, hq⟩ => ?_
    rw [condition_le_stageStepHom_iff]
    refine iSup_le fun ⟨p, hpv, hpsub⟩ => ?_
    have hq_α : q.value ≤ check ((levyTriplePSet κ α).Func idx) ∈ᴮ name q :=
      mem_congr (includeTripleIdx_check_eq h idx) bv_refl hq
    have hbd : q.value ≤ levyBoundPred (ordinalCarrier κ.ord) (ordinalCarrier α)
        (check ((levyTriplePSet κ α).Func idx)) := by
      change q.value ≤ ⨆ ξ : bSet (anonymousAlgebra κ), (ξ ∈ᴮ ordinalCarrier α) ⊓
        ⨆ η : bSet (anonymousAlgebra κ), (η ∈ᴮ ordinalCarrier κ.ord) ⊓
          ⨆ y : bSet (anonymousAlgebra κ), (y ∈ᴮ ξ) ⊓
            (check ((levyTriplePSet κ α).Func idx) =ᴮ pair (pair ξ η) y)
      have hy_ξ : (⊤ : anonymousAlgebra κ) ≤ check ((PSet.ordinalMk α).Func idx.2) ∈ᴮ
          check ((PSet.ordinalMk α).Func idx.1.1) :=
        mem_congr (bv_symm (check_bv_eq (ordOfPSetIdx_equiv idx.2)))
          (bv_symm (check_bv_eq (ordOfPSetIdx_equiv idx.1.1)))
          (check_mem (PSet.mk_mem_mk_of_lt hvalid))
      exact le_iSup_of_le (check ((PSet.ordinalMk α).Func idx.1.1))
        (le_inf (check_mem (PSet.func_mem _ idx.1.1))
          (le_iSup_of_le (check ((PSet.ordinalMk κ.ord).Func idx.1.2))
            (le_inf (check_mem (PSet.func_mem _ idx.1.2))
              (le_iSup_of_le (check ((PSet.ordinalMk α).Func idx.2))
                (le_inf (le_top.trans hy_ξ) (check_levyTriplePSet_func α idx))))))
    have hp_mem : p.value ≤ check ((levyTriplePSet κ α).Func idx) ∈ᴮ name p :=
      mem_of_mem_subset hpsub
        (mem_restrictLevy_iff.mpr ⟨hpv.trans hq_α, hpv.trans hbd⟩)
    exact le_iSup (fun r : {r : InternalLevyCondition κ α //
      r.value ≤ check ((levyTriplePSet κ α).Func idx) ∈ᴮ name r} => condition r.val) ⟨p, hp_mem⟩

end SmallSupportAndEntries

/-- Ground valid triples of `levyTriplePSet κ α` (`y < ξ`). -/
def GroundValidTriple (κ : Cardinal.{u}) (α : Ordinal.{u}) : Type u :=
  {idx : (levyTriplePSet κ α).Type // ordOfPSetIdx idx.2 < ordOfPSetIdx idx.1.1}

section StageMasterGraphs
variable {I : Type u} {κ θ : Cardinal.{u}}
variable (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]

/-- Ground `PSet` of lifted triples `((ξ, η), y)` at stage `α`:
`ξ, y < ordinalImage U a α` and `η < θ.ord`. -/
abbrev liftedTriplePSet (θ : Cardinal.{u}) (α : Ordinal.{u}) : PSet.{u} :=
  PSet.pSet_prod
    (PSet.pSet_prod (PSet.ordinalMk (ordinalImage U a α)) (PSet.ordinalMk θ.ord))
    (PSet.ordinalMk (ordinalImage U a α))

theorem liftedTriplePSet_inj (θ : Cardinal.{u}) (α : Ordinal.{u})
    {k₁ k₂ : (liftedTriplePSet U a θ α).Type} (hne : k₁ ≠ k₂) :
    ¬PSet.Equiv ((liftedTriplePSet U a θ α).Func k₁) ((liftedTriplePSet U a θ α).Func k₂) := by
  intro heqv
  rcases k₁ with ⟨⟨ξ₁, η₁⟩, y₁⟩
  rcases k₂ with ⟨⟨ξ₂, η₂⟩, y₂⟩
  obtain ⟨hp, hy⟩ := PSet.equiv_iff_eq_pSet_pair.mpr heqv
  obtain ⟨hξ, hη⟩ := PSet.equiv_iff_eq_pSet_pair.mpr hp
  have eq_ξ : ξ₁ = ξ₂ := by
    by_contra h1
    exact PSet.ordinalMk_inj _ _ _ h1 hξ
  have eq_η : η₁ = η₂ := by
    by_contra h1
    exact PSet.ordinalMk_inj _ _ _ h1 hη
  have eq_y : y₁ = y₂ := by
    by_contra h1
    exact PSet.ordinalMk_inj _ _ _ h1 hy
  exact hne (Prod.ext (Prod.ext eq_ξ eq_η) eq_y)

theorem check_liftedTriplePSet_func {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (θ : Cardinal.{u}) (α : Ordinal.{u}) (idx : (liftedTriplePSet U a θ α).Type) {Γ : B} :
    Γ ≤ check ((liftedTriplePSet U a θ α).Func idx) =ᴮ
      pair (pair (check ((PSet.ordinalMk (ordinalImage U a α)).Func idx.1.1))
        (check ((PSet.ordinalMk θ.ord).Func idx.1.2)))
        (check ((PSet.ordinalMk (ordinalImage U a α)).Func idx.2)) :=
  bv_trans check_pset_pair (pair_congr check_pset_pair bv_refl)

/-- Lifted triples `((ξ, η), y)` satisfying the Lévy bound `y < ξ`. -/
def ValidLiftedTriple (θ : Cardinal.{u}) (α : Ordinal.{u}) : Type u :=
  {idx : (liftedTriplePSet U a θ α).Type // ordOfPSetIdx idx.2 < ordOfPSetIdx idx.1.1}

/-- `< θ`-supported functional graph on `ValidLiftedTriple U a θ α` over `B`. -/
structure SmallGroundLevyGraph (θ : Cardinal.{u}) (α : Ordinal.{u})
    (B : Type u) [NontrivialCompleteBooleanAlgebra B] : Type (u + 1) where
  Idx : Type u
  card_lt : #Idx < θ
  triple : Idx → ValidLiftedTriple U a θ α
  weight : Idx → B
  func : (⊤ : B) ≤ is_func (.mk Idx (fun k => check ((liftedTriplePSet U a θ α).Func (triple k).val)) weight)

/-- Underlying `bSet B` of a `SmallGroundLevyGraph`. -/
def SmallGroundLevyGraph.toBSet {θ : Cardinal.{u}} {α : Ordinal.{u}}
    {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (G : SmallGroundLevyGraph U a θ α B) : bSet B :=
  .mk G.Idx (fun k => check ((liftedTriplePSet U a θ α).Func (G.triple k).val)) G.weight

private theorem is_func_liftedTriple_graph_of_cases {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {α : Ordinal.{u}} {J : Type u}
    (tr : J → ValidLiftedTriple U a θ α) (wt : J → B)
    (hcases : ∀ j₁ j₂ : J,
      (tr j₁).val.1.1 ≠ (tr j₂).val.1.1 ∨
      (tr j₁).val.1.2 ≠ (tr j₂).val.1.2 ∨
      j₁ = j₂ ∨
      wt j₁ ⊓ wt j₂ = ⊥ ∨
      ∃ F : bSet B, (⊤ : B) ≤ is_func F ∧
        wt j₁ ≤ check ((liftedTriplePSet U a θ α).Func (tr j₁).val) ∈ᴮ F ∧
        wt j₂ ≤ check ((liftedTriplePSet U a θ α).Func (tr j₂).val) ∈ᴮ F) :
    (⊤ : B) ≤ is_func (.mk J (fun j => check ((liftedTriplePSet U a θ α).Func (tr j).val)) wt) := by
  let M : bSet B := .mk J (fun j => check ((liftedTriplePSet U a θ α).Func (tr j).val)) wt
  refine le_iInf fun a₁ => le_iInf fun a₂ => le_iInf fun v₁ => le_iInf fun v₂ => ?_
  rw [← deduction, ← deduction]
  let Δ := ((⊤ : B) ⊓ (pair a₁ v₁ ∈ᴮ M ⊓ pair a₂ v₂ ∈ᴮ M)) ⊓ (a₁ =ᴮ a₂)
  have hm₁ : Δ ≤ pair a₁ v₁ ∈ᴮ M := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hm₂ : Δ ≤ pair a₂ v₂ ∈ᴮ M := inf_le_left.trans (inf_le_right.trans inf_le_right)
  dsimp only [M] at hm₁ hm₂
  rw [mem_unfold] at hm₁ hm₂
  apply (le_inf (le_inf inf_le_right hm₁) hm₂).trans
  erw [inf_iSup_eq]
  refine iSup_le fun j₂ => ?_
  erw [inf_iSup_eq, iSup_inf_eq]
  refine iSup_le fun j₁ => ?_
  let idx₁ := (tr j₁).val
  let idx₂ := (tr j₂).val
  let E := ((a₁ =ᴮ a₂) ⊓ (wt j₁ ⊓ (pair a₁ v₁ =ᴮ check ((liftedTriplePSet U a θ α).Func idx₁)))) ⊓
    (wt j₂ ⊓ (pair a₂ v₂ =ᴮ check ((liftedTriplePSet U a θ α).Func idx₂)))
  have hp₁ : E ≤ pair a₁ v₁ =ᴮ
      pair (pair (check ((PSet.ordinalMk (ordinalImage U a α)).Func idx₁.1.1))
        (check ((PSet.ordinalMk θ.ord).Func idx₁.1.2)))
        (check ((PSet.ordinalMk (ordinalImage U a α)).Func idx₁.2)) :=
    bv_trans ((inf_le_left.trans inf_le_right).trans inf_le_right)
      (check_liftedTriplePSet_func U a θ α idx₁)
  have hp₂ : E ≤ pair a₂ v₂ =ᴮ
      pair (pair (check ((PSet.ordinalMk (ordinalImage U a α)).Func idx₂.1.1))
        (check ((PSet.ordinalMk θ.ord).Func idx₂.1.2)))
        (check ((PSet.ordinalMk (ordinalImage U a α)).Func idx₂.2)) :=
    bv_trans (inf_le_right.trans inf_le_right)
      (check_liftedTriplePSet_func U a θ α idx₂)
  have hdom_eq : E ≤ pair (check ((PSet.ordinalMk (ordinalImage U a α)).Func idx₁.1.1))
        (check ((PSet.ordinalMk θ.ord).Func idx₁.1.2)) =ᴮ
      pair (check ((PSet.ordinalMk (ordinalImage U a α)).Func idx₂.1.1))
        (check ((PSet.ordinalMk θ.ord).Func idx₂.1.2)) :=
    bv_trans (bv_symm (pair_eq_pair_iff.mp hp₁).1)
      (bv_trans (inf_le_left.trans inf_le_left) (pair_eq_pair_iff.mp hp₂).1)
  rcases hcases j₁ j₂ with h1 | h2 | rfl | hbot | ⟨F, hF_fn, hF₁, hF₂⟩
  · have he1 := (pair_eq_pair_iff.mp hdom_eq).1
    rw [check_bv_eq_bot_of_not_equiv (PSet.ordinalMk_inj _ _ _ h1)] at he1
    exact he1.trans bot_le
  · have he2 := (pair_eq_pair_iff.mp hdom_eq).2
    rw [check_bv_eq_bot_of_not_equiv (PSet.ordinalMk_inj _ _ _ h2)] at he2
    exact he2.trans bot_le
  · exact bv_trans (pair_eq_pair_iff.mp hp₁).2 (bv_symm (pair_eq_pair_iff.mp hp₂).2)
  · have hboth : E ≤ wt j₁ ⊓ wt j₂ :=
      le_inf ((inf_le_left.trans inf_le_right).trans inf_le_left) (inf_le_right.trans inf_le_left)
    exact (hboth.trans_eq hbot).trans bot_le
  · have hmF₁ : E ≤ pair a₁ v₁ ∈ᴮ F :=
      mem_congr (bv_symm ((inf_le_left.trans inf_le_right).trans inf_le_right)) bv_refl
        (((inf_le_left.trans inf_le_right).trans inf_le_left).trans hF₁)
    have hmF₂ : E ≤ pair a₂ v₂ ∈ᴮ F :=
      mem_congr (bv_symm (inf_le_right.trans inf_le_right)) bv_refl
        ((inf_le_right.trans inf_le_left).trans hF₂)
    exact eq_of_is_func_of_eq (le_top.trans hF_fn) (inf_le_left.trans inf_le_left) hmF₁ hmF₂

theorem ordinalImage_strictMono (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    {ξ₁ ξ₂ : Ordinal.{u}} (hlt : ξ₁ < ξ₂) :
    ordinalImage U a ξ₁ < ordinalImage U a ξ₂ := by
  let VA := Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
  have hm_A : ∀ᶠ _ : I in U,
      ((check (PSet.ordinalMk ξ₁) : bSet (anonymousAlgebra κ)) ∈ᴮ check (PSet.ordinalMk ξ₂)) = ⊤ :=
    Eventually.of_forall fun _ => top_unique (check_mem (PSet.mk_mem_mk_of_lt hlt))
  have hm_VA : (⊤ : VA) ≤
      Preparation.boundedAnonName U a (fun _ => check (PSet.ordinalMk ξ₁)) ∈ᴮ
        Preparation.boundedAnonName U a (fun _ => check (PSet.ordinalMk ξ₂)) := by
    rw [← Preparation.boundedAnonName_mem U a hk hf hn ht hκ _ _
      (Preparation.Supported.const _) (Preparation.Supported.const _),
      value_eq_of_eventuallyEq U (g := fun _ => ⊤) hm_A, value_top]
  have hm_ord : (⊤ : VA) ≤
      (check (PSet.ordinalMk (ordinalImage U a ξ₁)) : bSet VA) ∈ᴮ
        check (PSet.ordinalMk (ordinalImage U a ξ₂)) :=
    mem_congr (Preparation.boundedAnon_ordinal U a hk hf hn ht hκ ξ₁)
      (Preparation.boundedAnon_ordinal U a hk hf hn ht hκ ξ₂) hm_VA
  by_contra hnot
  have hle : ordinalImage U a ξ₂ ≤ ordinalImage U a ξ₁ := le_of_not_gt hnot
  rw [mem_unfold] at hm_ord
  have hle_bot : (⊤ : VA) ≤ ⊥ := by
    refine hm_ord.trans (iSup_le fun k => ?_)
    have hneqv : ¬PSet.Equiv (PSet.ordinalMk (ordinalImage U a ξ₁))
        ((PSet.ordinalMk (ordinalImage U a ξ₂)).Func (check_cast k)) := by
      intro he
      have heq := Ordinal.toZFSet_injective (ZFSet.sound
        (PSet.Equiv.trans he (ordOfPSetIdx_equiv (check_cast k))))
      exact (hle.trans_lt (heq ▸ ordOfPSetIdx_lt (check_cast k))).false
    rw [check_func, check_bval_top, top_inf_eq, check_bv_eq_bot_of_not_equiv hneqv]
  exact top_ne_bot (le_bot_iff.mp hle_bot)

theorem ordinalImage_lt_iff (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    {ξ₁ ξ₂ : Ordinal.{u}} :
    ordinalImage U a ξ₁ < ordinalImage U a ξ₂ ↔ ξ₁ < ξ₂ := by
  constructor
  · intro hlt
    by_contra hnot
    rcases eq_or_lt_of_le (le_of_not_gt hnot) with rfl | hgt
    · exact hlt.false
    · exact (hlt.trans (ordinalImage_strictMono U a hk hf hn ht hκ hgt)).false
  · exact ordinalImage_strictMono U a hk hf hn ht hκ

theorem ordinalImage_inj (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible) :
    Function.Injective (ordinalImage U a) := by
  intro ξ₁ ξ₂ heq
  rcases lt_trichotomy ξ₁ ξ₂ with hlt | rfl | hgt
  · exact False.elim ((ordinalImage_strictMono U a hk hf hn ht hκ hlt).ne heq)
  · rfl
  · exact False.elim ((ordinalImage_strictMono U a hk hf hn ht hκ hgt).ne heq.symm)

/-- Map a ground valid triple at stage `α` to its lifted triple in `ValidLiftedTriple U a θ α`. -/
def liftValidTriple (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible) {α : Ordinal.{u}}
    (t : GroundValidTriple κ α) : ValidLiftedTriple U a θ α := by
  let i_ξ' : (PSet.ordinalMk (ordinalImage U a α)).Type :=
    (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt
      (ordinalImage_strictMono U a hk hf hn ht hκ (ordOfPSetIdx_lt t.val.1.1)))).choose
  let i_η' : (PSet.ordinalMk θ.ord).Type := includeOrdIdx (Cardinal.ord_le_ord.mpr hk) t.val.1.2
  let i_y' : (PSet.ordinalMk (ordinalImage U a α)).Type :=
    (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt
      (ordinalImage_strictMono U a hk hf hn ht hκ (ordOfPSetIdx_lt t.val.2)))).choose
  have hξ_ord : ordOfPSetIdx i_ξ' = ordinalImage U a (ordOfPSetIdx t.val.1.1) := by
    have heqv := PSet.Equiv.symm (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt
      (ordinalImage_strictMono U a hk hf hn ht hκ (ordOfPSetIdx_lt t.val.1.1)))).choose_spec
    exact Ordinal.toZFSet_injective (ZFSet.sound (PSet.Equiv.trans (PSet.Equiv.symm (ordOfPSetIdx_equiv i_ξ')) heqv))
  have hy_ord : ordOfPSetIdx i_y' = ordinalImage U a (ordOfPSetIdx t.val.2) := by
    have heqv := PSet.Equiv.symm (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt
      (ordinalImage_strictMono U a hk hf hn ht hκ (ordOfPSetIdx_lt t.val.2)))).choose_spec
    exact Ordinal.toZFSet_injective (ZFSet.sound (PSet.Equiv.trans (PSet.Equiv.symm (ordOfPSetIdx_equiv i_y')) heqv))
  refine ⟨((i_ξ', i_η'), i_y'), ?_⟩
  rw [hy_ord, hξ_ord]
  exact ordinalImage_strictMono U a hk hf hn ht hκ t.property

theorem liftValidTriple_ord_first (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible) {α : Ordinal.{u}}
    (t : GroundValidTriple κ α) :
    ordOfPSetIdx (liftValidTriple U a hk hf hn ht hκ t).val.1.1 =
      ordinalImage U a (ordOfPSetIdx t.val.1.1) := by
  have heqv := PSet.Equiv.symm (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt
    (ordinalImage_strictMono U a hk hf hn ht hκ (ordOfPSetIdx_lt t.val.1.1)))).choose_spec
  exact Ordinal.toZFSet_injective (ZFSet.sound (PSet.Equiv.trans
    (PSet.Equiv.symm (ordOfPSetIdx_equiv _)) heqv))

theorem liftValidTriple_ord_second (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible) {α : Ordinal.{u}}
    (t : GroundValidTriple κ α) :
    ordOfPSetIdx (liftValidTriple U a hk hf hn ht hκ t).val.1.2 =
      ordOfPSetIdx t.val.1.2 :=
  ordOfPSetIdx_includeOrdIdx (Cardinal.ord_le_ord.mpr hk) t.val.1.2

theorem liftValidTriple_ord_val (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible) {α : Ordinal.{u}}
    (t : GroundValidTriple κ α) :
    ordOfPSetIdx (liftValidTriple U a hk hf hn ht hκ t).val.2 =
      ordinalImage U a (ordOfPSetIdx t.val.2) := by
  have heqv := PSet.Equiv.symm (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt
    (ordinalImage_strictMono U a hk hf hn ht hκ (ordOfPSetIdx_lt t.val.2)))).choose_spec
  exact Ordinal.toZFSet_injective (ZFSet.sound (PSet.Equiv.trans
    (PSet.Equiv.symm (ordOfPSetIdx_equiv _)) heqv))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
theorem stageMasterGraph_card_lt (hk : κ < θ) (hθ : θ.IsInaccessible)
    {α : Ordinal.{u}} (hα : α < θ.ord) :
    #(GroundValidTriple κ α) < θ := by
  apply (Cardinal.mk_subtype_le _).trans_lt
  change Cardinal.mk (((PSet.ordinalMk α).Type × (PSet.ordinalMk κ.ord).Type) ×
    (PSet.ordinalMk α).Type) < θ
  simp only [Cardinal.mk_prod, Cardinal.lift_id, PSet.ordinalMk_type, Cardinal.mk_toType, Cardinal.card_ord]
  exact Cardinal.mul_lt_of_lt hθ.aleph0_lt.le
    (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le (Cardinal.lt_ord.mp hα) hk)
    (Cardinal.lt_ord.mp hα)

theorem stageMasterGraph_func_gen {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (α : Ordinal.{u}) (e : CompleteLatticeHom (InternalLevyStage κ α) B) :
    (⊤ : B) ≤ is_func (.mk (GroundValidTriple κ α)
      (fun t => check ((liftedTriplePSet U a θ α).Func (liftValidTriple U a hk hf hn ht hκ t).val))
      (fun t => e (levyEntry α t.val))) := by
  apply is_func_liftedTriple_graph_of_cases
  intro t₁ t₂
  let idx₁ := (liftValidTriple U a hk hf hn ht hκ t₁).val
  let idx₂ := (liftValidTriple U a hk hf hn ht hκ t₂).val
  by_cases h1 : idx₁.1.1 = idx₂.1.1
  · by_cases h2 : idx₁.1.2 = idx₂.1.2
    · have hd : idx₁.1 = idx₂.1 := Prod.ext h1 h2
      have hsrc_dom : t₁.val.1 = t₂.val.1 := by
        have hξ := ordOfPSetIdx_inj (ordinalImage_inj U a hk hf hn ht hκ
          ((liftValidTriple_ord_first U a hk hf hn ht hκ t₁).symm.trans
            ((congrArg (fun p => ordOfPSetIdx p.1) hd).trans
              (liftValidTriple_ord_first U a hk hf hn ht hκ t₂))))
        have hη := ordOfPSetIdx_inj
          ((liftValidTriple_ord_second U a hk hf hn ht hκ t₁).symm.trans
            ((congrArg (fun p => ordOfPSetIdx p.2) hd).trans
              (liftValidTriple_ord_second U a hk hf hn ht hκ t₂)))
        exact Prod.ext hξ hη
      by_cases hy : t₁.val.2 = t₂.val.2
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext (Prod.ext hsrc_dom hy))))
      · right; right; right; left
        exact (completeHom_inf e _ _).symm.trans
          ((congrArg e (levyEntry_disjoint α hsrc_dom hy)).trans (BotHomClass.map_bot e))
    · exact Or.inr (Or.inl h2)
  · exact Or.inl h1

/-- Stage-`α` master graph in `bSet (AmbientInternalLevy κ θ)` (`α < θ.ord`). -/
def stageMasterGraph (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {α : Ordinal.{u}} (hα : α < θ.ord) :
    SmallGroundLevyGraph U a θ α (AmbientInternalLevy κ θ) where
  Idx := GroundValidTriple κ α
  card_lt := stageMasterGraph_card_lt hk hθ hα
  triple := liftValidTriple U a hk.le hf hn ht hκ
  weight := fun t => ambientLevyStageHom hα.le (levyEntry α t.val)
  func := stageMasterGraph_func_gen U a hk.le hκ hf hn ht α (ambientLevyStageHom hα.le)

/-- Inclusion of `ValidLiftedTriple U a θ α` into `ValidLiftedTriple U a θ α'` (`α ≤ α'`). -/
def includeValidLiftedTriple (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    {α α' : Ordinal.{u}} (h : α ≤ α')
    (idx : ValidLiftedTriple U a θ α) : ValidLiftedTriple U a θ α' := by
  have himg : ordinalImage U a α ≤ ordinalImage U a α' := by
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · exact (ordinalImage_strictMono U a hk hf hn ht hκ hlt).le
  refine ⟨((includeOrdIdx himg idx.val.1.1, idx.val.1.2), includeOrdIdx himg idx.val.2), ?_⟩
  rw [ordOfPSetIdx_includeOrdIdx, ordOfPSetIdx_includeOrdIdx]
  exact idx.property

theorem includeValidLiftedTriple_check_eq {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    {α α' : Ordinal.{u}} (h : α ≤ α') (idx : ValidLiftedTriple U a θ α) {Γ : B} :
    Γ ≤ check ((liftedTriplePSet U a θ α').Func
        (includeValidLiftedTriple U a hk hf hn ht hκ h idx).val) =ᴮ
      check ((liftedTriplePSet U a θ α).Func idx.val) := by
  have himg : ordinalImage U a α ≤ ordinalImage U a α' := by
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · exact (ordinalImage_strictMono U a hk hf hn ht hκ hlt).le
  refine bv_trans (check_liftedTriplePSet_func U a θ α' _) ?_
  refine bv_trans ?_ (bv_symm (check_liftedTriplePSet_func U a θ α idx.val))
  dsimp only [includeValidLiftedTriple]
  exact pair_congr (pair_congr (check_bv_eq (includeOrdIdx_equiv himg idx.val.1.1)) bv_refl)
    (check_bv_eq (includeOrdIdx_equiv himg idx.val.2))

theorem amalgamateChain_func_gen {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {L : Type u} [LinearOrder L]
    (α_chain : L → Ordinal.{u}) {α' : Ordinal.{u}}
    (hle : ∀ l : L, α_chain l ≤ α')
    (G_chain : ∀ l : L, SmallGroundLevyGraph U a θ (α_chain l) B)
    (w_top : GroundValidTriple κ α' → B)
    (hM'_func : (⊤ : B) ≤ is_func (.mk (GroundValidTriple κ α')
      (fun t' => check ((liftedTriplePSet U a θ α').Func (liftValidTriple U a hk hf hn ht hκ t').val))
      w_top))
    (hmono : ∀ {l₁ l₂ : L}, l₁ ≤ l₂ → (⊤ : B) ≤ (G_chain l₁).toBSet ⊆ᴮ (G_chain l₂).toBSet)
    (hcompat : ∀ (l : L) (t : GroundValidTriple κ (α_chain l)),
      w_top ⟨includeTripleIdx (hle l) t.val, by
        dsimp only [includeTripleIdx]
        rw [ordOfPSetIdx_includeOrdIdx, ordOfPSetIdx_includeOrdIdx]
        exact t.property⟩ ≤
        check ((liftedTriplePSet U a θ (α_chain l)).Func (liftValidTriple U a hk hf hn ht hκ t).val) ∈ᴮ
          (G_chain l).toBSet) :
    (⊤ : B) ≤ is_func (.mk ((Σ l : L, (G_chain l).Idx) ⊕ GroundValidTriple κ α')
      (fun j => check ((liftedTriplePSet U a θ α').Func
        (Sum.elim
          (fun lk : Σ l : L, (G_chain l).Idx =>
            includeValidLiftedTriple U a hk hf hn ht hκ (hle lk.1) ((G_chain lk.1).triple lk.2))
          (liftValidTriple U a hk hf hn ht hκ) j).val))
      (Sum.elim (fun lk : Σ l : L, (G_chain l).Idx => (G_chain lk.1).weight lk.2) w_top)) := by
  let M'_bset : bSet B := .mk (GroundValidTriple κ α')
    (fun t' => check ((liftedTriplePSet U a θ α').Func (liftValidTriple U a hk hf hn ht hκ t').val))
    w_top
  have hmem_G (l : L) (k : (G_chain l).Idx) :
      (G_chain l).weight k ≤ check ((liftedTriplePSet U a θ α').Func
        (includeValidLiftedTriple U a hk hf hn ht hκ (hle l) ((G_chain l).triple k)).val) ∈ᴮ
          (G_chain l).toBSet := by
    have hm₀ : (G_chain l).weight k ≤ check ((liftedTriplePSet U a θ (α_chain l)).Func
        ((G_chain l).triple k).val) ∈ᴮ (G_chain l).toBSet := by
      dsimp only [SmallGroundLevyGraph.toBSet]
      rw [mem_unfold]
      exact le_iSup_of_le k (le_inf le_rfl bv_refl)
    exact mem_congr (bv_symm (includeValidLiftedTriple_check_eq U a hk hf hn ht hκ (hle l)
      ((G_chain l).triple k))) bv_refl hm₀
  have hmem_M' (t' : GroundValidTriple κ α') :
      w_top t' ≤ check ((liftedTriplePSet U a θ α').Func
        (liftValidTriple U a hk hf hn ht hκ t').val) ∈ᴮ M'_bset := by
    dsimp only [M'_bset]
    rw [mem_unfold]
    exact le_iSup_of_le t' (le_inf le_rfl bv_refl)
  have hcross (l : L) (k : (G_chain l).Idx) (t' : GroundValidTriple κ α') :
      (includeValidLiftedTriple U a hk hf hn ht hκ (hle l) ((G_chain l).triple k)).val.1.1 ≠
        (liftValidTriple U a hk hf hn ht hκ t').val.1.1 ∨
      ∃ F : bSet B, (⊤ : B) ≤ is_func F ∧
        (G_chain l).weight k ≤ check ((liftedTriplePSet U a θ α').Func
          (includeValidLiftedTriple U a hk hf hn ht hκ (hle l) ((G_chain l).triple k)).val) ∈ᴮ F ∧
        w_top t' ≤ check ((liftedTriplePSet U a θ α').Func
          (liftValidTriple U a hk hf hn ht hκ t').val) ∈ᴮ F := by
    by_cases hlt : ordOfPSetIdx t'.val.1.1 < α_chain l
    · right
      refine ⟨(G_chain l).toBSet, (G_chain l).func, hmem_G l k, ?_⟩
      have hy_lt : ordOfPSetIdx t'.val.2 < α_chain l := t'.property.trans hlt
      let i_ξ : (PSet.ordinalMk (α_chain l)).Type := (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt hlt)).choose
      let i_y : (PSet.ordinalMk (α_chain l)).Type := (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt hy_lt)).choose
      have hξ_eq : ordOfPSetIdx i_ξ = ordOfPSetIdx t'.val.1.1 := by
        have heqv := PSet.Equiv.symm (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt hlt)).choose_spec
        exact Ordinal.toZFSet_injective (ZFSet.sound (PSet.Equiv.trans (PSet.Equiv.symm (ordOfPSetIdx_equiv i_ξ)) heqv))
      have hy_eq : ordOfPSetIdx i_y = ordOfPSetIdx t'.val.2 := by
        have heqv := PSet.Equiv.symm (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt hy_lt)).choose_spec
        exact Ordinal.toZFSet_injective (ZFSet.sound (PSet.Equiv.trans (PSet.Equiv.symm (ordOfPSetIdx_equiv i_y)) heqv))
      let t : GroundValidTriple κ (α_chain l) := ⟨((i_ξ, t'.val.1.2), i_y), by rw [hy_eq, hξ_eq]; exact t'.property⟩
      have hinc_eq : includeTripleIdx (hle l) t.val = t'.val := by
        dsimp only [includeTripleIdx]
        exact Prod.ext
          (Prod.ext (ordOfPSetIdx_inj ((ordOfPSetIdx_includeOrdIdx (hle l) i_ξ).trans hξ_eq)) rfl)
          (ordOfPSetIdx_inj ((ordOfPSetIdx_includeOrdIdx (hle l) i_y).trans hy_eq))
      have ht'_eq : t' = ⟨includeTripleIdx (hle l) t.val, by
          dsimp only [includeTripleIdx]
          rw [ordOfPSetIdx_includeOrdIdx, ordOfPSetIdx_includeOrdIdx]
          exact t.property⟩ := Subtype.ext hinc_eq.symm
      let idx' := (liftValidTriple U a hk hf hn ht hκ t').val
      let idx₀ := (liftValidTriple U a hk hf hn ht hκ t).val
      have hchk_eq : (⊤ : B) ≤ check ((liftedTriplePSet U a θ α').Func idx') =ᴮ
          check ((liftedTriplePSet U a θ (α_chain l)).Func idx₀) := by
        refine bv_trans (check_liftedTriplePSet_func U a θ α' idx') ?_
        refine bv_trans ?_ (bv_symm (check_liftedTriplePSet_func U a θ (α_chain l) idx₀))
        have e1 : PSet.Equiv ((PSet.ordinalMk (ordinalImage U a α')).Func idx'.1.1)
            ((PSet.ordinalMk (ordinalImage U a (α_chain l))).Func idx₀.1.1) := by
          refine PSet.Equiv.trans (ordOfPSetIdx_equiv idx'.1.1) ?_
          rw [liftValidTriple_ord_first U a hk hf hn ht hκ t',
            ← hξ_eq, ← liftValidTriple_ord_first U a hk hf hn ht hκ t]
          exact PSet.Equiv.symm (ordOfPSetIdx_equiv idx₀.1.1)
        have e3 : PSet.Equiv ((PSet.ordinalMk (ordinalImage U a α')).Func idx'.2)
            ((PSet.ordinalMk (ordinalImage U a (α_chain l))).Func idx₀.2) := by
          refine PSet.Equiv.trans (ordOfPSetIdx_equiv idx'.2) ?_
          rw [liftValidTriple_ord_val U a hk hf hn ht hκ t',
            ← hy_eq, ← liftValidTriple_ord_val U a hk hf hn ht hκ t]
          exact PSet.Equiv.symm (ordOfPSetIdx_equiv idx₀.2)
        exact pair_congr (pair_congr (check_bv_eq e1) bv_refl) (check_bv_eq e3)
      have hm_low : w_top t' ≤ check ((liftedTriplePSet U a θ (α_chain l)).Func idx₀) ∈ᴮ (G_chain l).toBSet := by
        rw [ht'_eq]
        exact hcompat l t
      exact mem_congr (bv_symm (le_top.trans hchk_eq)) bv_refl hm_low
    · left
      intro heq
      have h1 : ordOfPSetIdx
          (includeValidLiftedTriple U a hk hf hn ht hκ (hle l) ((G_chain l).triple k)).val.1.1 <
          ordinalImage U a (α_chain l) := by
        dsimp only [includeValidLiftedTriple]
        rw [ordOfPSetIdx_includeOrdIdx]
        exact ordOfPSetIdx_lt _
      have h2 : ordinalImage U a (α_chain l) ≤
          ordOfPSetIdx (liftValidTriple U a hk hf hn ht hκ t').val.1.1 := by
        rw [liftValidTriple_ord_first U a hk hf hn ht hκ t']
        exact le_of_not_gt fun hlt' =>
          hlt ((ordinalImage_lt_iff U a hk hf hn ht hκ).mp hlt')
      exact (h2.trans_eq (congrArg ordOfPSetIdx heq.symm)).not_gt h1
  apply is_func_liftedTriple_graph_of_cases
  intro j₁ j₂
  rcases j₁ with ⟨l₁, k₁⟩ | t₁ <;> rcases j₂ with ⟨l₂, k₂⟩ | t₂
  · rcases le_total l₁ l₂ with h12 | h21
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(G_chain l₂).toBSet, (G_chain l₂).func,
        mem_of_mem_subset (le_top.trans (hmono h12)) (hmem_G l₁ k₁), hmem_G l₂ k₂⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(G_chain l₁).toBSet, (G_chain l₁).func,
        hmem_G l₁ k₁, mem_of_mem_subset (le_top.trans (hmono h21)) (hmem_G l₂ k₂)⟩)))
  · rcases hcross l₁ k₁ t₂ with hne | hF
    · exact Or.inl hne
    · exact Or.inr (Or.inr (Or.inr (Or.inr hF)))
  · rcases hcross l₂ k₂ t₁ with hne | ⟨F, hF_fn, hF_G, hF_M⟩
    · exact Or.inl hne.symm
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨F, hF_fn, hF_M, hF_G⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨M'_bset, hM'_func, hmem_M' t₁, hmem_M' t₂⟩)))

private theorem subset_amalgamate_inl_gen {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {L : Type u} (α_chain : L → Ordinal.{u}) {α' : Ordinal.{u}}
    (hle : ∀ l : L, α_chain l ≤ α')
    (G_chain : ∀ l : L, SmallGroundLevyGraph U a θ (α_chain l) B)
    (w_top : GroundValidTriple κ α' → B) (l : L) :
    (⊤ : B) ≤ (G_chain l).toBSet ⊆ᴮ
      .mk ((Σ m : L, (G_chain m).Idx) ⊕ GroundValidTriple κ α')
        (fun j => check ((liftedTriplePSet U a θ α').Func
          (Sum.elim
            (fun mk : Σ m : L, (G_chain m).Idx =>
              includeValidLiftedTriple U a hk hf hn ht hκ (hle mk.1) ((G_chain mk.1).triple mk.2))
            (liftValidTriple U a hk hf hn ht hκ) j).val))
        (Sum.elim (fun mk : Σ m : L, (G_chain m).Idx => (G_chain mk.1).weight mk.2) w_top) := by
  dsimp only [SmallGroundLevyGraph.toBSet]
  rw [subset_unfold]
  refine le_iInf fun k => deduction.mp ?_
  rw [mem_unfold]
  exact le_iSup_of_le (Sum.inl ⟨l, k⟩) (le_inf inf_le_right
    (bv_symm (includeValidLiftedTriple_check_eq U a hk hf hn ht hκ (hle l) ((G_chain l).triple k))))

private theorem subset_amalgamate_inr_gen {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {L : Type u} (α_chain : L → Ordinal.{u}) {α' : Ordinal.{u}}
    (hle : ∀ l : L, α_chain l ≤ α')
    (G_chain : ∀ l : L, SmallGroundLevyGraph U a θ (α_chain l) B)
    (w_top : GroundValidTriple κ α' → B) :
    (⊤ : B) ≤
      (.mk (GroundValidTriple κ α')
        (fun t => check ((liftedTriplePSet U a θ α').Func (liftValidTriple U a hk hf hn ht hκ t).val))
        w_top) ⊆ᴮ
      .mk ((Σ m : L, (G_chain m).Idx) ⊕ GroundValidTriple κ α')
        (fun j => check ((liftedTriplePSet U a θ α').Func
          (Sum.elim
            (fun mk : Σ m : L, (G_chain m).Idx =>
              includeValidLiftedTriple U a hk hf hn ht hκ (hle mk.1) ((G_chain mk.1).triple mk.2))
            (liftValidTriple U a hk hf hn ht hκ) j).val))
        (Sum.elim (fun mk : Σ m : L, (G_chain m).Idx => (G_chain mk.1).weight mk.2) w_top) := by
  rw [subset_unfold]
  refine le_iInf fun t => deduction.mp ?_
  rw [mem_unfold]
  exact le_iSup_of_le (Sum.inr t) (le_inf inf_le_right bv_refl)

private theorem mem_groundMaster_at {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {α : Ordinal.{u}} (w : GroundValidTriple κ α → B) (t : GroundValidTriple κ α) :
    w t ≤ check ((liftedTriplePSet U a θ α).Func (liftValidTriple U a hk hf hn ht hκ t).val) ∈ᴮ
      .mk (GroundValidTriple κ α)
        (fun s => check ((liftedTriplePSet U a θ α).Func (liftValidTriple U a hk hf hn ht hκ s).val))
        w := by
  rw [mem_unfold]
  exact le_iSup_of_le t (le_inf le_rfl bv_refl)

theorem amalgamateChain_card_lt {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (hk : κ < θ) (hθ : θ.IsInaccessible)
    {L : Type u} (hL : #L < θ)
    (α_chain : L → Ordinal.{u}) {α' : Ordinal.{u}} (hα' : α' < θ.ord)
    (G_chain : ∀ l : L, SmallGroundLevyGraph U a θ (α_chain l) B) :
    #((Σ l : L, (G_chain l).Idx) ⊕ GroundValidTriple κ α') < θ := by
  rw [Cardinal.mk_sum, Cardinal.mk_sigma, Cardinal.lift_id, Cardinal.lift_id]
  have hg (l : L) : (#(G_chain l).Idx).ord < θ.ord :=
    Cardinal.ord_lt_ord.mpr (G_chain l).card_lt
  let supOrd := ⨆ l : L, (#(G_chain l).Idx).ord + 1
  have hsup_ord : supOrd < θ.ord :=
    Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hθ.isRegular.cof_ord]) hg
  have hsup_card : supOrd.card < θ := Cardinal.lt_ord.mp hsup_ord
  have hle_sup (l : L) : #(G_chain l).Idx ≤ supOrd.card := by
    have ho : (#(G_chain l).Idx).ord ≤ supOrd :=
      (Ordinal.lt_iSup_add_one (fun m => (#(G_chain m).Idx).ord) l).le
    simpa only [Cardinal.card_ord] using Ordinal.card_le_card ho
  have hsum_lt : Cardinal.sum (fun l : L => #(G_chain l).Idx) < θ :=
    ((Cardinal.sum_le_sum _ _ hle_sup).trans_eq (Cardinal.sum_const' L supOrd.card)).trans_lt
      (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hL hsup_card)
  exact Cardinal.add_lt_of_lt hθ.aleph0_lt.le hsum_lt
    (stageMasterGraph_card_lt hk hθ hα')

theorem amalgamateChainWithMaster_compat
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {L : Type u} (α_chain : L → Ordinal.{u}) {α' : Ordinal.{u}} (hα' : α' < θ.ord)
    (hle : ∀ l : L, α_chain l ≤ α')
    (G_chain : ∀ l : L, SmallGroundLevyGraph U a θ (α_chain l) (AmbientInternalLevy κ θ))
    (hmaster : ∀ l : L,
      (⊤ : AmbientInternalLevy κ θ) ≤
        (stageMasterGraph U a hk hκ hθ hf hn ht ((hle l).trans_lt hα')).toBSet ⊆ᴮ
          (G_chain l).toBSet)
    (l : L) (t : GroundValidTriple κ (α_chain l)) :
    ambientLevyStageHom hα'.le (levyEntry α' (includeTripleIdx (hle l) t.val)) ≤
      check ((liftedTriplePSet U a θ (α_chain l)).Func
        (liftValidTriple U a hk.le hf hn ht hκ t).val) ∈ᴮ (G_chain l).toBSet := by
  have hw_eq : ambientLevyStageHom hα'.le (levyEntry α' (includeTripleIdx (hle l) t.val)) =
      ambientLevyStageHom ((hle l).trans hα'.le) (levyEntry (α_chain l) t.val) :=
    (congrArg (ambientLevyStageHom hα'.le)
      (stageStepHom_levyEntry (κ := κ) (hle l) t.val t.property).symm).trans
      (ambientLevyStageHom_comp (κ := κ) (θ := θ) (hle l) hα'.le (levyEntry (α_chain l) t.val))
  rw [hw_eq]
  exact mem_of_mem_subset (le_top.trans (hmaster l))
    (mem_groundMaster_at (B := AmbientInternalLevy κ θ) U a hk.le hκ hf hn ht
      (fun s => ambientLevyStageHom ((hle l).trans hα'.le) (levyEntry (α_chain l) s.val)) t)

/-- Amalgamate a `< θ`-indexed monotone chain of `SmallGroundLevyGraph`s extending their
stage master graphs with `stageMasterGraph α'` at any upper stage `α' < θ.ord`. -/
def amalgamateChainWithMaster (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {L : Type u} [LinearOrder L] (hL : #L < θ)
    (α_chain : L → Ordinal.{u}) {α' : Ordinal.{u}} (hα' : α' < θ.ord)
    (hle : ∀ l : L, α_chain l ≤ α')
    (G_chain : ∀ l : L, SmallGroundLevyGraph U a θ (α_chain l) (AmbientInternalLevy κ θ))
    (hmono : ∀ {l₁ l₂ : L}, l₁ ≤ l₂ →
      (⊤ : AmbientInternalLevy κ θ) ≤ (G_chain l₁).toBSet ⊆ᴮ (G_chain l₂).toBSet)
    (hmaster : ∀ l : L,
      (⊤ : AmbientInternalLevy κ θ) ≤
        (stageMasterGraph U a hk hκ hθ hf hn ht ((hle l).trans_lt hα')).toBSet ⊆ᴮ
          (G_chain l).toBSet) :
    SmallGroundLevyGraph U a θ α' (AmbientInternalLevy κ θ) where
  Idx := (Σ l : L, (G_chain l).Idx) ⊕ GroundValidTriple κ α'
  card_lt := amalgamateChain_card_lt (B := AmbientInternalLevy κ θ) U a hk hθ hL α_chain hα' G_chain
  triple := Sum.elim
    (fun lk : Σ l : L, (G_chain l).Idx =>
      includeValidLiftedTriple U a hk.le hf hn ht hκ (hle lk.1) ((G_chain lk.1).triple lk.2))
    (liftValidTriple U a hk.le hf hn ht hκ)
  weight := Sum.elim
    (fun lk : Σ l : L, (G_chain l).Idx => (G_chain lk.1).weight lk.2)
    (fun t => ambientLevyStageHom hα'.le (levyEntry α' t.val))
  func := amalgamateChain_func_gen (B := AmbientInternalLevy κ θ) U a hk.le hκ hf hn ht
    α_chain hle G_chain
    (fun t => ambientLevyStageHom hα'.le (levyEntry α' t.val))
    (stageMasterGraph_func_gen (B := AmbientInternalLevy κ θ) U a hk.le hκ hf hn ht α'
      (ambientLevyStageHom hα'.le))
    hmono
    (fun l t => amalgamateChainWithMaster_compat U a hk hκ hθ hf hn ht α_chain hα' hle G_chain hmaster l t)

theorem subset_amalgamateChainWithMaster_chain (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {L : Type u} [LinearOrder L] (hL : #L < θ)
    (α_chain : L → Ordinal.{u}) {α' : Ordinal.{u}} (hα' : α' < θ.ord)
    (hle : ∀ l : L, α_chain l ≤ α')
    (G_chain : ∀ l : L, SmallGroundLevyGraph U a θ (α_chain l) (AmbientInternalLevy κ θ))
    (hmono : ∀ {l₁ l₂ : L}, l₁ ≤ l₂ →
      (⊤ : AmbientInternalLevy κ θ) ≤ (G_chain l₁).toBSet ⊆ᴮ (G_chain l₂).toBSet)
    (hmaster : ∀ l : L,
      (⊤ : AmbientInternalLevy κ θ) ≤
        (stageMasterGraph U a hk hκ hθ hf hn ht ((hle l).trans_lt hα')).toBSet ⊆ᴮ
          (G_chain l).toBSet)
    (l : L) :
    (⊤ : AmbientInternalLevy κ θ) ≤ (G_chain l).toBSet ⊆ᴮ
      (amalgamateChainWithMaster U a hk hκ hθ hf hn ht hL α_chain hα' hle G_chain hmono hmaster).toBSet :=
  subset_amalgamate_inl_gen (B := AmbientInternalLevy κ θ) U a hk.le hκ hf hn ht α_chain hle G_chain
    (fun t => ambientLevyStageHom hα'.le (levyEntry α' t.val)) l

theorem subset_amalgamateChainWithMaster_master (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {L : Type u} [LinearOrder L] (hL : #L < θ)
    (α_chain : L → Ordinal.{u}) {α' : Ordinal.{u}} (hα' : α' < θ.ord)
    (hle : ∀ l : L, α_chain l ≤ α')
    (G_chain : ∀ l : L, SmallGroundLevyGraph U a θ (α_chain l) (AmbientInternalLevy κ θ))
    (hmono : ∀ {l₁ l₂ : L}, l₁ ≤ l₂ →
      (⊤ : AmbientInternalLevy κ θ) ≤ (G_chain l₁).toBSet ⊆ᴮ (G_chain l₂).toBSet)
    (hmaster : ∀ l : L,
      (⊤ : AmbientInternalLevy κ θ) ≤
        (stageMasterGraph U a hk hκ hθ hf hn ht ((hle l).trans_lt hα')).toBSet ⊆ᴮ
          (G_chain l).toBSet) :
    (⊤ : AmbientInternalLevy κ θ) ≤
      (stageMasterGraph U a hk hκ hθ hf hn ht hα').toBSet ⊆ᴮ
      (amalgamateChainWithMaster U a hk hκ hθ hf hn ht hL α_chain hα' hle G_chain hmono hmaster).toBSet :=
  subset_amalgamate_inr_gen (B := AmbientInternalLevy κ θ) U a hk.le hκ hf hn ht α_chain hle G_chain
    (fun t => ambientLevyStageHom hα'.le (levyEntry α' t.val))

end StageMasterGraphs

section StageLocalTests
variable {κ : Cardinal.{u}}

/-- Stage-`α` open set of conditions in `internalLevyPoset κ α` forcing `b`. -/
def levyTruthOpen (α : Ordinal.{u}) (b : InternalLevyStage κ α) : bSet (anonymousAlgebra κ) :=
  comprehend (levyReads α b) (internalLevyPoset κ α)

theorem mem_levyTruthOpen_iff {α : Ordinal.{u}} {b : InternalLevyStage κ α}
    {Γ : anonymousAlgebra κ} {g : bSet (anonymousAlgebra κ)} :
    Γ ≤ g ∈ᴮ levyTruthOpen α b ↔
      Γ ≤ g ∈ᴮ internalLevyPoset κ α ∧ Γ ≤ levyReads α b g := by
  rw [levyTruthOpen, mem_comprehend_and (levyReads_ext α b)]

theorem levyTruthOpen_subset (α : Ordinal.{u}) (b : InternalLevyStage κ α) :
    (⊤ : anonymousAlgebra κ) ≤ levyTruthOpen α b ⊆ᴮ internalLevyPoset κ α :=
  comprehend_subset (ϕ := levyReads α b) (internalLevyPoset κ α)

theorem levyTruthOpen_forces (α : Ordinal.{u}) (p : InternalLevyCondition κ α)
    (b : InternalLevyStage κ α) (h : condition p ≤ b) :
    p.value ≤ name p ∈ᴮ levyTruthOpen α b :=
  mem_levyTruthOpen_iff.mpr ⟨name_mem p,
    le_iSup_of_le ⟨p, h⟩ (le_inf le_rfl bv_refl)⟩

theorem levyTruthOpen_upward {α : Ordinal.{u}} {b : InternalLevyStage κ α}
    {Γ : anonymousAlgebra κ} {g r : bSet (anonymousAlgebra κ)}
    (hg : Γ ≤ g ∈ᴮ levyTruthOpen α b)
    (hr : Γ ≤ r ∈ᴮ internalLevyPoset κ α)
    (hsub : Γ ≤ g ⊆ᴮ r) :
    Γ ≤ r ∈ᴮ levyTruthOpen α b :=
  mem_levyTruthOpen_iff.mpr ⟨hr,
    (le_inf le_rfl (mem_levyTruthOpen_iff.mp hg).2).trans (levyReads_mono_of_subset hsub hr)⟩

theorem levyTruthOpen_disjoint (α : Ordinal.{u}) (b : InternalLevyStage κ α)
    (g : bSet (anonymousAlgebra κ)) :
    (g ∈ᴮ levyTruthOpen α b) ⊓ (g ∈ᴮ levyTruthOpen α bᶜ) = ⊥ := by
  apply le_bot_iff.mp
  let D : anonymousAlgebra κ := (g ∈ᴮ levyTruthOpen α b) ⊓ (g ∈ᴮ levyTruthOpen α bᶜ)
  have h1 : D ≤ levyReads α b g :=
    (mem_levyTruthOpen_iff.mp (inf_le_left : D ≤ g ∈ᴮ levyTruthOpen α b)).2
  have h2 : D ≤ levyReads α bᶜ g :=
    (mem_levyTruthOpen_iff.mp (inf_le_right : D ≤ g ∈ᴮ levyTruthOpen α bᶜ)).2
  exact (le_inf h1 h2).trans_eq (levyReads_inf_compl_eq_bot α b g)

/-- Stage-`α` row relation encoding `X : κ.ord.ToType → InternalLevyStage κ α`. -/
def levyRowRelation (α : Ordinal.{u}) (X : κ.ord.ToType → InternalLevyStage κ α) :
    bSet (anonymousAlgebra κ) :=
  .mk (Σ i : κ.ord.ToType, {p : InternalLevyCondition κ α // condition p ≤ X i})
    (fun z => pair (ordinalLabel z.1) (name z.2.val))
    (fun z => z.2.val.value)

theorem levyRowRelation_fiber (α : Ordinal.{u}) (X : κ.ord.ToType → InternalLevyStage κ α)
    (i : κ.ord.ToType) (g : bSet (anonymousAlgebra κ)) :
    (pair (ordinalLabel i) g ∈ᴮ levyRowRelation α X) = levyReads α (X i) g := by
  dsimp only [levyRowRelation, levyReads]
  rw [mem_unfold]
  apply le_antisymm
  · refine iSup_le fun ⟨j, p⟩ => ?_
    by_cases hij : i = j
    · subst hij
      exact le_iSup_of_le p (le_inf inf_le_left (pair_eq_pair_iff.mp inf_le_right).2)
    · have h0 : (ordinalLabel i : bSet (anonymousAlgebra κ)) =ᴮ ordinalLabel j = ⊥ := by
        rw [ordinalLabel_eq, if_neg hij]
      exact (le_inf le_rfl ((pair_eq_pair_iff.mp inf_le_right).1.trans_eq h0)).trans
        (inf_le_right.trans bot_le)
  · refine iSup_le fun p => ?_
    exact le_iSup_of_le ⟨i, p⟩ (le_inf inf_le_left (pair_congr bv_refl inf_le_right))

/-- Stage-`α` dense join test for an indexed family `b : J → InternalLevyStage κ α`. -/
def levyJoinTest (α : Ordinal.{u}) {J : Type u} (b : J → InternalLevyStage κ α) :
    bSet (anonymousAlgebra κ) :=
  comprehend (fun g => (⨆ j : J, levyReads α (b j) g) ⊔ levyReads α (⨆ j, b j)ᶜ g)
    (internalLevyPoset κ α)

theorem levyJoinTest_ext (α : Ordinal.{u}) {J : Type u} (b : J → InternalLevyStage κ α) :
    B_ext (fun g => (⨆ j : J, levyReads α (b j) g) ⊔ levyReads α (⨆ j, b j)ᶜ g) :=
  B_ext_sup (h₁ := B_ext_iSup (h := fun j => levyReads_ext α (b j)))
    (h₂ := levyReads_ext α (⨆ j, b j)ᶜ)

theorem mem_levyJoinTest_iff {α : Ordinal.{u}} {J : Type u} {b : J → InternalLevyStage κ α}
    {Γ : anonymousAlgebra κ} {g : bSet (anonymousAlgebra κ)} :
    Γ ≤ g ∈ᴮ levyJoinTest α b ↔
      Γ ≤ g ∈ᴮ internalLevyPoset κ α ∧
      Γ ≤ (⨆ j : J, levyReads α (b j) g) ⊔ levyReads α (⨆ j, b j)ᶜ g := by
  rw [levyJoinTest, mem_comprehend_and (levyJoinTest_ext α b)]

theorem levyJoinTest_subset (α : Ordinal.{u}) {J : Type u} (b : J → InternalLevyStage κ α) :
    (⊤ : anonymousAlgebra κ) ≤ levyJoinTest α b ⊆ᴮ internalLevyPoset κ α :=
  comprehend_subset (ϕ := fun g => (⨆ j : J, levyReads α (b j) g) ⊔ levyReads α (⨆ j, b j)ᶜ g)
    (internalLevyPoset κ α)

theorem levyJoinTest_dense (α : Ordinal.{u}) {J : Type u} (b : J → InternalLevyStage κ α) :
    (⊤ : anonymousAlgebra κ) ≤
      allIn (internalLevyPoset κ α) (fun g =>
        someIn (levyJoinTest α b) (fun r => g ⊆ᴮ r)) := by
  refine allIn_intro fun {Γ} _ g hg => ?_
  let V := someIn (levyJoinTest α b) (fun r => g ⊆ᴮ r)
  by_contra hnot
  have hpos : Γ ⊓ Vᶜ ≠ ⊥ := fun h0 =>
    hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
  obtain ⟨p, hpb, hpeq⟩ := exists_canonical_refinement hpos (inf_le_left.trans hg)
  let sign : Option J → InternalLevyStage κ α := fun s => match s with
    | none => (⨆ j, b j)ᶜ
    | some j => b j
  have hall : condition p ≤ ⨆ s, sign s :=
    le_top.trans ((sup_compl_eq_top (x := ⨆ j, b j)).ge.trans (sup_le
      (iSup_le fun j => le_iSup_of_le (some j) le_rfl) (le_iSup_of_le none le_rfl)))
  have hmeet : condition p ⊓ ⨆ s, sign s ≠ ⊥ := by
    erw [inf_of_le hall]
    exact condition_ne_bot p
  obtain ⟨s, hs_ne⟩ := exists_mem_iSup_inf_ne_bot hmeet
  obtain ⟨q, hq⟩ := exists_condition_le hs_ne
  obtain ⟨t, htq, htp⟩ :=
    (mem_condition_iff p q).mp (condition_le_iff.mp (hq.trans inf_le_left)) q le_rfl
  have hbs : condition t ≤ sign s := (condition_mono htq).trans (hq.trans inf_le_right)
  have hsub : t.value ≤ g ⊆ᴮ name t :=
    subset_trans' (bSet.subset_of_eq (htp.1.trans hpeq)) htp.2
  have hmem_test : t.value ≤ name t ∈ᴮ levyJoinTest α b := by
    refine mem_levyJoinTest_iff.mpr ⟨name_mem t, ?_⟩
    cases s with
    | none =>
      exact (le_iSup_of_le ⟨t, hbs⟩ (le_inf le_rfl bv_refl)).trans le_sup_right
    | some j =>
      exact (le_iSup_of_le j (le_iSup_of_le ⟨t, hbs⟩ (le_inf le_rfl bv_refl))).trans le_sup_left
  have ht_V : t.value ≤ V := le_iSup_of_le (name t) (le_inf hmem_test hsub)
  exact t.nonzero (le_bot_iff.mp ((le_inf ht_V (htp.1.trans (hpb.trans inf_le_right))).trans inf_compl_eq_bot.le))

theorem levyRegressiveTest_mem (α : Ordinal.{u})
    (H : κ.ord.ToType → κ.ord.ToType → InternalLevyStage κ α) (k : κ.ord.ToType)
    (g : bSet (anonymousAlgebra κ)) :
    (g ∈ᴮ levyJoinTest α (fun i : Set.Iio k => H i.val k)) =
      (g ∈ᴮ internalLevyPoset κ α) ⊓
        (someIn (ordinalLabel k) (fun z => pair z g ∈ᴮ levyRowRelation α (fun j => H j k)) ⊔
          levyReads α (diagonal κ H k)ᶜ g) := by
  have hm : (g ∈ᴮ levyJoinTest α (fun i : Set.Iio k => H i.val k)) =
      (g ∈ᴮ internalLevyPoset κ α) ⊓
        ((⨆ i : Set.Iio k, levyReads α (H i.val k) g) ⊔
          levyReads α (⨆ i : Set.Iio k, H i.val k)ᶜ g) := by
    apply le_antisymm
    · obtain ⟨h1, h2⟩ := mem_levyJoinTest_iff.mp le_rfl
      exact le_inf h1 h2
    · exact mem_levyJoinTest_iff.mpr ⟨inf_le_left, inf_le_right⟩
  rw [hm]
  congr 2
  change (⨆ i : Set.Iio k, levyReads α (H i.val k) g) =
    someIn (ordinalCarrier k.toOrd.val) (fun z => pair z g ∈ᴮ levyRowRelation α (fun j => H j k))
  apply le_antisymm
  · refine iSup_le fun i => le_iSup_of_le (ordinalLabel i.val) ?_
    exact le_inf (check_mem (PSet.mk_mem_mk_of_lt (Ordinal.ToType.mk.symm.strictMono i.property)))
      (levyRowRelation_fiber α (fun j => H j k) i.val g).ge
  · rw [someIn_checked _ _ B_ext_pair_mem_left]
    refine iSup_le fun j => ?_
    let i := StringName.includeIndex (toOrd_lt k).le j
    have heq : i.toOrd.val = j.toOrd.val := StringName.includeIndex_toOrd _ _
    have hhit : i < k := Ordinal.ToType.mk.symm.lt_iff_lt.mp
      (show i.toOrd.val < k.toOrd.val from heq ▸ toOrd_lt j)
    have hlab : (ordinalLabel i : bSet (anonymousAlgebra κ)) = ordinalLabel j :=
      congrArg (fun o => check (PSet.ordinalMk o)) heq
    rw [← hlab, levyRowRelation_fiber]
    exact le_iSup_of_le (⟨i, hhit⟩ : Set.Iio k) le_rfl

end StageLocalTests

end Erdos1172AnonymousInternalLevy
