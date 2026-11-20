/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4AnonymousInternalLevyCodingCompression
public import Erdos1172.Part4HugeCardinalCharacterization
public import Erdos1172.Part4InternalGCHPart4Theory

@[expose] public section

/-! # Normal seed valuation on `InternalLevyAlgebra κ θ` and consistency of `gchPart4Theory`

Using `stageMaster_forces_constant_truthOpen`, `code_small_ground_func_into_stage`, and
`compress_lifted_witness_to_R` over `R := AmbientInternalLevy κ θ`, we execute a `θ.ord`-length
transfinite construction producing a scalar-faithful, initial-segment-vanishing, normal valuation
`μ : BoundedLatticeHom (κ.ord.ToType → InternalLevyAlgebra κ θ) (AmbientInternalLevy κ θ)`.

Combined with `ambientLevy_exists_denseOver` (`≤ κ` relative density of `R` over
`InternalLevyAlgebra κ θ`), `internal_ideal_and_basis`, `internalLevy_fullGCH_eq_top`, and
`consistent_gchPart4_of_nonzero_ideal`, this proves `Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent`
relative to two inaccessible cardinals `κ < θ`, ground tail GCH at `≥ θ`, and a `(κ, θ)`-fine
normal `κ`-complete ultrafilter `(U, a)`.
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
open Erdos1172Shioya.UltrapowerStage (ordinalImage ordinalImage_code criticalOrdinalPoint)

universe u

namespace Erdos1172AnonymousInternalLevy

section StageTruthOpenLaws
variable {κ : Cardinal.{u}}

theorem levyTruthOpen_stage_upward {α₁ α₂ : Ordinal.{u}} (h : α₁ ≤ α₂)
    {b : InternalLevyStage κ α₁} {Γ : anonymousAlgebra κ}
    {g₁ g₂ : bSet (anonymousAlgebra κ)}
    (hg₁ : Γ ≤ g₁ ∈ᴮ levyTruthOpen α₁ b)
    (hg₂ : Γ ≤ g₂ ∈ᴮ internalLevyPoset κ α₂)
    (hsub : Γ ≤ g₁ ⊆ᴮ g₂) :
    Γ ≤ g₂ ∈ᴮ levyTruthOpen α₂ (stageStepHom h b) := by
  refine mem_levyTruthOpen_iff.mpr ⟨hg₂, ?_⟩
  have hr₁ : Γ ≤ levyReads α₁ b g₁ := (mem_levyTruthOpen_iff.mp hg₁).2
  by_contra hnot
  let V := levyReads α₂ (stageStepHom h b) g₂
  have hpos : Γ ⊓ Vᶜ ≠ ⊥ := fun h0 =>
    hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
  have hmeet : (Γ ⊓ Vᶜ) ⊓ levyReads α₁ b g₁ ≠ ⊥ := by
    erw [inf_of_le (inf_le_left.trans hr₁)]
    exact hpos
  obtain ⟨⟨p, hpb⟩, hp_ne⟩ := exists_mem_iSup_inf_ne_bot hmeet
  obtain ⟨q, hqv, hqeq⟩ := exists_canonical_refinement hp_ne
    ((inf_le_left.trans inf_le_left).trans hg₂)
  have hqv_p : q.value ≤ p.value := hqv.trans (inf_le_right.trans inf_le_left)
  have hp_sub_q : q.value ≤ name p ⊆ᴮ name q :=
    subset_trans' (bSet.subset_of_eq (bv_symm (hqv.trans (inf_le_right.trans inf_le_right))))
      (subset_trans' ((hqv.trans (inf_le_left.trans inf_le_left)).trans hsub)
        (bSet.subset_of_eq hqeq))
  have hq_b : condition q ≤ stageStepHom (κ := κ) h b := by
    have hc_le : condition q ≤ stageStepHom (κ := κ) h (condition p) := by
      rw [stageStepHom_condition]
      exact le_iSup (fun s : {s : InternalLevyCondition κ α₂ //
        s.value ≤ p.value ∧ s.value ≤ name p ⊆ᴮ name s} => condition s.val) ⟨q, hqv_p, hp_sub_q⟩
    exact hc_le.trans (OrderHomClass.mono (stageStepHom (κ := κ) h) hpb)
  have hq_V : q.value ≤ V := le_iSup_of_le ⟨q, hq_b⟩ (le_inf le_rfl hqeq)
  have hq_notV : q.value ≤ Vᶜ := hqv.trans (inf_le_left.trans inf_le_right)
  exact q.nonzero (le_bot_iff.mp ((le_inf hq_V hq_notV).trans inf_compl_eq_bot.le))

theorem levyTruthOpen_top (α : Ordinal.{u}) {Γ : anonymousAlgebra κ}
    {g : bSet (anonymousAlgebra κ)} (hg : Γ ≤ g ∈ᴮ internalLevyPoset κ α) :
    Γ ≤ g ∈ᴮ levyTruthOpen α ⊤ := by
  refine mem_levyTruthOpen_iff.mpr ⟨hg, ?_⟩
  let V := levyReads α (⊤ : InternalLevyStage κ α) g
  by_contra hnot
  have hpos : Γ ⊓ Vᶜ ≠ ⊥ := fun h0 =>
    hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
  obtain ⟨p, hpb, hpeq⟩ := exists_canonical_refinement hpos (inf_le_left.trans hg)
  have hp_V : p.value ≤ V := le_iSup_of_le ⟨p, le_top⟩ (le_inf le_rfl hpeq)
  exact p.nonzero (le_bot_iff.mp ((le_inf hp_V (hpb.trans inf_le_right)).trans inf_compl_eq_bot.le))

theorem levyTruthOpen_bot_disjoint (α : Ordinal.{u}) (g : bSet (anonymousAlgebra κ)) :
    (g ∈ᴮ internalLevyPoset κ α) ⊓ (g ∈ᴮ levyTruthOpen α ⊥) = ⊥ := by
  apply le_bot_iff.mp
  have htop : g ∈ᴮ internalLevyPoset κ α ≤ g ∈ᴮ levyTruthOpen α ⊤ := levyTruthOpen_top α le_rfl
  have hbot : (⊥ : InternalLevyStage κ α) = (⊤ : InternalLevyStage κ α)ᶜ := compl_top.symm
  rw [hbot]
  exact (inf_le_inf_right _ htop).trans_eq (levyTruthOpen_disjoint α ⊤ g)

theorem levyTruthOpen_inf_eq (α : Ordinal.{u}) (b₁ b₂ : InternalLevyStage κ α)
    (g : bSet (anonymousAlgebra κ)) :
    (g ∈ᴮ levyTruthOpen α (b₁ ⊓ b₂)) =
      (g ∈ᴮ levyTruthOpen α b₁) ⊓ (g ∈ᴮ levyTruthOpen α b₂) := by
  apply le_antisymm
  · obtain ⟨hg_P, hr⟩ := mem_levyTruthOpen_iff.mp (le_refl (g ∈ᴮ levyTruthOpen α (b₁ ⊓ b₂)))
    exact le_inf
      (mem_levyTruthOpen_iff.mpr ⟨hg_P, hr.trans (iSup_le fun ⟨p, hp⟩ =>
        le_iSup_of_le ⟨p, hp.trans inf_le_left⟩ le_rfl)⟩)
      (mem_levyTruthOpen_iff.mpr ⟨hg_P, hr.trans (iSup_le fun ⟨p, hp⟩ =>
        le_iSup_of_le ⟨p, hp.trans inf_le_right⟩ le_rfl)⟩)
  · let D := (g ∈ᴮ levyTruthOpen α b₁) ⊓ (g ∈ᴮ levyTruthOpen α b₂)
    have hg_P : D ≤ g ∈ᴮ internalLevyPoset κ α :=
      (mem_levyTruthOpen_iff.mp (inf_le_left : D ≤ _)).1
    refine mem_levyTruthOpen_iff.mpr ⟨hg_P, ?_⟩
    have hr₁ : D ≤ levyReads α b₁ g := (mem_levyTruthOpen_iff.mp (inf_le_left : D ≤ _)).2
    have hr₂ : D ≤ levyReads α b₂ g := (mem_levyTruthOpen_iff.mp (inf_le_right : D ≤ _)).2
    let V := levyReads α (b₁ ⊓ b₂) g
    by_contra hnot
    have hpos : D ⊓ Vᶜ ≠ ⊥ := fun h0 =>
      hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    have hm₁ : (D ⊓ Vᶜ) ⊓ levyReads α b₁ g ≠ ⊥ := by
      erw [inf_of_le (inf_le_left.trans hr₁)]
      exact hpos
    obtain ⟨⟨p₁, hp₁⟩, hp₁_ne⟩ := exists_mem_iSup_inf_ne_bot hm₁
    have hm₂ : ((D ⊓ Vᶜ) ⊓ (p₁.value ⊓ (g =ᴮ name p₁))) ⊓ levyReads α b₂ g ≠ ⊥ := by
      erw [inf_of_le ((inf_le_left.trans inf_le_left).trans hr₂)]
      exact hp₁_ne
    obtain ⟨⟨p₂, hp₂⟩, hp₂_ne⟩ := exists_mem_iSup_inf_ne_bot hm₂
    let v := ((D ⊓ Vᶜ) ⊓ (p₁.value ⊓ (g =ᴮ name p₁))) ⊓ (p₂.value ⊓ (g =ᴮ name p₂))
    let r := shrink p₁ v hp₂_ne (inf_le_left.trans (inf_le_right.trans inf_le_left))
    have hr_p₁ : r ≤ p₁ := shrink_le p₁ v hp₂_ne _
    have hr_p₂ : r ≤ p₂ :=
      ⟨inf_le_right.trans inf_le_left,
       bSet.subset_of_eq (bv_trans (bv_symm (inf_le_right.trans inf_le_right))
         (inf_le_left.trans (inf_le_right.trans inf_le_right)))⟩
    have hr_cone : condition r ≤ b₁ ⊓ b₂ :=
      le_inf ((condition_mono hr_p₁).trans hp₁) ((condition_mono hr_p₂).trans hp₂)
    have hr_V : v ≤ V :=
      le_iSup_of_le ⟨r, hr_cone⟩ (le_inf le_rfl (inf_le_left.trans (inf_le_right.trans inf_le_right)))
    have hr_notV : v ≤ Vᶜ := (inf_le_left.trans inf_le_left).trans inf_le_right
    exact hp₂_ne (le_bot_iff.mp ((le_inf hr_V hr_notV).trans inf_compl_eq_bot.le))

def levyDecisionOpen (α : Ordinal.{u}) (b : InternalLevyStage κ α) : bSet (anonymousAlgebra κ) :=
  binary_union (levyTruthOpen α b) (levyTruthOpen α bᶜ)

theorem levyDecisionOpen_subset (α : Ordinal.{u}) (b : InternalLevyStage κ α) :
    (⊤ : anonymousAlgebra κ) ≤ levyDecisionOpen α b ⊆ᴮ internalLevyPoset κ α :=
  binary_union_subset (levyTruthOpen_subset α b) (levyTruthOpen_subset α bᶜ)

theorem levyDecisionOpen_dense (α : Ordinal.{u}) (b : InternalLevyStage κ α) :
    (⊤ : anonymousAlgebra κ) ≤ allIn (internalLevyPoset κ α) (fun g =>
      someIn (levyDecisionOpen α b) (fun r => g ⊆ᴮ r)) := by
  have htest := levyJoinTest_dense α (fun _ : PUnit.{u + 1} => b)
  refine allIn_intro fun {Γ} _ g hg => ?_
  refine (allIn_elim (le_top.trans htest) hg).trans (iSup_mono fun r => inf_le_inf_right _ ?_)
  obtain ⟨hr_P, hr_or⟩ := mem_levyJoinTest_iff.mp (le_refl (r ∈ᴮ levyJoinTest α (fun _ : PUnit.{u + 1} => b)))
  have hsup_eq : (⨆ _ : PUnit.{u + 1}, b) = b := ciSup_const
  rw [hsup_eq] at hr_or
  have h1 : (⨆ _ : PUnit.{u + 1}, levyReads α b r) ≤ levyReads α b r := iSup_le fun _ => le_rfl
  have hor' : r ∈ᴮ levyJoinTest α (fun _ : PUnit.{u + 1} => b) ≤
      (r ∈ᴮ internalLevyPoset κ α) ⊓ (levyReads α b r ⊔ levyReads α bᶜ r) :=
    le_inf hr_P (hr_or.trans (sup_le_sup_right h1 _))
  rw [inf_sup_left] at hor'
  rw [levyDecisionOpen, mem_binary_union]
  exact hor'.trans (sup_le_sup
    (mem_levyTruthOpen_iff.mpr ⟨inf_le_left, inf_le_right⟩)
    (mem_levyTruthOpen_iff.mpr ⟨inf_le_left, inf_le_right⟩))

end StageTruthOpenLaws

section SupportedDenseAndCardinality
variable {I : Type u} {κ θ : Cardinal.{u}}
variable (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]

def suppDenseFormula : InterpretedMaster.Formula Bool :=
  .allIn false (.someIn (some true) (.allIn (some none) (.mem none (some none))))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
private theorem suppDenseFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (D P : bSet B) :
    suppDenseFormula.eval (fun bl => if bl then D else P) =
      allIn P (fun g => someIn D (fun r => allIn g (fun x => x ∈ᴮ r))) :=
  rfl

theorem exists_supported_dense_test_extension {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (α : Ordinal.{u}) (D : I → bSet (anonymousAlgebra κ)) (hD : Preparation.Supported U a D)
    (hD_sub : ∀ i, (⊤ : anonymousAlgebra κ) ≤ D i ⊆ᴮ internalLevyPoset κ α)
    (hD_dense : ∀ i, (⊤ : anonymousAlgebra κ) ≤
      allIn (internalLevyPoset κ α) (fun g => someIn (D i) (fun r => g ⊆ᴮ r)))
    {Γ : W₁} {q₀ : bSet W₁}
    (hq₀ : Γ ≤ q₀ ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α))) :
    ∃ z : bSet W₁,
      Γ ≤ z ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α)) ∧
      Γ ≤ z ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a D) ∧
      Γ ≤ q₀ ⊆ᴮ z := by
  obtain ⟨ν, F_D, hF_D⟩ := hD
  let P_A := internalLevyPoset κ α
  let env (i : I) : Bool → bSet (anonymousAlgebra κ) :=
    fun bl => if bl then D i else P_A
  have henv : Preparation.SupportedEnv U a env :=
    ⟨ν, fun S bl => if bl then F_D S else P_A,
      hF_D.mono fun i hi => funext fun bl => by cases bl <;> simp [env, hi]⟩
  have hφ_W := transfer_supported_formula U a hk hf hn ht hκ j₀ suppDenseFormula env henv
    (Eventually.of_forall fun i => by
      rw [suppDenseFormula_eval]
      simp_rw [← subset_iff_allIn_mem]
      exact hD_dense i)
  let P_W := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => P_A))
  let D_W := mapNames j₀ (Preparation.boundedAnonName U a D)
  have henv_W : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun i => env i v))) =
      (fun bl => if bl then D_W else P_W) := by
    funext bl; cases bl <;> rfl
  rw [henv_W, suppDenseFormula_eval] at hφ_W
  simp_rw [← subset_iff_allIn_mem] at hφ_W
  have hex_W : Γ ≤ ⨆ r : bSet W₁, (r ∈ᴮ D_W) ⊓ (q₀ ⊆ᴮ r) :=
    allIn_elim (le_top.trans hφ_W) hq₀
  obtain ⟨z, hz⟩ := exists_convert hex_W (B_ext_inf B_ext_mem_left B_ext_subset_right)
  have hDP_VA : (⊤ : Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) ≤
      Preparation.boundedAnonName U a D ⊆ᴮ
        Preparation.boundedAnonName U a (fun _ => P_A) := by
    rw [← Preparation.boundedAnonName_subset U a hk hf hn ht hκ D (fun _ => P_A)
      ⟨ν, F_D, hF_D⟩ (Preparation.Supported.const P_A),
      value_eq_of_eventuallyEq U (g := fun _ => ⊤) (Eventually.of_forall fun i => top_unique (hD_sub i)),
      value_top]
  have hDP_W : (⊤ : W₁) ≤ D_W ⊆ᴮ P_W := by
    simpa only [TopHomClass.map_top, map_subset] using OrderHomClass.mono j₀ hDP_VA
  exact ⟨z, mem_of_mem_subset (le_top.trans hDP_W) (hz.trans inf_le_left),
    hz.trans inf_le_left, hz.trans inf_le_right⟩

theorem seed_gt_eventually [CardinalInterFilter (U : Filter I) κ]
    (hk : κ < θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (i₀ : κ.ord.ToType) :
    ∀ᶠ i in U, i₀ < Erdos1172Shioya.UltrapowerStage.repr U a
      (criticalOrdinalPoint U a hf hn ht hk) i := by
  let VA := Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
  let A := anonymousAlgebra κ
  let seed := criticalOrdinalPoint U a hf hn ht hk
  let o₁ : Ordinal.{u} := Order.succ i₀.toOrd.val
  have ho₁_lt : o₁ < κ.ord := (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt (toOrd_lt i₀)
  by_contra hnot
  have hev_le : ∀ᶠ i in U, Erdos1172Shioya.UltrapowerStage.repr U a seed i ≤ i₀ := by
    simpa only [not_lt] using U.eventually_not.mpr hnot
  let c_seed (i : I) : bSet A :=
    check (PSet.ordinalMk (Erdos1172Shioya.UltrapowerStage.repr U a seed i).toOrd.val)
  have hseed_supp : Preparation.Supported U a c_seed :=
    ⟨seed.property.choose,
      fun S => check (PSet.ordinalMk ((seed.property.choose_spec.choose S).toOrd.val)),
      EventuallyEq.rfl⟩
  have hVA_mem : (⊤ : VA) ≤
      Preparation.boundedAnonName U a c_seed ∈ᴮ
      Preparation.boundedAnonName U a (fun _ => check (PSet.ordinalMk o₁)) := by
    rw [← Preparation.boundedAnonName_mem U a hk.le hf hn ht hκ c_seed
      (fun _ => check (PSet.ordinalMk o₁)) hseed_supp (Preparation.Supported.const _),
      value_eq_of_eventuallyEq U (g := fun _ => ⊤) _, value_top]
    exact hev_le.mono fun i hi => top_unique (check_mem (PSet.mk_mem_mk_of_lt
      ((Subtype.mk_le_mk.mp (Ordinal.ToType.mk.symm.monotone hi)).trans_lt
        (Order.lt_succ i₀.toOrd.val))))
  have hκ_mem_o₁ : (⊤ : VA) ≤ (check (PSet.ordinalMk κ.ord) : bSet VA) ∈ᴮ check (PSet.ordinalMk o₁) :=
    mem_congr (Preparation.boundedAnon_seed U a hf hn ht hκ hk)
      (Preparation.boundedAnon_fix_below U a hk.le hf hn ht hκ ho₁_lt) hVA_mem
  rw [mem_unfold] at hκ_mem_o₁
  have hbot : (⊤ : VA) ≤ ⊥ := hκ_mem_o₁.trans (iSup_le fun k => by
    have hneqv : ¬PSet.Equiv (PSet.ordinalMk κ.ord) ((PSet.ordinalMk o₁).Func (check_cast k)) := by
      intro he
      have heq := Ordinal.toZFSet_injective (ZFSet.sound
        (PSet.Equiv.trans he (ordOfPSetIdx_equiv (check_cast k))))
      exact (ho₁_lt.not_ge (heq ▸ (ordOfPSetIdx_lt (check_cast k)).le)).elim
    rw [check_func, check_bval_top, top_inf_eq, check_bv_eq_bot_of_not_equiv hneqv])
  exact top_ne_bot (le_bot_iff.mp hbot)

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
private theorem strict_upper_bound_theta'' (hθ : θ.IsRegular)
    {D : Type u} (hD : #D < θ) (f : D → θ.ord.ToType) :
    ∃ b : θ.ord.ToType, ∀ d : D, f d < b := by
  by_contra! h
  have hc : IsCofinal (Set.range f) := fun x => by
    obtain ⟨d, hd⟩ := h x
    exact ⟨f d, Set.mem_range_self d, hd⟩
  have hh := Order.cof_le hc
  rw [Ordinal.cof_toType, hθ.cof_ord] at hh
  exact hD.not_ge (hh.trans Cardinal.mk_range_le)

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
theorem internalLevyAlgebra_cardinal_le (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible) :
    #(InternalLevyAlgebra κ θ) ≤ θ := by
  classical
  let F := InternalLevyAlgebra κ θ
  obtain ⟨D, hD_le, hD_dense⟩ := internalLevy_dense_size hk hκ hθ
  obtain ⟨e_D⟩ : Nonempty (D ↪ θ.ord.ToType) :=
    (Cardinal.le_def D θ.ord.ToType).mp (hD_le.trans_eq (Cardinal.mk_ord_toType θ).symm)
  have hcov (b : F) : (⨆ x : {d : D // condition d.val ≤ b}, condition x.val.val) = b := by
    apply le_antisymm (iSup_le fun x => x.property)
    by_contra hnot
    let S_join := ⨆ x : {d : D // condition d.val ≤ b}, condition x.val.val
    have hpos : b ⊓ S_joinᶜ ≠ ⊥ := fun h0 =>
      hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    obtain ⟨q, hq⟩ := exists_condition_le hpos
    obtain ⟨d, hdD, hdq⟩ := hD_dense q
    have hd_b : condition d ≤ b := (condition_mono hdq).trans (hq.trans inf_le_left)
    have hd_S : condition d ≤ S_join :=
      le_iSup (fun x : {d : D // condition d.val ≤ b} => condition x.val.val) ⟨⟨d, hdD⟩, hd_b⟩
    exact condition_ne_bot d
      (le_bot_iff.mp ((le_inf hd_S ((condition_mono hdq).trans (hq.trans inf_le_right))).trans
        inf_compl_eq_bot.le))
  choose Sub hSub_lt hSub_eq using fun b : F =>
    exists_small_subfamily θ (internalLevy_strictCC hk hκ hθ)
      (fun x : {d : D // condition d.val ≤ b} => condition x.val.val)
  choose ν_of hν_of using fun b : F =>
    strict_upper_bound_theta'' hθ.isRegular (hSub_lt b) (fun s : Sub b => e_D s.val.val)
  let Code := Σ ν : θ.ord.ToType, Set (Set.Iio ν)
  let encode (b : F) : Code :=
    ⟨ν_of b, {z : Set.Iio (ν_of b) | ∃ s : Sub b, e_D s.val.val = z.val}⟩
  have hmem_iff (b : F) (d : D) :
      (∃ hx : e_D d < (encode b).1, (⟨e_D d, hx⟩ : Set.Iio (encode b).1) ∈ (encode b).2) ↔
        ∃ s : Sub b, s.val.val = d := by
    constructor
    · rintro ⟨_, s, hs⟩
      exact ⟨s, e_D.injective hs⟩
    · rintro ⟨s, rfl⟩
      exact ⟨hν_of b s, s, rfl⟩
  have henc_inj : Function.Injective encode := by
    intro b₁ b₂ heq
    have hD_same (d : D) : (∃ s : Sub b₁, s.val.val = d) ↔ (∃ s : Sub b₂, s.val.val = d) := by
      rw [← hmem_iff b₁ d, ← hmem_iff b₂ d, heq]
    rw [← hcov b₁, ← hSub_eq b₁, ← hcov b₂, ← hSub_eq b₂]
    apply le_antisymm
    · refine iSup_le fun s₁ => ?_
      obtain ⟨s₂, hs₂⟩ := (hD_same s₁.val.val).mp ⟨s₁, rfl⟩
      exact (congrArg (fun d : D => condition d.val) hs₂.symm).le.trans
        (le_iSup (fun s : Sub b₂ => condition s.val.val.val) s₂)
    · refine iSup_le fun s₂ => ?_
      obtain ⟨s₁, hs₁⟩ := (hD_same s₂.val.val).mpr ⟨s₂, rfl⟩
      exact (congrArg (fun d : D => condition d.val) hs₁.symm).le.trans
        (le_iSup (fun s : Sub b₁ => condition s.val.val.val) s₁)
  apply (Cardinal.mk_le_of_injective henc_inj).trans
  rw [Cardinal.mk_sigma]
  have hpiece (ν : θ.ord.ToType) : #(Set (Set.Iio ν)) ≤ θ := by
    rw [Cardinal.mk_set]
    exact (hθ.isStrongPrelimit
      ((Cardinal.mk_Iio_lt ν (by simp)).trans_eq (Cardinal.mk_ord_toType θ))).le
  exact ((Cardinal.sum_le_sum _ _ hpiece).trans_eq (Cardinal.sum_const' _ θ)).trans_eq
    (by rw [Cardinal.mk_ord_toType, Cardinal.mul_eq_self hθ.aleph0_lt.le])

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
theorem small_func_cardinal_le (hθ : θ.IsInaccessible)
    {X Y : Type u} (hX : #X < θ) (hY : #Y ≤ θ) : #(X → Y) ≤ θ := by
  classical
  obtain ⟨e_Y⟩ : Nonempty (Y ↪ θ.ord.ToType) :=
    (Cardinal.le_def Y θ.ord.ToType).mp (hY.trans_eq (Cardinal.mk_ord_toType θ).symm)
  choose ν_of hν_of using fun f : X → Y =>
    strict_upper_bound_theta'' hθ.isRegular hX (fun x => e_Y (f x))
  let Code := Σ ν : θ.ord.ToType, (X → Set.Iio ν)
  let encode (f : X → Y) : Code := ⟨ν_of f, fun x => ⟨e_Y (f x), hν_of f x⟩⟩
  have henc_inj : Function.Injective encode := by
    intro f₁ f₂ heq
    funext x
    exact e_Y.injective (congrArg (fun c : Code => (c.2 x).val) heq)
  apply (Cardinal.mk_le_of_injective henc_inj).trans
  rw [Cardinal.mk_sigma]
  have hpiece (ν : θ.ord.ToType) : #(X → Set.Iio ν) ≤ θ := by
    let gr (g : X → Set.Iio ν) : Set (X × Set.Iio ν) := {p | g p.1 = p.2}
    have hgr_inj : Function.Injective gr := fun g₁ g₂ he =>
      funext fun x => (he ▸ (show (x, g₁ x) ∈ gr g₁ from rfl) : (x, g₁ x) ∈ gr g₂).symm
    apply (Cardinal.mk_le_of_injective hgr_inj).trans
    rw [Cardinal.mk_set, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    have hν_lt : #(Set.Iio ν) < θ :=
      (Cardinal.mk_Iio_lt ν (by simp)).trans_eq (Cardinal.mk_ord_toType θ)
    exact (hθ.isStrongPrelimit (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hX hν_lt)).le
  exact ((Cardinal.sum_le_sum _ _ hpiece).trans_eq (Cardinal.sum_const' _ θ)).trans_eq
    (by rw [Cardinal.mk_ord_toType, Cardinal.mul_eq_self hθ.aleph0_lt.le])

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
theorem array_factors_at_stage (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    {X : Type u} (hX : #X < θ) (v : X → InternalLevyAlgebra κ θ) :
    ∃ (α : Ordinal.{u}) (hα : α < θ.ord) (v_α : X → InternalLevyStage κ α),
      ∀ x, stageStepHom hα.le (v_α x) = v x := by
  have hb_le {i j : θ.ord.ToType} (hij : i ≤ j) :
      Order.succ i.toOrd.val ≤ Order.succ j.toOrd.val :=
    Order.succ_le_succ (Ordinal.ToType.mk.symm.monotone hij)
  obtain ⟨i, f, hf⟩ := source_array_from_stage
    (B := fun i : θ.ord.ToType => InternalLevyStage κ (Order.succ i.toOrd.val))
    (fun {_ _} hij => stageStepHom (hb_le hij))
    (fun i => stageStepHom (Order.succ_le_of_lt (toOrd_lt i)))
    (fun {_ _} hij y => stageStepHom_comp (hb_le hij) _ y)
    hθ (internalLevy_strictCC hk hκ hθ) (internalLevy_denseStageUnion hk hκ hθ) hX v
  exact ⟨Order.succ i.toOrd.val,
    (Cardinal.isSuccLimit_ord hθ.aleph0_lt.le).succ_lt (toOrd_lt i), f, hf⟩

end SupportedDenseAndCardinality

section TransfiniteValuation
variable {I : Type u} {κ θ : Cardinal.{u}}
variable (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem decide_pair_of_disjoint {L : Type u} [BooleanAlgebra L] {c u₁ u₂ v : L}
    (hp : c ⊓ v ≤ u₁) (hn : c ⊓ vᶜ ≤ u₂) (hd : u₁ ⊓ u₂ = ⊥) :
    c ⊓ u₁ = c ⊓ v ∧ c ⊓ u₂ = c ⊓ vᶜ := by
  have hu₂_compl : u₂ ≤ u₁ᶜ := le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr ((inf_comm u₂ u₁).trans hd))
  have hu₁_compl : u₁ ≤ u₂ᶜ := le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hd)
  exact ⟨cone_eq_of_le_and_compl_le hp (hn.trans hu₂_compl),
    cone_eq_of_le_and_compl_le hn ((compl_compl v).symm ▸ hp.trans hu₁_compl)⟩

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem inf_cone_distrib {L : Type u} [BooleanAlgebra L] (c x y : L) :
    (c ⊓ x) ⊓ (c ⊓ y) = c ⊓ (x ⊓ y) := by
  ac_rfl

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem cone_neg_from_or {L : Type u} [BooleanAlgebra L] {c r_pos w_pos w_neg : L}
    (h1 : c ⊓ r_posᶜ ≤ w_posᶜ) (hor : c ≤ w_pos ⊔ w_neg) :
    c ⊓ r_posᶜ ≤ w_neg := by
  calc
    c ⊓ r_posᶜ ≤ c ⊓ w_posᶜ := le_inf inf_le_left h1
    _ ≤ (w_pos ⊔ w_neg) ⊓ w_posᶜ := inf_le_inf_right w_posᶜ hor
    _ = (w_pos ⊓ w_posᶜ) ⊔ (w_neg ⊓ w_posᶜ) := inf_sup_right _ _ _
    _ ≤ w_neg := by rw [inf_compl_eq_bot, bot_sup_eq]; exact inf_le_left

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem cone_le_from_cover {L : Type u} [BooleanAlgebra L] {c u d : L}
    (hcov : c ≤ (c ⊓ u) ⊔ (c ⊓ dᶜ)) : c ⊓ d ≤ c ⊓ u := by
  calc
    c ⊓ d ≤ ((c ⊓ u) ⊔ (c ⊓ dᶜ)) ⊓ d := inf_le_inf_right d hcov
    _ = ((c ⊓ u) ⊓ d) ⊔ ((c ⊓ dᶜ) ⊓ d) := inf_sup_right _ _ _
    _ ≤ (c ⊓ u) ⊔ (dᶜ ⊓ d) := sup_le_sup inf_le_left (inf_le_inf_right d inf_le_right)
    _ = c ⊓ u := by rw [compl_inf_eq_bot, sup_bot_eq]

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem cone_normal_from_reg {K R L : Type u}
    [CompleteBooleanAlgebra R] [CompleteBooleanAlgebra L]
    (j_R : CompleteLatticeHom R L) {c w_diag : L} {w_row : K → L} {u_row : K → R} {u_diag : R}
    (hreg : c ≤ (⨆ l : K, w_row l) ⊔ w_diag)
    (hrow_up : ∀ l : K, c ⊓ w_row l ≤ c ⊓ j_R (u_row l))
    (hdiag_up : c ⊓ w_diag ≤ c ⊓ (j_R u_diag)ᶜ) :
    c ⊓ j_R u_diag ≤ c ⊓ j_R (⨆ l : K, u_row l) := by
  refine cone_le_from_cover ?_
  calc
    c ≤ c ⊓ ((⨆ l : K, w_row l) ⊔ w_diag) := le_inf le_rfl hreg
    _ = (c ⊓ ⨆ l : K, w_row l) ⊔ (c ⊓ w_diag) := inf_sup_left _ _ _
    _ ≤ (c ⊓ j_R (⨆ l : K, u_row l)) ⊔ (c ⊓ (j_R u_diag)ᶜ) := by
      refine sup_le_sup ?_ hdiag_up
      rw [inf_iSup_eq, _root_.map_iSup j_R, inf_iSup_eq]
      exact iSup_mono hrow_up

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem sup_eq_compl_inf_compl {B : Type u} [BooleanAlgebra B] (x y : B) :
    x ⊔ y = (xᶜ ⊓ yᶜ)ᶜ := by
  rw [compl_inf, compl_compl, compl_compl]

def stageUpFormula : InterpretedMaster.Formula (Fin 3) :=
  .allIn 0 (.allIn (some 1)
    (.imp (.allIn (some none) (.mem none (some none))) (.mem none (some (some 2)))))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem stageUpFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (O₁ P₂ O₂ : bSet B) :
    stageUpFormula.eval ![O₁, P₂, O₂] =
      allIn O₁ (fun g₁ => allIn P₂ (fun g₂ => _root_.imp (allIn g₁ (fun x => x ∈ᴮ g₂)) (g₂ ∈ᴮ O₂))) :=
  rfl

omit [CardinalInterFilter (U : Filter I) κ] in
private theorem liftedTruthOpen_stage_upward {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (seed_idx : I → κ.ord.ToType) (hseed : Preparation.Supported U a seed_idx)
    {α₁ α₂ : Ordinal.{u}} (h : α₁ ≤ α₂) (Y : κ.ord.ToType → InternalLevyStage κ α₁)
    {Γ : W₁} {q₁ q₂ : bSet W₁}
    (hq₁ : Γ ≤ q₁ ∈ᴮ mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a
      (fun i => levyTruthOpen α₁ (Y (seed_idx i)))))
    (hq₂ : Γ ≤ q₂ ∈ᴮ mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a
      (fun _ => internalLevyPoset κ α₂)))
    (hsub : Γ ≤ q₁ ⊆ᴮ q₂) :
    Γ ≤ q₂ ∈ᴮ mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a
      (fun i => levyTruthOpen α₂ (stageStepHom (κ := κ) h (Y (seed_idx i))))) := by
  obtain ⟨ν_s, f_s, hf_s⟩ := hseed
  let A := anonymousAlgebra κ
  let env (i : I) : Fin 3 → bSet A :=
    ![levyTruthOpen α₁ (Y (seed_idx i)),
      internalLevyPoset κ α₂,
      levyTruthOpen α₂ (stageStepHom (κ := κ) h (Y (seed_idx i)))]
  have henv : Preparation.SupportedEnv U a env :=
    ⟨ν_s, fun S => ![levyTruthOpen α₁ (Y (f_s S)), internalLevyPoset κ α₂,
      levyTruthOpen α₂ (stageStepHom (κ := κ) h (Y (f_s S)))],
      hf_s.mono fun i hi => congrArg
        (fun k => ![levyTruthOpen α₁ (Y k), internalLevyPoset κ α₂,
          levyTruthOpen α₂ (stageStepHom (κ := κ) h (Y k))]) hi.symm⟩
  have hφ_W := transfer_supported_formula U a hk hf hn ht hκ j₀ stageUpFormula env henv
    (Eventually.of_forall fun i => by
      rw [stageUpFormula_eval]
      refine allIn_intro fun {Δ₁} _ g₁ hg₁ =>
        allIn_intro fun {Δ₂} hΔ g₂ hg₂ => deduction.mp ?_
      rw [← subset_iff_allIn_mem (X := g₁) (Y := g₂)]
      exact levyTruthOpen_stage_upward h (inf_le_left.trans (hΔ.trans hg₁))
        (inf_le_left.trans hg₂) inf_le_right)
  have henv_W : (fun v => mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a (fun i => env i v))) =
      ![mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a (fun i => levyTruthOpen α₁ (Y (seed_idx i)))),
        mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a (fun _ => internalLevyPoset κ α₂)),
        mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a
          (fun i => levyTruthOpen α₂ (stageStepHom (κ := κ) h (Y (seed_idx i)))))] := by
    funext idx; fin_cases idx <;> rfl
  rw [henv_W, stageUpFormula_eval] at hφ_W
  have himp := allIn_elim (allIn_elim (le_top.trans hφ_W) hq₁) hq₂
  rw [← subset_iff_allIn_mem (X := q₁) (Y := q₂)] at himp
  exact (le_inf himp hsub).trans bv_imp_elim

def disjBoolFormula : InterpretedMaster.Formula Bool :=
  .allIn true (.neg (.mem none (some false)))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem disjBoolFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (O₁ O₂ : bSet B) :
    disjBoolFormula.eval (fun bl => if bl then O₁ else O₂) = allIn O₁ (fun z => (z ∈ᴮ O₂)ᶜ) :=
  rfl

omit [CardinalInterFilter (U : Filter I) κ] in
private theorem liftedTruthOpen_disjoint {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (seed_idx : I → κ.ord.ToType) (hseed : Preparation.Supported U a seed_idx)
    (α : Ordinal.{u}) (Y : κ.ord.ToType → InternalLevyStage κ α) (q : bSet W₁) :
    (q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (Y (seed_idx i))))) ⊓
      (q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (Y (seed_idx i))ᶜ))) = ⊥ := by
  obtain ⟨ν_s, f_s, hf_s⟩ := hseed
  let env (i : I) : Bool → bSet (anonymousAlgebra κ) := fun bl =>
    if bl then levyTruthOpen α (Y (seed_idx i)) else levyTruthOpen α (Y (seed_idx i))ᶜ
  have henv : Preparation.SupportedEnv U a env :=
    ⟨ν_s, fun S bl => if bl then levyTruthOpen α (Y (f_s S)) else levyTruthOpen α (Y (f_s S))ᶜ,
      hf_s.mono fun i hi => funext fun bl => by cases bl <;> simp [env, hi]⟩
  have hφ_W := transfer_supported_formula U a hk hf hn ht hκ j₀ disjBoolFormula env henv
    (Eventually.of_forall fun i => by
      rw [disjBoolFormula_eval]
      exact allIn_intro fun _ z hz => hz.trans
        (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr (levyTruthOpen_disjoint α _ z))))
  let O₁ := mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (Y (seed_idx i))))
  let O₂ := mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (Y (seed_idx i))ᶜ))
  have henv_W : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun i => env i v))) =
      (fun bl => if bl then O₁ else O₂) := by
    funext bl; cases bl <;> rfl
  rw [henv_W, disjBoolFormula_eval] at hφ_W
  exact disjoint_iff.mp (le_compl_iff_disjoint_right.mp
    (allIn_elim (le_top.trans hφ_W) (le_rfl : (q ∈ᴮ O₁) ≤ q ∈ᴮ O₁)))

omit [CardinalInterFilter (U : Filter I) κ] in
private theorem liftedTruthOpen_bot {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (α : Ordinal.{u}) {Γ : W₁} {q : bSet W₁}
    (hq : Γ ≤ q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α))) :
    Γ ⊓ (q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => levyTruthOpen α ⊥))) = ⊥ := by
  let P_A := internalLevyPoset κ α
  let O_A := levyTruthOpen (κ := κ) α ⊥
  let env : Bool → bSet (anonymousAlgebra κ) := fun bl => if bl then P_A else O_A
  have hφ_W := transfer_const_formula U a hk hf hn ht hκ j₀ disjBoolFormula env (by
    rw [disjBoolFormula_eval]
    exact allIn_intro fun _ z hz => hz.trans
      (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr (levyTruthOpen_bot_disjoint α z))))
  let P_W := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => P_A))
  let O_W := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => O_A))
  have henv_W : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun _ => env v))) =
      (fun bl => if bl then P_W else O_W) := by
    funext bl; cases bl <;> rfl
  rw [henv_W, disjBoolFormula_eval] at hφ_W
  exact le_bot_iff.mp ((inf_le_inf_right (q ∈ᴮ O_W) (allIn_elim (le_top.trans hφ_W) hq)).trans
    compl_inf_eq_bot.le)

def infOpenFormula : InterpretedMaster.Formula (Fin 4) :=
  .allIn 0 (.both
    (.imp (.mem none (some 1)) (.both (.mem none (some 2)) (.mem none (some 3))))
    (.imp (.both (.mem none (some 2)) (.mem none (some 3))) (.mem none (some 1))))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem infOpenFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (P O₁₂ O₁ O₂ : bSet B) :
    infOpenFormula.eval ![P, O₁₂, O₁, O₂] =
      allIn P (fun z =>
        _root_.imp (z ∈ᴮ O₁₂) ((z ∈ᴮ O₁) ⊓ (z ∈ᴮ O₂)) ⊓
          _root_.imp ((z ∈ᴮ O₁) ⊓ (z ∈ᴮ O₂)) (z ∈ᴮ O₁₂)) :=
  rfl

omit [CardinalInterFilter (U : Filter I) κ] in
private theorem liftedTruthOpen_inf {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (seed_idx : I → κ.ord.ToType) (hseed : Preparation.Supported U a seed_idx)
    (α : Ordinal.{u}) (Y₁ Y₂ : κ.ord.ToType → InternalLevyStage κ α)
    {Γ : W₁} {q : bSet W₁}
    (hq : Γ ≤ q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α))) :
    Γ ⊓ (q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (Y₁ (seed_idx i) ⊓ Y₂ (seed_idx i))))) =
      (Γ ⊓ (q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (Y₁ (seed_idx i)))))) ⊓
        (Γ ⊓ (q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (Y₂ (seed_idx i)))))) := by
  obtain ⟨ν_s, f_s, hf_s⟩ := hseed
  let env (i : I) : Fin 4 → bSet (anonymousAlgebra κ) :=
    ![internalLevyPoset κ α,
      levyTruthOpen α (Y₁ (seed_idx i) ⊓ Y₂ (seed_idx i)),
      levyTruthOpen α (Y₁ (seed_idx i)),
      levyTruthOpen α (Y₂ (seed_idx i))]
  have henv : Preparation.SupportedEnv U a env :=
    ⟨ν_s, fun S => ![internalLevyPoset κ α,
      levyTruthOpen α (Y₁ (f_s S) ⊓ Y₂ (f_s S)),
      levyTruthOpen α (Y₁ (f_s S)),
      levyTruthOpen α (Y₂ (f_s S))],
      hf_s.mono fun i hi => funext fun idx => by fin_cases idx <;> simp [env, hi]⟩
  have hφ_W := transfer_supported_formula U a hk hf hn ht hκ j₀ infOpenFormula env henv
    (Eventually.of_forall fun i => by
      rw [infOpenFormula_eval]
      exact allIn_intro fun _ z _ => le_inf
        (deduction.mp (inf_le_right.trans_eq (levyTruthOpen_inf_eq α _ _ z)))
        (deduction.mp (inf_le_right.trans_eq (levyTruthOpen_inf_eq α _ _ z).symm)))
  let P_W := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α))
  let O₁₂ := mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (Y₁ (seed_idx i) ⊓ Y₂ (seed_idx i))))
  let O₁ := mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (Y₁ (seed_idx i))))
  let O₂ := mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (Y₂ (seed_idx i))))
  have henv_W : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun i => env i v))) =
      ![P_W, O₁₂, O₁, O₂] := by
    funext idx; fin_cases idx <;> rfl
  rw [henv_W, infOpenFormula_eval] at hφ_W
  have hq_iff := allIn_elim (le_top.trans hφ_W) hq
  apply le_antisymm
  · have h12 : Γ ⊓ (q ∈ᴮ O₁₂) ≤ (q ∈ᴮ O₁) ⊓ (q ∈ᴮ O₂) :=
      (le_inf (inf_le_left.trans (hq_iff.trans inf_le_left)) inf_le_right).trans bv_imp_elim
    exact le_inf
      (le_inf inf_le_left (h12.trans inf_le_left))
      (le_inf inf_le_left (h12.trans inf_le_right))
  · refine le_inf (inf_le_left.trans inf_le_left) ?_
    exact (le_inf ((inf_le_left.trans inf_le_left).trans (hq_iff.trans inf_le_right))
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))).trans bv_imp_elim

def decOrFormula : InterpretedMaster.Formula (Fin 3) :=
  .allIn 0 (.either (.mem none (some 1)) (.mem none (some 2)))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem decOrFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (D O₁ O₂ : bSet B) :
    decOrFormula.eval ![D, O₁, O₂] = allIn D (fun g => (g ∈ᴮ O₁) ⊔ (g ∈ᴮ O₂)) :=
  rfl

omit [CardinalInterFilter (U : Filter I) κ] in
private theorem liftedDecisionOpen_or {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (seed_idx : I → κ.ord.ToType) (hseed : Preparation.Supported U a seed_idx)
    (α : Ordinal.{u}) (X_β : κ.ord.ToType → InternalLevyStage κ α)
    {Γ : W₁} {q : bSet W₁}
    (hq : Γ ≤ q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a
      (fun i => levyDecisionOpen α (X_β (seed_idx i))))) :
    Γ ≤ (q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (X_β (seed_idx i))))) ⊔
      (q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (X_β (seed_idx i))ᶜ))) := by
  obtain ⟨ν_s, f_s, hf_s⟩ := hseed
  let env_u (i : I) : Fin 3 → bSet (anonymousAlgebra κ) :=
    ![levyDecisionOpen α (X_β (seed_idx i)),
      levyTruthOpen α (X_β (seed_idx i)),
      levyTruthOpen α (X_β (seed_idx i))ᶜ]
  have henv_u : Preparation.SupportedEnv U a env_u :=
    ⟨ν_s, fun S => ![levyDecisionOpen α (X_β (f_s S)),
      levyTruthOpen α (X_β (f_s S)), levyTruthOpen α (X_β (f_s S))ᶜ],
      hf_s.mono fun i hi => funext fun idx => by fin_cases idx <;> simp [env_u, hi]⟩
  have hφ_W := transfer_supported_formula U a hk hf hn ht hκ j₀ decOrFormula env_u henv_u
    (Eventually.of_forall fun i => by
      rw [decOrFormula_eval]
      exact allIn_intro fun _ g hg => hg.trans_eq (mem_binary_union _ _ g))
  let D_W := mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyDecisionOpen α (X_β (seed_idx i))))
  let O₁ := mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (X_β (seed_idx i))))
  let O₂ := mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (X_β (seed_idx i))ᶜ))
  have henv_W : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun i => env_u i v))) =
      ![D_W, O₁, O₂] := by
    funext idx; fin_cases idx <;> rfl
  rw [henv_W, decOrFormula_eval] at hφ_W
  exact allIn_elim (le_top.trans hφ_W) hq

def regFormula : InterpretedMaster.Formula (Fin 4) :=
  .allIn 0 (.either
    (.someIn (some 1) (.edge (some (some 2)) none (some none)))
    (.mem none (some 3)))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem regFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (D S R O : bSet B) :
    regFormula.eval ![D, S, R, O] =
      allIn D (fun g => someIn S (fun x => edge R x g) ⊔ (g ∈ᴮ O)) :=
  rfl

def fibFormula : InterpretedMaster.Formula (Fin 4) :=
  .allIn 0 (.imp (.edge (some 1) (some 2) none) (.mem none (some 3)))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem fibFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (P R L O : bSet B) :
    fibFormula.eval ![P, R, L, O] = allIn P (fun g => _root_.imp (edge R L g) (g ∈ᴮ O)) :=
  rfl

private theorem liftedRegressiveTest_or {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ < θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (α : Ordinal.{u}) (H_β : κ.ord.ToType → κ.ord.ToType → InternalLevyStage κ α)
    {Γ : W₁} {q : bSet W₁}
    (hq_P : Γ ≤ q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α)))
    (hq_D : Γ ≤ q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i =>
      let s := Erdos1172Shioya.UltrapowerStage.repr U a (criticalOrdinalPoint U a hf hn ht hk) i
      levyJoinTest α (fun l : Set.Iio s => H_β l.val s)))) :
    let seed_idx (i : I) := Erdos1172Shioya.UltrapowerStage.repr U a (criticalOrdinalPoint U a hf hn ht hk) i
    Γ ≤ (⨆ l : κ.ord.ToType,
        q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (H_β l (seed_idx i))))) ⊔
      (q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (diagonal κ H_β (seed_idx i))ᶜ))) := by
  intro seed_idx
  let A := anonymousAlgebra κ
  let seed := criticalOrdinalPoint U a hf hn ht hk
  have hseed : Preparation.Supported U a seed_idx :=
    ⟨seed.property.choose, seed.property.choose_spec.choose,
      Germ.coe_eq.mp ((Erdos1172Shioya.UltrapowerStage.repr_eq U a seed).trans
        seed.property.choose_spec.choose_spec.symm)⟩
  obtain ⟨ν_s, f_s, hf_s⟩ := hseed
  let D_H (i : I) : bSet A := levyJoinTest α (fun l : Set.Iio (seed_idx i) => H_β l.val (seed_idx i))
  let R_rel (k : κ.ord.ToType) : bSet A := levyRowRelation α (fun l => H_β l k)
  let env_reg (i : I) : Fin 4 → bSet A :=
    ![D_H i, ordinalLabel (seed_idx i), R_rel (seed_idx i),
      levyTruthOpen α (diagonal κ H_β (seed_idx i))ᶜ]
  have henv_reg : Preparation.SupportedEnv U a env_reg :=
    ⟨ν_s, fun S => ![levyJoinTest α (fun l : Set.Iio (f_s S) => H_β l.val (f_s S)),
      ordinalLabel (f_s S), R_rel (f_s S),
      levyTruthOpen α (diagonal κ H_β (f_s S))ᶜ],
      hf_s.mono fun i hi => congrArg
        (fun k => ![levyJoinTest α (fun l : Set.Iio k => H_β l.val k),
          ordinalLabel k, R_rel k, levyTruthOpen α (diagonal κ H_β k)ᶜ]) hi.symm⟩
  have hφ_W := transfer_supported_formula U a hk.le hf hn ht hκ j₀ regFormula env_reg henv_reg
    (Eventually.of_forall fun i => by
      rw [regFormula_eval]
      exact allIn_intro fun _ g hg => by
        have hm := hg.trans_eq (levyRegressiveTest_mem α H_β (seed_idx i) g)
        rw [inf_sup_left] at hm
        exact hm.trans (sup_le_sup inf_le_right
          (mem_levyTruthOpen_iff.mpr ⟨inf_le_left, inf_le_right⟩)))
  let D_W := mapNames j₀ (Preparation.boundedAnonName U a D_H)
  let S_W := mapNames j₀ (Preparation.boundedAnonName U a (fun i => ordinalLabel (seed_idx i)))
  let R_W := mapNames j₀ (Preparation.boundedAnonName U a (fun i => R_rel (seed_idx i)))
  let O_diag := mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (diagonal κ H_β (seed_idx i))ᶜ))
  have henv_W : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun i => env_reg i v))) =
      ![D_W, S_W, R_W, O_diag] := by
    funext idx; fin_cases idx <;> rfl
  rw [henv_W, regFormula_eval] at hφ_W
  have hhit := allIn_elim (le_top.trans hφ_W) hq_D
  have hS_eq : (⊤ : W₁) ≤ S_W =ᴮ ordinalCarrier κ.ord := by
    have hm := OrderHomClass.mono j₀ (Preparation.boundedAnon_seed U a hf hn ht hκ hk)
    rw [TopHomClass.map_top, map_bv_eq, map_check] at hm
    exact hm
  have hsome_le : Γ ⊓ someIn S_W (fun x => edge R_W x q) ≤
      ⨆ l : κ.ord.ToType, q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (H_β l (seed_idx i)))) := by
    have hs1 : someIn S_W (fun x => edge R_W x q) ≤
        someIn (ordinalCarrier κ.ord) (fun x => edge R_W x q) :=
      bv_rw'' (ϕ := fun Z => someIn Z (fun x => edge R_W x q)) (le_top.trans hS_eq) le_rfl
        (someIn_ext id_congr fun _ => B_ext_const)
    dsimp only [edge] at hs1
    rw [someIn_checked _ _ B_ext_pair_mem_left] at hs1
    apply ((inf_le_inf_left Γ hs1).trans_eq (inf_iSup_eq Γ _)).trans
    refine iSup_le fun l => ?_
    have hl_chk : (⊤ : W₁) ≤ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => ordinalLabel l)) =ᴮ
        ordinalLabel l := by
      have hm := OrderHomClass.mono j₀
        (Preparation.boundedAnon_fix_below U a hk.le hf hn ht hκ (toOrd_lt l))
      simpa only [ordinalLabel, TopHomClass.map_top, map_bv_eq, map_check] using hm
    let env_fib (i : I) : Fin 4 → bSet A :=
      ![internalLevyPoset κ α, R_rel (seed_idx i), ordinalLabel l,
        levyTruthOpen α (H_β l (seed_idx i))]
    have henv_fib : Preparation.SupportedEnv U a env_fib :=
      ⟨ν_s, fun S => ![internalLevyPoset κ α, R_rel (f_s S), ordinalLabel l,
        levyTruthOpen α (H_β l (f_s S))],
        hf_s.mono fun i hi => funext fun m => by fin_cases m <;> simp [env_fib, R_rel, hi]⟩
    have hfib_W := transfer_supported_formula U a hk.le hf hn ht hκ j₀ fibFormula env_fib henv_fib
      (Eventually.of_forall fun i => by
        rw [fibFormula_eval]
        exact allIn_intro fun _ g hg => deduction.mp
          (mem_levyTruthOpen_iff.mpr ⟨inf_le_left.trans hg,
            inf_le_right.trans_eq (levyRowRelation_fiber α _ l g)⟩))
    let P_W := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α))
    let L_W := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => ordinalLabel l))
    let O_l := mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (H_β l (seed_idx i))))
    have henv_fib_W : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun i => env_fib i v))) =
        ![P_W, R_W, L_W, O_l] := by
      funext m; fin_cases m <;> rfl
    rw [henv_fib_W, fibFormula_eval] at hfib_W
    have hedge_l : Γ ⊓ (pair (ordinalLabel l) q ∈ᴮ R_W) ≤ edge R_W L_W q :=
      mem_congr (pair_congr (le_top.trans (bv_symm hl_chk)) bv_refl) bv_refl inf_le_right
    exact ((le_inf (inf_le_left.trans (allIn_elim (le_top.trans hfib_W) hq_P)) hedge_l).trans
      bv_imp_elim).trans (le_iSup (fun m : κ.ord.ToType =>
        q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (H_β m (seed_idx i))))) l)
  calc
    Γ ≤ Γ ⊓ (someIn S_W (fun x => edge R_W x q) ⊔ (q ∈ᴮ O_diag)) := le_inf le_rfl hhit
    _ = (Γ ⊓ someIn S_W (fun x => edge R_W x q)) ⊔ (Γ ⊓ (q ∈ᴮ O_diag)) := inf_sup_left _ _ _
    _ ≤ (⨆ l : κ.ord.ToType,
          q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun i => levyTruthOpen α (H_β l (seed_idx i))))) ⊔
        (q ∈ᴮ O_diag) := sup_le_sup hsome_le inf_le_right

structure ValuationStepState (R : Type u) [NontrivialCompleteBooleanAlgebra R] : Type (u + 1) where
  p : bSet R
  hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p
  α : Ordinal.{u}
  hα : α < θ.ord
  G : SmallGroundLevyGraph U a θ α R
  r : R

def ValuationGoodStep
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {m₀ : bSet (AmbientInternalLevy κ θ)}
    (hm₀ : (⊤ : AmbientInternalLevy κ θ) ≤ ErdosCohen.condition omegaOne m₀)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))
      (LocalizedSourceCohen (AmbientInternalLevy κ θ) m₀ hm₀))
    (rowStage : (κ.ord.ToType → InternalLevyAlgebra κ θ) → Ordinal.{u})
    (rowRep : ∀ X : κ.ord.ToType → InternalLevyAlgebra κ θ,
      κ.ord.ToType → InternalLevyStage κ (rowStage X))
    (matStage : (κ.ord.ToType → κ.ord.ToType → InternalLevyAlgebra κ θ) → Ordinal.{u})
    (matRep : ∀ H : κ.ord.ToType → κ.ord.ToType → InternalLevyAlgebra κ θ,
      κ.ord.ToType → κ.ord.ToType → InternalLevyStage κ (matStage H))
    (t : (κ.ord.ToType → InternalLevyAlgebra κ θ) ⊕
      (κ.ord.ToType → κ.ord.ToType → InternalLevyAlgebra κ θ))
    (β : θ.ord.ToType)
    (prev : Set.Iio β → ValuationStepState U a (AmbientInternalLevy κ θ))
    (s : ValuationStepState U a (AmbientInternalLevy κ θ)) : Prop :=
  let R := AmbientInternalLevy κ θ
  let j_R := localizedFirstStageHom hm₀
  let seed_idx (i : I) := Erdos1172Shioya.UltrapowerStage.repr U a (criticalOrdinalPoint U a hf hn ht hk) i
  let P_W (α : Ordinal.{u}) :=
    mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a (fun _ => internalLevyPoset κ α))
  let O_lift (α : Ordinal.{u}) (Y : κ.ord.ToType → InternalLevyStage κ α) :=
    mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a (fun i => levyTruthOpen α (Y (seed_idx i))))
  (match t with | Sum.inl X => rowStage X | Sum.inr H => matStage H) ≤ s.α ∧
  (∀ γ : Set.Iio β, (prev γ).α ≤ s.α) ∧
  (∃ hsub_m₀ : (⊤ : R) ≤ m₀ ⊆ᴮ s.p,
    (∀ γ : Set.Iio β, (⊤ : R) ≤ (prev γ).p ⊆ᴮ s.p) ∧
    (⊤ : R) ≤ (stageMasterGraph U a hk hκ hθ hf hn ht s.hα).toBSet ⊆ᴮ s.G.toBSet ∧
    (∀ γ : Set.Iio β, (⊤ : R) ≤ (prev γ).G.toBSet ⊆ᴮ s.G.toBSet) ∧
    coneInMaster hm₀ s.hp hsub_m₀ ≤ mapNames j_R s.G.toBSet ∈ᴮ P_W s.α ∧
    match t with
    | Sum.inl X =>
      ∀ (h_le : rowStage X ≤ s.α),
        let X_s (k : κ.ord.ToType) := stageStepHom (κ := κ) h_le (rowRep X k)
        coneInMaster hm₀ s.hp hsub_m₀ ⊓ j_R s.r ≤
          mapNames j_R s.G.toBSet ∈ᴮ O_lift s.α X_s ∧
        coneInMaster hm₀ s.hp hsub_m₀ ⊓ (j_R s.r)ᶜ ≤
          mapNames j_R s.G.toBSet ∈ᴮ O_lift s.α (fun k => (X_s k)ᶜ)
    | Sum.inr H =>
      ∀ (h_le : matStage H ≤ s.α),
        let H_s (l k : κ.ord.ToType) := stageStepHom (κ := κ) h_le (matRep H l k)
        coneInMaster hm₀ s.hp hsub_m₀ ≤
          (⨆ l : κ.ord.ToType, mapNames j_R s.G.toBSet ∈ᴮ O_lift s.α (H_s l)) ⊔
            (mapNames j_R s.G.toBSet ∈ᴮ O_lift s.α (fun k => (diagonal κ H_s k)ᶜ)))

private theorem exists_valuationGoodStep
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {m₀ : bSet (AmbientInternalLevy κ θ)}
    (hm₀ : (⊤ : AmbientInternalLevy κ θ) ≤ ErdosCohen.condition omegaOne m₀)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))
      (LocalizedSourceCohen (AmbientInternalLevy κ θ) m₀ hm₀))
    (hj₀_sub : (⊤ : LocalizedSourceCohen (AmbientInternalLevy κ θ) m₀ hm₀) ≤
      mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a (fun _ => anonymousSubset κ)) =ᴮ
        mapNames (LocalizedBelow.restrict (masterPositive m₀ hm₀))
          (Erdos1172CohenIteration.subsetName (B := AmbientInternalLevy κ θ) (PSet.ordinalMk θ.ord)))
    (rowStage : (κ.ord.ToType → InternalLevyAlgebra κ θ) → Ordinal.{u})
    (hrowStage : ∀ X, rowStage X < θ.ord)
    (rowRep : ∀ X : κ.ord.ToType → InternalLevyAlgebra κ θ,
      κ.ord.ToType → InternalLevyStage κ (rowStage X))
    (matStage : (κ.ord.ToType → κ.ord.ToType → InternalLevyAlgebra κ θ) → Ordinal.{u})
    (hmatStage : ∀ H, matStage H < θ.ord)
    (matRep : ∀ H : κ.ord.ToType → κ.ord.ToType → InternalLevyAlgebra κ θ,
      κ.ord.ToType → κ.ord.ToType → InternalLevyStage κ (matStage H))
    (taskAt : θ.ord.ToType →
      (κ.ord.ToType → InternalLevyAlgebra κ θ) ⊕
      (κ.ord.ToType → κ.ord.ToType → InternalLevyAlgebra κ θ))
    (β : θ.ord.ToType)
    (prev : Set.Iio β → ValuationStepState U a (AmbientInternalLevy κ θ))
    (ih : ∀ γ : Set.Iio β,
      ValuationGoodStep U a hk hκ hθ hf hn ht hm₀ j₀ rowStage rowRep matStage matRep
        (taskAt γ.val) γ.val
        (fun δ => prev ⟨δ.val, Set.mem_Iio.mpr ((Set.mem_Iio.mp δ.property).trans (Set.mem_Iio.mp γ.property))⟩)
        (prev γ)) :
    ∃ s, ValuationGoodStep U a hk hκ hθ hf hn ht hm₀ j₀ rowStage rowRep matStage matRep
      (taskAt β) β prev s := by
  classical
  let A := anonymousAlgebra κ
  let R := AmbientInternalLevy κ θ
  let K := κ.ord.ToType
  let W₁ := LocalizedSourceCohen R m₀ hm₀
  let j_R := localizedFirstStageHom hm₀
  let seed := criticalOrdinalPoint U a hf hn ht hk
  let seed_idx (i : I) : K := Erdos1172Shioya.UltrapowerStage.repr U a seed i
  have hseed_supp : Preparation.Supported U a seed_idx :=
    ⟨seed.property.choose, seed.property.choose_spec.choose,
      Germ.coe_eq.mp ((Erdos1172Shioya.UltrapowerStage.repr_eq U a seed).trans
        seed.property.choose_spec.choose_spec.symm)⟩
  let P_W (α : Ordinal.{u}) : bSet W₁ :=
    mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a (fun _ => internalLevyPoset κ α))
  let O_lift (α : Ordinal.{u}) (Y : K → InternalLevyStage κ α) : bSet W₁ :=
    mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a (fun i => levyTruthOpen α (Y (seed_idx i))))
  have hIio_lt : #(Set.Iio β) < θ :=
    (Cardinal.mk_Iio_lt β (by simp)).trans_eq (Cardinal.mk_ord_toType θ)
  have hprev_sub_m₀ (γ : Set.Iio β) : (⊤ : R) ≤ m₀ ⊆ᴮ (prev γ).p :=
    (ih γ).2.2.choose
  have hprev_mono_p (γ₁ γ₂ : Set.Iio β) (hle : γ₁ ≤ γ₂) :
      (⊤ : R) ≤ (prev γ₁).p ⊆ᴮ (prev γ₂).p := by
    rcases hle.lt_or_eq with hlt | rfl
    · exact (ih γ₂).2.2.choose_spec.1 ⟨γ₁.val, hlt⟩
    · exact subset_self
  have hprev_mono_G {γ₁ γ₂ : Set.Iio β} (hle : γ₁ ≤ γ₂) :
      (⊤ : R) ≤ (prev γ₁).G.toBSet ⊆ᴮ (prev γ₂).G.toBSet := by
    rcases hle.lt_or_eq with hlt | rfl
    · exact (ih γ₂).2.2.choose_spec.2.2.1 ⟨γ₁.val, hlt⟩
    · exact subset_self
  obtain ⟨p_in, hp_in, hsub_m₀_in, hp_in_ext⟩ :=
    prefix_union_condition_with_master (ambientInternalLevy_theta_eq_omegaOne hk hκ hθ)
      hm₀ β (fun γ => (prev γ).p) (fun γ => (prev γ).hp) hprev_sub_m₀ hprev_mono_p
  let sup_prev : Ordinal.{u} := ⨆ γ : Set.Iio β, (prev γ).α + 1
  have hsup_prev_lt : sup_prev < θ.ord :=
    Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hθ.isRegular.cof_ord])
      (fun γ => (prev γ).hα)
  let tStage : Ordinal.{u} := match taskAt β with | Sum.inl X => rowStage X | Sum.inr H => matStage H
  have htStage_lt : tStage < θ.ord := by
    dsimp only [tStage]
    cases taskAt β with
    | inl X => exact hrowStage X
    | inr H => exact hmatStage H
  let α_β : Ordinal.{u} := max tStage sup_prev
  have hα_β : α_β < θ.ord := max_lt htStage_lt hsup_prev_lt
  have htask_le : tStage ≤ α_β := le_max_left _ _
  have hprev_α_le (γ : Set.Iio β) : (prev γ).α ≤ α_β :=
    ((Ordinal.lt_iSup_add_one (fun m : Set.Iio β => (prev m).α) γ).le).trans (le_max_right _ _)
  have hprev_master (γ : Set.Iio β) :
      (⊤ : AmbientInternalLevy κ θ) ≤
        (stageMasterGraph U a hk hκ hθ hf hn ht ((hprev_α_le γ).trans_lt hα_β)).toBSet ⊆ᴮ
          (prev γ).G.toBSet :=
    (ih γ).2.2.choose_spec.2.1
  let G_in := amalgamateChainWithMaster U a hk hκ hθ hf hn ht hIio_lt
    (fun γ : Set.Iio β => (prev γ).α) hα_β hprev_α_le (fun γ : Set.Iio β => (prev γ).G)
    hprev_mono_G hprev_master
  have hG_in_master : (⊤ : R) ≤ (stageMasterGraph U a hk hκ hθ hf hn ht hα_β).toBSet ⊆ᴮ G_in.toBSet :=
    subset_amalgamateChainWithMaster_master U a hk hκ hθ hf hn ht hIio_lt
      (fun γ : Set.Iio β => (prev γ).α) hα_β hprev_α_le (fun γ : Set.Iio β => (prev γ).G)
      hprev_mono_G hprev_master
  have hG_in_chain (γ : Set.Iio β) : (⊤ : R) ≤ (prev γ).G.toBSet ⊆ᴮ G_in.toBSet :=
    subset_amalgamateChainWithMaster_chain U a hk hκ hθ hf hn ht hIio_lt
      (fun l : Set.Iio β => (prev l).α) hα_β hprev_α_le (fun l : Set.Iio β => (prev l).G)
      hprev_mono_G hprev_master γ
  obtain ⟨p_mid, hp_mid, hsub_in_mid, q_mid, hq_mid_P, hq_mid_eq⟩ :=
    code_small_ground_func_into_stage U a hk hκ hθ hf hn ht hm₀ hp_in hsub_m₀_in
      j₀ hj₀_sub α_β G_in
  let hsub_m₀_mid : (⊤ : R) ≤ m₀ ⊆ᴮ p_mid := subset_trans' hsub_m₀_in hsub_in_mid
  cases ht_eq : taskAt β with
  | inl X =>
    have h_le_X : rowStage X ≤ α_β := by simpa only [tStage, ht_eq] using htask_le
    let X_β (k : K) : InternalLevyStage κ α_β := stageStepHom (κ := κ) h_le_X (rowRep X k)
    let D_X (i : I) : bSet A := levyDecisionOpen α_β (X_β (seed_idx i))
    obtain ⟨z, hz_P, hz_D, hq_sub_z⟩ :=
      exists_supported_dense_test_extension U a hk.le hf hn ht hκ j₀ α_β D_X
        (hseed_supp.map fun k => levyDecisionOpen α_β (X_β k))
        (fun _ => levyDecisionOpen_subset α_β _)
        (fun _ => levyDecisionOpen_dense α_β _) hq_mid_P
    obtain ⟨p_raw, hp_raw, hsub_mid_raw, G_β, hz_eq_G⟩ :=
      compress_lifted_witness_to_R U a hk hκ hθ hf hn ht hm₀ hp_mid hsub_m₀_mid
        j₀ α_β z hz_P
    let hsub_m₀_raw : (⊤ : R) ≤ m₀ ⊆ᴮ p_raw := subset_trans' hsub_m₀_mid hsub_mid_raw
    let c_raw := coneInMaster hm₀ hp_raw hsub_m₀_raw
    have hc_raw_mid : c_raw ≤ coneInMaster hm₀ hp_mid hsub_m₀_mid :=
      coneInMaster_mono hm₀ hp_mid hsub_m₀_mid hp_raw hsub_m₀_raw hsub_mid_raw
    have hG_in_sub_Gβ : (⊤ : R) ≤ G_in.toBSet ⊆ᴮ G_β.toBSet := by
      have hc_sub : c_raw ≤ mapNames j_R G_in.toBSet ⊆ᴮ mapNames j_R G_β.toBSet :=
        subset_trans' (bSet.subset_of_eq (bv_symm (hc_raw_mid.trans hq_mid_eq)))
          (subset_trans' (hc_raw_mid.trans hq_sub_z) (bSet.subset_of_eq hz_eq_G))
      rw [← map_subset j_R] at hc_sub
      exact ((coneInMaster_le_firstStageHom_iff hm₀ hp_raw hsub_m₀_raw _).mp hc_sub).ge
    have hGβ_P : c_raw ≤ mapNames j_R G_β.toBSet ∈ᴮ P_W α_β :=
      mem_congr hz_eq_G bv_refl (hc_raw_mid.trans hz_P)
    have hGβ_or : c_raw ≤
        (mapNames j_R G_β.toBSet ∈ᴮ O_lift α_β X_β) ⊔
        (mapNames j_R G_β.toBSet ∈ᴮ O_lift α_β (fun k => (X_β k)ᶜ)) :=
      liftedDecisionOpen_or U a hk.le hκ hf hn ht j₀ seed_idx hseed_supp α_β X_β
        (mem_congr hz_eq_G bv_refl (hc_raw_mid.trans hz_D))
    let w_pos : W₁ := mapNames j_R G_β.toBSet ∈ᴮ O_lift α_β X_β
    obtain ⟨p_β, hp_β, hsub_raw_β, hdec_β⟩ :=
      Erdos1172CohenIteration.exists_deciding_condition_extension hp_raw w_pos.val
    let r_β : R := Erdos1172CohenIteration.reads w_pos.val p_β
    let hsub_m₀_β : (⊤ : R) ≤ m₀ ⊆ᴮ p_β := subset_trans' hsub_m₀_raw hsub_raw_β
    let c_β := coneInMaster hm₀ hp_β hsub_m₀_β
    have hc_β_raw : c_β ≤ c_raw :=
      coneInMaster_mono hm₀ hp_raw hsub_m₀_raw hp_β hsub_m₀_β hsub_raw_β
    have hr_pos_le : c_β ⊓ j_R r_β ≤ w_pos :=
      coneInMaster_inf_firstStageHom_reads_le hm₀ hp_β hsub_m₀_β w_pos
    have hr_neg_le : c_β ⊓ (j_R r_β)ᶜ ≤ mapNames j_R G_β.toBSet ∈ᴮ O_lift α_β (fun k => (X_β k)ᶜ) := by
      let r_neg : R := Erdos1172CohenIteration.reads (w_pos.val)ᶜ p_β
      have hsup_top : r_β ⊔ r_neg = ⊤ := top_unique hdec_β
      have hc_le_rneg : (r_β)ᶜ ≤ r_neg := by
        calc
          (r_β)ᶜ = (r_β)ᶜ ⊓ (r_β ⊔ r_neg) := by rw [hsup_top, inf_top_eq]
          _ = ((r_β)ᶜ ⊓ r_β) ⊔ ((r_β)ᶜ ⊓ r_neg) := inf_sup_left _ _ _
          _ ≤ r_neg := by rw [compl_inf_eq_bot, bot_sup_eq]; exact inf_le_right
      have h1 : c_β ⊓ (j_R r_β)ᶜ ≤ c_β ⊓ j_R r_neg := by
        rw [← completeHom_compl j_R]
        exact inf_le_inf_left c_β (OrderHomClass.mono j_R hc_le_rneg)
      have h2 : c_β ⊓ j_R r_neg ≤ w_posᶜ := by
        change nameCone _ p_β ⊓ (Erdos1172CohenIteration.omegaOneFirstStageHom r_neg ⊓ _) ≤
          (masterPositive m₀ hm₀).val ⊓ (w_pos.val)ᶜ
        exact le_inf (inf_le_right.trans inf_le_right)
          ((inf_le_inf_left (nameCone (ErdosCohen.conditions (omegaOne : bSet R)) p_β) inf_le_left).trans
            (nameCone_inf_firstStageHom_reads_le _))
      exact cone_neg_from_or (h1.trans h2) (hc_β_raw.trans hGβ_or)
    let s_out : ValuationStepState U a R := ⟨p_β, hp_β, α_β, hα_β, G_β, r_β⟩
    refine ⟨s_out, ?_, hprev_α_le, hsub_m₀_β, ?_, ?_, ?_, hc_β_raw.trans hGβ_P, ?_⟩
    · exact h_le_X
    · intro γ
      exact subset_trans' (hp_in_ext γ)
        (subset_trans' hsub_in_mid (subset_trans' hsub_mid_raw hsub_raw_β))
    · exact subset_trans' hG_in_master hG_in_sub_Gβ
    · intro γ
      exact subset_trans' (hG_in_chain γ) hG_in_sub_Gβ
    · intro _
      exact ⟨hr_pos_le, hr_neg_le⟩
  | inr H =>
    have h_le_H : matStage H ≤ α_β := by simpa only [tStage, ht_eq] using htask_le
    let H_β (l k : K) : InternalLevyStage κ α_β := stageStepHom (κ := κ) h_le_H (matRep H l k)
    let D_H (i : I) : bSet A :=
      levyJoinTest α_β (fun l : Set.Iio (seed_idx i) => H_β l.val (seed_idx i))
    obtain ⟨z, hz_P, hz_D, hq_sub_z⟩ :=
      exists_supported_dense_test_extension U a hk.le hf hn ht hκ j₀ α_β D_H
        (hseed_supp.map fun k => levyJoinTest α_β (fun l : Set.Iio k => H_β l.val k))
        (fun _ => levyJoinTest_subset α_β _)
        (fun _ => levyJoinTest_dense α_β _) hq_mid_P
    obtain ⟨p_β, hp_β, hsub_mid_β, G_β, hz_eq_G⟩ :=
      compress_lifted_witness_to_R U a hk hκ hθ hf hn ht hm₀ hp_mid hsub_m₀_mid
        j₀ α_β z hz_P
    let hsub_m₀_β : (⊤ : R) ≤ m₀ ⊆ᴮ p_β := subset_trans' hsub_m₀_mid hsub_mid_β
    let c_β := coneInMaster hm₀ hp_β hsub_m₀_β
    have hc_β_mid : c_β ≤ coneInMaster hm₀ hp_mid hsub_m₀_mid :=
      coneInMaster_mono hm₀ hp_mid hsub_m₀_mid hp_β hsub_m₀_β hsub_mid_β
    have hG_in_sub_Gβ : (⊤ : R) ≤ G_in.toBSet ⊆ᴮ G_β.toBSet := by
      have hc_sub : c_β ≤ mapNames j_R G_in.toBSet ⊆ᴮ mapNames j_R G_β.toBSet :=
        subset_trans' (bSet.subset_of_eq (bv_symm (hc_β_mid.trans hq_mid_eq)))
          (subset_trans' (hc_β_mid.trans hq_sub_z) (bSet.subset_of_eq hz_eq_G))
      rw [← map_subset j_R] at hc_sub
      exact ((coneInMaster_le_firstStageHom_iff hm₀ hp_β hsub_m₀_β _).mp hc_sub).ge
    have hGβ_P : c_β ≤ mapNames j_R G_β.toBSet ∈ᴮ P_W α_β :=
      mem_congr hz_eq_G bv_refl (hc_β_mid.trans hz_P)
    have hGβ_reg : c_β ≤
        (⨆ l : K, mapNames j_R G_β.toBSet ∈ᴮ O_lift α_β (H_β l)) ⊔
        (mapNames j_R G_β.toBSet ∈ᴮ O_lift α_β (fun k => (diagonal κ H_β k)ᶜ)) :=
      liftedRegressiveTest_or U a hk hκ hf hn ht j₀ α_β H_β hGβ_P
        (mem_congr hz_eq_G bv_refl (hc_β_mid.trans hz_D))
    let s_out : ValuationStepState U a R := ⟨p_β, hp_β, α_β, hα_β, G_β, ⊥⟩
    refine ⟨s_out, ?_, hprev_α_le, hsub_m₀_β, ?_, ?_, ?_, hGβ_P, ?_⟩
    · exact h_le_H
    · intro γ
      exact subset_trans' (hp_in_ext γ) (subset_trans' hsub_in_mid hsub_mid_β)
    · exact subset_trans' hG_in_master hG_in_sub_Gβ
    · intro γ
      exact subset_trans' (hG_in_chain γ) hG_in_sub_Gβ
    · intro _
      exact hGβ_reg

/-- Existence of a scalar-faithful, initial-segment-vanishing, normal valuation
`μ : BoundedLatticeHom (κ.ord.ToType → InternalLevyAlgebra κ θ) (AmbientInternalLevy κ θ)`. -/
theorem exists_normal_valuation_into_ambientLevy
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    ∃ μ : BoundedLatticeHom (κ.ord.ToType → InternalLevyAlgebra κ θ) (AmbientInternalLevy κ θ),
      (∀ b : InternalLevyAlgebra κ θ,
        μ (fun _ => b) = ambientLevyStageHom (κ := κ) (θ := θ) le_rfl b) ∧
      (∀ i : κ.ord.ToType, μ (initialValue κ i) = ⊥) ∧
      (∀ H : κ.ord.ToType → κ.ord.ToType → InternalLevyAlgebra κ θ,
        μ (diagonal κ H) ≤ ⨆ i, μ (H i)) := by
  classical
  let A := anonymousAlgebra κ
  let F := InternalLevyAlgebra κ θ
  let R := AmbientInternalLevy κ θ
  let K := κ.ord.ToType
  let u_src := ambientLevySourceHom κ θ
  let m₀ := sourceCohenMaster u_src
  obtain ⟨hm₀, j₀, hj₀_base, hj₀_sub⟩ :=
    exists_ambient_stageOne_lift U a hk hκ hθ hf hn ht
  let W₁ := LocalizedSourceCohen R m₀ hm₀
  let j_R := localizedFirstStageHom hm₀
  let seed := criticalOrdinalPoint U a hf hn ht hk
  let seed_idx (i : I) : K := Erdos1172Shioya.UltrapowerStage.repr U a seed i
  have hseed_supp : Preparation.Supported U a seed_idx :=
    ⟨seed.property.choose, seed.property.choose_spec.choose,
      Germ.coe_eq.mp ((Erdos1172Shioya.UltrapowerStage.repr_eq U a seed).trans
        seed.property.choose_spec.choose_spec.symm)⟩
  let P_W (α : Ordinal.{u}) : bSet W₁ :=
    mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a (fun _ => internalLevyPoset κ α))
  let O_lift (α : Ordinal.{u}) (Y : K → InternalLevyStage κ α) : bSet W₁ :=
    mapNames j₀ (Preparation.boundedAnonName (κ := κ) U a (fun i => levyTruthOpen α (Y (seed_idx i))))
  -- Stage factorization and `< θ`-enumeration of all tasks `(K → F) ⊕ (K → K → F)`.
  let Task := (K → F) ⊕ (K → K → F)
  have hK_lt : #K < θ := (Cardinal.mk_ord_toType κ).trans_lt hk
  have hKK_lt : #(K × K) < θ := by
    rw [Cardinal.mk_prod, Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hK_lt hK_lt
  have hF_le : #F ≤ θ := internalLevyAlgebra_cardinal_le hk hκ hθ
  have hTask_le : #Task ≤ θ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    have h1 : #(K → F) ≤ θ := small_func_cardinal_le hθ hK_lt hF_le
    have h2 : #(K → K → F) ≤ θ :=
      (Cardinal.mk_congr (Equiv.curry K K F).symm).le.trans
        (small_func_cardinal_le hθ hKK_lt hF_le)
    exact (add_le_add h1 h2).trans_eq (Cardinal.add_eq_self hθ.aleph0_lt.le)
  obtain ⟨emb_task⟩ : Nonempty (Task ↪ θ.ord.ToType) :=
    (Cardinal.le_def Task θ.ord.ToType).mp (hTask_le.trans_eq (Cardinal.mk_ord_toType θ).symm)
  have : Nonempty Task := ⟨Sum.inl (fun _ => ⊥)⟩
  have htaskAt_ex : ∃ f : θ.ord.ToType → Task, ∀ t, f (emb_task t) = t :=
    ⟨Function.invFun emb_task, Function.leftInverse_invFun emb_task.injective⟩
  obtain ⟨taskAt, htaskAt_emb⟩ := htaskAt_ex
  have hrow_ex (X : K → F) :
      ∃ p : Σ α : Ordinal.{u}, PLift (α < θ.ord) × (K → InternalLevyStage κ α),
        ∀ k, stageStepHom (κ := κ) p.2.1.down.le (p.2.2 k) = X k := by
    obtain ⟨α, hα, v_α, hv⟩ := array_factors_at_stage hk hκ hθ hK_lt X
    exact ⟨⟨α, ⟨hα⟩, v_α⟩, hv⟩
  obtain ⟨rowPack, hrowRep⟩ := Classical.axiomOfChoice hrow_ex
  let rowStage (X : K → F) : Ordinal.{u} := (rowPack X).1
  have hrowStage (X : K → F) : rowStage X < θ.ord := (rowPack X).2.1.down
  let rowRep (X : K → F) : K → InternalLevyStage κ (rowStage X) := (rowPack X).2.2
  have hmat_ex (H : K → K → F) :
      ∃ p : Σ α : Ordinal.{u}, PLift (α < θ.ord) × (K → K → InternalLevyStage κ α),
        ∀ l k, stageStepHom (κ := κ) p.2.1.down.le (p.2.2 l k) = H l k := by
    obtain ⟨α, hα, v_α, hv⟩ := array_factors_at_stage hk hκ hθ hKK_lt (Function.uncurry H)
    exact ⟨⟨α, ⟨hα⟩, fun l k => v_α (l, k)⟩, fun l k => hv (l, k)⟩
  obtain ⟨matPack, hmatRep⟩ := Classical.axiomOfChoice hmat_ex
  let matStage (H : K → K → F) : Ordinal.{u} := (matPack H).1
  have hmatStage (H : K → K → F) : matStage H < θ.ord := (matPack H).2.1.down
  let matRep (H : K → K → F) : K → K → InternalLevyStage κ (matStage H) := (matPack H).2.2
  let GoodStep (β : θ.ord.ToType) (prev : Set.Iio β → ValuationStepState U a R)
      (s : ValuationStepState U a R) : Prop :=
    ValuationGoodStep U a hk hκ hθ hf hn ht hm₀ j₀ rowStage rowRep matStage matRep
      (taskAt β) β prev s
  let defaultState : ValuationStepState U a R :=
    { p := m₀
      hp := hm₀
      α := 0
      hα := hθ.isRegular.ord_pos
      G := stageMasterGraph U a hk hκ hθ hf hn ht hθ.isRegular.ord_pos
      r := ⊥ }
  let stepFn (β : θ.ord.ToType) (rec : ∀ γ : θ.ord.ToType, γ < β → ValuationStepState U a R) :
      ValuationStepState U a R :=
    if h : ∃ s, GoodStep β (fun γ => rec γ.val γ.property) s then h.choose else defaultState
  have hrun_ex : ∃ r : θ.ord.ToType → ValuationStepState U a R,
      ∀ β, r β = stepFn β (fun γ _ => r γ) :=
    ⟨(wellFounded_lt : WellFounded ((· < ·) : θ.ord.ToType → θ.ord.ToType → Prop)).fix stepFn,
      fun _ => WellFounded.fix_eq _ _ _⟩
  obtain ⟨run, hrun_eq⟩ := hrun_ex
  have hrun_good (β : θ.ord.ToType) : GoodStep β (fun γ => run γ.val) (run β) := by
    induction β using (wellFounded_lt : WellFounded ((· < ·) : θ.ord.ToType → θ.ord.ToType → Prop)).induction with
    | h β ih =>
      have hex : ∃ s, GoodStep β (fun γ => run γ.val) s :=
        exists_valuationGoodStep U a hk hκ hθ hf hn ht hm₀ j₀ hj₀_sub
          rowStage hrowStage rowRep matStage hmatStage matRep taskAt β
          (fun γ => run γ.val) (fun γ => ih γ.val γ.property)
      rw [hrun_eq β]
      change GoodStep β (fun γ => run γ.val)
        (if h : ∃ s, GoodStep β (fun γ => run γ.val) s then h.choose else defaultState)
      rw [dif_pos hex]
      exact hex.choose_spec
  -- Monotonicity helpers across arbitrary `β₁ ≤ β₂`.
  have hrun_sub_m₀ (β : θ.ord.ToType) : (⊤ : R) ≤ m₀ ⊆ᴮ (run β).p :=
    (hrun_good β).2.2.choose
  have hrun_mono_α {β₁ β₂ : θ.ord.ToType} (hle : β₁ ≤ β₂) : (run β₁).α ≤ (run β₂).α := by
    rcases hle.lt_or_eq with hlt | rfl
    · exact (hrun_good β₂).2.1 ⟨β₁, hlt⟩
    · exact le_rfl
  have hrun_mono_p {β₁ β₂ : θ.ord.ToType} (hle : β₁ ≤ β₂) :
      (⊤ : R) ≤ (run β₁).p ⊆ᴮ (run β₂).p := by
    rcases hle.lt_or_eq with hlt | rfl
    · exact (hrun_good β₂).2.2.choose_spec.1 ⟨β₁, hlt⟩
    · exact subset_self
  have hrun_mono_G {β₁ β₂ : θ.ord.ToType} (hle : β₁ ≤ β₂) :
      (⊤ : R) ≤ (run β₁).G.toBSet ⊆ᴮ (run β₂).G.toBSet := by
    rcases hle.lt_or_eq with hlt | rfl
    · exact (hrun_good β₂).2.2.choose_spec.2.2.1 ⟨β₁, hlt⟩
    · exact subset_self
  let coneAt (β : θ.ord.ToType) : W₁ := coneInMaster hm₀ (run β).hp (hrun_sub_m₀ β)
  have hcone_anti {β₁ β₂ : θ.ord.ToType} (hle : β₁ ≤ β₂) : coneAt β₂ ≤ coneAt β₁ :=
    coneInMaster_mono hm₀ (run β₁).hp (hrun_sub_m₀ β₁) (run β₂).hp (hrun_sub_m₀ β₂) (hrun_mono_p hle)
  -- Read valuation `μ_fn X` and prove stage-independent decision persistence `row_decides_at`.
  let μ_fn (X : K → F) : R := (run (emb_task (Sum.inl X))).r
  have hrow_decides_at (X : K → F) {γ : θ.ord.ToType} (hγ : emb_task (Sum.inl X) ≤ γ)
      (Y : K → InternalLevyStage κ (run γ).α)
      (hY : ∀ k, stageStepHom (κ := κ) (run γ).hα.le (Y k) = X k) :
      coneAt γ ⊓ (mapNames j_R (run γ).G.toBSet ∈ᴮ O_lift (run γ).α Y) =
        coneAt γ ⊓ j_R (μ_fn X) ∧
      coneAt γ ⊓ (mapNames j_R (run γ).G.toBSet ∈ᴮ O_lift (run γ).α (fun k => (Y k)ᶜ)) =
        coneAt γ ⊓ (j_R (μ_fn X))ᶜ := by
    let β₀ := emb_task (Sum.inl X)
    have htask_β₀ : taskAt β₀ = Sum.inl X := htaskAt_emb (Sum.inl X)
    have hgood₀ : ValuationGoodStep U a hk hκ hθ hf hn ht hm₀ j₀
        rowStage rowRep matStage matRep (taskAt β₀) β₀ (fun δ => run δ.val) (run β₀) :=
      hrun_good β₀
    rw [htask_β₀] at hgood₀
    have h_le₀ : rowStage X ≤ (run β₀).α := hgood₀.1
    obtain ⟨hpos₀, hneg₀⟩ := hgood₀.2.2.choose_spec.2.2.2.2 h_le₀
    let X₀ (k : K) := stageStepHom (κ := κ) h_le₀ (rowRep X k)
    have hα₀_γ : (run β₀).α ≤ (run γ).α := hrun_mono_α hγ
    have hY_eq : Y = fun k => stageStepHom (κ := κ) hα₀_γ (X₀ k) := by
      funext k
      apply stageStepHom_injective (κ := κ) (run γ).hα.le
      rw [hY k, stageStepHom_comp (κ := κ), stageStepHom_comp (κ := κ), hrowRep X k]
    have hYc_eq : (fun k => (Y k)ᶜ) = fun k => stageStepHom (κ := κ) hα₀_γ (X₀ k)ᶜ := by
      funext k
      rw [hY_eq, completeHom_compl]
    have hGγ_P : coneAt γ ≤ mapNames j_R (run γ).G.toBSet ∈ᴮ P_W (run γ).α :=
      (hrun_good γ).2.2.choose_spec.2.2.2.1
    have hG₀_sub_γ : (⊤ : W₁) ≤ mapNames j_R (run β₀).G.toBSet ⊆ᴮ mapNames j_R (run γ).G.toBSet := by
      simpa only [TopHomClass.map_top, map_subset] using OrderHomClass.mono j_R (hrun_mono_G hγ)
    have hpos_γ : coneAt γ ⊓ j_R (μ_fn X) ≤ mapNames j_R (run γ).G.toBSet ∈ᴮ O_lift (run γ).α Y := by
      rw [hY_eq]
      exact liftedTruthOpen_stage_upward U a hk.le hκ hf hn ht j₀ seed_idx hseed_supp hα₀_γ X₀
        ((inf_le_inf_right (j_R (μ_fn X)) (hcone_anti hγ)).trans hpos₀)
        (inf_le_left.trans hGγ_P) (le_top.trans hG₀_sub_γ)
    have hneg_γ : coneAt γ ⊓ (j_R (μ_fn X))ᶜ ≤
        mapNames j_R (run γ).G.toBSet ∈ᴮ O_lift (run γ).α (fun k => (Y k)ᶜ) := by
      rw [hYc_eq]
      exact liftedTruthOpen_stage_upward U a hk.le hκ hf hn ht j₀ seed_idx hseed_supp hα₀_γ (fun k => (X₀ k)ᶜ)
        ((inf_le_inf_right (j_R (μ_fn X))ᶜ (hcone_anti hγ)).trans hneg₀)
        (inf_le_left.trans hGγ_P) (le_top.trans hG₀_sub_γ)
    exact decide_pair_of_disjoint hpos_γ hneg_γ
      (liftedTruthOpen_disjoint U a hk.le hκ hf hn ht j₀ seed_idx hseed_supp (run γ).α Y
        (mapNames j_R (run γ).G.toBSet))
  -- Algebraic laws of `μ_fn`.
  have hμ_bot : μ_fn (⊥ : K → F) = ⊥ := by
    let γ := emb_task (Sum.inl (⊥ : K → F))
    have hdec := (hrow_decides_at (⊥ : K → F) le_rfl (fun _ => ⊥)
      (fun _ => BotHomClass.map_bot _)).1
    have h0 := liftedTruthOpen_bot U a hk.le hκ hf hn ht j₀ (run γ).α
      (hrun_good γ).2.2.choose_spec.2.2.2.1
    rw [h0] at hdec
    exact coneInMaster_eq_unique hm₀ (run γ).hp (hrun_sub_m₀ γ)
      (hdec.symm.trans (by rw [BotHomClass.map_bot, inf_bot_eq]))
  have hμ_compl (X : K → F) : μ_fn Xᶜ = (μ_fn X)ᶜ := by
    let γ := max (emb_task (Sum.inl X)) (emb_task (Sum.inl Xᶜ))
    have hX_le : rowStage X ≤ (run γ).α := by
      have h1 : rowStage X ≤ (run (emb_task (Sum.inl X))).α := by
        have hg := (hrun_good (emb_task (Sum.inl X))).1
        rwa [htaskAt_emb] at hg
      exact h1.trans (hrun_mono_α (le_max_left _ _))
    let Y (k : K) : InternalLevyStage κ (run γ).α := stageStepHom (κ := κ) hX_le (rowRep X k)
    have hY (k : K) : stageStepHom (κ := κ) (run γ).hα.le (Y k) = X k := by
      dsimp only [Y]
      rw [stageStepHom_comp (κ := κ), hrowRep X k]
    have hYc (k : K) : stageStepHom (κ := κ) (run γ).hα.le (Y k)ᶜ = (Xᶜ) k := by
      rw [completeHom_compl, hY k]
      rfl
    have hd1 := (hrow_decides_at X (le_max_left _ _) Y hY).2
    have hd2 := (hrow_decides_at Xᶜ (le_max_right _ _) (fun k => (Y k)ᶜ) hYc).1
    have heq : coneAt γ ⊓ j_R (μ_fn Xᶜ) = coneAt γ ⊓ j_R (μ_fn X)ᶜ := by
      rw [← hd2, hd1, completeHom_compl]
    exact coneInMaster_eq_unique hm₀ (run γ).hp (hrun_sub_m₀ γ) heq
  have hμ_inf (X₁ X₂ : K → F) : μ_fn (X₁ ⊓ X₂) = μ_fn X₁ ⊓ μ_fn X₂ := by
    let γ := max (max (emb_task (Sum.inl X₁)) (emb_task (Sum.inl X₂))) (emb_task (Sum.inl (X₁ ⊓ X₂)))
    have h1_le : rowStage X₁ ≤ (run γ).α := by
      have hg := (hrun_good (emb_task (Sum.inl X₁))).1
      rw [htaskAt_emb] at hg
      exact hg.trans (hrun_mono_α ((le_max_left _ _).trans (le_max_left _ _)))
    have h2_le : rowStage X₂ ≤ (run γ).α := by
      have hg := (hrun_good (emb_task (Sum.inl X₂))).1
      rw [htaskAt_emb] at hg
      exact hg.trans (hrun_mono_α ((le_max_right _ _).trans (le_max_left _ _)))
    let Y₁ (k : K) := stageStepHom (κ := κ) h1_le (rowRep X₁ k)
    let Y₂ (k : K) := stageStepHom (κ := κ) h2_le (rowRep X₂ k)
    have hY₁ (k : K) : stageStepHom (κ := κ) (run γ).hα.le (Y₁ k) = X₁ k := by
      dsimp only [Y₁]; rw [stageStepHom_comp (κ := κ), hrowRep X₁ k]
    have hY₂ (k : K) : stageStepHom (κ := κ) (run γ).hα.le (Y₂ k) = X₂ k := by
      dsimp only [Y₂]; rw [stageStepHom_comp (κ := κ), hrowRep X₂ k]
    have hY₁₂ (k : K) : stageStepHom (κ := κ) (run γ).hα.le (Y₁ k ⊓ Y₂ k) = (X₁ ⊓ X₂) k :=
      (completeHom_inf (stageStepHom (κ := κ) (run γ).hα.le) (Y₁ k) (Y₂ k)).trans
        (by rw [hY₁ k, hY₂ k]; rfl)
    have hd1 := (hrow_decides_at X₁ ((le_max_left _ _).trans (le_max_left _ _)) Y₁ hY₁).1
    have hd2 := (hrow_decides_at X₂ ((le_max_right _ _).trans (le_max_left _ _)) Y₂ hY₂).1
    have hd12 := (hrow_decides_at (X₁ ⊓ X₂) (le_max_right _ _) (fun k => Y₁ k ⊓ Y₂ k) hY₁₂).1
    have hjR_inf : j_R (μ_fn X₁ ⊓ μ_fn X₂) = j_R (μ_fn X₁) ⊓ j_R (μ_fn X₂) :=
      completeHom_inf j_R (μ_fn X₁) (μ_fn X₂)
    have heq : coneAt γ ⊓ j_R (μ_fn (X₁ ⊓ X₂)) = coneAt γ ⊓ j_R (μ_fn X₁ ⊓ μ_fn X₂) := by
      rw [← hd12,
        liftedTruthOpen_inf U a hk.le hκ hf hn ht j₀ seed_idx hseed_supp (run γ).α Y₁ Y₂
          (hrun_good γ).2.2.choose_spec.2.2.2.1,
        hd1, hd2, hjR_inf]
      exact inf_cone_distrib (coneAt γ) (j_R (μ_fn X₁)) (j_R (μ_fn X₂))
    exact coneInMaster_eq_unique hm₀ (run γ).hp (hrun_sub_m₀ γ) heq
  let μ : BoundedLatticeHom (K → F) R :=
    { toFun := μ_fn
      map_inf' := hμ_inf
      map_bot' := hμ_bot
      map_top' := by
        have h : μ_fn (⊥ : K → F)ᶜ = (μ_fn (⊥ : K → F))ᶜ := hμ_compl (⊥ : K → F)
        have htop : (⊥ : K → F)ᶜ = ⊤ := funext fun _ => compl_bot
        rw [htop, hμ_bot, compl_bot] at h
        exact h
      map_sup' := fun X₁ X₂ =>
        calc
          μ_fn (X₁ ⊔ X₂) = μ_fn (X₁ᶜ ⊓ X₂ᶜ)ᶜ :=
            congrArg μ_fn (funext fun k => sup_eq_compl_inf_compl (X₁ k) (X₂ k))
          _ = (μ_fn (X₁ᶜ ⊓ X₂ᶜ))ᶜ := hμ_compl _
          _ = (μ_fn X₁ᶜ ⊓ μ_fn X₂ᶜ)ᶜ := congrArg Compl.compl (hμ_inf X₁ᶜ X₂ᶜ)
          _ = ((μ_fn X₁)ᶜ ⊓ (μ_fn X₂)ᶜ)ᶜ := by rw [hμ_compl, hμ_compl]
          _ = μ_fn X₁ ⊔ μ_fn X₂ := (sup_eq_compl_inf_compl (μ_fn X₁) (μ_fn X₂)).symm }
  -- Scalar faithfulness: `μ (fun _ => b) = ambientLevyStageHom le_rfl b`.
  have hμ_scalar (b : F) : μ (fun _ => b) = ambientLevyStageHom (κ := κ) (θ := θ) le_rfl b := by
    let X_b : K → F := fun _ => b
    let γ := emb_task (Sum.inl X_b)
    have h_le : rowStage X_b ≤ (run γ).α := by
      have hg := (hrun_good γ).1
      rwa [htaskAt_emb] at hg
    obtain ⟨k₀⟩ : Nonempty K := Cardinal.mk_ne_zero_iff.mp
      ((Cardinal.mk_ord_toType κ).trans_ne (Cardinal.aleph0_pos.trans_le hκ.aleph0_lt.le).ne')
    let b₀ : InternalLevyStage κ (run γ).α := stageStepHom (κ := κ) h_le (rowRep X_b k₀)
    have hb₀ : stageStepHom (κ := κ) (run γ).hα.le b₀ = b := by
      dsimp only [b₀]
      rw [stageStepHom_comp (κ := κ)]
      exact hrowRep X_b k₀
    have hd_row := (hrow_decides_at X_b le_rfl (fun _ => b₀) (fun _ => hb₀)).1
    have hd_master := stageMaster_forces_constant_truthOpen U a hk hκ hθ hf hn ht
      (run γ).hα hm₀ (run γ).hp (hrun_sub_m₀ γ) j₀ hj₀_base
      (mapNames j_R (run γ).G.toBSet)
      (hrun_good γ).2.2.choose_spec.2.2.2.1
      (le_top.trans (by
        simpa only [TopHomClass.map_top, map_subset] using
          OrderHomClass.mono j_R (hrun_good γ).2.2.choose_spec.2.1))
      b₀
    have hamb_eq :
        ambientLevyStageHom (κ := κ) (θ := θ) (run γ).hα.le b₀ =
          ambientLevyStageHom (κ := κ) (θ := θ) le_rfl b :=
      (ambientLevyStageHom_comp (κ := κ) (θ := θ) (run γ).hα.le le_rfl b₀).symm.trans
        (congrArg (ambientLevyStageHom (κ := κ) (θ := θ) le_rfl) hb₀)
    have heq : coneAt γ ⊓ j_R (μ X_b) = coneAt γ ⊓ j_R (ambientLevyStageHom (κ := κ) (θ := θ) le_rfl b) := by
      change coneAt γ ⊓ j_R (μ_fn X_b) = _
      rw [← hd_row, ← hamb_eq]
      exact hd_master
    exact coneInMaster_eq_unique hm₀ (run γ).hp (hrun_sub_m₀ γ) heq
  -- Initial-segment vanishing: `μ (initialValue κ i₀) = ⊥`.
  have hμ_init (i₀ : K) : μ (initialValue κ i₀) = ⊥ := by
    let γ := emb_task (Sum.inl (initialValue κ i₀))
    let Y_init (k : K) : InternalLevyStage κ (run γ).α := if k ≤ i₀ then ⊤ else ⊥
    have hY_init (k : K) : stageStepHom (κ := κ) (run γ).hα.le (Y_init k) = initialValue κ i₀ k := by
      dsimp only [Y_init, initialValue]
      split_ifs
      · exact TopHomClass.map_top _
      · exact BotHomClass.map_bot _
    have hd_init := (hrow_decides_at (initialValue κ i₀) le_rfl Y_init hY_init).1
    have hO_eq : (⊤ : W₁) ≤ O_lift (run γ).α Y_init =ᴮ O_lift (run γ).α (fun _ => ⊥) := by
      have hVA_eq : (⊤ : Erdos1172BooleanUltrapower.Algebra U A) ≤
          Preparation.boundedAnonName (κ := κ) U a (fun i => levyTruthOpen (run γ).α (Y_init (seed_idx i))) =ᴮ
          Preparation.boundedAnonName (κ := κ) U a (fun _ => levyTruthOpen (run γ).α ⊥) := by
        rw [← Preparation.boundedAnonName_eq U a hk.le hf hn ht hκ
          (fun i => levyTruthOpen (run γ).α (Y_init (seed_idx i)))
          (fun _ => levyTruthOpen (run γ).α ⊥)
          (hseed_supp.map fun k => levyTruthOpen (run γ).α (Y_init k))
          (Preparation.Supported.const _),
          value_eq_of_eventuallyEq U (g := fun _ => ⊤) _, value_top]
        filter_upwards [seed_gt_eventually U a hk hκ hf hn ht i₀] with i hi
        dsimp only [Y_init, seed_idx]
        rw [if_neg (not_le_of_gt hi)]
        exact top_unique bv_refl
      simpa only [TopHomClass.map_top, map_bv_eq] using OrderHomClass.mono j₀ hVA_eq
    have hbot_mem : coneAt γ ⊓ (mapNames j_R (run γ).G.toBSet ∈ᴮ O_lift (run γ).α Y_init) = ⊥ := by
      apply le_bot_iff.mp
      have hm : coneAt γ ⊓ (mapNames j_R (run γ).G.toBSet ∈ᴮ O_lift (run γ).α Y_init) ≤
          coneAt γ ⊓ (mapNames j_R (run γ).G.toBSet ∈ᴮ O_lift (run γ).α (fun _ => ⊥)) :=
        le_inf inf_le_left (mem_congr bv_refl (le_top.trans hO_eq) inf_le_right)
      exact hm.trans_eq (liftedTruthOpen_bot U a hk.le hκ hf hn ht j₀ (run γ).α
        (hrun_good γ).2.2.choose_spec.2.2.2.1)
    exact coneInMaster_eq_unique hm₀ (run γ).hp (hrun_sub_m₀ γ)
      (hd_init.symm.trans (hbot_mem.trans (by rw [BotHomClass.map_bot, inf_bot_eq])))
  -- Normality: `μ (diagonal κ H) ≤ ⨆ l, μ (H l)`.
  have hμ_normal (H : K → K → F) : μ (diagonal κ H) ≤ ⨆ l : K, μ (H l) := by
    let β_H := emb_task (Sum.inr H)
    let β_diag := emb_task (Sum.inl (diagonal κ H))
    let idx_fam : (PUnit.{u + 1} ⊕ PUnit.{u + 1} ⊕ K) → θ.ord.ToType
      | Sum.inl _ => β_H
      | Sum.inr (Sum.inl _) => β_diag
      | Sum.inr (Sum.inr l) => emb_task (Sum.inl (H l))
    have hfam_lt : #(PUnit.{u + 1} ⊕ PUnit.{u + 1} ⊕ K) < θ := by
      simp only [Cardinal.mk_sum, Cardinal.mk_punit, Cardinal.lift_id]
      exact Cardinal.add_lt_of_lt hθ.aleph0_lt.le
        (Cardinal.one_lt_aleph0.trans hθ.aleph0_lt)
        (Cardinal.add_lt_of_lt hθ.aleph0_lt.le
          (Cardinal.one_lt_aleph0.trans hθ.aleph0_lt) hK_lt)
    obtain ⟨γ, hγ_gt⟩ := strict_upper_bound_theta'' hθ.isRegular hfam_lt idx_fam
    have hH_γ : β_H ≤ γ := (hγ_gt (Sum.inl PUnit.unit)).le
    have hdiag_γ : β_diag ≤ γ := (hγ_gt (Sum.inr (Sum.inl PUnit.unit))).le
    have hrow_γ (l : K) : emb_task (Sum.inl (H l)) ≤ γ := (hγ_gt (Sum.inr (Sum.inr l))).le
    have htask_βH : taskAt β_H = Sum.inr H := htaskAt_emb (Sum.inr H)
    have hgood_H : ValuationGoodStep U a hk hκ hθ hf hn ht hm₀ j₀
        rowStage rowRep matStage matRep (taskAt β_H) β_H (fun δ => run δ.val) (run β_H) :=
      hrun_good β_H
    rw [htask_βH] at hgood_H
    have h_le_H₀ : matStage H ≤ (run β_H).α := hgood_H.1
    have hreg₀ := hgood_H.2.2.choose_spec.2.2.2.2 h_le_H₀
    let H₀ (l k : K) := stageStepHom (κ := κ) h_le_H₀ (matRep H l k)
    have hα_H_γ : (run β_H).α ≤ (run γ).α := hrun_mono_α hH_γ
    let H_γ (l k : K) := stageStepHom (κ := κ) hα_H_γ (H₀ l k)
    have hH_γ_rep (l k : K) : stageStepHom (κ := κ) (run γ).hα.le (H_γ l k) = H l k := by
      dsimp only [H_γ, H₀]
      rw [stageStepHom_comp (κ := κ), stageStepHom_comp (κ := κ), hmatRep H l k]
    have hdiag_rep (k : K) : stageStepHom (κ := κ) (run γ).hα.le (diagonal κ H_γ k) = diagonal κ H k := by
      dsimp only [Erdos1172RelativeValuation.diagonal]
      rw [_root_.map_iSup]
      exact iSup_congr fun i => hH_γ_rep i.val k
    have hGγ_P : coneAt γ ≤ mapNames j_R (run γ).G.toBSet ∈ᴮ P_W (run γ).α :=
      (hrun_good γ).2.2.choose_spec.2.2.2.1
    have hG_H_sub_γ : (⊤ : W₁) ≤ mapNames j_R (run β_H).G.toBSet ⊆ᴮ mapNames j_R (run γ).G.toBSet := by
      simpa only [TopHomClass.map_top, map_subset] using OrderHomClass.mono j_R (hrun_mono_G hH_γ)
    have hrow_up (l : K) :
        coneAt γ ⊓ (mapNames j_R (run β_H).G.toBSet ∈ᴮ O_lift (run β_H).α (H₀ l)) ≤
          coneAt γ ⊓ j_R (μ (H l)) := by
      have hup := liftedTruthOpen_stage_upward U a hk.le hκ hf hn ht j₀ seed_idx hseed_supp
        hα_H_γ (H₀ l) inf_le_right (inf_le_left.trans hGγ_P) (le_top.trans hG_H_sub_γ)
      exact (le_inf inf_le_left hup).trans_eq
        (hrow_decides_at (H l) (hrow_γ l) (H_γ l) (hH_γ_rep l)).1
    have hdiag_up :
        coneAt γ ⊓ (mapNames j_R (run β_H).G.toBSet ∈ᴮ O_lift (run β_H).α (fun k => (diagonal κ H₀ k)ᶜ)) ≤
          coneAt γ ⊓ (j_R (μ (diagonal κ H)))ᶜ := by
      have hdiag_step (k : K) : stageStepHom (κ := κ) hα_H_γ (diagonal κ H₀ k)ᶜ = (diagonal κ H_γ k)ᶜ := by
        rw [completeHom_compl]
        congr 1
        dsimp only [Erdos1172RelativeValuation.diagonal, H_γ]
        exact _root_.map_iSup (stageStepHom (κ := κ) hα_H_γ) _
      have hup := liftedTruthOpen_stage_upward U a hk.le hκ hf hn ht j₀ seed_idx hseed_supp
        hα_H_γ (fun k => (diagonal κ H₀ k)ᶜ) inf_le_right
        (inf_le_left.trans hGγ_P) (le_top.trans hG_H_sub_γ)
      simp only [hdiag_step] at hup
      exact (le_inf inf_le_left hup).trans_eq
        (hrow_decides_at (diagonal κ H) hdiag_γ (diagonal κ H_γ) hdiag_rep).2
    exact coneInMaster_le_unique hm₀ (run γ).hp (hrun_sub_m₀ γ)
      (cone_normal_from_reg j_R ((hcone_anti hH_γ).trans hreg₀) hrow_up hdiag_up)
  exact ⟨μ, hμ_scalar, hμ_init, hμ_normal⟩

end TransfiniteValuation

section MainConsistency
open Erdos1172Part4InternalFullGCHSentence bSet.ErdosFullGCH

/-- In `InternalLevyAlgebra κ θ`, `fullGCHValue = ⊤` and there exists an internal normal
`ω₁`-complete `ω₁`-dense ideal (`properIdeal`, `countableAbsorption`, `countableClosure`,
`diagonalClosure`, `is_function`, `positiveValues`, `denseValues`, `injects_into`). -/
theorem exists_internalLevy_fullGCH_and_normal_dense_ideal
    {I : Type u} {κ θ : Cardinal.{u}}
    (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
    [CountableInterFilter (U : Filter I)] [CardinalInterFilter (U : Filter I) κ]
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (tail : ∀ μ : Cardinal.{u}, θ ≤ μ → (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    let F := InternalLevyAlgebra κ θ
    (fullGCHValue : F) = ⊤ ∧
    ∃ J I_idx D : bSet F,
      (⊤ : F) ≤ ErdosIdeal.properIdeal omegaOne J ∧
      (⊤ : F) ≤ ErdosIdeal.countableAbsorption omegaOne J ∧
      (⊤ : F) ≤ ErdosIdeal.countableClosure J ∧
      (⊤ : F) ≤ ErdosIdeal.diagonalClosure omegaOne J ∧
      (⊤ : F) ≤ is_function I_idx (bv_powerset omegaOne) D ∧
      (⊤ : F) ≤ ErdosDenseBasis.positiveValues omegaOne J I_idx D ∧
      (⊤ : F) ≤ ErdosDenseBasis.denseValues omegaOne J I_idx D ∧
      (⊤ : F) ≤ injects_into I_idx omegaOne := by
  intro F
  have : Nonempty θ.ord.ToType := Cardinal.mk_ne_zero_iff.mp
    ((Cardinal.mk_ord_toType θ).trans_ne (Cardinal.aleph0_pos.trans_le hθ.aleph0_lt.le).ne')
  obtain ⟨μ, hscalar, hinit, hnormal⟩ :=
    exists_normal_valuation_into_ambientLevy U a hk hκ hθ hf hn ht
  obtain ⟨d, hdense⟩ := ambientLevy_exists_denseOver (θ := θ) hκ
  exact ⟨internalLevy_fullGCH_eq_top hk hκ hθ tail,
    internal_ideal_and_basis κ (ambientLevyStageHom (κ := κ) (θ := θ) le_rfl)
      (ambientLevyStageHom_injective le_rfl) μ hscalar hinit hnormal d hdense
      hκ.aleph0_lt (internalLevyStage_checked_eq_omegaOne hκ θ.ord)⟩

/-- Strengthened form of `exists_internalLevy_fullGCH_and_normal_dense_ideal` deriving
`κ.IsInaccessible` and `θ.IsInaccessible` automatically from the `(κ, θ)`-fine normal measure. -/
theorem exists_internalLevy_fullGCH_and_normal_dense_ideal_minimal
    {I : Type u} {κ θ : Cardinal.{u}}
    (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
    [CountableInterFilter (U : Filter I)] [CardinalInterFilter (U : Filter I) κ]
    (hk : κ < θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (tail : ∀ μ : Cardinal.{u}, θ ≤ μ → (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    let F := InternalLevyAlgebra κ θ
    (fullGCHValue : F) = ⊤ ∧
    ∃ J I_idx D : bSet F,
      (⊤ : F) ≤ ErdosIdeal.properIdeal omegaOne J ∧
      (⊤ : F) ≤ ErdosIdeal.countableAbsorption omegaOne J ∧
      (⊤ : F) ≤ ErdosIdeal.countableClosure J ∧
      (⊤ : F) ≤ ErdosIdeal.diagonalClosure omegaOne J ∧
      (⊤ : F) ≤ is_function I_idx (bv_powerset omegaOne) D ∧
      (⊤ : F) ≤ ErdosDenseBasis.positiveValues omegaOne J I_idx D ∧
      (⊤ : F) ≤ ErdosDenseBasis.denseValues omegaOne J I_idx D ∧
      (⊤ : F) ≤ injects_into I_idx omegaOne := by
  obtain ⟨hκ, hθ⟩ := inaccessible_pair_of_fine_order_type U hk hf hn ht
  exact exists_internalLevy_fullGCH_and_normal_dense_ideal U a hk hκ hθ hf hn ht tail

/-- Canonical Kanamori huge-cardinal form of `exists_internalLevy_fullGCH_and_normal_dense_ideal`. -/
theorem exists_internalLevy_fullGCH_and_normal_dense_ideal_of_hugeWithTarget
    {κ θ : Cardinal.{u}} (hHuge : IsHugeWithTarget κ θ)
    (tail : ∀ μ : Cardinal.{u}, θ ≤ μ → (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    let F := InternalLevyAlgebra κ θ
    (fullGCHValue : F) = ⊤ ∧
    ∃ J I_idx D : bSet F,
      (⊤ : F) ≤ ErdosIdeal.properIdeal omegaOne J ∧
      (⊤ : F) ≤ ErdosIdeal.countableAbsorption omegaOne J ∧
      (⊤ : F) ≤ ErdosIdeal.countableClosure J ∧
      (⊤ : F) ≤ ErdosIdeal.diagonalClosure omegaOne J ∧
      (⊤ : F) ≤ is_function I_idx (bv_powerset omegaOne) D ∧
      (⊤ : F) ≤ ErdosDenseBasis.positiveValues omegaOne J I_idx D ∧
      (⊤ : F) ≤ ErdosDenseBasis.denseValues omegaOne J I_idx D ∧
      (⊤ : F) ≤ injects_into I_idx omegaOne := by
  obtain ⟨I, U, a, hcnt, hcard, hk, hf, hn, ht⟩ :=
    isHugeWithTarget_iff_exists_fine_measure.mp hHuge
  have : CountableInterFilter (U : Filter I) := hcnt
  have : CardinalInterFilter (U : Filter I) κ := hcard
  exact exists_internalLevy_fullGCH_and_normal_dense_ideal_minimal U a hk hf hn ht tail

/-- Relative consistency of `ZFC + GCH + Part 4 (balanced ordinal Ramsey theorem on ω₂)`
from two inaccessible cardinals `κ < θ`, ground tail GCH at `≥ θ`, and a `(κ, θ)`-fine normal
`κ`-complete ultrafilter `(U, a)`. -/
theorem gchPart4Theory_is_consistent
    {I : Type 0} {κ θ : Cardinal.{0}}
    (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
    [CountableInterFilter (U : Filter I)] [CardinalInterFilter (U : Filter I) κ]
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (tail : ∀ μ : Cardinal.{0}, θ ≤ μ → (2 : Cardinal.{0}) ^ μ = Order.succ μ) :
    Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent := by
  obtain ⟨hgch, J, I_idx, D, hj, ha, hc, hn_id, hf_fn, hp_val, hd_val, hi_inj⟩ :=
    exists_internalLevy_fullGCH_and_normal_dense_ideal U a hk hκ hθ hf hn ht tail
  exact Erdos1172Part4InternalGCHTheory.consistent_gchPart4_of_nonzero_ideal
    (β := InternalLevyAlgebra κ θ) (Γ := ⊤)
    top_ne_bot hgch.symm.le hj ha hc hn_id hf_fn hp_val hd_val hi_inj

/-- Strengthened relative consistency theorem dropping the redundant `κ.IsInaccessible` and
`θ.IsInaccessible` hypotheses. -/
theorem gchPart4Theory_is_consistent_minimal
    {I : Type 0} {κ θ : Cardinal.{0}}
    (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
    [CountableInterFilter (U : Filter I)] [CardinalInterFilter (U : Filter I) κ]
    (hk : κ < θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (tail : ∀ μ : Cardinal.{0}, θ ≤ μ → (2 : Cardinal.{0}) ^ μ = Order.succ μ) :
    Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent := by
  obtain ⟨hκ, hθ⟩ := inaccessible_pair_of_fine_order_type U hk hf hn ht
  exact gchPart4Theory_is_consistent U a hk hκ hθ hf hn ht tail

/-- Variant of `gchPart4Theory_is_consistent_minimal` assuming `ℵ₀ < κ` instead of
`[CountableInterFilter (U : Filter I)]`. -/
theorem gchPart4Theory_is_consistent_of_aleph0_lt
    {I : Type 0} {κ θ : Cardinal.{0}}
    (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
    [CardinalInterFilter (U : Filter I) κ]
    (hω : ℵ₀ < κ) (hk : κ < θ)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (tail : ∀ μ : Cardinal.{0}, θ ≤ μ → (2 : Cardinal.{0}) ^ μ = Order.succ μ) :
    Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent := by
  have : CountableInterFilter (U : Filter I) :=
    CardinalInterFilter.toCountableInterFilter (U : Filter I) hω
  exact gchPart4Theory_is_consistent_minimal U a hk hf hn ht tail

/-- Relative consistency of `gchPart4Theory` (`ZFC + GCH + ω₂ → (ω₁ + ω, ω₁ + ω)²`) from
Kanamori's canonical hugeness predicate `IsHugeWithTarget κ θ` and ground tail GCH above `θ`. -/
theorem gchPart4Theory_is_consistent_of_hugeWithTarget
    {κ θ : Cardinal.{0}} (hHuge : IsHugeWithTarget κ θ)
    (tail : ∀ μ : Cardinal.{0}, θ ≤ μ → (2 : Cardinal.{0}) ^ μ = Order.succ μ) :
    Erdos1172Part4InternalGCHTheory.gchPart4Theory.is_consistent := by
  obtain ⟨I, U, a, hcnt, hcard, hk, hf, hn, ht⟩ :=
    isHugeWithTarget_iff_exists_fine_measure.mp hHuge
  have : CountableInterFilter (U : Filter I) := hcnt
  have : CardinalInterFilter (U : Filter I) κ := hcard
  exact gchPart4Theory_is_consistent_minimal U a hk hf hn ht tail

end MainConsistency

end Erdos1172AnonymousInternalLevy
