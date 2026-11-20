/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4AnonymousInternalLevyMaster
public import Erdos1172.Part4CohenNamedDenseRun
public import Erdos1172.Part4BooleanUltrapowerConstants

@[expose] public section

/-! # Localized Cohen cone calculus and stage-master truth-open forcing

This module proves:
1. `coneInMaster`: the principal-ideal cone in `LocalizedSourceCohen R m₀ hm₀` attached to any
   first-stage Cohen condition `p : bSet R` extending `m₀`, with exact faithfulness over `R`
   (`coneInMaster_inf_firstStageHom_eq_bot_iff`, `coneInMaster_le_firstStageHom_iff`,
   `coneInMaster_eq_unique`) and `< θ`-chain union closure (`prefix_union_condition_with_master`).
2. Δ₀ `InterpretedMaster.Formula` transfer from `anonymousAlgebra κ` through `boundedAnonName` and
   `j₀` into `W₁`, yielding same-cone dense-test extensions (`exists_dense_test_extension`).
3. `stageMaster_forces_constant_truthOpen`: whenever `q` lies in the lifted stage-`α` Lévy poset
   and extends `mapNames j_R (stageMasterGraph α).toBSet` on `coneInMaster hm₀ hp hsub`,
   membership `q ∈ᴮ O_lift(α, fun _ => b)` agrees on `coneInMaster hm₀ hp hsub` with the
   first-stage image `j_R (ambientLevyStageHom hα.le b)`.
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

universe u

namespace Erdos1172AnonymousInternalLevy

section LocalizedConeCalculus
variable {R : Type u} [NontrivialCompleteBooleanAlgebra R]

theorem nameCone_mono_of_subset {K p₁ p₂ : bSet R}
    (hp₁ : (⊤ : R) ≤ p₁ ∈ᴮ K) (hsub : (⊤ : R) ≤ p₁ ⊆ᴮ p₂) :
    nameCone K p₂ ≤ nameCone K p₁ := by
  let _ : Nonempty (Condition K) := condition_nonempty_of_mem hp₁
  let _ : NontrivialCompleteBooleanAlgebra (Erdos1172BooleanNameIteration.Algebra K) :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  unfold nameCone
  refine iSup_le fun ⟨q, hq_eq⟩ => ?_
  by_contra hnot
  let C₁ : Erdos1172BooleanNameIteration.Algebra K :=
    ⨆ r : {r : Condition K // r.value ≤ p₁ =ᴮ name r}, condition r.val
  have hpos : condition q ⊓ C₁ᶜ ≠ ⊥ := fun h0 =>
    hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
  obtain ⟨s, hs⟩ := exists_condition_le hpos
  obtain ⟨t, hts, htq⟩ :=
    (mem_condition_iff q s).mp (condition_le_iff.mp (hs.trans inf_le_left)) s le_rfl
  obtain ⟨r, hrv, hreq⟩ := exists_canonical_refinement t.nonzero (le_top.trans hp₁)
  let t' := shrink t r.value r.nonzero hrv
  have ht'_t : t' ≤ t := shrink_le t r.value r.nonzero hrv
  have ht'_r : t' ≤ r :=
    ⟨le_rfl,
     subset_trans' (bSet.subset_of_eq (bv_symm hreq))
       (subset_trans' (le_top.trans hsub)
         (subset_trans' (bSet.subset_of_eq ((ht'_t.1.trans htq.1).trans hq_eq))
           (ht'_t.1.trans htq.2)))⟩
  have hc_in : condition t' ≤ C₁ :=
    (condition_mono ht'_r).trans
      (le_iSup (fun x : {x : Condition K // x.value ≤ p₁ =ᴮ name x} => condition x.val) ⟨r, hreq⟩)
  have hc_out : condition t' ≤ C₁ᶜ :=
    (condition_mono (ht'_t.trans hts)).trans (hs.trans inf_le_right)
  exact condition_ne_bot t' (le_bot_iff.mp ((le_inf hc_in hc_out).trans inf_compl_eq_bot.le))

/-- Cone in `LocalizedSourceCohen R m₀ hm₀` attached to any first-stage Cohen condition `p`
extending `m₀`. -/
def coneInMaster {m₀ p : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : R) ≤ m₀ ⊆ᴮ p) :
    LocalizedSourceCohen R m₀ hm₀ :=
  ⟨(masterPositive p hp).val,
   nameCone_mono_of_subset (ErdosCohen.mem_conditions_iff.mpr hm₀) hsub⟩

theorem coneInMaster_ne_bot {m₀ p : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : R) ≤ m₀ ⊆ᴮ p) :
    coneInMaster hm₀ hp hsub ≠ ⊥ :=
  fun h0 => (masterPositive p hp).property (congrArg Subtype.val h0)

theorem coneInMaster_self {m₀ : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀) :
    coneInMaster hm₀ hm₀ subset_self = ⊤ :=
  Subtype.ext rfl

theorem coneInMaster_mono {m₀ p₁ p₂ : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp₁ : (⊤ : R) ≤ ErdosCohen.condition omegaOne p₁)
    (hsub₁ : (⊤ : R) ≤ m₀ ⊆ᴮ p₁)
    (hp₂ : (⊤ : R) ≤ ErdosCohen.condition omegaOne p₂)
    (hsub₂ : (⊤ : R) ≤ m₀ ⊆ᴮ p₂)
    (h₁₂ : (⊤ : R) ≤ p₁ ⊆ᴮ p₂) :
    coneInMaster hm₀ hp₂ hsub₂ ≤ coneInMaster hm₀ hp₁ hsub₁ :=
  nameCone_mono_of_subset (ErdosCohen.mem_conditions_iff.mpr hp₁) h₁₂

theorem coneInMaster_inf_firstStageHom_eq_bot_iff {m₀ p : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : R) ≤ m₀ ⊆ᴮ p) (r : R) :
    coneInMaster hm₀ hp hsub ⊓ localizedFirstStageHom hm₀ r = ⊥ ↔ r = ⊥ := by
  constructor
  · intro hbot
    by_contra hr_ne
    have hp_mem : (⊤ : R) ≤ p ∈ᴮ ErdosCohen.conditions (omegaOne : bSet R) :=
      ErdosCohen.mem_conditions_iff.mpr hp
    obtain ⟨q, hqv, hqeq⟩ := exists_canonical_refinement hr_ne (le_top.trans hp_mem)
    have hloc : nameCone (ErdosCohen.conditions (omegaOne : bSet R)) p ⊓
        Erdos1172CohenIteration.omegaOneFirstStageHom q.value = condition q :=
      nameCone_local (ErdosCohen.conditions (omegaOne : bSet R)) q hqeq
    have hle : condition q ≤ (coneInMaster hm₀ hp hsub ⊓ localizedFirstStageHom hm₀ r).val := by
      change condition q ≤ (masterPositive p hp).val ⊓
        (Erdos1172CohenIteration.omegaOneFirstStageHom r ⊓ (masterPositive m₀ hm₀).val)
      rw [← hloc]
      exact le_inf inf_le_left (le_inf
        (inf_le_right.trans (OrderHomClass.mono Erdos1172CohenIteration.omegaOneFirstStageHom hqv))
        (inf_le_left.trans (coneInMaster hm₀ hp hsub).property))
    rw [hbot] at hle
    exact condition_ne_bot q (le_bot_iff.mp hle)
  · rintro rfl
    rw [BotHomClass.map_bot, inf_bot_eq]

theorem coneInMaster_le_firstStageHom_iff {m₀ p : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : R) ≤ m₀ ⊆ᴮ p) (r : R) :
    coneInMaster hm₀ hp hsub ≤ localizedFirstStageHom hm₀ r ↔ r = ⊤ := by
  rw [← disjoint_compl_right_iff, disjoint_iff, ← completeHom_compl,
    coneInMaster_inf_firstStageHom_eq_bot_iff hm₀ hp hsub rᶜ, compl_eq_bot]

omit [NontrivialCompleteBooleanAlgebra R] in
private theorem inf_compl_le_bot_of_inf_le {L : Type u} [BooleanAlgebra L] {c a b : L}
    (h : c ⊓ a ≤ c ⊓ b) : c ⊓ (a ⊓ bᶜ) ≤ ⊥ := by
  calc
    c ⊓ (a ⊓ bᶜ) = (c ⊓ a) ⊓ bᶜ := (inf_assoc c a bᶜ).symm
    _ ≤ (c ⊓ b) ⊓ bᶜ := inf_le_inf_right bᶜ h
    _ = c ⊓ (b ⊓ bᶜ) := inf_assoc c b bᶜ
    _ = ⊥ := by rw [inf_compl_eq_bot, inf_bot_eq]

omit [NontrivialCompleteBooleanAlgebra R] in
theorem cone_eq_of_le_and_compl_le {L : Type u} [BooleanAlgebra L] {c u v : L}
    (h1 : c ⊓ v ≤ u) (h0 : c ⊓ vᶜ ≤ uᶜ) : c ⊓ u = c ⊓ v := by
  apply le_antisymm
  · calc
      c ⊓ u = (c ⊓ u) ⊓ (v ⊔ vᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
      _ = ((c ⊓ u) ⊓ v) ⊔ ((c ⊓ u) ⊓ vᶜ) := inf_sup_left _ _ _
      _ ≤ (c ⊓ v) ⊔ (u ⊓ uᶜ) := by
        refine sup_le_sup (inf_le_inf_right v inf_le_left) ?_
        have hcomm : (c ⊓ u) ⊓ vᶜ = u ⊓ (c ⊓ vᶜ) := by ac_rfl
        rw [hcomm]
        exact inf_le_inf_left u h0
      _ = c ⊓ v := by rw [inf_compl_eq_bot, sup_bot_eq]
  · exact le_inf inf_le_left h1

theorem coneInMaster_le_unique {m₀ p : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : R) ≤ m₀ ⊆ᴮ p) {r₁ r₂ : R}
    (hle : coneInMaster hm₀ hp hsub ⊓ localizedFirstStageHom hm₀ r₁ ≤
      coneInMaster hm₀ hp hsub ⊓ localizedFirstStageHom hm₀ r₂) :
    r₁ ≤ r₂ := by
  have hbot : coneInMaster hm₀ hp hsub ⊓ localizedFirstStageHom hm₀ (r₁ ⊓ r₂ᶜ) = ⊥ := by
    apply le_bot_iff.mp
    rw [completeHom_inf, completeHom_compl]
    exact inf_compl_le_bot_of_inf_le hle
  exact disjoint_compl_right_iff.mp (disjoint_iff.mpr
    ((coneInMaster_inf_firstStageHom_eq_bot_iff hm₀ hp hsub _).mp hbot))

theorem coneInMaster_eq_unique {m₀ p : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : R) ≤ m₀ ⊆ᴮ p) {r₁ r₂ : R}
    (heq : coneInMaster hm₀ hp hsub ⊓ localizedFirstStageHom hm₀ r₁ =
      coneInMaster hm₀ hp hsub ⊓ localizedFirstStageHom hm₀ r₂) :
    r₁ = r₂ :=
  le_antisymm (coneInMaster_le_unique hm₀ hp hsub heq.le)
    (coneInMaster_le_unique hm₀ hp hsub heq.ge)

theorem prefix_union_condition_with_master {θ : Cardinal.{u}}
    (hθ_w1 : (⊤ : R) ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaOne)
    {m₀ : bSet R} (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (β : θ.ord.ToType) (p_fam : Set.Iio β → bSet R)
    (hcond : ∀ γ, (⊤ : R) ≤ ErdosCohen.condition omegaOne (p_fam γ))
    (hsub₀ : ∀ γ, (⊤ : R) ≤ m₀ ⊆ᴮ p_fam γ)
    (hmono : ∀ γ₁ γ₂, γ₁ ≤ γ₂ → (⊤ : R) ≤ p_fam γ₁ ⊆ᴮ p_fam γ₂) :
    ∃ p_in : bSet R,
      (⊤ : R) ≤ ErdosCohen.condition omegaOne p_in ∧
      (⊤ : R) ≤ m₀ ⊆ᴮ p_in ∧
      ∀ γ : Set.Iio β, (⊤ : R) ≤ p_fam γ ⊆ᴮ p_in := by
  classical
  by_cases hne : Nonempty (Set.Iio β)
  · let γ₀ := Classical.choice hne
    let F : bSet R := .mk (Set.Iio β) p_fam (fun _ => ⊤)
    have hF_ext (γ : Set.Iio β) : (⊤ : R) ≤ p_fam γ ⊆ᴮ bv_union F := by
      rw [subset_unfold']
      refine le_iInf fun x => deduction.mp ?_
      exact (bv_union_spec_split F x).mpr
        (le_iSup_of_le (p_fam γ) (le_inf (le_top.trans (mem_mk' F γ)) inf_le_right))
    have hp_in : (⊤ : R) ≤ ErdosCohen.condition omegaOne (bv_union F) :=
      Erdos1172CohenIteration.NamedRun.prefix_union_condition
        (bv_symm hθ_w1) β p_fam hcond hmono
    exact ⟨bv_union F, hp_in, subset_trans' (hsub₀ γ₀) (hF_ext γ₀), hF_ext⟩
  · exact ⟨m₀, hm₀, subset_self, fun γ => (hne ⟨γ⟩).elim⟩

end LocalizedConeCalculus

section DeltaZeroTransferHelpers
variable {I : Type u} {κ θ : Cardinal.{u}}
variable (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]

theorem transfer_supported_formula {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    {V : Type*} (φ : InterpretedMaster.Formula V)
    (env : I → V → bSet (anonymousAlgebra κ)) (henv : Preparation.SupportedEnv U a env)
    (htruth : ∀ᶠ i in U, (⊤ : anonymousAlgebra κ) ≤ φ.eval (env i)) :
    (⊤ : W₁) ≤ φ.eval (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun i => env i v))) := by
  have hv : value U (fun i => φ.eval (env i)) = ⊤ :=
    value_eq_of_eventuallyEq U (g := fun _ => ⊤) (htruth.mono fun _ hi => top_unique hi)
      |>.trans (value_top U)
  have hVA : (⊤ : Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) ≤
      φ.eval (fun v => Preparation.boundedAnonName U a (fun i => env i v)) := by
    rw [← Preparation.boundedAnon_formula_eval U a hk hf hn ht hκ φ env henv, hv]
  have hm := OrderHomClass.mono j₀ hVA
  rw [TopHomClass.map_top, InterpretedMaster.Formula.map_eval] at hm
  exact hm

theorem transfer_const_formula {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    {V : Type*} (φ : InterpretedMaster.Formula V)
    (env : V → bSet (anonymousAlgebra κ))
    (htruth : (⊤ : anonymousAlgebra κ) ≤ φ.eval env) :
    (⊤ : W₁) ≤ φ.eval (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun _ => env v))) :=
  transfer_supported_formula U a hk hf hn ht hκ j₀ φ (fun _ => env)
    ⟨Classical.choice ‹Nonempty θ.ord.ToType›, fun _ => env, Eventually.of_forall fun _ => rfl⟩
    (Eventually.of_forall fun _ => htruth)

theorem transfer_const_subset {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (X Y : bSet (anonymousAlgebra κ)) (hsub : (⊤ : anonymousAlgebra κ) ≤ X ⊆ᴮ Y) :
    (⊤ : W₁) ≤ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => X)) ⊆ᴮ
      mapNames j₀ (Preparation.boundedAnonName U a (fun _ => Y)) := by
  have hVA : (⊤ : Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) ≤
      Preparation.boundedAnonName U a (fun _ => X) ⊆ᴮ
        Preparation.boundedAnonName U a (fun _ => Y) := by
    rw [← Preparation.boundedAnonName_subset U a hk hf hn ht hκ (fun _ => X) (fun _ => Y)
      (Preparation.Supported.const X) (Preparation.Supported.const Y),
      value_eq_of_eventuallyEq U (g := fun _ => ⊤) (Eventually.of_forall fun _ => top_unique hsub),
      value_top]
  have hm := OrderHomClass.mono j₀ hVA
  rw [TopHomClass.map_top, map_subset] at hm
  exact hm

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
theorem subset_iff_allIn_mem {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (X Y : bSet B) :
    (X ⊆ᴮ Y) = allIn X (fun z => z ∈ᴮ Y) :=
  subset_unfold'

def denseTestFormula : InterpretedMaster.Formula Bool :=
  .allIn false (.someIn (some true) (.allIn (some none) (.mem none (some none))))

private theorem denseTestFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (D P : bSet B) :
    denseTestFormula.eval (fun b => if b then D else P) =
      allIn P (fun g => someIn D (fun r => allIn g (fun x => x ∈ᴮ r))) :=
  rfl

/-- Every stage-`α` dense subset `D ⊆ᴮ internalLevyPoset κ α` admits an actual mixed witness
`z : bSet W₁` extending `q₀` at the UNCHANGED Boolean condition `Γ : W₁`. -/
theorem exists_dense_test_extension {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (α : Ordinal.{u}) (D : bSet (anonymousAlgebra κ))
    (hD_sub : (⊤ : anonymousAlgebra κ) ≤ D ⊆ᴮ internalLevyPoset κ α)
    (hD_dense : (⊤ : anonymousAlgebra κ) ≤
      allIn (internalLevyPoset κ α) (fun g => someIn D (fun r => g ⊆ᴮ r)))
    {Γ : W₁} {q₀ : bSet W₁}
    (hq₀ : Γ ≤ q₀ ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α))) :
    ∃ z : bSet W₁,
      Γ ≤ z ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α)) ∧
      Γ ≤ z ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => D)) ∧
      Γ ≤ q₀ ⊆ᴮ z := by
  let P_A := internalLevyPoset κ α
  let env : Bool → bSet (anonymousAlgebra κ) := fun b => if b then D else P_A
  have hφ_A : (⊤ : anonymousAlgebra κ) ≤ denseTestFormula.eval env := by
    rw [denseTestFormula_eval]
    simp_rw [← subset_iff_allIn_mem]
    exact hD_dense
  have hφ_W := transfer_const_formula U a hk hf hn ht hκ j₀ denseTestFormula env hφ_A
  let P_W := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => P_A))
  let D_W := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => D))
  have henv_W : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun _ => env v))) =
      (fun b => if b then D_W else P_W) := by
    funext b; cases b <;> rfl
  rw [henv_W, denseTestFormula_eval] at hφ_W
  simp_rw [← subset_iff_allIn_mem] at hφ_W
  have hex_W : Γ ≤ ⨆ r : bSet W₁, (r ∈ᴮ D_W) ⊓ (q₀ ⊆ᴮ r) :=
    allIn_elim (le_top.trans hφ_W) hq₀
  obtain ⟨z, hz⟩ := exists_convert hex_W (B_ext_inf B_ext_mem_left B_ext_subset_right)
  have hDP_W := transfer_const_subset U a hk hf hn ht hκ j₀ D P_A hD_sub
  exact ⟨z, mem_of_mem_subset (le_top.trans hDP_W) (hz.trans inf_le_left),
    hz.trans inf_le_left, hz.trans inf_le_right⟩

end DeltaZeroTransferHelpers

section StageMasterTruthOpen
variable {I : Type u} {κ θ : Cardinal.{u}}
variable (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]

private theorem liftA_check_groundValidTriple (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    {α : Ordinal.{u}} (t : GroundValidTriple κ α) :
    let VA := Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
    (⊤ : VA) ≤ Preparation.boundedAnonName U a (fun _ => check ((levyTriplePSet κ α).Func t.val)) =ᴮ
      check ((liftedTriplePSet U a θ α).Func (liftValidTriple U a hk hf hn ht hκ t).val) := by
  intro VA
  let A := anonymousAlgebra κ
  let ξ_ord := ordOfPSetIdx t.val.1.1
  let η_ord := ordOfPSetIdx t.val.1.2
  let y_ord := ordOfPSetIdx t.val.2
  let P_lhs : bSet A := check ((levyTriplePSet κ α).Func t.val)
  let P_ξ : bSet A := check (PSet.ordinalMk ξ_ord)
  let P_η : bSet A := check (PSet.ordinalMk η_ord)
  let P_y : bSet A := check (PSet.ordinalMk y_ord)
  let P_pair1 : bSet A := pair P_ξ P_η
  let P_rhs : bSet A := pair P_pair1 P_y
  have hA_eq : (⊤ : A) ≤ P_lhs =ᴮ P_rhs :=
    bv_trans (check_levyTriplePSet_func α t.val)
      (pair_congr
        (pair_congr (check_bv_eq (ordOfPSetIdx_equiv t.val.1.1))
          (check_bv_eq (ordOfPSetIdx_equiv t.val.1.2)))
        (check_bv_eq (ordOfPSetIdx_equiv t.val.2)))
  have hVA_1 : (⊤ : VA) ≤
      Preparation.boundedAnonName U a (fun _ => P_lhs) =ᴮ
      Preparation.boundedAnonName U a (fun _ => P_rhs) := by
    rw [← Preparation.boundedAnonName_eq U a hk hf hn ht hκ (fun _ => P_lhs) (fun _ => P_rhs)
      (Preparation.Supported.const P_lhs) (Preparation.Supported.const P_rhs),
      value_eq_of_eventuallyEq U (g := fun _ => ⊤) (Eventually.of_forall fun _ => top_unique hA_eq),
      value_top]
  have hVA_2 : (⊤ : VA) ≤
      Preparation.boundedAnonName U a (fun _ => P_rhs) =ᴮ
      pair (pair (check (PSet.ordinalMk (ordinalImage U a ξ_ord)))
        (check (PSet.ordinalMk η_ord)))
        (check (PSet.ordinalMk (ordinalImage U a y_ord))) := by
    refine bv_trans (Preparation.boundedAnonName_pair U a hk hf hn ht hκ
      (fun _ => P_pair1) (fun _ => P_y)
      (Preparation.Supported.const P_pair1) (Preparation.Supported.const P_y)) ?_
    refine pair_congr ?_ (Preparation.boundedAnon_ordinal U a hk hf hn ht hκ y_ord)
    refine bv_trans (Preparation.boundedAnonName_pair U a hk hf hn ht hκ
      (fun _ => P_ξ) (fun _ => P_η)
      (Preparation.Supported.const P_ξ) (Preparation.Supported.const P_η)) ?_
    exact pair_congr (Preparation.boundedAnon_ordinal U a hk hf hn ht hκ ξ_ord)
      (Preparation.boundedAnon_fix_below U a hk hf hn ht hκ (ordOfPSetIdx_lt t.val.1.2))
  let idx' := (liftValidTriple U a hk hf hn ht hκ t).val
  have heq1 : PSet.ordinalMk (ordinalImage U a ξ_ord) = PSet.ordinalMk (ordOfPSetIdx idx'.1.1) :=
    congrArg PSet.ordinalMk (liftValidTriple_ord_first U a hk hf hn ht hκ t).symm
  have heq2 : PSet.ordinalMk η_ord = PSet.ordinalMk (ordOfPSetIdx idx'.1.2) :=
    congrArg PSet.ordinalMk (liftValidTriple_ord_second U a hk hf hn ht hκ t).symm
  have heq3 : PSet.ordinalMk (ordinalImage U a y_ord) = PSet.ordinalMk (ordOfPSetIdx idx'.2) :=
    congrArg PSet.ordinalMk (liftValidTriple_ord_val U a hk hf hn ht hκ t).symm
  have e1 : PSet.Equiv (PSet.ordinalMk (ordinalImage U a ξ_ord))
      ((PSet.ordinalMk (ordinalImage U a α)).Func idx'.1.1) :=
    heq1 ▸ PSet.Equiv.symm (ordOfPSetIdx_equiv idx'.1.1)
  have e2 : PSet.Equiv (PSet.ordinalMk η_ord)
      ((PSet.ordinalMk θ.ord).Func idx'.1.2) :=
    heq2 ▸ PSet.Equiv.symm (ordOfPSetIdx_equiv idx'.1.2)
  have e3 : PSet.Equiv (PSet.ordinalMk (ordinalImage U a y_ord))
      ((PSet.ordinalMk (ordinalImage U a α)).Func idx'.2) :=
    heq3 ▸ PSet.Equiv.symm (ordOfPSetIdx_equiv idx'.2)
  exact bv_trans hVA_1 (bv_trans hVA_2
    (bv_trans (pair_congr (pair_congr (check_bv_eq e1) (check_bv_eq e2)) (check_bv_eq e3))
      (bv_symm (check_liftedTriplePSet_func U a θ α idx'))))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem bot_of_ground_levyBoundPred_ge {α : Ordinal.{u}}
    (idx : (levyTriplePSet κ α).Type) (hge : ordOfPSetIdx idx.1.1 ≤ ordOfPSetIdx idx.2) :
    levyBoundPred (ordinalCarrier κ.ord) (ordinalCarrier α)
      (check ((levyTriplePSet κ α).Func idx) : bSet (anonymousAlgebra κ)) ≤ ⊥ := by
  let A := anonymousAlgebra κ
  let P₀ : bSet A := pair
    (pair (check ((PSet.ordinalMk α).Func idx.1.1))
      (check ((PSet.ordinalMk κ.ord).Func idx.1.2)))
    (check ((PSet.ordinalMk α).Func idx.2))
  have hp₀ : (⊤ : A) ≤ check ((levyTriplePSet κ α).Func idx) =ᴮ P₀ :=
    check_levyTriplePSet_func α idx
  change (⨆ ξ : bSet A, (ξ ∈ᴮ ordinalCarrier α) ⊓ _) ≤ ⊥
  refine iSup_le fun ξ => ?_
  change (ξ ∈ᴮ _) ⊓ (⨆ η : bSet A, (η ∈ᴮ ordinalCarrier κ.ord) ⊓ _) ≤ ⊥
  erw [inf_iSup_eq]
  refine iSup_le fun η => ?_
  change (ξ ∈ᴮ _) ⊓ ((η ∈ᴮ _) ⊓ (⨆ y : bSet A, (y ∈ᴮ ξ) ⊓ _)) ≤ ⊥
  erw [← inf_assoc, inf_iSup_eq]
  refine iSup_le fun y => ?_
  let F : A := ((ξ ∈ᴮ ordinalCarrier α) ⊓ (η ∈ᴮ ordinalCarrier κ.ord)) ⊓
    ((y ∈ᴮ ξ) ⊓ (check ((levyTriplePSet κ α).Func idx) =ᴮ pair (pair ξ η) y))
  have hp_eq : F ≤ P₀ =ᴮ pair (pair ξ η) y :=
    bv_trans (le_top.trans (bv_symm hp₀)) (inf_le_right.trans inf_le_right)
  have hξ_eq : F ≤ check ((PSet.ordinalMk α).Func idx.1.1) =ᴮ ξ :=
    (pair_eq_pair_iff.mp (pair_eq_pair_iff.mp hp_eq).1).1
  have hy_eq : F ≤ check ((PSet.ordinalMk α).Func idx.2) =ᴮ y :=
    (pair_eq_pair_iff.mp hp_eq).2
  have hy_in : F ≤ check (PSet.ordinalMk (ordOfPSetIdx idx.2)) ∈ᴮ
      check (PSet.ordinalMk (ordOfPSetIdx idx.1.1)) :=
    mem_congr
      (bv_trans (bv_symm hy_eq) (check_bv_eq (ordOfPSetIdx_equiv idx.2)))
      (bv_trans (bv_symm hξ_eq) (check_bv_eq (ordOfPSetIdx_equiv idx.1.1)))
      (inf_le_right.trans inf_le_left)
  rw [mem_unfold] at hy_in
  refine hy_in.trans (iSup_le fun k => ?_)
  have hneqv : ¬PSet.Equiv (PSet.ordinalMk (ordOfPSetIdx idx.2))
      ((PSet.ordinalMk (ordOfPSetIdx idx.1.1)).Func (check_cast k)) := by
    intro he
    have heq := Ordinal.toZFSet_injective (ZFSet.sound
      (PSet.Equiv.trans he (ordOfPSetIdx_equiv (check_cast k))))
    exact (hge.trans_lt (heq ▸ ordOfPSetIdx_lt (check_cast k))).false
  rw [check_func, check_bval_top, top_inf_eq, check_bv_eq_bot_of_not_equiv hneqv]

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem smallLevyCondition_checked_cover {α : Ordinal.{u}}
    (s : SmallLevyCondition κ α) :
    ∃ (S : Type u) (_hS : #S < κ) (tr : S → GroundValidTriple κ α),
      s.val.value ≤ name s.val ⊆ᴮ
        .mk S (fun k => check ((levyTriplePSet κ α).Func (tr k).val))
          (fun k => s.val.value ⊓ (check ((levyTriplePSet κ α).Func (tr k).val) ∈ᴮ name s.val)) := by
  let A := anonymousAlgebra κ
  let P_α := levyTriplePSet κ α
  let S_set : Set (GroundValidTriple κ α) :=
    {t | s.val.value ⊓ (check (P_α.Func t.val) ∈ᴮ name s.val) ≠ ⊥}
  have hS_lt : #S_set < κ := by
    let emb (x : S_set) : tripleSupport α s.val :=
      ⟨⟨x.val.val, s.val.value ⊓ (check (P_α.Func x.val.val) ∈ᴮ name s.val)⟩, x.property, rfl⟩
    have hinj : Function.Injective emb := by
      intro x₁ x₂ heq
      exact Subtype.ext (Subtype.ext (Prod.mk.inj (congrArg Subtype.val heq)).1)
    exact (Cardinal.mk_le_of_injective hinj).trans_lt s.property
  refine ⟨S_set, hS_lt, Subtype.val, ?_⟩
  have hs_sub : s.val.value ≤ name s.val ⊆ᴮ check P_α :=
    subset_trans' (countableCollapse_mem.mp (mem_internalLevyCollapse.mp (name_mem s.val)).1).1
      (bSet.subset_of_eq (le_top.trans (prod_ordinalCarrier_eq_check_levyTriplePSet (B := A) α)))
  have hs_bd : s.val.value ≤ levyAllBounded (ordinalCarrier κ.ord) (ordinalCarrier α) (name s.val) :=
    (mem_internalLevyCollapse.mp (name_mem s.val)).2
  rw [subset_unfold']
  refine le_iInf fun z => deduction.mp ?_
  let cP : bSet A := check P_α
  have hz_P : s.val.value ⊓ (z ∈ᴮ name s.val) ≤ z ∈ᴮ cP :=
    mem_of_mem_subset (inf_le_left.trans hs_sub) inf_le_right
  conv at hz_P => rhs; rw [mem_unfold]
  refine ((le_inf le_rfl hz_P).trans_eq (inf_iSup_eq _ _)).trans (iSup_le fun k => ?_)
  let idx : P_α.Type := check_cast (𝔹 := A) k
  let E : A := (s.val.value ⊓ (z ∈ᴮ name s.val)) ⊓
    (cP.bval k ⊓ (z =ᴮ cP.func k))
  have hE_eq : E ≤ z =ᴮ check (P_α.Func idx) := by
    have hr : E ≤ z =ᴮ cP.func k := inf_le_right.trans inf_le_right
    exact (@check_func A _ P_α k) ▸ hr
  have hE_mem : E ≤ s.val.value ⊓ (check (P_α.Func idx) ∈ᴮ name s.val) :=
    le_inf (inf_le_left.trans inf_le_left)
      (mem_congr hE_eq bv_refl (inf_le_left.trans inf_le_right))
  by_cases hw : s.val.value ⊓ (check (P_α.Func idx) ∈ᴮ name s.val) = ⊥
  · exact (hE_mem.trans_eq hw).trans bot_le
  · have hvalid : ordOfPSetIdx idx.2 < ordOfPSetIdx idx.1.1 := by
      by_contra hnot
      have hbd_w : s.val.value ⊓ (check (P_α.Func idx) ∈ᴮ name s.val) ≤
          levyBoundPred (ordinalCarrier κ.ord) (ordinalCarrier α) (check (P_α.Func idx)) :=
        allIn_elim (inf_le_left.trans hs_bd) inf_le_right
      exact hw (le_bot_iff.mp (hbd_w.trans (bot_of_ground_levyBoundPred_ge idx (le_of_not_gt hnot))))
    let t_s : S_set := ⟨⟨idx, hvalid⟩, hw⟩
    exact (le_inf hE_mem hE_eq).trans
      ((le_iSup (fun m : S_set =>
          (s.val.value ⊓ (check (P_α.Func m.val.val) ∈ᴮ name s.val)) ⊓
            (z =ᴮ check (P_α.Func m.val.val))) t_s).trans_eq
        (mem_unfold (u := z) (v := .mk S_set (fun k => check (P_α.Func k.val.val))
          (fun k => s.val.value ⊓ (check (P_α.Func k.val.val) ∈ᴮ name s.val)))).symm)

def upwardFormula : InterpretedMaster.Formula Bool :=
  .allIn true (.allIn (some false)
    (.imp (.allIn (some none) (.mem none (some none))) (.mem none (some (some true)))))

private theorem upwardFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (O P : bSet B) :
    upwardFormula.eval (fun bl => if bl then O else P) =
      allIn O (fun g => allIn P (fun r => _root_.imp (allIn g (fun z => z ∈ᴮ r)) (r ∈ᴮ O))) :=
  rfl

def disjFormula : InterpretedMaster.Formula Bool :=
  .allIn true (.neg (.mem none (some false)))

private theorem disjFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (O₁ O₂ : bSet B) :
    disjFormula.eval (fun bl => if bl then O₁ else O₂) =
      allIn O₁ (fun z => (z ∈ᴮ O₂)ᶜ) :=
  rfl

private theorem stageMaster_forces_constant_truthOpen_gen
    {R W₁ : Type u} [NontrivialCompleteBooleanAlgebra R] [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    {α : Ordinal.{u}}
    (u : CompleteLatticeHom (Erdos1172LevyCohen.Algebra κ) R)
    (e_α : CompleteLatticeHom (InternalLevyStage κ α) R)
    (he_src : ∀ d : anonymousAlgebra κ,
      e_α (sourceHom (internalLevyPoset κ α) d) = u (inclusion (anonymousAlgebra κ) d))
    (j_R : CompleteLatticeHom R W₁)
    (c_p : W₁)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (hj₀_base : ∀ d : anonymousAlgebra κ,
      j₀ (value U (fun _ => d)) = j_R (u (inclusion (anonymousAlgebra κ) d)))
    (q : bSet W₁)
    (hq_poset : c_p ≤
      q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α)))
    (hq_master : c_p ≤
      mapNames j_R
        (.mk (GroundValidTriple κ α)
          (fun t => check ((liftedTriplePSet U a θ α).Func (liftValidTriple U a hk hf hn ht hκ t).val))
          (fun t => e_α (levyEntry α t.val))) ⊆ᴮ q)
    (b : InternalLevyStage κ α) :
    c_p ⊓ (q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => levyTruthOpen α b))) =
    c_p ⊓ j_R (e_α b) := by
  let A := anonymousAlgebra κ
  let VA := Erdos1172BooleanUltrapower.Algebra U A
  let P_A := internalLevyPoset κ α
  let P_W := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => P_A))
  let M_R : bSet R := .mk (GroundValidTriple κ α)
    (fun t => check ((liftedTriplePSet U a θ α).Func (liftValidTriple U a hk hf hn ht hκ t).val))
    (fun t => e_α (levyEntry α t.val))
  have hone_dir (x : InternalLevyStage κ α) :
      c_p ⊓ j_R (e_α x) ≤
        q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => levyTruthOpen α x)) := by
    let O_A := levyTruthOpen α x
    let O_W := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => O_A))
    -- Upward closure of `O_W` inside `P_W` via Δ₀ formula transfer.
    let env_up : Bool → bSet A := fun bl => if bl then O_A else P_A
    have hup_A : (⊤ : A) ≤ upwardFormula.eval env_up := by
      rw [upwardFormula_eval]
      simp_rw [← subset_iff_allIn_mem]
      exact allIn_intro fun {Δ₁} _ g hg => allIn_intro fun {Δ₂} hΔ g' hg' => deduction.mp
        (levyTruthOpen_upward (inf_le_left.trans (hΔ.trans hg)) (inf_le_left.trans hg') inf_le_right)
    have hup_W := transfer_const_formula U a hk hf hn ht hκ j₀ upwardFormula env_up hup_A
    have henv_up_W : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun _ => env_up v))) =
        (fun bl => if bl then O_W else P_W) := by
      funext bl; cases bl <;> rfl
    rw [henv_up_W, upwardFormula_eval] at hup_W
    simp_rw [← subset_iff_allIn_mem] at hup_W
    conv_lhs => rw [← smallLevyCondition_iSup_eq hκ α x, _root_.map_iSup e_α, _root_.map_iSup j_R]
    rw [inf_iSup_eq]
    refine iSup_le fun ⟨s, hs_x⟩ => ?_
    let v_s := s.val.value
    have hv_le : j_R (e_α (condition s.val)) ≤ j₀ (value U (fun _ => v_s)) := by
      rw [hj₀_base v_s, ← he_src v_s]
      exact OrderHomClass.mono (j_R.comp e_α) ((condition_le_source (internalLevyPoset κ α) s.val v_s).mpr le_rfl)
    -- `mapNames j₀ (liftA (name s.val)) ∈ᴮ O_W` on `j₀ (value U (fun _ => v_s))`.
    have hs_in_O : j₀ (value U (fun _ => v_s)) ≤
        mapNames j₀ (Preparation.boundedAnonName U a (fun _ => name s.val)) ∈ᴮ O_W := by
      have hA_in : v_s ≤ name s.val ∈ᴮ O_A := levyTruthOpen_forces α s.val x hs_x
      have hVA_in : value U (fun _ => v_s) ≤
          Preparation.boundedAnonName U a (fun _ => name s.val) ∈ᴮ
            Preparation.boundedAnonName U a (fun _ => O_A) := by
        rw [← Preparation.boundedAnonName_mem U a hk hf hn ht hκ (fun _ => name s.val) (fun _ => O_A)
          (Preparation.Supported.const _) (Preparation.Supported.const _)]
        exact (value_le_value_iff U).mpr (Eventually.of_forall fun _ => hA_in)
      simpa only [map_mem] using OrderHomClass.mono j₀ hVA_in
    -- `mapNames j₀ (liftA (name s.val)) ⊆ᴮ q` on `c_p ⊓ j_R (e_α (condition s.val))`.
    obtain ⟨S, hS_lt, tr, hcov_A⟩ := smallLevyCondition_checked_cover s
    let wt_s (k : S) : A := v_s ⊓ (check ((levyTriplePSet κ α).Func (tr k).val) ∈ᴮ name s.val)
    let N_s : bSet A := .mk S (fun k => check ((levyTriplePSet κ α).Func (tr k).val)) wt_s
    have hsub_Ns : j₀ (value U (fun _ => v_s)) ≤
        mapNames j₀ (Preparation.boundedAnonName U a (fun _ => name s.val)) ⊆ᴮ
          mapNames j₀ (Preparation.boundedAnonName U a (fun _ => N_s)) := by
      have hVA_sub : value U (fun _ => v_s) ≤
          Preparation.boundedAnonName U a (fun _ => name s.val) ⊆ᴮ
            Preparation.boundedAnonName U a (fun _ => N_s) := by
        rw [← Preparation.boundedAnonName_subset U a hk hf hn ht hκ (fun _ => name s.val) (fun _ => N_s)
          (Preparation.Supported.const _) (Preparation.Supported.const _)]
        exact (value_le_value_iff U).mpr (Eventually.of_forall fun _ => hcov_A)
      simpa only [map_subset] using OrderHomClass.mono j₀ hVA_sub
    let G_VA : bSet VA := .mk S
      (fun k => check ((liftedTriplePSet U a θ α).Func (liftValidTriple U a hk hf hn ht hκ (tr k)).val))
      (fun k => value U (fun _ => wt_s k))
    have hNs_GVA : (⊤ : VA) ≤ Preparation.boundedAnonName U a (fun _ => N_s) ⊆ᴮ G_VA := by
      rw [Preparation.boundedAnonName_unfold (κ := κ) U a (fun _ => N_s), subset_unfold]
      refine le_iInf fun ch => deduction.mp ?_
      rw [top_inf_eq]
      have hch_mem : value U (Erdos1172BooleanUltrapower.weight U (fun _ => N_s) ch.val) ≤
          value U (fun i => Erdos1172BooleanUltrapower.child U (fun _ => N_s) ch.val i ∈ᴮ N_s) := by
        apply (value_le_value_iff U).mpr
        filter_upwards [ch.val.large] with i hi
        simpa only [Erdos1172BooleanUltrapower.weight, selected, Erdos1172BooleanUltrapower.child,
          dif_pos hi] using mem_mk' N_s (ch.val.pick ⟨i, hi⟩)
      have hsmall_mem : value U (fun i => Erdos1172BooleanUltrapower.child U (fun _ => N_s) ch.val i ∈ᴮ N_s) ≤
          Preparation.boundedAnonName U a (Erdos1172BooleanUltrapower.child U (fun _ => N_s) ch.val) ∈ᴮ G_VA := by
        dsimp only [N_s]
        conv_lhs => enter [2, i]; rw [mem_unfold]
        dsimp only [bSet.type, bSet.bval, bSet.func]
        rw [value_small_iSup U κ hS_lt]
        dsimp only [G_VA]
        rw [mem_unfold]
        dsimp only [bSet.type, bSet.bval, bSet.func]
        refine iSup_mono fun k => ?_
        let f_ch := Erdos1172BooleanUltrapower.child U (fun _ => N_s) ch.val
        let f_tr : I → bSet A := fun _ => check ((levyTriplePSet κ α).Func (tr k).val)
        rw [value_inf, Preparation.boundedAnonName_eq U a hk hf hn ht hκ f_ch f_tr
          ch.property (Preparation.Supported.const _)]
        exact le_inf inf_le_left
          (bv_trans inf_le_right (le_top.trans (liftA_check_groundValidTriple U a hk hf hn ht hκ (tr k))))
      exact hch_mem.trans hsmall_mem
    have hGVA_MR : j_R (e_α (condition s.val)) ≤ mapNames j₀ G_VA ⊆ᴮ mapNames j_R M_R := by
      dsimp only [G_VA, M_R]
      rw [mapNames_mk, mapNames_mk, subset_unfold]
      dsimp only [bSet.type, bSet.bval, bSet.func]
      refine le_iInf fun k => deduction.mp ?_
      rw [mem_unfold]
      dsimp only [bSet.type, bSet.bval, bSet.func]
      refine le_iSup_of_le (tr k) (le_inf ?_ ?_)
      · rw [hj₀_base (wt_s k), ← he_src (wt_s k), ← completeHom_inf j_R, ← completeHom_inf e_α]
        exact OrderHomClass.mono (j_R.comp e_α)
          (condition_inf_sourceHom_le_levyEntry α s.val (tr k).val)
      · exact le_top.trans (by rw [map_check, map_check]; exact bv_refl)
    have hnm_sub_q : c_p ⊓ j_R (e_α (condition s.val)) ≤
        mapNames j₀ (Preparation.boundedAnonName U a (fun _ => name s.val)) ⊆ᴮ q := by
      have h1 : c_p ⊓ j_R (e_α (condition s.val)) ≤
          mapNames j₀ (Preparation.boundedAnonName U a (fun _ => name s.val)) ⊆ᴮ
            mapNames j₀ (Preparation.boundedAnonName U a (fun _ => N_s)) :=
        inf_le_right.trans (hv_le.trans hsub_Ns)
      have h2 : c_p ⊓ j_R (e_α (condition s.val)) ≤
          mapNames j₀ (Preparation.boundedAnonName U a (fun _ => N_s)) ⊆ᴮ mapNames j₀ G_VA := by
        have hm := OrderHomClass.mono j₀ hNs_GVA
        rw [TopHomClass.map_top, map_subset] at hm
        exact le_top.trans hm
      exact subset_trans' h1
        (subset_trans' h2 (subset_trans' (inf_le_right.trans hGVA_MR) (inf_le_left.trans hq_master)))
    have himp := allIn_elim
      (allIn_elim (le_top.trans hup_W) (inf_le_right.trans (hv_le.trans hs_in_O)))
      (inf_le_left.trans hq_poset)
    exact (le_inf himp hnm_sub_q).trans bv_imp_elim
  -- Disjointness of `O_W(b)` and `O_W(bᶜ)` via Δ₀ formula transfer.
  let O_b_A := levyTruthOpen α b
  let O_bc_A := levyTruthOpen α bᶜ
  let env_disj : Bool → bSet A := fun bl => if bl then O_b_A else O_bc_A
  have hdisj_A : (⊤ : A) ≤ disjFormula.eval env_disj := by
    rw [disjFormula_eval]
    exact allIn_intro fun _ z hz => hz.trans
      (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr (levyTruthOpen_disjoint α b z)))
  have hdisj_W := transfer_const_formula U a hk hf hn ht hκ j₀ disjFormula env_disj hdisj_A
  let O_b := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => O_b_A))
  let O_bc := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => O_bc_A))
  have henv_disj_W : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun _ => env_disj v))) =
      (fun bl => if bl then O_b else O_bc) := by
    funext bl; cases bl <;> rfl
  rw [henv_disj_W, disjFormula_eval] at hdisj_W
  have hq_disj : (q ∈ᴮ O_b) ⊓ (q ∈ᴮ O_bc) = ⊥ :=
    disjoint_iff.mp (le_compl_iff_disjoint_right.mp
      (allIn_elim (le_top.trans hdisj_W) (le_rfl : (q ∈ᴮ O_b) ≤ q ∈ᴮ O_b)))
  have h1 : c_p ⊓ j_R (e_α b) ≤ q ∈ᴮ O_b := hone_dir b
  have h0 : c_p ⊓ (j_R (e_α b))ᶜ ≤ (q ∈ᴮ O_b)ᶜ := by
    rw [← completeHom_compl j_R, ← completeHom_compl e_α]
    exact (hone_dir bᶜ).trans
      (le_compl_iff_disjoint_right.mpr
        (disjoint_iff.mpr ((inf_comm (q ∈ᴮ O_bc) (q ∈ᴮ O_b)).trans hq_disj)))
  exact cone_eq_of_le_and_compl_le h1 h0

/-- Stage-master truth-open forcing over `R := AmbientInternalLevy κ θ`:
any lifted stage-`α` condition `q` extending `stageMasterGraph α` on `coneInMaster hm₀ hp hsub`
evaluates `q ∈ᴮ O_lift(α, fun _ => b)` to `localizedFirstStageHom hm₀ (ambientLevyStageHom hα.le b)`. -/
theorem stageMaster_forces_constant_truthOpen
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {α : Ordinal.{u}} (hα : α < θ.ord)
    {m₀ p : bSet (AmbientInternalLevy κ θ)}
    (hm₀ : (⊤ : AmbientInternalLevy κ θ) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : AmbientInternalLevy κ θ) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : AmbientInternalLevy κ θ) ≤ m₀ ⊆ᴮ p)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))
      (LocalizedSourceCohen (AmbientInternalLevy κ θ) m₀ hm₀))
    (hj₀_base : ∀ d : anonymousAlgebra κ,
      j₀ (value U (fun _ => d)) =
        localizedFirstStageHom hm₀ (ambientLevySourceHom κ θ (inclusion (anonymousAlgebra κ) d)))
    (q : bSet (LocalizedSourceCohen (AmbientInternalLevy κ θ) m₀ hm₀))
    (hq_poset : coneInMaster hm₀ hp hsub ≤
      q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α)))
    (hq_master : coneInMaster hm₀ hp hsub ≤
      mapNames (localizedFirstStageHom hm₀)
        (stageMasterGraph U a hk hκ hθ hf hn ht hα).toBSet ⊆ᴮ q)
    (b : InternalLevyStage κ α) :
    coneInMaster hm₀ hp hsub ⊓
      (q ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => levyTruthOpen α b))) =
    coneInMaster hm₀ hp hsub ⊓ localizedFirstStageHom hm₀ (ambientLevyStageHom hα.le b) :=
  stageMaster_forces_constant_truthOpen_gen U a hk.le hf hn ht hκ
    (ambientLevySourceHom κ θ) (ambientLevyStageHom hα.le)
    (ambientLevyStageHom_sourceHom hα.le)
    (localizedFirstStageHom hm₀) (coneInMaster hm₀ hp hsub) j₀ hj₀_base q hq_poset hq_master b

end StageMasterTruthOpen

end Erdos1172AnonymousInternalLevy
