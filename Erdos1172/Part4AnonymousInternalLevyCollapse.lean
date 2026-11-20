/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCollapseStructure
public import Erdos1172.Part4ShioyaLevyChainCondition
public import Erdos1172.Part4LevyMatchingTowerReading

@[expose] public section

/-! # Internal Lévy collapse `Col(ω₁, < θ)` over the anonymous preparation algebra

Over any complete Boolean algebra `B`, `internalLevyCollapse H Λ` consists of countable partial
functions `g ∈ countableCollapse (prod Λ H) Λ` whose pairs have the form `((ξ, i), y)` with
`ξ ∈ Λ`, `i ∈ H`, and `y ∈ ξ`. Specializing `B := anonymousAlgebra κ`, `H := ordinalCarrier κ.ord`,
and `Λ := ordinalCarrier α` (`α ≤ θ.ord`) yields `InternalLevyStage κ α` and
`InternalLevyAlgebra κ θ := InternalLevyStage κ θ.ord`, together with:
1. Exact coordinate-restriction projections (`restrictLevy`, `amalgamate_mem`, `stageStepHom`),
2. Strict `< θ` condition-cardinality bounds on all stages `α < θ.ord`, `≤ 2^κ` canonical triple
   support (`tripleSupport`), `DenseStageUnion`, `≤ θ` dense subset size, and
   `StrictCC (InternalLevyAlgebra κ θ) θ` via the Δ-system lemma.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Flypitch Ordinal
open Cardinal bSet Lattice ErdosNameTransport
open ErdosPartialInjection ErdosIdeal ErdosSmallPoolOperations ErdosRelationGraph ErdosInjectionExtension
open Erdos1172LevyCohen Erdos1172CompleteSubalgebra Erdos1172BooleanNameIteration
open Erdos1172PosetCompletion Erdos1172PositiveBoolean Erdos1172Shioya.ForcingCover
open Erdos1172BooleanUltrapower Erdos1172LevyCollapse.Matching bSet.ErdosShioyaInternal

universe u

namespace Erdos1172AnonymousInternalLevy

theorem inf_of_le {α : Type u} [SemilatticeInf α] {x y : α} (h : x ≤ y) :
    x ⊓ y = x := inf_eq_left.mpr h

theorem exists_mem_iSup_inf_ne_bot {α : Type u} [CompleteBooleanAlgebra α]
    {ι : Sort*} {f : ι → α} {c : α} (h : c ⊓ (⨆ i, f i) ≠ ⊥) : ∃ i, c ⊓ f i ≠ ⊥ := by
  by_contra hnone
  apply h
  rw [inf_iSup_eq]
  exact iSup_eq_bot.mpr fun i => by_contra fun hi => hnone ⟨i, hi⟩

theorem is_func_of_subset {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {Γ : B} {g₁ g₂ : bSet B} (hsub : Γ ≤ g₁ ⊆ᴮ g₂) (hfn : Γ ≤ is_func g₂) :
    Γ ≤ is_func g₁ := by
  refine le_iInf fun a₁ => le_iInf fun a₂ => le_iInf fun y₁ => le_iInf fun y₂ => ?_
  rw [← deduction, ← deduction]
  have hm₁ : ((Γ ⊓ (pair a₁ y₁ ∈ᴮ g₁ ⊓ pair a₂ y₂ ∈ᴮ g₁)) ⊓ (a₁ =ᴮ a₂)) ≤ pair a₁ y₁ ∈ᴮ g₂ :=
    mem_of_mem_subset ((inf_le_left.trans inf_le_left).trans hsub)
      (inf_le_left.trans (inf_le_right.trans inf_le_left))
  have hm₂ : ((Γ ⊓ (pair a₁ y₁ ∈ᴮ g₁ ⊓ pair a₂ y₂ ∈ᴮ g₁)) ⊓ (a₁ =ᴮ a₂)) ≤ pair a₂ y₂ ∈ᴮ g₂ :=
    mem_of_mem_subset ((inf_le_left.trans inf_le_left).trans hsub)
      (inf_le_left.trans (inf_le_right.trans inf_le_right))
  exact eq_of_is_func_of_eq ((inf_le_left.trans inf_le_left).trans hfn) inf_le_right hm₁ hm₂

section GeneralInternalLevy
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]

/-- Entrywise Lévy bound: `z = ((ξ, i), y)` with `ξ ∈ Λ`, `i ∈ H`, and `y ∈ ξ`. -/
def levyBoundPred (H Λ z : bSet B) : B :=
  someIn Λ fun ξ => someIn H fun i => someIn ξ fun y => z =ᴮ pair (pair ξ i) y

theorem levyBoundPred_ext (H Λ : bSet B) : B_ext (levyBoundPred H Λ) :=
  someIn_ext (const_congr Λ) fun ξ =>
    someIn_ext (const_congr H) fun _ =>
      someIn_ext (const_congr ξ) fun _ => B_ext_bv_eq_left

/-- All members of a graph `g` satisfy `levyBoundPred H Λ`. -/
def levyAllBounded (H Λ g : bSet B) : B :=
  allIn g (levyBoundPred H Λ)

theorem levyAllBounded_ext (H Λ : bSet B) : B_ext (levyAllBounded H Λ) :=
  allIn_ext id_congr fun _ =>
    someIn_ext (const_congr Λ) fun _ =>
      someIn_ext (const_congr H) fun _ =>
        someIn_ext (const_congr _) fun _ => B_ext_const

/-- Internal Lévy collapse `Col(H, < Λ)` represented by countable partial function graphs. -/
def internalLevyCollapse (H Λ : bSet B) : bSet B :=
  comprehend (levyAllBounded H Λ) (countableCollapse (prod Λ H) Λ)

theorem mem_internalLevyCollapse {Γ : B} {H Λ g : bSet B} :
    Γ ≤ g ∈ᴮ internalLevyCollapse H Λ ↔
      Γ ≤ g ∈ᴮ countableCollapse (prod Λ H) Λ ∧ Γ ≤ levyAllBounded H Λ g := by
  rw [internalLevyCollapse, mem_comprehend_and (levyAllBounded_ext H Λ)]

theorem empty_mem_internalLevyCollapse {Γ : B} (H Λ : bSet B) :
    Γ ≤ (∅ : bSet B) ∈ᴮ internalLevyCollapse H Λ := by
  have hemp_fn : Γ ≤ is_func (∅ : bSet B) :=
    le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
      deduction.mp ((bot_of_mem_empty (inf_le_right.trans inf_le_left)).trans bot_le)
  have hemp_cc : Γ ≤ (∅ : bSet B) ∈ᴮ countableCollapse (prod Λ H) Λ :=
    countableCollapse_mem.mpr ⟨empty_subset, hemp_fn, injects_into_of_subset empty_subset⟩
  refine mem_internalLevyCollapse.mpr ⟨hemp_cc, ?_⟩
  exact allIn_intro fun _ _ hz => (bot_of_mem_empty hz).trans bot_le

theorem levyBoundPred_mono {Γ : B} {H Λ₁ Λ₂ z : bSet B} (hΛ : Γ ≤ Λ₁ ⊆ᴮ Λ₂)
    (hz : Γ ≤ levyBoundPred H Λ₁ z) : Γ ≤ levyBoundPred H Λ₂ z := by
  apply (le_inf le_rfl hz).trans
  change Γ ⊓ (⨆ ξ : bSet B, (ξ ∈ᴮ Λ₁) ⊓ _) ≤ ⨆ ξ : bSet B, (ξ ∈ᴮ Λ₂) ⊓ _
  rw [inf_iSup_eq]
  refine iSup_le fun ξ => le_iSup_of_le ξ ?_
  exact le_inf (mem_of_mem_subset (inf_le_left.trans hΛ) (inf_le_right.trans inf_le_left))
    (inf_le_right.trans inf_le_right)

theorem levyBoundPred_mem_prod {Γ : B} {H Λ z : bSet B} (hOrd : Γ ≤ Ord Λ)
    (hz : Γ ≤ levyBoundPred H Λ z) : Γ ≤ z ∈ᴮ prod (prod Λ H) Λ := by
  apply (le_inf hOrd hz).trans
  change Ord Λ ⊓ (⨆ ξ : bSet B, (ξ ∈ᴮ Λ) ⊓ _) ≤ _
  rw [inf_iSup_eq]
  refine iSup_le fun ξ => ?_
  change Ord Λ ⊓ ((ξ ∈ᴮ Λ) ⊓ (⨆ i : bSet B, (i ∈ᴮ H) ⊓ _)) ≤ _
  rw [← inf_assoc, inf_iSup_eq]
  refine iSup_le fun i => ?_
  change (Ord Λ ⊓ (ξ ∈ᴮ Λ)) ⊓ ((i ∈ᴮ H) ⊓ (⨆ y : bSet B, (y ∈ᴮ ξ) ⊓ (z =ᴮ pair (pair ξ i) y))) ≤ _
  rw [← inf_assoc, inf_iSup_eq]
  refine iSup_le fun y => ?_
  let d := ((Ord Λ ⊓ (ξ ∈ᴮ Λ)) ⊓ (i ∈ᴮ H)) ⊓ ((y ∈ᴮ ξ) ⊓ (z =ᴮ pair (pair ξ i) y))
  have hOrd_d : d ≤ Ord Λ := ((inf_le_left.trans inf_le_left).trans inf_le_left)
  have hξ_d : d ≤ ξ ∈ᴮ Λ := ((inf_le_left.trans inf_le_left).trans inf_le_right)
  have hi_d : d ≤ i ∈ᴮ H := (inf_le_left.trans inf_le_right)
  have hy_ξ : d ≤ y ∈ᴮ ξ := (inf_le_right.trans inf_le_left)
  have heq : d ≤ z =ᴮ pair (pair ξ i) y := (inf_le_right.trans inf_le_right)
  have hy_Λ : d ≤ y ∈ᴮ Λ := mem_of_mem_Ord hy_ξ hξ_d hOrd_d
  exact mem_congr (bv_symm heq) bv_refl (mem_prod (mem_prod hξ_d hi_d) hy_Λ)

theorem internalLevyCollapse_mono {Γ : B} {H Λ₁ Λ₂ : bSet B} (hΛ : Γ ≤ Λ₁ ⊆ᴮ Λ₂) :
    Γ ≤ internalLevyCollapse H Λ₁ ⊆ᴮ internalLevyCollapse H Λ₂ := by
  rw [subset_unfold']
  refine le_iInf fun g => projection_imp.mpr fun d hd hg => ?_
  obtain ⟨hg_cc, hg_bd⟩ := mem_internalLevyCollapse.mp hg
  obtain ⟨hsub, hfunc, hcnt⟩ := countableCollapse_mem.mp hg_cc
  have hprod : d ≤ prod (prod Λ₁ H) Λ₁ ⊆ᴮ prod (prod Λ₂ H) Λ₂ := by
    rw [subset_unfold']
    refine le_iInf fun z => projection_imp.mpr fun e he hz => ?_
    obtain ⟨p, hp, y, hy, eq1⟩ := mem_prod_iff₂.mp hz
    obtain ⟨ξ, hξ, i, hi, eq2⟩ := mem_prod_iff₂.mp hp
    have hξ₂ : e ≤ ξ ∈ᴮ Λ₂ := mem_of_mem_subset ((he.trans hd).trans hΛ) hξ
    have hy₂ : e ≤ y ∈ᴮ Λ₂ := mem_of_mem_subset ((he.trans hd).trans hΛ) hy
    exact mem_congr (bv_symm (bv_trans eq1 (pair_congr eq2 bv_refl))) bv_refl
      (mem_prod (mem_prod hξ₂ hi) hy₂)
  refine mem_internalLevyCollapse.mpr ⟨countableCollapse_mem.mpr
    ⟨subset_trans' hsub hprod, hfunc, hcnt⟩, ?_⟩
  exact allIn_intro fun he _ hz =>
    levyBoundPred_mono ((he.trans hd).trans hΛ) (allIn_elim (he.trans hg_bd) hz)

theorem internalLevyCollapse_union {Γ : B} {H Λ U : bSet B}
    (sub : Γ ≤ U ⊆ᴮ internalLevyCollapse H Λ)
    (count : Γ ≤ injects_into U omega)
    (chain : Γ ≤ ErdosInjectionChain.inclusionChain U) :
    Γ ≤ bv_union U ∈ᴮ internalLevyCollapse H Λ := by
  have sub_cc : Γ ≤ U ⊆ᴮ countableCollapse (prod Λ H) Λ := by
    rw [subset_unfold']
    refine le_iInf fun g => projection_imp.mpr fun d hd hg => ?_
    exact (mem_internalLevyCollapse.mp (mem_of_mem_subset (hd.trans sub) hg)).1
  refine mem_internalLevyCollapse.mpr ⟨CollapsePath.collapse_union sub_cc count chain, ?_⟩
  refine allIn_intro fun hd z hz => ?_
  obtain ⟨g, hg⟩ := exists_convert (mem_bv_union_iff.mp hz) (B_ext_inf B_ext_mem_left B_ext_mem_right)
  have hg_mem : _ ≤ g ∈ᴮ internalLevyCollapse H Λ :=
    mem_of_mem_subset (hd.trans sub) (hg.trans inf_le_left)
  exact allIn_elim (mem_internalLevyCollapse.mp hg_mem).2 (hg.trans inf_le_right)

theorem internalLevyCollapse_insert {Γ : B} {H Λ g ξ i y : bSet B}
    (hOrd : Γ ≤ Ord Λ)
    (hg : Γ ≤ g ∈ᴮ internalLevyCollapse H Λ)
    (hξ : Γ ≤ ξ ∈ᴮ Λ) (hi : Γ ≤ i ∈ᴮ H) (hy : Γ ≤ y ∈ᴮ ξ)
    (fresh : Γ ≤ (pair ξ i ∈ᴮ graphDomain (prod Λ H) Λ g)ᶜ) :
    Γ ≤ bSet.insert1 (pair (pair ξ i) y) g ∈ᴮ internalLevyCollapse H Λ := by
  obtain ⟨hg_cc, hg_bd⟩ := mem_internalLevyCollapse.mp hg
  have hy_Λ : Γ ≤ y ∈ᴮ Λ := mem_of_mem_Ord hy hξ hOrd
  have hcc : Γ ≤ bSet.insert1 (pair (pair ξ i) y) g ∈ᴮ countableCollapse (prod Λ H) Λ :=
    CollapsePath.collapse_insert hg_cc (mem_prod hξ hi) hy_Λ fresh
  refine mem_internalLevyCollapse.mpr ⟨hcc, allIn_intro fun {Δ} hd z hz => ?_⟩
  have hor : Δ ≤ (z =ᴮ pair (pair ξ i) y) ⊔ (z ∈ᴮ g) := hz.trans_eq mem_insert1
  apply (le_inf le_rfl hor).trans
  rw [inf_sup_left]
  refine sup_le ?_ (allIn_elim ((inf_le_left.trans hd).trans hg_bd) inf_le_right)
  have he_Γ : Δ ⊓ (z =ᴮ pair (pair ξ i) y) ≤ Γ := inf_le_left.trans hd
  change Δ ⊓ (z =ᴮ pair (pair ξ i) y) ≤
    ⨆ ξ' : bSet B, (ξ' ∈ᴮ Λ) ⊓ ⨆ i' : bSet B, (i' ∈ᴮ H) ⊓ ⨆ y' : bSet B,
      (y' ∈ᴮ ξ') ⊓ (z =ᴮ pair (pair ξ' i') y')
  exact le_iSup_of_le ξ (le_inf (he_Γ.trans hξ)
    (le_iSup_of_le i (le_inf (he_Γ.trans hi)
      (le_iSup_of_le y (le_inf (he_Γ.trans hy) inf_le_right)))))

/-- Coordinate restriction of a graph `g` to first coordinates in `Λ₀`. -/
def restrictLevy (H Λ₀ g : bSet B) : bSet B :=
  comprehend (levyBoundPred H Λ₀) g

theorem restrictLevy_subset (H Λ₀ g : bSet B) :
    (⊤ : B) ≤ restrictLevy H Λ₀ g ⊆ᴮ g :=
  comprehend_subset (ϕ := levyBoundPred H Λ₀) g

theorem mem_restrictLevy_iff {Γ : B} {H Λ₀ g z : bSet B} :
    Γ ≤ z ∈ᴮ restrictLevy H Λ₀ g ↔ Γ ≤ z ∈ᴮ g ∧ Γ ≤ levyBoundPred H Λ₀ z := by
  rw [restrictLevy, mem_comprehend_and (levyBoundPred_ext H Λ₀)]

theorem restrictLevy_congr {Γ : B} {H Λ₀ g₁ g₂ : bSet B} (heq : Γ ≤ g₁ =ᴮ g₂) :
    Γ ≤ restrictLevy H Λ₀ g₁ =ᴮ restrictLevy H Λ₀ g₂ := by
  apply subset_ext <;>
  · rw [subset_unfold']
    refine le_iInf fun z => projection_imp.mpr fun d hd hz => ?_
    obtain ⟨hz_g, hz_b⟩ := mem_restrictLevy_iff.mp hz
    first
    | exact mem_restrictLevy_iff.mpr ⟨mem_congr bv_refl (hd.trans heq) hz_g, hz_b⟩
    | exact mem_restrictLevy_iff.mpr ⟨mem_congr bv_refl (bv_symm (hd.trans heq)) hz_g, hz_b⟩

theorem restrictLevy_mem {Γ : B} {H Λ₀ Λ₁ g : bSet B}
    (hOrd : Γ ≤ Ord Λ₀) (hg : Γ ≤ g ∈ᴮ internalLevyCollapse H Λ₁) :
    Γ ≤ restrictLevy H Λ₀ g ∈ᴮ internalLevyCollapse H Λ₀ := by
  obtain ⟨hg_cc, _⟩ := mem_internalLevyCollapse.mp hg
  obtain ⟨_, hfunc, hcnt⟩ := countableCollapse_mem.mp hg_cc
  have hsub_g : Γ ≤ restrictLevy H Λ₀ g ⊆ᴮ g := le_top.trans (restrictLevy_subset H Λ₀ g)
  have hsub_prod : Γ ≤ restrictLevy H Λ₀ g ⊆ᴮ prod (prod Λ₀ H) Λ₀ := by
    rw [subset_unfold']
    refine le_iInf fun z => projection_imp.mpr fun d hd hz => ?_
    exact levyBoundPred_mem_prod (hd.trans hOrd) (mem_restrictLevy_iff.mp hz).2
  have hfunc₀ : Γ ≤ is_func (restrictLevy H Λ₀ g) := is_func_of_subset hsub_g hfunc
  have hcnt₀ : Γ ≤ injects_into (restrictLevy H Λ₀ g) omega :=
    injects_into_trans (injects_into_of_subset hsub_g) hcnt
  refine mem_internalLevyCollapse.mpr ⟨countableCollapse_mem.mpr ⟨hsub_prod, hfunc₀, hcnt₀⟩, ?_⟩
  exact allIn_intro fun _ _ hz => (mem_restrictLevy_iff.mp hz).2

theorem restrictLevy_eq_self {Γ : B} {H Λ₀ g : bSet B}
    (hg : Γ ≤ g ∈ᴮ internalLevyCollapse H Λ₀) :
    Γ ≤ restrictLevy H Λ₀ g =ᴮ g := by
  apply subset_ext (le_top.trans (restrictLevy_subset H Λ₀ g))
  rw [subset_unfold']
  refine le_iInf fun z => projection_imp.mpr fun d hd hz => ?_
  exact mem_restrictLevy_iff.mpr ⟨hz, allIn_elim ((hd.trans (mem_internalLevyCollapse.mp hg).2)) hz⟩

theorem restrictLevy_idem {Γ : B} {H Λ₀ Λ₁ g : bSet B} (hΛ : Γ ≤ Λ₀ ⊆ᴮ Λ₁) :
    Γ ≤ restrictLevy H Λ₀ (restrictLevy H Λ₁ g) =ᴮ restrictLevy H Λ₀ g := by
  apply subset_ext
  · rw [subset_unfold']
    refine le_iInf fun z => projection_imp.mpr fun _ _ hz => ?_
    obtain ⟨hz₁, hz₀⟩ := mem_restrictLevy_iff.mp hz
    exact mem_restrictLevy_iff.mpr ⟨(mem_restrictLevy_iff.mp hz₁).1, hz₀⟩
  · rw [subset_unfold']
    refine le_iInf fun z => projection_imp.mpr fun d hd hz => ?_
    obtain ⟨hz_g, hz₀⟩ := mem_restrictLevy_iff.mp hz
    exact mem_restrictLevy_iff.mpr ⟨mem_restrictLevy_iff.mpr
      ⟨hz_g, levyBoundPred_mono (hd.trans hΛ) hz₀⟩, hz₀⟩

theorem levyBoundPred_of_first_mem {Γ : B} {H Λ₀ Λ₁ p y z : bSet B}
    (hz : Γ ≤ z =ᴮ pair p y)
    (hbd₁ : Γ ≤ levyBoundPred H Λ₁ z)
    (hp_mem : Γ ≤ someIn Λ₀ fun ξ₀ => someIn H fun i₀ => p =ᴮ pair ξ₀ i₀) :
    Γ ≤ levyBoundPred H Λ₀ z := by
  apply (le_inf (le_inf hz hbd₁) hp_mem).trans
  change ((z =ᴮ pair p y) ⊓ (⨆ ξ : bSet B, (ξ ∈ᴮ Λ₁) ⊓ _)) ⊓ _ ≤ _
  rw [inf_iSup_eq, iSup_inf_eq]
  refine iSup_le fun ξ => ?_
  change ((z =ᴮ pair p y) ⊓ ((ξ ∈ᴮ Λ₁) ⊓ (⨆ i : bSet B, (i ∈ᴮ H) ⊓ _))) ⊓ _ ≤ _
  rw [← inf_assoc (z =ᴮ pair p y) (ξ ∈ᴮ Λ₁), inf_iSup_eq, iSup_inf_eq]
  refine iSup_le fun i => ?_
  change (((z =ᴮ pair p y) ⊓ (ξ ∈ᴮ Λ₁)) ⊓ ((i ∈ᴮ H) ⊓ (⨆ y' : bSet B, (y' ∈ᴮ ξ) ⊓ (z =ᴮ pair (pair ξ i) y')))) ⊓ _ ≤ _
  rw [← inf_assoc ((z =ᴮ pair p y) ⊓ (ξ ∈ᴮ Λ₁)) (i ∈ᴮ H), inf_iSup_eq, iSup_inf_eq]
  refine iSup_le fun y' => ?_
  change _ ⊓ (⨆ ξ₀ : bSet B, (ξ₀ ∈ᴮ Λ₀) ⊓ _) ≤ _
  rw [inf_iSup_eq]
  refine iSup_le fun ξ₀ => ?_
  change _ ⊓ ((ξ₀ ∈ᴮ Λ₀) ⊓ (⨆ i₀ : bSet B, (i₀ ∈ᴮ H) ⊓ (p =ᴮ pair ξ₀ i₀))) ≤ _
  rw [← inf_assoc _ (ξ₀ ∈ᴮ Λ₀), inf_iSup_eq]
  refine iSup_le fun i₀ => ?_
  let d := (((((z =ᴮ pair p y) ⊓ (ξ ∈ᴮ Λ₁)) ⊓ (i ∈ᴮ H)) ⊓ ((y' ∈ᴮ ξ) ⊓ (z =ᴮ pair (pair ξ i) y'))) ⊓
    (ξ₀ ∈ᴮ Λ₀)) ⊓ ((i₀ ∈ᴮ H) ⊓ (p =ᴮ pair ξ₀ i₀))
  have hz_py : d ≤ z =ᴮ pair p y :=
    ((((inf_le_left.trans inf_le_left).trans inf_le_left).trans inf_le_left).trans inf_le_left)
  have hi_H : d ≤ i ∈ᴮ H :=
    ((((inf_le_left.trans inf_le_left).trans inf_le_left).trans inf_le_right))
  have hy'_ξ : d ≤ y' ∈ᴮ ξ :=
    ((((inf_le_left.trans inf_le_left).trans inf_le_right).trans inf_le_left))
  have hz_eq : d ≤ z =ᴮ pair (pair ξ i) y' :=
    ((((inf_le_left.trans inf_le_left).trans inf_le_right).trans inf_le_right))
  have hξ₀_Λ₀ : d ≤ ξ₀ ∈ᴮ Λ₀ := (inf_le_left.trans inf_le_right)
  have hp_eq : d ≤ p =ᴮ pair ξ₀ i₀ := (inf_le_right.trans inf_le_right)
  have hpair_eq : d ≤ pair p y =ᴮ pair (pair ξ i) y' := bv_trans (bv_symm hz_py) hz_eq
  have hp_ξi : d ≤ p =ᴮ pair ξ i := (pair_eq_pair_iff.mp hpair_eq).1
  have hξ_ξ₀ : d ≤ ξ =ᴮ ξ₀ := (pair_eq_pair_iff.mp (bv_trans (bv_symm hp_ξi) hp_eq)).1
  have hξ_Λ₀ : d ≤ ξ ∈ᴮ Λ₀ := mem_congr (bv_symm hξ_ξ₀) bv_refl hξ₀_Λ₀
  change d ≤ ⨆ ξ' : bSet B, (ξ' ∈ᴮ Λ₀) ⊓ ⨆ i' : bSet B, (i' ∈ᴮ H) ⊓ ⨆ y'' : bSet B,
    (y'' ∈ᴮ ξ') ⊓ (z =ᴮ pair (pair ξ' i') y'')
  exact le_iSup_of_le ξ (le_inf hξ_Λ₀
    (le_iSup_of_le i (le_inf hi_H
      (le_iSup_of_le y' (le_inf hy'_ξ hz_eq)))))

private theorem domain_coord_in_first {Γ : B} {H Λ₀ p y g : bSet B}
    (hg : Γ ≤ g ∈ᴮ internalLevyCollapse H Λ₀)
    (hmem : Γ ≤ pair p y ∈ᴮ g) :
    Γ ≤ someIn Λ₀ fun ξ₀ => someIn H fun i₀ => p =ᴮ pair ξ₀ i₀ := by
  have hbd : Γ ≤ levyBoundPred H Λ₀ (pair p y) :=
    allIn_elim (mem_internalLevyCollapse.mp hg).2 hmem
  apply hbd.trans
  refine iSup_le fun ξ => ?_
  change (ξ ∈ᴮ Λ₀) ⊓ (⨆ i : bSet B, (i ∈ᴮ H) ⊓ _) ≤ _
  rw [inf_iSup_eq]
  refine iSup_le fun i => ?_
  change (ξ ∈ᴮ Λ₀) ⊓ ((i ∈ᴮ H) ⊓ (⨆ y' : bSet B, (y' ∈ᴮ ξ) ⊓ (pair p y =ᴮ pair (pair ξ i) y'))) ≤ _
  rw [← inf_assoc, inf_iSup_eq]
  refine iSup_le fun y' => ?_
  let d := ((ξ ∈ᴮ Λ₀) ⊓ (i ∈ᴮ H)) ⊓ ((y' ∈ᴮ ξ) ⊓ (pair p y =ᴮ pair (pair ξ i) y'))
  have hξ : d ≤ ξ ∈ᴮ Λ₀ := (inf_le_left.trans inf_le_left)
  have hi : d ≤ i ∈ᴮ H := (inf_le_left.trans inf_le_right)
  have hp_eq : d ≤ p =ᴮ pair ξ i := (pair_eq_pair_iff.mp (inf_le_right.trans inf_le_right)).1
  exact le_iSup_of_le ξ (le_inf hξ (le_iSup_of_le i (le_inf hi hp_eq)))

/-- Disjoint-coordinate amalgamation: if `p ∈ internalLevyCollapse H Λ₀`, `q ∈ internalLevyCollapse H Λ₁`
(`Λ₀ ⊆ Λ₁`), and `restrictLevy H Λ₀ q ⊆ p`, then `binary_union p q ∈ internalLevyCollapse H Λ₁`
and its restriction back to `Λ₀` equals `p`. -/
theorem amalgamate_mem {Γ : B} {H Λ₀ Λ₁ p q : bSet B}
    (hΛ : Γ ≤ Λ₀ ⊆ᴮ Λ₁)
    (hp : Γ ≤ p ∈ᴮ internalLevyCollapse H Λ₀)
    (hq : Γ ≤ q ∈ᴮ internalLevyCollapse H Λ₁)
    (hcompat : Γ ≤ restrictLevy H Λ₀ q ⊆ᴮ p) :
    Γ ≤ binary_union p q ∈ᴮ internalLevyCollapse H Λ₁ ∧
      Γ ≤ restrictLevy H Λ₀ (binary_union p q) =ᴮ p := by
  have hp₁ : Γ ≤ p ∈ᴮ internalLevyCollapse H Λ₁ :=
    mem_of_mem_subset (internalLevyCollapse_mono hΛ) hp
  obtain ⟨hp_cc, hp_bd⟩ := mem_internalLevyCollapse.mp hp₁
  obtain ⟨hq_cc, hq_bd⟩ := mem_internalLevyCollapse.mp hq
  obtain ⟨hp_sub, hp_fn, hp_cnt⟩ := countableCollapse_mem.mp hp_cc
  obtain ⟨hq_sub, hq_fn, hq_cnt⟩ := countableCollapse_mem.mp hq_cc
  have hu_sub : Γ ≤ binary_union p q ⊆ᴮ prod (prod Λ₁ H) Λ₁ :=
    binary_union_subset hp_sub hq_sub
  have hu_cnt : Γ ≤ injects_into (binary_union p q) omega :=
    ErdosFusionActiveHistory.binary_union_countable hp_cnt hq_cnt
  have hu_fn : Γ ≤ is_func (binary_union p q) := by
    refine le_iInf fun a₁ => le_iInf fun a₂ => le_iInf fun y₁ => le_iInf fun y₂ => ?_
    rw [← deduction, ← deduction]
    let Δ := (Γ ⊓ (pair a₁ y₁ ∈ᴮ binary_union p q ⊓ pair a₂ y₂ ∈ᴮ binary_union p q)) ⊓ (a₁ =ᴮ a₂)
    have hΔ_Γ : Δ ≤ Γ := inf_le_left.trans inf_le_left
    have ha₁₂ : Δ ≤ a₁ =ᴮ a₂ := inf_le_right
    have hm₁ : Δ ≤ (pair a₁ y₁ ∈ᴮ p) ⊔ (pair a₁ y₁ ∈ᴮ q) :=
      (inf_le_left.trans (inf_le_right.trans inf_le_left)).trans_eq (mem_binary_union p q _)
    have hm₂ : Δ ≤ (pair a₂ y₂ ∈ᴮ p) ⊔ (pair a₂ y₂ ∈ᴮ q) :=
      (inf_le_left.trans (inf_le_right.trans inf_le_right)).trans_eq (mem_binary_union p q _)
    apply (le_inf le_rfl hm₁).trans
    rw [inf_sup_left]
    apply sup_le
    · apply (le_inf le_rfl (inf_le_left.trans hm₂)).trans
      rw [inf_sup_left]
      apply sup_le
      · exact eq_of_is_func_of_eq (((inf_le_left.trans inf_le_left).trans hΔ_Γ).trans hp_fn)
          ((inf_le_left.trans inf_le_left).trans ha₁₂)
          (inf_le_left.trans inf_le_right) inf_le_right
      · let E := (Δ ⊓ (pair a₁ y₁ ∈ᴮ p)) ⊓ (pair a₂ y₂ ∈ᴮ q)
        have hE_Γ : E ≤ Γ := (inf_le_left.trans inf_le_left).trans hΔ_Γ
        have ha₁_in : E ≤ someIn Λ₀ fun ξ₀ => someIn H fun i₀ => a₁ =ᴮ pair ξ₀ i₀ :=
          domain_coord_in_first (hE_Γ.trans hp) (inf_le_left.trans inf_le_right)
        have ha₂_in : E ≤ someIn Λ₀ fun ξ₀ => someIn H fun i₀ => a₂ =ᴮ pair ξ₀ i₀ :=
          bv_rw'' ((inf_le_left.trans inf_le_left).trans ha₁₂) ha₁_in
            (someIn_ext (const_congr Λ₀) fun _ => someIn_ext (const_congr H) fun _ => B_ext_bv_eq_left)
        have hbd₂ : E ≤ levyBoundPred H Λ₀ (pair a₂ y₂) :=
          levyBoundPred_of_first_mem bv_refl
            (allIn_elim (hE_Γ.trans hq_bd) inf_le_right) ha₂_in
        have hin_p : E ≤ pair a₂ y₂ ∈ᴮ p :=
          mem_of_mem_subset (hE_Γ.trans hcompat) (mem_restrictLevy_iff.mpr ⟨inf_le_right, hbd₂⟩)
        exact eq_of_is_func_of_eq (hE_Γ.trans hp_fn) ((inf_le_left.trans inf_le_left).trans ha₁₂)
          (inf_le_left.trans inf_le_right) hin_p
    · apply (le_inf le_rfl (inf_le_left.trans hm₂)).trans
      rw [inf_sup_left]
      apply sup_le
      · let E := (Δ ⊓ (pair a₁ y₁ ∈ᴮ q)) ⊓ (pair a₂ y₂ ∈ᴮ p)
        have hE_Γ : E ≤ Γ := (inf_le_left.trans inf_le_left).trans hΔ_Γ
        have ha₂_in : E ≤ someIn Λ₀ fun ξ₀ => someIn H fun i₀ => a₂ =ᴮ pair ξ₀ i₀ :=
          domain_coord_in_first (hE_Γ.trans hp) inf_le_right
        have ha₁_in : E ≤ someIn Λ₀ fun ξ₀ => someIn H fun i₀ => a₁ =ᴮ pair ξ₀ i₀ :=
          bv_rw'' (bv_symm ((inf_le_left.trans inf_le_left).trans ha₁₂)) ha₂_in
            (someIn_ext (const_congr Λ₀) fun _ => someIn_ext (const_congr H) fun _ => B_ext_bv_eq_left)
        have hbd₁ : E ≤ levyBoundPred H Λ₀ (pair a₁ y₁) :=
          levyBoundPred_of_first_mem bv_refl
            (allIn_elim (hE_Γ.trans hq_bd) (inf_le_left.trans inf_le_right)) ha₁_in
        have hin_p : E ≤ pair a₁ y₁ ∈ᴮ p :=
          mem_of_mem_subset (hE_Γ.trans hcompat)
            (mem_restrictLevy_iff.mpr ⟨inf_le_left.trans inf_le_right, hbd₁⟩)
        exact eq_of_is_func_of_eq (hE_Γ.trans hp_fn) ((inf_le_left.trans inf_le_left).trans ha₁₂)
          hin_p inf_le_right
      · exact eq_of_is_func_of_eq (((inf_le_left.trans inf_le_left).trans hΔ_Γ).trans hq_fn)
          ((inf_le_left.trans inf_le_left).trans ha₁₂)
          (inf_le_left.trans inf_le_right) inf_le_right
  have hu_bd : Γ ≤ levyAllBounded H Λ₁ (binary_union p q) := by
    refine allIn_intro fun hd z hz => ?_
    have hor : _ ≤ (z ∈ᴮ p) ⊔ (z ∈ᴮ q) := hz.trans_eq (mem_binary_union p q z)
    apply (le_inf le_rfl hor).trans
    rw [inf_sup_left]
    exact sup_le (allIn_elim ((inf_le_left.trans hd).trans hp_bd) inf_le_right)
      (allIn_elim ((inf_le_left.trans hd).trans hq_bd) inf_le_right)
  refine ⟨mem_internalLevyCollapse.mpr ⟨countableCollapse_mem.mpr ⟨hu_sub, hu_fn, hu_cnt⟩, hu_bd⟩, ?_⟩
  apply subset_ext
  · rw [subset_unfold']
    refine le_iInf fun z => projection_imp.mpr fun _ hd hz => ?_
    obtain ⟨hz_u, hz_b⟩ := mem_restrictLevy_iff.mp hz
    have hor : _ ≤ (z ∈ᴮ p) ⊔ (z ∈ᴮ q) := hz_u.trans_eq (mem_binary_union p q z)
    apply (le_inf le_rfl hor).trans
    rw [inf_sup_left]
    refine sup_le inf_le_right ?_
    exact mem_of_mem_subset ((inf_le_left.trans hd).trans hcompat)
      (mem_restrictLevy_iff.mpr ⟨inf_le_right, inf_le_left.trans hz_b⟩)
  · rw [subset_unfold']
    refine le_iInf fun z => projection_imp.mpr fun _ hd hz => ?_
    exact mem_restrictLevy_iff.mpr ⟨mem_of_mem_subset (le_top.trans subset_binary_union_left) hz,
      allIn_elim ((hd.trans (mem_internalLevyCollapse.mp hp).2)) hz⟩

end GeneralInternalLevy

section AnonymousStages
variable (κ : Cardinal.{u})

/-- Stage `α` of the internal Lévy collapse `Col(κ, < α)` over `anonymousAlgebra κ`. -/
def internalLevyPoset (α : Ordinal.{u}) : bSet (anonymousAlgebra κ) :=
  internalLevyCollapse (ordinalCarrier κ.ord) (ordinalCarrier α)

/-- Canonical conditions of `internalLevyPoset κ α`. -/
abbrev InternalLevyCondition (α : Ordinal.{u}) : Type u :=
  Erdos1172BooleanNameIteration.Condition (internalLevyPoset κ α)

/-- Completed Boolean algebra of stage `α`. -/
abbrev InternalLevyStage (α : Ordinal.{u}) : Type u :=
  Erdos1172BooleanNameIteration.Algebra (internalLevyPoset κ α)

/-- Full internal Lévy collapse `Col(κ, < θ)` over `anonymousAlgebra κ`. -/
abbrev InternalLevyAlgebra (θ : Cardinal.{u}) : Type u :=
  InternalLevyStage κ θ.ord

instance internalLevyConditionNonempty (α : Ordinal.{u}) :
    Nonempty (InternalLevyCondition κ α) :=
  condition_nonempty_of_mem (empty_mem_internalLevyCollapse (ordinalCarrier κ.ord) (ordinalCarrier α))

instance internalLevyStageNCBA (α : Ordinal.{u}) :
    NontrivialCompleteBooleanAlgebra (InternalLevyStage κ α) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

/-- Ground `PSet` carrier of candidate triples `((ξ, η), y)` at stage `α`. -/
def levyTriplePSet (α : Ordinal.{u}) : PSet.{u} :=
  PSet.pSet_prod (PSet.pSet_prod (PSet.ordinalMk α) (PSet.ordinalMk κ.ord)) (PSet.ordinalMk α)

variable {κ}

theorem prod_ordinalCarrier_eq_check_levyTriplePSet {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (α : Ordinal.{u}) {Γ : B} :
    Γ ≤ prod (prod (ordinalCarrier α) (ordinalCarrier κ.ord)) (ordinalCarrier α) =ᴮ
      check (levyTriplePSet κ α) :=
  bv_trans (prod_congr (bv_symm check_pset_prod) bv_refl) (bv_symm check_pset_prod)

theorem check_levyTriplePSet_func {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (α : Ordinal.{u}) (idx : (levyTriplePSet κ α).Type) {Γ : B} :
    Γ ≤ check ((levyTriplePSet κ α).Func idx) =ᴮ
      pair (pair (check ((PSet.ordinalMk α).Func idx.1.1))
        (check ((PSet.ordinalMk κ.ord).Func idx.1.2)))
        (check ((PSet.ordinalMk α).Func idx.2)) :=
  bv_trans check_pset_pair (pair_congr check_pset_pair bv_refl)

theorem levyTriplePSet_inj (α : Ordinal.{u}) {k₁ k₂ : (levyTriplePSet κ α).Type} (hne : k₁ ≠ k₂) :
    ¬PSet.Equiv ((levyTriplePSet κ α).Func k₁) ((levyTriplePSet κ α).Func k₂) := by
  intro heqv
  rcases k₁ with ⟨⟨ξ₁, η₁⟩, y₁⟩
  rcases k₂ with ⟨⟨ξ₂, η₂⟩, y₂⟩
  have hchk : (⊤ : anonymousAlgebra κ) ≤
      pair (pair (check ((PSet.ordinalMk α).Func ξ₁)) (check ((PSet.ordinalMk κ.ord).Func η₁)))
        (check ((PSet.ordinalMk α).Func y₁)) =ᴮ
      pair (pair (check ((PSet.ordinalMk α).Func ξ₂)) (check ((PSet.ordinalMk κ.ord).Func η₂)))
        (check ((PSet.ordinalMk α).Func y₂)) :=
    bv_trans (bv_symm (check_levyTriplePSet_func α ((ξ₁, η₁), y₁)))
      (bv_trans (check_bv_eq heqv) (check_levyTriplePSet_func α ((ξ₂, η₂), y₂)))
  have hpair₁ := (pair_eq_pair_iff.mp hchk)
  have hpair₂ := (pair_eq_pair_iff.mp hpair₁.1)
  have eq_ξ : ξ₁ = ξ₂ := by
    by_contra h1
    exact top_ne_bot (le_bot_iff.mp (hpair₂.1.trans_eq
      (check_bv_eq_bot_of_not_equiv (PSet.ordinalMk_inj α ξ₁ ξ₂ h1))))
  have eq_η : η₁ = η₂ := by
    by_contra h1
    exact top_ne_bot (le_bot_iff.mp (hpair₂.2.trans_eq
      (check_bv_eq_bot_of_not_equiv (PSet.ordinalMk_inj κ.ord η₁ η₂ h1))))
  have eq_y : y₁ = y₂ := by
    by_contra h1
    exact top_ne_bot (le_bot_iff.mp (hpair₁.2.trans_eq
      (check_bv_eq_bot_of_not_equiv (PSet.ordinalMk_inj α y₁ y₂ h1))))
  exact hne (Prod.ext (Prod.ext eq_ξ eq_η) eq_y)

/-- Nonzero localized triple-membership weights of a stage condition `q`. -/
def tripleSupport (α : Ordinal.{u}) (q : InternalLevyCondition κ α) :
    Set ((levyTriplePSet κ α).Type × anonymousAlgebra κ) :=
  {sw | sw.2 ≠ ⊥ ∧ sw.2 = q.value ⊓ (check ((levyTriplePSet κ α).Func sw.1) ∈ᴮ name q)}

theorem tripleSupport_card_le (hκ : κ.IsInaccessible) (α : Ordinal.{u})
    (q : InternalLevyCondition κ α) :
    #(tripleSupport α q) ≤ (2 : Cardinal.{u}) ^ κ := by
  classical
  let A := anonymousAlgebra κ
  have hA_le : #A ≤ (2 : Cardinal.{u}) ^ κ :=
    (Cardinal.mk_le_of_injective (inclusion_injective A)).trans (completion_cardinal_le_two_power κ hκ)
  obtain ⟨hq_cc, _⟩ := mem_internalLevyCollapse.mp (name_mem q)
  obtain ⟨_, _, hq_cnt⟩ := countableCollapse_mem.mp hq_cc
  obtain ⟨x, hx⟩ := Erdos1172BooleanUltrapower.exists_countable_member_cover (name q) q.value hq_cnt
  let hit (n : ULift.{u} ℕ) (idx : (levyTriplePSet κ α).Type) : A :=
    q.value ⊓ (x n ∈ᴮ name q) ⊓ (check ((levyTriplePSet κ α).Func idx) =ᴮ x n)
  let I_n (n : ULift.{u} ℕ) := {idx : (levyTriplePSet κ α).Type // hit n idx ≠ ⊥}
  have hinj_n (n : ULift.{u} ℕ) : Function.Injective (fun idx : I_n n => hit n idx.val) := by
    intro i₁ i₂ heq
    apply Subtype.ext
    by_contra hne
    have hsame : hit n i₁.val ≤ check ((levyTriplePSet κ α).Func i₁.val) =ᴮ
        check ((levyTriplePSet κ α).Func i₂.val) :=
      bv_trans inf_le_right (bv_symm (heq.le.trans inf_le_right))
    rw [check_bv_eq_bot_of_not_equiv (levyTriplePSet_inj α hne)] at hsame
    exact i₁.property (le_bot_iff.mp hsame)
  have hcov' (sw : tripleSupport α q) : ∃ n : ULift.{u} ℕ, hit n sw.val.1 ≠ ⊥ := by
    have hw_ne : sw.val.2 ≠ ⊥ := sw.property.1
    have hw_eq : sw.val.2 = q.value ⊓ (check ((levyTriplePSet κ α).Func sw.val.1) ∈ᴮ name q) :=
      sw.property.2
    by_contra! hall
    apply hw_ne
    rw [hw_eq]
    apply le_antisymm ?_ bot_le
    have hstep := le_inf (inf_le_left :
      q.value ⊓ (check ((levyTriplePSet κ α).Func sw.val.1) ∈ᴮ name q) ≤ q.value)
      (hx (check ((levyTriplePSet κ α).Func sw.val.1)))
    rw [inf_iSup_eq] at hstep
    refine hstep.trans (iSup_le fun n => ?_)
    have hle_hit : q.value ⊓ ((x n ∈ᴮ name q) ⊓
        (check ((levyTriplePSet κ α).Func sw.val.1) =ᴮ x n)) ≤ hit n sw.val.1 := by
      dsimp only [hit]
      rw [← inf_assoc]
    exact hle_hit.trans_eq (hall n)
  choose fn hfn using hcov'
  let toSigma (sw : tripleSupport α q) : Σ n : ULift.{u} ℕ, I_n n := ⟨fn sw, ⟨sw.val.1, hfn sw⟩⟩
  have hto_inj : Function.Injective toSigma := by
    intro sw₁ sw₂ h
    have hidx : sw₁.val.1 = sw₂.val.1 := congrArg (fun s : Σ n : ULift.{u} ℕ, I_n n => s.2.val) h
    apply Subtype.ext
    apply Prod.ext hidx
    rw [sw₁.property.2, sw₂.property.2, hidx]
  apply (Cardinal.mk_le_of_injective hto_inj).trans
  rw [Cardinal.mk_sigma]
  exact (Cardinal.sum_le_sum _ (fun _ => (2 : Cardinal.{u}) ^ κ) fun n =>
    (Cardinal.mk_le_of_injective (hinj_n n)).trans hA_le).trans_eq (by
      rw [Cardinal.sum_const', Cardinal.mk_uLift, Cardinal.mk_denumerable, Cardinal.lift_aleph0,
        Cardinal.aleph0_mul_eq (hκ.aleph0_lt.le.trans (Cardinal.cantor κ).le)])

theorem condition_eq_of_tripleSupport_eq {α : Ordinal.{u}}
    {q₁ q₂ : InternalLevyCondition κ α}
    (hv : q₁.value = q₂.value) (hs : tripleSupport α q₁ = tripleSupport α q₂) :
    condition q₁ = condition q₂ := by
  let P_α := levyTriplePSet κ α
  have hprod_eq : (⊤ : anonymousAlgebra κ) ≤
      prod (prod (ordinalCarrier α) (ordinalCarrier κ.ord)) (ordinalCarrier α) =ᴮ check P_α :=
    prod_ordinalCarrier_eq_check_levyTriplePSet α
  have hsub₁ : q₁.value ≤ name q₁ ⊆ᴮ check P_α :=
    subset_trans' (countableCollapse_mem.mp (mem_internalLevyCollapse.mp (name_mem q₁)).1).1
      (subset_of_eq (le_top.trans hprod_eq))
  have hsub₂ : q₁.value ≤ name q₂ ⊆ᴮ check P_α :=
    subset_trans' (hv.le.trans (countableCollapse_mem.mp (mem_internalLevyCollapse.mp (name_mem q₂)).1).1)
      (subset_of_eq (le_top.trans hprod_eq))
  have hrow (idx : P_α.Type) :
      q₁.value ⊓ (check (P_α.Func idx) ∈ᴮ name q₁) =
      q₁.value ⊓ (check (P_α.Func idx) ∈ᴮ name q₂) := by
    let w₁ := q₁.value ⊓ (check (P_α.Func idx) ∈ᴮ name q₁)
    let w₂ := q₂.value ⊓ (check (P_α.Func idx) ∈ᴮ name q₂)
    change w₁ = q₁.value ⊓ _
    rw [hv]
    change w₁ = w₂
    by_cases hw₁ : w₁ = ⊥
    · rw [hw₁]
      symm
      by_contra hw₂
      have hm₂ : (idx, w₂) ∈ tripleSupport α q₂ := ⟨hw₂, rfl⟩
      rw [← hs] at hm₂
      exact hm₂.1 (hm₂.2.trans hw₁)
    · have hm₁ : (idx, w₁) ∈ tripleSupport α q₁ := ⟨hw₁, rfl⟩
      rw [hs] at hm₁
      exact hm₁.2
  have rep (Y : bSet (anonymousAlgebra κ)) (sub : q₁.value ≤ Y ⊆ᴮ check P_α) :
      q₁.value ≤ Y =ᴮ ErdosCheckedIndicator.checkedIndicator P_α
        (fun k => q₁.value ⊓ (check (P_α.Func k) ∈ᴮ Y)) := by
    have h0 : q₁.value ≤ Y =ᴮ ErdosCheckedIndicator.checkedIndicator P_α
        (fun k => check (P_α.Func k) ∈ᴮ Y) := by
      rw [ErdosCheckedIndicator.checkedIndicator_membership_eq]
      exact eq_membership_indicator_of_subset sub
    refine bv_trans h0 (subset_ext
      (ErdosCheckedIndicator.checkedIndicator_subset_of_coefficients _ fun _ => le_inf inf_le_left inf_le_right)
      (ErdosCheckedIndicator.checkedIndicator_subset_of_coefficients _ fun _ => inf_le_right.trans inf_le_right))
  have hnm_eq : q₁.value ≤ name q₁ =ᴮ name q₂ := by
    have r₁ := rep (name q₁) hsub₁
    simp_rw [hrow] at r₁
    exact bv_trans r₁ (bv_symm (rep (name q₂) hsub₂))
  exact le_antisymm
    (condition_mono ⟨hv.le, subset_of_eq (bv_symm hnm_eq)⟩)
    (condition_mono ⟨hv.symm.le, subset_of_eq (hv.symm.le.trans hnm_eq)⟩)

def stageProjCone {α β : Ordinal.{u}} (_h : α ≤ β) (q : InternalLevyCondition κ β) :
    InternalLevyStage κ α :=
  ⨆ p : {p : InternalLevyCondition κ α //
      p.value ≤ q.value ∧ p.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) ⊆ᴮ name p},
    condition p.val

theorem stageProjCone_ne_bot {α β : Ordinal.{u}} (h : α ≤ β) (q : InternalLevyCondition κ β) :
    stageProjCone h q ≠ ⊥ := by
  have hmem : q.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) ∈ᴮ
      internalLevyPoset κ α :=
    restrictLevy_mem (check_Ord (PSet.Ord_mk α)) (name_mem q)
  obtain ⟨p, hpv, hpeq⟩ := exists_canonical_refinement q.nonzero hmem
  intro h0
  have hle : condition p ≤ stageProjCone h q :=
    le_iSup (fun r : {r : InternalLevyCondition κ α //
      r.value ≤ q.value ∧ r.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) ⊆ᴮ name r} =>
        condition r.val) ⟨p, hpv, subset_of_eq hpeq⟩
  exact condition_ne_bot p (le_bot_iff.mp (hle.trans_eq h0))

theorem stageProjCone_mono {α β : Ordinal.{u}} (h : α ≤ β)
    {q₁ q₂ : InternalLevyCondition κ β} (hq : q₁ ≤ q₂) :
    stageProjCone h q₁ ≤ stageProjCone h q₂ := by
  refine iSup_le fun ⟨p, hpv, hpsub⟩ => ?_
  have hres_mono : p.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q₂) ⊆ᴮ
      restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q₁) := by
    rw [subset_unfold']
    refine le_iInf fun z => projection_imp.mpr fun d hd hz => ?_
    obtain ⟨hz_q₂, hz_b⟩ := mem_restrictLevy_iff.mp hz
    exact mem_restrictLevy_iff.mpr ⟨mem_of_mem_subset ((hd.trans hpv).trans hq.2) hz_q₂, hz_b⟩
  exact le_iSup (fun r : {r : InternalLevyCondition κ α //
    r.value ≤ q₂.value ∧ r.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q₂) ⊆ᴮ name r} =>
      condition r.val) ⟨p, hpv.trans hq.1, subset_trans' hres_mono hpsub⟩

private theorem stageProjCone_le_of_restrict_eq {α β : Ordinal.{u}} (h : α ≤ β)
    {q : InternalLevyCondition κ β} {p : InternalLevyCondition κ α}
    (hqv : q.value ≤ p.value)
    (hres : q.value ≤ name p ⊆ᴮ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q)) :
    stageProjCone h q ≤ condition p := by
  refine iSup_le fun ⟨r, hrv, hrsub⟩ => ?_
  exact condition_mono ⟨hrv.trans hqv, subset_trans' (hrv.trans hres) hrsub⟩

def stageProjOrderHom {α β : Ordinal.{u}} (h : α ≤ β) :
    InternalLevyCondition κ β →o Positive (InternalLevyStage κ α) :=
  ⟨fun q => ⟨stageProjCone h q, stageProjCone_ne_bot h q⟩, fun _ _ hq => stageProjCone_mono h hq⟩

theorem stageProjOrderHom_lifts {α β : Ordinal.{u}} (h : α ≤ β) :
    Lifts (stageProjOrderHom (κ := κ) h) := by
  intro q c hc
  have hc_val : c.val ≤ stageProjCone h q := hc
  have hmeet : c.val ⊓ stageProjCone h q ≠ ⊥ := by
    erw [inf_of_le hc_val]
    exact c.property
  obtain ⟨⟨p, hpv, hpsub⟩, hcp⟩ := exists_mem_iSup_inf_ne_bot hmeet
  obtain ⟨p₁, hp₁⟩ := exists_condition_le hcp
  obtain ⟨p₂, hp₂_p₁, hp₂_p⟩ :=
    (mem_condition_iff p p₁).mp (condition_le_iff.mp (hp₁.trans inf_le_right)) p₁ le_rfl
  have hp₂_c : condition p₂ ≤ c.val := (condition_mono hp₂_p₁).trans (hp₁.trans inf_le_left)
  have hΛ : (⊤ : anonymousAlgebra κ) ≤ ordinalCarrier α ⊆ᴮ ordinalCarrier β :=
    check_subset (ZFSet.subset_iff.mp (Ordinal.toZFSet_monotone h))
  have hp₂_qv : p₂.value ≤ q.value := hp₂_p.1.trans hpv
  have hcompat : p₂.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) ⊆ᴮ name p₂ :=
    subset_trans' (hp₂_p.1.trans hpsub) hp₂_p.2
  obtain ⟨hu_mem, hu_res⟩ := amalgamate_mem (le_top.trans hΛ) (name_mem p₂)
    (hp₂_qv.trans (name_mem q)) hcompat
  obtain ⟨r, hrv, hreq⟩ := exists_canonical_refinement p₂.nonzero hu_mem
  have hr_q : r ≤ q :=
    ⟨hrv.trans hp₂_qv,
     subset_trans' (le_top.trans subset_binary_union_right) (subset_of_eq hreq)⟩
  have hr_res : r.value ≤ name p₂ ⊆ᴮ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name r) :=
    subset_of_eq (bv_symm (bv_trans (restrictLevy_congr (bv_symm hreq)) (hrv.trans hu_res)))
  exact ⟨r, hr_q, (stageProjCone_le_of_restrict_eq h hrv hr_res).trans hp₂_c⟩

private theorem stageProjOrderHom_dense {α β : Ordinal.{u}} (h : α ≤ β)
    (c : Positive (InternalLevyStage κ α)) :
    ∃ q, stageProjOrderHom (κ := κ) h q ≤ c := by
  obtain ⟨p, hpc⟩ := exists_condition_le c.property
  have hΛ : (⊤ : anonymousAlgebra κ) ≤ ordinalCarrier α ⊆ᴮ ordinalCarrier β :=
    check_subset (ZFSet.subset_iff.mp (Ordinal.toZFSet_monotone h))
  have hp_β : p.value ≤ name p ∈ᴮ internalLevyPoset κ β :=
    mem_of_mem_subset (le_top.trans (internalLevyCollapse_mono hΛ)) (name_mem p)
  obtain ⟨q, hqv, hqeq⟩ := exists_canonical_refinement p.nonzero hp_β
  have hres : q.value ≤ name p ⊆ᴮ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) :=
    subset_of_eq (bv_symm (bv_trans (restrictLevy_congr (bv_symm hqeq))
      (restrictLevy_eq_self (hqv.trans (name_mem p)))))
  exact ⟨q, (stageProjCone_le_of_restrict_eq h hqv hres).trans hpc⟩

/-- Complete Boolean stage embedding `InternalLevyStage κ α → InternalLevyStage κ β` (`α ≤ β`). -/
def stageStepHom {α β : Ordinal.{u}} (h : α ≤ β) :
    CompleteLatticeHom (InternalLevyStage κ α) (InternalLevyStage κ β) :=
  (booleanHom (stageProjOrderHom (κ := κ) h) (stageProjOrderHom_lifts h)).comp
    (CompleteLatticeHom.OrderIso.toCompleteLatticeHom (completionOrderIso (B := InternalLevyStage κ α)))

theorem stageStepHom_injective {α β : Ordinal.{u}} (h : α ≤ β) :
    Function.Injective (stageStepHom (κ := κ) h) :=
  (booleanHom_injective (stageProjOrderHom (κ := κ) h) (stageProjOrderHom_lifts h)
    (stageProjOrderHom_dense h)).comp (completionOrderIso (B := InternalLevyStage κ α)).injective

theorem condition_le_stageStepHom_iff {α β : Ordinal.{u}} (h : α ≤ β)
    (q : InternalLevyCondition κ β) (x : InternalLevyStage κ α) :
    condition q ≤ stageStepHom (κ := κ) h x ↔ stageProjCone h q ≤ x := by
  rw [condition_le_iff]
  change stageProjOrderHom h q ∈ (completionOrderIso x).val ↔ stageProjCone h q ≤ x
  rw [completionOrderIso_apply, mem_element]
  rfl

theorem stageStepHom_sourceHom {α β : Ordinal.{u}} (h : α ≤ β) (a : anonymousAlgebra κ) :
    stageStepHom (κ := κ) h (sourceHom (internalLevyPoset κ α) a) =
      sourceHom (internalLevyPoset κ β) a := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro q
  rw [← condition_le_iff, ← condition_le_iff, condition_le_stageStepHom_iff, condition_le_source]
  constructor
  · intro hle
    have hmem : q.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) ∈ᴮ
        internalLevyPoset κ α :=
      restrictLevy_mem (check_Ord (PSet.Ord_mk α)) (name_mem q)
    by_contra hnot
    have hpos : q.value ⊓ aᶜ ≠ ⊥ := fun h0 =>
      hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    obtain ⟨p, hpv, hpeq⟩ := exists_canonical_refinement hpos (inf_le_left.trans hmem)
    have hp_cone : condition p ≤ stageProjCone h q :=
      le_iSup (fun r : {r : InternalLevyCondition κ α //
        r.value ≤ q.value ∧ r.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) ⊆ᴮ name r} =>
          condition r.val) ⟨p, hpv.trans inf_le_left, subset_of_eq hpeq⟩
    have hp_a : p.value ≤ a := (condition_le_source _ p a).mp (hp_cone.trans hle)
    exact p.nonzero (le_bot_iff.mp ((le_inf hp_a (hpv.trans inf_le_right)).trans inf_compl_eq_bot.le))
  · intro hqa
    exact iSup_le fun ⟨p, hpv, _⟩ => (condition_le_source _ p a).mpr (hpv.trans hqa)

theorem stageStepHom_comp {α β γ : Ordinal.{u}} (h₁ : α ≤ β) (h₂ : β ≤ γ)
    (x : InternalLevyStage κ α) :
    stageStepHom (κ := κ) h₂ (stageStepHom (κ := κ) h₁ x) = stageStepHom (κ := κ) (h₁.trans h₂) x := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro q
  rw [← condition_le_iff, ← condition_le_iff, condition_le_stageStepHom_iff, condition_le_stageStepHom_iff]
  have hΛ₁ : (⊤ : anonymousAlgebra κ) ≤ ordinalCarrier α ⊆ᴮ ordinalCarrier β :=
    check_subset (ZFSet.subset_iff.mp (Ordinal.toZFSet_monotone h₁))
  constructor
  · intro hle
    refine iSup_le fun ⟨p, hpv, hpsub⟩ => ?_
    by_contra hnot
    have hpos : condition p ⊓ xᶜ ≠ ⊥ := fun h0 =>
      hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    obtain ⟨p', hp'⟩ := exists_condition_le hpos
    obtain ⟨p'', hp''_p', hp''_p⟩ :=
      (mem_condition_iff p p').mp (condition_le_iff.mp (hp'.trans inf_le_left)) p' le_rfl
    have hp''_qv : p''.value ≤ q.value := hp''_p.1.trans hpv
    have hq_β : q.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier β) (name q) ∈ᴮ
        internalLevyPoset κ β :=
      restrictLevy_mem (check_Ord (PSet.Ord_mk β)) (name_mem q)
    have hcompat : p''.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α)
        (restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier β) (name q)) ⊆ᴮ name p'' :=
      subset_trans' (subset_of_eq (le_top.trans (restrictLevy_idem hΛ₁)))
        (subset_trans' (hp''_p.1.trans hpsub) hp''_p.2)
    obtain ⟨hu_mem, hu_res⟩ := amalgamate_mem (le_top.trans hΛ₁) (name_mem p'')
      (hp''_qv.trans hq_β) hcompat
    obtain ⟨r, hrv, hreq⟩ := exists_canonical_refinement p''.nonzero hu_mem
    have hr_cone : condition r ≤ stageProjCone h₂ q :=
      le_iSup (fun s : {s : InternalLevyCondition κ β //
        s.value ≤ q.value ∧ s.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier β) (name q) ⊆ᴮ name s} =>
          condition s.val)
        ⟨r, hrv.trans hp''_qv,
         subset_trans' (le_top.trans subset_binary_union_right) (subset_of_eq hreq)⟩
    have hr_x : stageProjCone h₁ r ≤ x :=
      (condition_le_stageStepHom_iff h₁ r x).mp (hr_cone.trans hle)
    have hm : r.value ≤ name p'' ∈ᴮ internalLevyPoset κ α := hrv.trans (name_mem p'')
    obtain ⟨t, htv, hteq⟩ := exists_canonical_refinement r.nonzero hm
    have hres_r : r.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name r) =ᴮ name p'' :=
      bv_trans (restrictLevy_congr (bv_symm hreq)) (hrv.trans hu_res)
    have hsub_t : t.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name r) ⊆ᴮ name t :=
      bSet.subset_of_eq (bv_trans (htv.trans hres_r) hteq)
    have ht_cone : condition t ≤ stageProjCone h₁ r :=
      le_iSup (fun s : {s : InternalLevyCondition κ α //
        s.value ≤ r.value ∧ s.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name r) ⊆ᴮ name s} =>
          condition s.val) ⟨t, htv, hsub_t⟩
    have ht_p'' : t ≤ p'' := ⟨htv.trans hrv, subset_of_eq hteq⟩
    have ht_xc : condition t ≤ xᶜ :=
      (condition_mono (ht_p''.trans hp''_p')).trans (hp'.trans inf_le_right)
    exact condition_ne_bot t
      (le_bot_iff.mp ((le_inf (ht_cone.trans hr_x) ht_xc).trans inf_compl_eq_bot.le))
  · intro hle
    refine iSup_le fun ⟨r, hrv, hrsub⟩ => ?_
    rw [condition_le_stageStepHom_iff]
    refine iSup_le fun ⟨p, hpv, hpsub⟩ => ?_
    have hp_sub_q : p.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) ⊆ᴮ name p := by
      have h1 : p.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α)
          (restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier β) (name q)) ⊆ᴮ
          restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name r) := by
        rw [subset_unfold']
        refine le_iInf fun z => projection_imp.mpr fun d hd hz => ?_
        obtain ⟨hz_q, hz_b⟩ := mem_restrictLevy_iff.mp hz
        exact mem_restrictLevy_iff.mpr ⟨mem_of_mem_subset ((hd.trans hpv).trans hrsub) hz_q, hz_b⟩
      exact subset_trans' (subset_of_eq (bv_symm (le_top.trans (restrictLevy_idem hΛ₁))))
        (subset_trans' h1 hpsub)
    exact (le_iSup (fun s : {s : InternalLevyCondition κ α //
      s.value ≤ q.value ∧ s.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) ⊆ᴮ name s} =>
        condition s.val) ⟨p, hpv.trans hrv, hp_sub_q⟩).trans hle

theorem stageStepHom_condition {α β : Ordinal.{u}} (h : α ≤ β) (p : InternalLevyCondition κ α) :
    stageStepHom (κ := κ) h (condition p) =
      ⨆ q : {q : InternalLevyCondition κ β // q.value ≤ p.value ∧ q.value ≤ name p ⊆ᴮ name q},
        condition q.val := by
  let rhs := ⨆ q : {q : InternalLevyCondition κ β // q.value ≤ p.value ∧ q.value ≤ name p ⊆ᴮ name q},
    condition q.val
  have hΛ : (⊤ : anonymousAlgebra κ) ≤ ordinalCarrier α ⊆ᴮ ordinalCarrier β :=
    check_subset (ZFSet.subset_iff.mp (Ordinal.toZFSet_monotone h))
  apply le_antisymm
  · apply le_of_dense_conditions_le Set.univ (fun q => ⟨q, Set.mem_univ _, le_rfl⟩)
    rintro ⟨q, _⟩ hq
    have hcone : stageProjCone h q ≤ condition p := (condition_le_stageStepHom_iff h q _).mp hq
    by_contra hnot
    have hpos : condition q ⊓ rhsᶜ ≠ ⊥ := fun h0 =>
      hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    obtain ⟨q₁, hq₁⟩ := exists_condition_le hpos
    obtain ⟨q₂, hq₂_q₁, hq₂_q⟩ :=
      (mem_condition_iff q q₁).mp (condition_le_iff.mp (hq₁.trans inf_le_left)) q₁ le_rfl
    have hres_mem : q₂.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q₂) ∈ᴮ
        internalLevyPoset κ α :=
      restrictLevy_mem (check_Ord (PSet.Ord_mk α)) (name_mem q₂)
    obtain ⟨r₀, hr₀v, hr₀eq⟩ := exists_canonical_refinement q₂.nonzero hres_mem
    have hr₀_cone : condition r₀ ≤ stageProjCone h q := by
      have hsub : r₀.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) ⊆ᴮ name r₀ := by
        refine subset_trans' ?_ (subset_of_eq hr₀eq)
        rw [subset_unfold']
        refine le_iInf fun z => projection_imp.mpr fun d hd hz => ?_
        obtain ⟨hz_q, hz_b⟩ := mem_restrictLevy_iff.mp hz
        exact mem_restrictLevy_iff.mpr ⟨mem_of_mem_subset ((hd.trans hr₀v).trans hq₂_q.2) hz_q, hz_b⟩
      exact le_iSup (fun s : {s : InternalLevyCondition κ α //
        s.value ≤ q.value ∧ s.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) ⊆ᴮ name s} =>
          condition s.val) ⟨r₀, hr₀v.trans hq₂_q.1, hsub⟩
    obtain ⟨r₁, hr₁_r₀, hr₁_p⟩ :=
      (mem_condition_iff p r₀).mp (condition_le_iff.mp (hr₀_cone.trans hcone)) r₀ le_rfl
    have hcompat : r₁.value ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q₂) ⊆ᴮ name r₁ :=
      subset_trans' (subset_of_eq ((hr₁_r₀.1).trans hr₀eq)) hr₁_r₀.2
    obtain ⟨hu_mem, _⟩ := amalgamate_mem (le_top.trans hΛ) (name_mem r₁)
      ((hr₁_r₀.1.trans hr₀v).trans (name_mem q₂)) hcompat
    obtain ⟨q₃, hq₃v, hq₃eq⟩ := exists_canonical_refinement r₁.nonzero hu_mem
    have hq₃_rhs : condition q₃ ≤ rhs :=
      le_iSup (fun s : {s : InternalLevyCondition κ β // s.value ≤ p.value ∧ s.value ≤ name p ⊆ᴮ name s} =>
        condition s.val)
        ⟨q₃, hq₃v.trans hr₁_p.1,
         subset_trans' (hq₃v.trans hr₁_p.2)
           (subset_trans' (le_top.trans subset_binary_union_left) (subset_of_eq hq₃eq))⟩
    have hq₃_q₂ : q₃ ≤ q₂ :=
      ⟨hq₃v.trans (hr₁_r₀.1.trans hr₀v),
       subset_trans' (le_top.trans subset_binary_union_right) (subset_of_eq hq₃eq)⟩
    have hq₃_not : condition q₃ ≤ rhsᶜ :=
      (condition_mono (hq₃_q₂.trans hq₂_q₁)).trans (hq₁.trans inf_le_right)
    exact condition_ne_bot q₃ (le_bot_iff.mp ((le_inf hq₃_rhs hq₃_not).trans inf_compl_eq_bot.le))
  · refine iSup_le fun ⟨q, hqv, hqsub⟩ => ?_
    rw [condition_le_stageStepHom_iff]
    refine iSup_le fun ⟨r, hrv, hrsub⟩ => ?_
    have hp_sub_res : q.value ≤ name p ⊆ᴮ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier α) (name q) := by
      rw [subset_unfold']
      refine le_iInf fun z => projection_imp.mpr fun d hd hz => ?_
      exact mem_restrictLevy_iff.mpr ⟨mem_of_mem_subset (hd.trans hqsub) hz,
        allIn_elim (((hd.trans hqv).trans (mem_internalLevyCollapse.mp (name_mem p)).2)) hz⟩
    exact condition_mono ⟨hrv.trans hqv, subset_trans' (hrv.trans hp_sub_res) hrsub⟩

/-- Stage embedding into `InternalLevyAlgebra κ θ`. -/
abbrev stageHom {θ : Cardinal.{u}} {α : Ordinal.{u}} (h : α ≤ θ.ord) :
    CompleteLatticeHom (InternalLevyStage κ α) (InternalLevyAlgebra κ θ) :=
  stageStepHom (κ := κ) h

/-- Every condition in `InternalLevyCondition κ θ.ord` is bounded below some `α < θ.ord`. -/
theorem condition_bounded_below_theta {θ : Cardinal.{u}}
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (q : InternalLevyCondition κ θ.ord) :
    ∃ i : θ.ord.ToType, q.value ≤ name q ∈ᴮ internalLevyPoset κ (Order.succ i.toOrd.val) := by
  have hts : #(tripleSupport θ.ord q) < θ :=
    (tripleSupport_card_le hκ θ.ord q).trans_lt (hθ.isStrongPrelimit hk)
  let firstOrd (sw : tripleSupport θ.ord q) : Ordinal.{u} :=
    ((PSet.mem_ordinalMk_iff.mp (PSet.func_mem (PSet.ordinalMk θ.ord) sw.val.1.1.1)).choose)
  have hfirst_lt (sw : tripleSupport θ.ord q) : firstOrd sw < θ.ord :=
    (PSet.mem_ordinalMk_iff.mp (PSet.func_mem (PSet.ordinalMk θ.ord) sw.val.1.1.1)).choose_spec.1
  let sup_ord := ⨆ sw : tripleSupport θ.ord q, firstOrd sw
  have hsup_lt : sup_ord < θ.ord := by
    apply Ordinal.lift_iSup_lt_of_lt_cof _ hfirst_lt
    simpa [hθ.isRegular.cof_ord] using hts
  let i₀ : θ.ord.ToType := Ordinal.ToType.mk ⟨sup_ord, hsup_lt⟩
  have hi₀_ord : i₀.toOrd.val = sup_ord :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  refine ⟨i₀, ?_⟩
  let P_θ := levyTriplePSet κ θ.ord
  have hprod_eq : (⊤ : anonymousAlgebra κ) ≤
      prod (prod (ordinalCarrier θ.ord) (ordinalCarrier κ.ord)) (ordinalCarrier θ.ord) =ᴮ check P_θ :=
    prod_ordinalCarrier_eq_check_levyTriplePSet θ.ord
  have hsub_P : q.value ≤ name q ⊆ᴮ check P_θ :=
    subset_trans' (countableCollapse_mem.mp (mem_internalLevyCollapse.mp (name_mem q)).1).1
      (subset_of_eq (le_top.trans hprod_eq))
  have hres_eq : q.value ≤ restrictLevy (ordinalCarrier κ.ord)
      (ordinalCarrier (Order.succ i₀.toOrd.val)) (name q) =ᴮ name q := by
    apply subset_ext (le_top.trans (restrictLevy_subset _ _ _))
    rw [subset_unfold']
    refine le_iInf fun z => projection_imp.mpr fun d hd hz => ?_
    have hz_P : d ≤ z ∈ᴮ check P_θ := mem_of_mem_subset (hd.trans hsub_P) hz
    rw [check_unfold, mem_unfold] at hz_P
    apply (le_inf (le_inf hd hz) hz_P).trans
    rw [inf_iSup_eq]
    refine iSup_le fun idx => ?_
    let c := (q.value ⊓ (z ∈ᴮ name q)) ⊓ (⊤ ⊓ (z =ᴮ check (P_θ.Func idx)))
    have hc_mem : c ≤ q.value ⊓ (check (P_θ.Func idx) ∈ᴮ name q) :=
      le_inf (inf_le_left.trans inf_le_left)
        (mem_congr (inf_le_right.trans inf_le_right) bv_refl (inf_le_left.trans inf_le_right))
    let w := q.value ⊓ (check (P_θ.Func idx) ∈ᴮ name q)
    by_cases hw : w = ⊥
    · exact (hc_mem.trans_eq hw).trans bot_le
    · refine mem_restrictLevy_iff.mpr ⟨inf_le_left.trans inf_le_right, ?_⟩
      let sw : tripleSupport θ.ord q := ⟨(idx, w), hw, rfl⟩
      have hspec := (PSet.mem_ordinalMk_iff.mp (PSet.func_mem (PSet.ordinalMk θ.ord) idx.1.1)).choose_spec
      have hlt : firstOrd sw < Order.succ i₀.toOrd.val := by
        rw [hi₀_ord]
        exact (Ordinal.le_iSup firstOrd sw).trans_lt (Order.lt_succ sup_ord)
      have hξ_mem : c ≤ check ((PSet.ordinalMk θ.ord).Func idx.1.1) ∈ᴮ
          ordinalCarrier (Order.succ i₀.toOrd.val) :=
        mem_congr (bv_symm (check_bv_eq hspec.2)) bv_refl (check_mem (PSet.mk_mem_mk_of_lt hlt))
      have hchk_eq : (⊤ : anonymousAlgebra κ) ≤ check (P_θ.Func idx) =ᴮ
          pair (pair (check ((PSet.ordinalMk θ.ord).Func idx.1.1))
            (check ((PSet.ordinalMk κ.ord).Func idx.1.2)))
            (check ((PSet.ordinalMk θ.ord).Func idx.2)) :=
        check_levyTriplePSet_func θ.ord idx
      have hbd_θ : c ≤ levyBoundPred (ordinalCarrier κ.ord) (ordinalCarrier θ.ord) z :=
        allIn_elim ((inf_le_left.trans inf_le_left).trans (mem_internalLevyCollapse.mp (name_mem q)).2)
          (inf_le_left.trans inf_le_right)
      exact levyBoundPred_of_first_mem (bv_trans (inf_le_right.trans inf_le_right) (le_top.trans hchk_eq))
        hbd_θ
        (le_iSup_of_le (check ((PSet.ordinalMk θ.ord).Func idx.1.1))
          (le_inf hξ_mem (le_iSup_of_le (check ((PSet.ordinalMk κ.ord).Func idx.1.2))
            (le_inf (check_mem (PSet.func_mem _ idx.1.2)) bv_refl))))
  exact mem_congr hres_eq bv_refl
    (restrictLevy_mem (check_Ord (PSet.Ord_mk _)) (name_mem q))

theorem internalLevyCondition_cardinal_lt {θ : Cardinal.{u}}
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    {α : Ordinal.{u}} (hα : α < θ.ord) :
    #(InternalLevyCondition κ α) < θ := by
  let A := anonymousAlgebra κ
  have hA : #A < θ :=
    (Cardinal.mk_le_of_injective (inclusion_injective A)).trans_lt
      ((completion_cardinal_le_two_power κ hκ).trans_lt (hθ.isStrongPrelimit hk))
  let X : bSet A := prod (prod (ordinalCarrier α) (ordinalCarrier κ.ord)) (ordinalCarrier α)
  have hX : Cardinal.mk X.type < θ := by
    change Cardinal.mk (((ordinalCarrier α : bSet A).type × (ordinalCarrier κ.ord : bSet A).type) ×
      (ordinalCarrier α : bSet A).type) < θ
    simp only [Cardinal.mk_prod, Cardinal.lift_id, ordinalCarrier, check_type', PSet.ordinalMk_type,
      Cardinal.mk_toType, Cardinal.card_ord]
    exact Cardinal.mul_lt_of_lt hθ.aleph0_lt.le
      (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le (Cardinal.lt_ord.mp hα) hk)
      (Cardinal.lt_ord.mp hα)
  have hpow : Cardinal.mk (X.type → A) < θ := by
    let gr (b : X.type → A) : Set (X.type × A) := {t | b t.1 = t.2}
    have hinj : Function.Injective gr := fun b c eq =>
      _root_.funext fun i => (eq ▸ (show (i, b i) ∈ gr b from rfl) : (i, b i) ∈ gr c).symm
    apply (Cardinal.mk_le_of_injective hinj).trans_lt
    rw [Cardinal.mk_set, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact hθ.isStrongPrelimit (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hX hA)
  have htype : (internalLevyPoset κ α).type = (X.type → A) := rfl
  let code (p : InternalLevyCondition κ α) : A × (internalLevyPoset κ α).type := (p.value, p.index)
  have hcode_inj : Function.Injective code := by
    rintro ⟨v₁, _, i₁, _⟩ ⟨v₂, _, i₂, _⟩ h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl
  apply (Cardinal.mk_le_of_injective hcode_inj).trans_lt
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, htype]
  exact Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hA hpow

theorem toOrd_lt {α : Ordinal.{u}} (i : α.ToType) : i.toOrd.val < α :=
  i.toOrd.property

/-- `DenseStageUnion` for the `(i.toOrd.val + 1)`-indexed stage filtration of `InternalLevyAlgebra κ θ`. -/
theorem internalLevy_denseStageUnion {θ : Cardinal.{u}}
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible) :
    DenseStageUnion (fun i : θ.ord.ToType =>
      stageHom (κ := κ) (θ := θ) (Order.succ_le_of_lt (toOrd_lt i))) := by
  intro z hz
  obtain ⟨q, hqz⟩ := exists_condition_le hz
  obtain ⟨i, hi_mem⟩ := condition_bounded_below_theta hk hκ hθ q
  obtain ⟨p, hpv, hpeq⟩ := exists_canonical_refinement q.nonzero hi_mem
  have himg_le : stageHom (κ := κ) (θ := θ) (Order.succ_le_of_lt (toOrd_lt i)) (condition p) ≤ z := by
    rw [stageStepHom_condition]
    refine iSup_le fun ⟨r, hrv, hrsub⟩ => ?_
    have hr_q : r ≤ q := ⟨hrv.trans hpv, subset_trans' (subset_of_eq (hrv.trans hpeq)) hrsub⟩
    exact (condition_mono hr_q).trans hqz
  have himg_ne : stageHom (κ := κ) (θ := θ) (Order.succ_le_of_lt (toOrd_lt i)) (condition p) ≠ ⊥ :=
    fun h0 => condition_ne_bot p (stageStepHom_injective _ (h0.trans (BotHomClass.map_bot _).symm))
  exact ⟨i, condition p, himg_ne, himg_le⟩

/-- `InternalLevyCondition κ θ.ord` admits a dense subset `D` of cardinality `#D ≤ θ`. -/
theorem internalLevy_dense_size {θ : Cardinal.{u}}
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible) :
    ∃ D : Set (InternalLevyCondition κ θ.ord), #D ≤ θ ∧ ∀ q, ∃ d ∈ D, d ≤ q := by
  classical
  let Idx := Σ i : θ.ord.ToType, InternalLevyCondition κ (Order.succ i.toOrd.val)
  have hIdx : #Idx ≤ θ := by
    rw [Cardinal.mk_sigma]
    exact (Cardinal.sum_le_sum _ (fun _ => θ) fun i =>
      (internalLevyCondition_cardinal_lt hk hκ hθ
        ((Cardinal.isSuccLimit_ord hθ.aleph0_lt.le).succ_lt (toOrd_lt i))).le).trans_eq
      (by rw [Cardinal.sum_const', Cardinal.mk_ord_toType, Cardinal.mul_eq_self hθ.aleph0_lt.le])
  let liftCond (s : Idx) : InternalLevyCondition κ θ.ord :=
    let hΛ : (⊤ : anonymousAlgebra κ) ≤
        ordinalCarrier (Order.succ s.1.toOrd.val) ⊆ᴮ ordinalCarrier θ.ord :=
      check_subset (ZFSet.subset_iff.mp
        (Ordinal.toZFSet_monotone (Order.succ_le_of_lt (toOrd_lt s.1))))
    let hm : s.2.value ≤ name s.2 ∈ᴮ internalLevyPoset κ θ.ord :=
      mem_of_mem_subset (le_top.trans (internalLevyCollapse_mono hΛ)) (name_mem s.2)
    (exists_canonical_refinement s.2.nonzero hm).choose
  refine ⟨Set.range liftCond, Cardinal.mk_range_le.trans hIdx, fun q => ?_⟩
  obtain ⟨i, hi⟩ := condition_bounded_below_theta hk hκ hθ q
  obtain ⟨p, hpv, hpeq⟩ := exists_canonical_refinement q.nonzero hi
  let s : Idx := ⟨i, p⟩
  have hspec := (exists_canonical_refinement p.nonzero
    (mem_of_mem_subset (le_top.trans (internalLevyCollapse_mono
      (check_subset (ZFSet.subset_iff.mp
        (Ordinal.toZFSet_monotone (Order.succ_le_of_lt (toOrd_lt i)))))))
      (name_mem p))).choose_spec
  refine ⟨liftCond s, Set.mem_range_self s, ⟨hspec.1.trans hpv, ?_⟩⟩
  exact subset_trans' (subset_of_eq (hspec.1.trans hpeq)) (subset_of_eq hspec.2)

def firstToType {θ : Cardinal.{u}} (i_ξ : (PSet.ordinalMk θ.ord).Type) : θ.ord.ToType :=
  Ordinal.ToType.mk ⟨(PSet.mem_ordinalMk_iff.mp (PSet.func_mem (PSet.ordinalMk θ.ord) i_ξ)).choose,
    (PSet.mem_ordinalMk_iff.mp (PSet.func_mem (PSet.ordinalMk θ.ord) i_ξ)).choose_spec.1⟩

def tripleFirstSupport {θ : Cardinal.{u}} (q : InternalLevyCondition κ θ.ord) : Set θ.ord.ToType :=
  (fun sw : tripleSupport θ.ord q => firstToType sw.val.1.1.1) '' Set.univ

private theorem strictCC_cross_case {θ : Cardinal.{u}}
    (q₁ q₂ : InternalLevyCondition κ θ.ord) (cut : θ.ord.ToType)
    {v E : anonymousAlgebra κ} {a₁ a₂ y₁ y₂ : bSet (anonymousAlgebra κ)}
    (hv₁ : v = q₁.value) (hv₂ : v = q₂.value)
    (hg₁_P : v ≤ name q₁ ⊆ᴮ check (levyTriplePSet κ θ.ord))
    (hg₂_P : v ≤ name q₂ ⊆ᴮ check (levyTriplePSet κ θ.ord))
    (hg₂_bd : v ≤ levyAllBounded (ordinalCarrier κ.ord) (ordinalCarrier θ.ord) (name q₂))
    (hg₁_fn : v ≤ is_func (name q₁))
    (hcut_g : v ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier cut.toOrd.val) (name q₂) ⊆ᴮ name q₁)
    (hsub_both : tripleFirstSupport q₁ ∩ tripleFirstSupport q₂ ⊆ Set.Iio cut)
    (hE_v : E ≤ v) (hE_1 : E ≤ pair a₁ y₁ ∈ᴮ name q₁)
    (hE_2 : E ≤ pair a₂ y₂ ∈ᴮ name q₂) (hE_eq : E ≤ a₁ =ᴮ a₂) : E ≤ y₁ =ᴮ y₂ := by
  let P_θ := levyTriplePSet κ θ.ord
  have hp₁_P : E ≤ pair a₁ y₁ ∈ᴮ check P_θ := mem_of_mem_subset (hE_v.trans hg₁_P) hE_1
  have hp₂_P' : E ≤ pair a₂ y₂ ∈ᴮ check P_θ := mem_of_mem_subset (hE_v.trans hg₂_P) hE_2
  rw [check_unfold, mem_unfold] at hp₁_P hp₂_P'
  apply (le_inf (le_inf le_rfl hp₁_P) hp₂_P').trans
  rw [inf_iSup_eq]
  refine iSup_le fun idx₂ => ?_
  rw [inf_iSup_eq, iSup_inf_eq]
  refine iSup_le fun idx₁ => ?_
  let M := (E ⊓ (⊤ ⊓ (pair a₁ y₁ =ᴮ check (P_θ.Func idx₁)))) ⊓
    (⊤ ⊓ (pair a₂ y₂ =ᴮ check (P_θ.Func idx₂)))
  have hM_E : M ≤ E := inf_le_left.trans inf_le_left
  have hM_1 : M ≤ pair a₁ y₁ =ᴮ check (P_θ.Func idx₁) := (inf_le_left.trans inf_le_right).trans inf_le_right
  have hM_2 : M ≤ pair a₂ y₂ =ᴮ check (P_θ.Func idx₂) := inf_le_right.trans inf_le_right
  let w₁ := q₁.value ⊓ (check (P_θ.Func idx₁) ∈ᴮ name q₁)
  let w₂ := q₂.value ⊓ (check (P_θ.Func idx₂) ∈ᴮ name q₂)
  have hM_w₁ : M ≤ w₁ := le_inf (hv₁ ▸ (hM_E.trans hE_v)) (mem_congr hM_1 bv_refl (hM_E.trans hE_1))
  have hM_w₂ : M ≤ w₂ := le_inf (hv₂ ▸ (hM_E.trans hE_v)) (mem_congr hM_2 bv_refl (hM_E.trans hE_2))
  by_cases hw₁ : w₁ = ⊥
  · exact (hM_w₁.trans_eq hw₁).trans bot_le
  · by_cases hw₂ : w₂ = ⊥
    · exact (hM_w₂.trans_eq hw₂).trans bot_le
    · have hchk_1 : (⊤ : anonymousAlgebra κ) ≤ check (P_θ.Func idx₁) =ᴮ
          pair (pair (check ((PSet.ordinalMk θ.ord).Func idx₁.1.1))
            (check ((PSet.ordinalMk κ.ord).Func idx₁.1.2)))
            (check ((PSet.ordinalMk θ.ord).Func idx₁.2)) :=
        check_levyTriplePSet_func θ.ord idx₁
      have hchk_2 : (⊤ : anonymousAlgebra κ) ≤ check (P_θ.Func idx₂) =ᴮ
          pair (pair (check ((PSet.ordinalMk θ.ord).Func idx₂.1.1))
            (check ((PSet.ordinalMk κ.ord).Func idx₂.1.2)))
            (check ((PSet.ordinalMk θ.ord).Func idx₂.2)) :=
        check_levyTriplePSet_func θ.ord idx₂
      have ha₁_eq : M ≤ a₁ =ᴮ pair (check ((PSet.ordinalMk θ.ord).Func idx₁.1.1))
          (check ((PSet.ordinalMk κ.ord).Func idx₁.1.2)) :=
        (pair_eq_pair_iff.mp (bv_trans hM_1 (le_top.trans hchk_1))).1
      have ha₂_eq : M ≤ a₂ =ᴮ pair (check ((PSet.ordinalMk θ.ord).Func idx₂.1.1))
          (check ((PSet.ordinalMk κ.ord).Func idx₂.1.2)) :=
        (pair_eq_pair_iff.mp (bv_trans hM_2 (le_top.trans hchk_2))).1
      have hξ₁₂ : M ≤ check ((PSet.ordinalMk θ.ord).Func idx₁.1.1) =ᴮ
          check ((PSet.ordinalMk θ.ord).Func idx₂.1.1) :=
        (pair_eq_pair_iff.mp (bv_trans (bv_symm ha₁_eq) (bv_trans (hM_E.trans hE_eq) ha₂_eq))).1
      by_cases hidx_ξ : idx₁.1.1 = idx₂.1.1
      · have hft_eq : firstToType idx₁.1.1 = firstToType idx₂.1.1 := congrArg firstToType hidx_ξ
        have hin₁ : firstToType idx₁.1.1 ∈ tripleFirstSupport q₁ :=
          ⟨⟨(idx₁, w₁), hw₁, rfl⟩, Set.mem_univ _, rfl⟩
        have hin₂ : firstToType idx₁.1.1 ∈ tripleFirstSupport q₂ :=
          hft_eq ▸ ⟨⟨(idx₂, w₂), hw₂, rfl⟩, Set.mem_univ _, rfl⟩
        have hlt_cut : firstToType idx₂.1.1 < cut := hft_eq ▸ hsub_both ⟨hin₁, hin₂⟩
        have hspec₂ := (PSet.mem_ordinalMk_iff.mp
          (PSet.func_mem (PSet.ordinalMk θ.ord) idx₂.1.1)).choose_spec
        have hord_lt : (PSet.mem_ordinalMk_iff.mp
            (PSet.func_mem (PSet.ordinalMk θ.ord) idx₂.1.1)).choose < cut.toOrd.val := by
          have ho : (firstToType idx₂.1.1).toOrd.val = _ :=
            congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
          have hsub_lt : (firstToType idx₂.1.1).toOrd.val < cut.toOrd.val :=
            Ordinal.ToType.mk.symm.strictMono hlt_cut
          exact ho.symm.trans_lt hsub_lt
        have hξ₂_cut : M ≤ check ((PSet.ordinalMk θ.ord).Func idx₂.1.1) ∈ᴮ
            ordinalCarrier cut.toOrd.val :=
          mem_congr (bv_symm (check_bv_eq hspec₂.2)) bv_refl (check_mem (PSet.mk_mem_mk_of_lt hord_lt))
        have hbd₂ : M ≤ levyBoundPred (ordinalCarrier κ.ord) (ordinalCarrier cut.toOrd.val)
            (pair a₂ y₂) :=
          levyBoundPred_of_first_mem bv_refl
            (allIn_elim ((hM_E.trans hE_v).trans hg₂_bd) (hM_E.trans hE_2))
            (le_iSup_of_le (check ((PSet.ordinalMk θ.ord).Func idx₂.1.1))
              (le_inf hξ₂_cut (le_iSup_of_le (check ((PSet.ordinalMk κ.ord).Func idx₂.1.2))
                (le_inf (check_mem (PSet.func_mem _ idx₂.1.2)) ha₂_eq))))
        have hin_1 : M ≤ pair a₂ y₂ ∈ᴮ name q₁ :=
          mem_of_mem_subset ((hM_E.trans hE_v).trans hcut_g)
            (mem_restrictLevy_iff.mpr ⟨hM_E.trans hE_2, hbd₂⟩)
        exact eq_of_is_func_of_eq ((hM_E.trans hE_v).trans hg₁_fn) (hM_E.trans hE_eq)
          (hM_E.trans hE_1) hin_1
      · rw [check_bv_eq_bot_of_not_equiv (PSet.ordinalMk_inj θ.ord _ _ hidx_ξ)] at hξ₁₂
        exact hξ₁₂.trans bot_le

/-- `StrictCC (InternalLevyAlgebra κ θ) θ` via `tripleSupport_card_le` + `exists_pair_agree_on_common_support`. -/
theorem internalLevy_strictCC {θ : Cardinal.{u}}
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible) :
    StrictCC (InternalLevyAlgebra κ θ) θ := by
  classical
  let A := anonymousAlgebra κ
  have hA_le : #A ≤ (2 : Cardinal.{u}) ^ κ :=
    (Cardinal.mk_le_of_injective (inclusion_injective A)).trans (completion_cardinal_le_two_power κ hκ)
  let ρ := Order.succ ((2 : Cardinal.{u}) ^ κ)
  have h2κ_lt : (2 : Cardinal.{u}) ^ κ < θ := hθ.isStrongPrelimit hk
  have hρ_lt : ρ < θ := hθ.isSuccLimit.succ_lt h2κ_lt
  have hρ_reg : ρ.IsRegular := Cardinal.isRegular_succ (hκ.aleph0_lt.le.trans (Cardinal.cantor κ).le)
  intro J w hpos hdisj
  by_contra! hJ
  choose q₀ hq₀ using fun j : J => exists_condition_le (hpos j)
  obtain ⟨emb⟩ : Nonempty (θ.ord.ToType ↪ J) := (Cardinal.mk_ord_toType θ).le.trans hJ
  let q (i : θ.ord.ToType) := q₀ (emb i)
  let supp (i : θ.ord.ToType) : Set θ.ord.ToType := tripleFirstSupport (q i)
  have hsupp_lt (i : θ.ord.ToType) : #(supp i) < ρ :=
    (Cardinal.mk_image_le.trans ((Cardinal.mk_univ.le.trans (tripleSupport_card_le hκ θ.ord (q i))))).trans_lt
      (Order.lt_succ _)
  let C (cut : θ.ord.ToType) := A × ((levyTriplePSet κ cut.toOrd.val).Type → A)
  let code (cut : θ.ord.ToType) (i : θ.ord.ToType) : C cut :=
    ((q i).value, fun idx =>
      (q i).value ⊓ (check ((levyTriplePSet κ cut.toOrd.val).Func idx) ∈ᴮ name (q i)))
  have hc_lt (cut : θ.ord.ToType) : #(C cut) < θ := by
    let T_cut := (levyTriplePSet κ cut.toOrd.val).Type
    have hA_lt : #A < θ := hA_le.trans_lt h2κ_lt
    have hT_lt : #T_cut < θ := by
      change Cardinal.mk (((PSet.ordinalMk cut.toOrd.val).Type × (PSet.ordinalMk κ.ord).Type) ×
        (PSet.ordinalMk cut.toOrd.val).Type) < θ
      simp only [Cardinal.mk_prod, Cardinal.lift_id, PSet.ordinalMk_type, Cardinal.mk_toType, Cardinal.card_ord]
      exact Cardinal.mul_lt_of_lt hθ.aleph0_lt.le
        (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le (Cardinal.lt_ord.mp (toOrd_lt cut)) hk)
        (Cardinal.lt_ord.mp (toOrd_lt cut))
    have hpow : #(T_cut → A) < θ := by
      let gr (b : T_cut → A) : Set (T_cut × A) := {t | b t.1 = t.2}
      have hinj : Function.Injective gr := fun b c eq =>
        _root_.funext fun x => (eq ▸ (show (x, b x) ∈ gr b from rfl) : (x, b x) ∈ gr c).symm
      apply (Cardinal.mk_le_of_injective hinj).trans_lt
      rw [Cardinal.mk_set, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
      exact hθ.isStrongPrelimit (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hT_lt hA_lt)
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hA_lt hpow
  obtain ⟨a, b, hab, cut, hcode_eq, hsupp_sub⟩ :=
    Erdos1172Shioya.LevyProduct.exists_pair_agree_on_common_support
      hθ.isRegular hρ_reg hρ_lt supp hsupp_lt code hc_lt
  have hv_eq : (q a).value = (q b).value := congrArg Prod.fst hcode_eq
  have hbits_eq := congrArg Prod.snd hcode_eq
  let v := (q a).value
  have hqa_mem : v ≤ name (q a) ∈ᴮ internalLevyPoset κ θ.ord := name_mem (q a)
  have hqb_mem : v ≤ name (q b) ∈ᴮ internalLevyPoset κ θ.ord := hv_eq.le.trans (name_mem (q b))
  obtain ⟨hqa_cc, hqa_bd⟩ := mem_internalLevyCollapse.mp hqa_mem
  obtain ⟨hqb_cc, hqb_bd⟩ := mem_internalLevyCollapse.mp hqb_mem
  obtain ⟨hqa_sub, hqa_fn, hqa_cnt⟩ := countableCollapse_mem.mp hqa_cc
  obtain ⟨hqb_sub, hqb_fn, hqb_cnt⟩ := countableCollapse_mem.mp hqb_cc
  have hu_sub : v ≤ binary_union (name (q a)) (name (q b)) ⊆ᴮ
      prod (prod (ordinalCarrier θ.ord) (ordinalCarrier κ.ord)) (ordinalCarrier θ.ord) :=
    binary_union_subset hqa_sub hqb_sub
  have hu_cnt : v ≤ injects_into (binary_union (name (q a)) (name (q b))) omega :=
    ErdosFusionActiveHistory.binary_union_countable hqa_cnt hqb_cnt
  have hu_bd : v ≤ levyAllBounded (ordinalCarrier κ.ord) (ordinalCarrier θ.ord)
      (binary_union (name (q a)) (name (q b))) := by
    refine allIn_intro fun hd z hz => ?_
    have hor : _ ≤ (z ∈ᴮ name (q a)) ⊔ (z ∈ᴮ name (q b)) := hz.trans_eq (mem_binary_union _ _ z)
    apply (le_inf le_rfl hor).trans
    rw [inf_sup_left]
    exact sup_le (allIn_elim ((inf_le_left.trans hd).trans hqa_bd) inf_le_right)
      (allIn_elim ((inf_le_left.trans hd).trans hqb_bd) inf_le_right)
  let P_θ := levyTriplePSet κ θ.ord
  have hprod_θ : (⊤ : A) ≤ prod (prod (ordinalCarrier θ.ord) (ordinalCarrier κ.ord))
      (ordinalCarrier θ.ord) =ᴮ check P_θ :=
    prod_ordinalCarrier_eq_check_levyTriplePSet θ.ord
  have hqa_P : v ≤ name (q a) ⊆ᴮ check P_θ :=
    subset_trans' hqa_sub (subset_of_eq (le_top.trans hprod_θ))
  have hqb_P : v ≤ name (q b) ⊆ᴮ check P_θ :=
    subset_trans' hqb_sub (subset_of_eq (le_top.trans hprod_θ))
  have hcut_agree : v ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier cut.toOrd.val) (name (q a)) =ᴮ
      restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier cut.toOrd.val) (name (q b)) := by
    let P_cut := levyTriplePSet κ cut.toOrd.val
    have hprod_cut : (⊤ : A) ≤ prod (prod (ordinalCarrier cut.toOrd.val) (ordinalCarrier κ.ord))
        (ordinalCarrier cut.toOrd.val) =ᴮ check P_cut :=
      prod_ordinalCarrier_eq_check_levyTriplePSet cut.toOrd.val
    have hsub_P (g : bSet A) : (⊤ : A) ≤ restrictLevy (ordinalCarrier κ.ord)
        (ordinalCarrier cut.toOrd.val) g ⊆ᴮ check P_cut := by
      refine subset_trans' ?_ (subset_of_eq hprod_cut)
      rw [subset_unfold']
      refine le_iInf fun z => projection_imp.mpr fun _ _ hz =>
        levyBoundPred_mem_prod (check_Ord (PSet.Ord_mk _)) (mem_restrictLevy_iff.mp hz).2
    have hrow (idx : P_cut.Type) :
        v ⊓ (check (P_cut.Func idx) ∈ᴮ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier cut.toOrd.val) (name (q a))) =
        v ⊓ (check (P_cut.Func idx) ∈ᴮ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier cut.toOrd.val) (name (q b))) := by
      rcases idx with ⟨⟨i_ξ, i_η⟩, i_y⟩
      have hchk_eq : (⊤ : A) ≤ check (P_cut.Func ((i_ξ, i_η), i_y)) =ᴮ
          pair (pair (check ((PSet.ordinalMk cut.toOrd.val).Func i_ξ))
            (check ((PSet.ordinalMk κ.ord).Func i_η)))
            (check ((PSet.ordinalMk cut.toOrd.val).Func i_y)) :=
        check_levyTriplePSet_func cut.toOrd.val ((i_ξ, i_η), i_y)
      have h1 := congrFun hbits_eq ((i_ξ, i_η), i_y)
      dsimp only [code] at h1
      have hiff (g : bSet A) (hg : v ≤ g ∈ᴮ internalLevyPoset κ θ.ord) :
          v ⊓ (check (P_cut.Func ((i_ξ, i_η), i_y)) ∈ᴮ
            restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier cut.toOrd.val) g) =
          v ⊓ (check (P_cut.Func ((i_ξ, i_η), i_y)) ∈ᴮ g) := by
        apply le_antisymm
        · exact inf_le_inf_left v
            (mem_of_mem_subset (le_top.trans (restrictLevy_subset _ _ _)) le_rfl)
        · refine le_inf inf_le_left (mem_restrictLevy_iff.mpr ⟨inf_le_right, ?_⟩)
          have hbd_θ : v ⊓ _ ≤ levyBoundPred (ordinalCarrier κ.ord) (ordinalCarrier θ.ord)
              (check (P_cut.Func ((i_ξ, i_η), i_y))) :=
            allIn_elim (inf_le_left.trans (mem_internalLevyCollapse.mp hg).2) inf_le_right
          exact levyBoundPred_of_first_mem (le_top.trans hchk_eq) hbd_θ
            (le_iSup_of_le (check ((PSet.ordinalMk cut.toOrd.val).Func i_ξ))
              (le_inf (check_mem (PSet.func_mem _ i_ξ))
                (le_iSup_of_le (check ((PSet.ordinalMk κ.ord).Func i_η))
                  (le_inf (check_mem (PSet.func_mem _ i_η)) bv_refl))))
      rw [hiff (name (q a)) hqa_mem, hiff (name (q b)) hqb_mem]
      change (q a).value ⊓ _ = (q a).value ⊓ _
      rw [h1, hv_eq]
    have rep (Y : bSet A) (sub : (⊤ : A) ≤ Y ⊆ᴮ check P_cut) :
        v ≤ Y =ᴮ ErdosCheckedIndicator.checkedIndicator P_cut (fun k => v ⊓ (check (P_cut.Func k) ∈ᴮ Y)) := by
      have h0 : v ≤ Y =ᴮ ErdosCheckedIndicator.checkedIndicator P_cut (fun k => check (P_cut.Func k) ∈ᴮ Y) := by
        rw [ErdosCheckedIndicator.checkedIndicator_membership_eq]
        exact eq_membership_indicator_of_subset (le_top.trans sub)
      refine bv_trans h0 (subset_ext
        (ErdosCheckedIndicator.checkedIndicator_subset_of_coefficients _ fun _ => le_inf inf_le_left inf_le_right)
        (ErdosCheckedIndicator.checkedIndicator_subset_of_coefficients _ fun _ => inf_le_right.trans inf_le_right))
    have hra := rep _ (hsub_P (name (q a)))
    simp_rw [hrow] at hra
    exact bv_trans hra (bv_symm (rep _ (hsub_P (name (q b)))))
  have hu_fn : v ≤ is_func (binary_union (name (q a)) (name (q b))) := by
    refine le_iInf fun a₁ => le_iInf fun a₂ => le_iInf fun y₁ => le_iInf fun y₂ => ?_
    rw [← deduction, ← deduction]
    let Δ := (v ⊓ (pair a₁ y₁ ∈ᴮ binary_union (name (q a)) (name (q b)) ⊓
      pair a₂ y₂ ∈ᴮ binary_union (name (q a)) (name (q b)))) ⊓ (a₁ =ᴮ a₂)
    have hΔ_v : Δ ≤ v := inf_le_left.trans inf_le_left
    have ha₁₂ : Δ ≤ a₁ =ᴮ a₂ := inf_le_right
    have hm₁ : Δ ≤ (pair a₁ y₁ ∈ᴮ name (q a)) ⊔ (pair a₁ y₁ ∈ᴮ name (q b)) :=
      (inf_le_left.trans (inf_le_right.trans inf_le_left)).trans_eq (mem_binary_union _ _ _)
    have hm₂ : Δ ≤ (pair a₂ y₂ ∈ᴮ name (q a)) ⊔ (pair a₂ y₂ ∈ᴮ name (q b)) :=
      (inf_le_left.trans (inf_le_right.trans inf_le_right)).trans_eq (mem_binary_union _ _ _)
    have hcut_ba : v ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier cut.toOrd.val) (name (q b)) ⊆ᴮ
        name (q a) :=
      subset_trans' (bSet.subset_of_eq (bv_symm hcut_agree)) (le_top.trans (restrictLevy_subset _ _ _))
    have hcut_ab : v ≤ restrictLevy (ordinalCarrier κ.ord) (ordinalCarrier cut.toOrd.val) (name (q a)) ⊆ᴮ
        name (q b) :=
      subset_trans' (bSet.subset_of_eq hcut_agree) (le_top.trans (restrictLevy_subset _ _ _))
    apply (le_inf le_rfl hm₁).trans
    rw [inf_sup_left]
    apply sup_le
    · apply (le_inf le_rfl (inf_le_left.trans hm₂)).trans
      rw [inf_sup_left]
      apply sup_le
      · exact eq_of_is_func_of_eq (((inf_le_left.trans inf_le_left).trans hΔ_v).trans hqa_fn)
          ((inf_le_left.trans inf_le_left).trans ha₁₂) (inf_le_left.trans inf_le_right) inf_le_right
      · exact strictCC_cross_case (q a) (q b) cut rfl hv_eq hqa_P hqb_P hqb_bd hqa_fn
          hcut_ba hsupp_sub
          ((inf_le_left.trans inf_le_left).trans hΔ_v) (inf_le_left.trans inf_le_right)
          inf_le_right ((inf_le_left.trans inf_le_left).trans ha₁₂)
    · apply (le_inf le_rfl (inf_le_left.trans hm₂)).trans
      rw [inf_sup_left]
      apply sup_le
      · exact strictCC_cross_case (q b) (q a) cut hv_eq rfl hqb_P hqa_P hqa_bd hqb_fn
          hcut_ab (fun _ hx => hsupp_sub ⟨hx.2, hx.1⟩)
          ((inf_le_left.trans inf_le_left).trans hΔ_v) (inf_le_left.trans inf_le_right)
          inf_le_right ((inf_le_left.trans inf_le_left).trans ha₁₂)
      · exact eq_of_is_func_of_eq (((inf_le_left.trans inf_le_left).trans hΔ_v).trans hqb_fn)
          ((inf_le_left.trans inf_le_left).trans ha₁₂) (inf_le_left.trans inf_le_right) inf_le_right
  have hu_mem : v ≤ binary_union (name (q a)) (name (q b)) ∈ᴮ internalLevyPoset κ θ.ord :=
    mem_internalLevyCollapse.mpr ⟨countableCollapse_mem.mpr ⟨hu_sub, hu_fn, hu_cnt⟩, hu_bd⟩
  obtain ⟨r, hrv, hreq⟩ := exists_canonical_refinement (q a).nonzero hu_mem
  have hr_qa : r ≤ q a :=
    ⟨hrv, subset_trans' (le_top.trans subset_binary_union_left) (bSet.subset_of_eq hreq)⟩
  have hr_qb : r ≤ q b :=
    ⟨hrv.trans hv_eq.le, subset_trans' (le_top.trans subset_binary_union_right) (bSet.subset_of_eq hreq)⟩
  have hr_both : condition r ≤ w (emb a) ⊓ w (emb b) :=
    le_inf ((condition_mono hr_qa).trans (hq₀ (emb a))) ((condition_mono hr_qb).trans (hq₀ (emb b)))
  exact condition_ne_bot r
    (le_bot_iff.mp (hr_both.trans_eq (hdisj (emb a) (emb b) (fun he => hab.ne (emb.injective he)))))

end AnonymousStages

end Erdos1172AnonymousInternalLevy
