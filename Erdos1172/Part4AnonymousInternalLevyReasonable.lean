/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4AnonymousInternalLevyGCH
public import Erdos1172.Part4ShioyaPreparationAuxiliarySquare
public import Erdos1172.Part4LevyMatchingRegularPowers
public import Erdos1172.Part4LevyMatchingAnonymousLift

@[expose] public section

/-! # Reasonable collapsing-stage decomposition of the ambient internal Lévy collapse

Over `AuxiliaryAmbient κ = JointForcing (Erdos1172LevyCohen.Algebra κ) κ.ord.ToType`,
`AmbientInternalLevyStage κ α` is `Algebra (mapNames (auxiliaryInclusion κ) (internalLevyPoset κ α))`
and `AmbientInternalLevy κ θ := AmbientInternalLevyStage κ θ.ord`.

This module establishes:
1. Commutation with `anonymousSmallAuxiliaryWithCollapse κ hκ` (`internalLevyStageAuxIso`),
2. Functorial injective stage embeddings (`ambientStageStepHom`),
3. `DenseStageUnion`, `StrictCC (AmbientInternalLevy κ θ) θ`, and `RegularCollapsingStages`, and
4. The Stage-1 bounded-ultrapower anonymous lift (`exists_ambient_stageOne_lift`) and
   `ambientInternalLevy_theta_eq_omegaOne`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Flypitch Ordinal
open Cardinal Filter bSet Lattice ErdosOmegaTwo ErdosNameTransport ErdosPartialInjection
open Erdos1172LevyCohen Erdos1172CompleteSubalgebra Erdos1172BooleanNameIteration
open Erdos1172BooleanFactor Erdos1172PosetProjection Erdos1172PosetCompletion Erdos1172PositiveBoolean
open Erdos1172GroundUltrapower Erdos1172BooleanUltrapower Erdos1172LevyCollapse
open Erdos1172LevyCollapse.Matching bSet.ErdosShioyaInternal

universe u

namespace Erdos1172AnonymousInternalLevy

section AmbientStages
variable (κ : Cardinal.{u})

/-- Stage `α` of the internal Lévy collapse transported over `AuxiliaryAmbient κ`. -/
abbrev AmbientInternalLevyStage (α : Ordinal.{u}) : Type u :=
  Erdos1172BooleanNameIteration.Algebra (mapNames (auxiliaryInclusion κ) (internalLevyPoset κ α))

/-- Full ambient internal Lévy collapse `AmbientInternalLevy κ θ`. -/
def AmbientInternalLevy (θ : Cardinal.{u}) : Type u :=
  AmbientInternalLevyStage κ θ.ord

theorem empty_mem_mapped_internalLevyPoset (α : Ordinal.{u}) :
    (⊤ : AuxiliaryAmbient κ) ≤
      mapNames (auxiliaryInclusion κ) (∅ : bSet (anonymousAlgebra κ)) ∈ᴮ
        mapNames (auxiliaryInclusion κ) (internalLevyPoset κ α) := by
  rw [← map_mem, ← TopHomClass.map_top (auxiliaryInclusion κ)]
  exact OrderHomClass.mono _ (empty_mem_internalLevyCollapse _ _)

instance ambientInternalLevyConditionNonempty (α : Ordinal.{u}) :
    Nonempty (Condition (mapNames (auxiliaryInclusion κ) (internalLevyPoset κ α))) :=
  condition_nonempty_of_mem (empty_mem_mapped_internalLevyPoset κ α)

instance ambientInternalLevyStageNCBA (α : Ordinal.{u}) :
    NontrivialCompleteBooleanAlgebra (AmbientInternalLevyStage κ α) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

instance ambientInternalLevyNCBA (θ : Cardinal.{u}) :
    NontrivialCompleteBooleanAlgebra (AmbientInternalLevy κ θ) :=
  ambientInternalLevyStageNCBA κ θ.ord

/-- Canonical source embedding `Erdos1172LevyCohen.Algebra κ → AmbientInternalLevy κ θ`. -/
def ambientLevySourceHom (θ : Cardinal.{u}) :
    CompleteLatticeHom (Erdos1172LevyCohen.Algebra κ) (AmbientInternalLevy κ θ) :=
  (sourceHom (mapNames (auxiliaryInclusion κ) (internalLevyPoset κ θ.ord))).comp
    (jointSourceHom κ.ord.ToType)

theorem ambientLevySourceHom_injective (θ : Cardinal.{u}) (hκ : κ.IsInaccessible) :
    Function.Injective (ambientLevySourceHom κ θ) := by
  have : Nonempty κ.ord.ToType := Cardinal.mk_ne_zero_iff.mp
    ((Cardinal.mk_ord_toType κ).trans_ne (Cardinal.aleph0_pos.trans_le hκ.aleph0_lt.le).ne')
  exact (sourceHom_injective _ (empty_mem_mapped_internalLevyPoset κ θ.ord)).comp
    jointSourceHom_injective

variable {κ}

theorem auxForcing_nonempty (hκ : κ.IsInaccessible) :
    Nonempty (Condition (anonymousSmallAuxiliaryWithCollapse κ hκ).forcing) :=
  condition_nonempty_of_mem (auxiliary_member (anonymousSmallAuxiliaryWithCollapse κ hκ) hκ).choose_spec

theorem mappedAuxForcing_nonempty (hκ : κ.IsInaccessible) (α : Ordinal.{u}) :
    Nonempty (Condition (mapNames (sourceHom (internalLevyPoset κ α))
      (anonymousSmallAuxiliaryWithCollapse κ hκ).forcing)) := by
  obtain ⟨q, hq⟩ := auxiliary_member (anonymousSmallAuxiliaryWithCollapse κ hκ) hκ
  have hm : (⊤ : InternalLevyStage κ α) ≤
      mapNames (sourceHom (internalLevyPoset κ α)) q ∈ᴮ
        mapNames (sourceHom (internalLevyPoset κ α)) (anonymousSmallAuxiliaryWithCollapse κ hκ).forcing := by
    rw [← map_mem, ← TopHomClass.map_top (sourceHom (internalLevyPoset κ α))]
    exact OrderHomClass.mono _ hq
  exact condition_nonempty_of_mem hm

/-- `InternalLevyStage κ α` followed by the `κ`-enumerated auxiliary side forcing is isomorphic
to `AmbientInternalLevyStage κ α`. -/
def internalLevyStageAuxIso (hκ : κ.IsInaccessible) (α : Ordinal.{u}) :
    Erdos1172BooleanNameIteration.Algebra
      (mapNames (sourceHom (internalLevyPoset κ α))
        (anonymousSmallAuxiliaryWithCollapse κ hκ).forcing) ≃o
      AmbientInternalLevyStage κ α := by
  let T := anonymousSmallAuxiliaryWithCollapse κ hκ
  letI := auxForcing_nonempty hκ
  letI : NontrivialCompleteBooleanAlgebra (Erdos1172BooleanNameIteration.Algebra T.forcing) :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  have over (a : anonymousAlgebra κ) :
      T.completion.symm (sourceHom T.forcing a) = auxiliaryInclusion κ a :=
    T.completion.symm_apply_eq.mpr (T.over_source a).symm
  exact (Joint.commutation (internalLevyPoset κ α) T.forcing).trans
    (Joint.changeCompletion (sourceHom T.forcing) (auxiliaryInclusion κ)
      T.completion.symm over (internalLevyPoset κ α))

theorem internalLevyStageAuxIso_levy (hκ : κ.IsInaccessible) (α : Ordinal.{u})
    (b : InternalLevyStage κ α) :
    internalLevyStageAuxIso hκ α
      (sourceHom (mapNames (sourceHom (internalLevyPoset κ α))
        (anonymousSmallAuxiliaryWithCollapse κ hκ).forcing) b) =
      BaseChange.hom (auxiliaryInclusion κ) (internalLevyPoset κ α) b := by
  let _ := auxForcing_nonempty hκ
  let _ : NontrivialCompleteBooleanAlgebra
      (Erdos1172BooleanNameIteration.Algebra (anonymousSmallAuxiliaryWithCollapse κ hκ).forcing) :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  unfold internalLevyStageAuxIso
  rw [OrderIso.trans_apply, Joint.commutation_left, Joint.changeCompletion_factor]

/-- `PairCondition` presentation of `AmbientInternalLevyStage κ α`. -/
def ambientStagePairIso (hκ : κ.IsInaccessible) (α : Ordinal.{u}) :
    AmbientInternalLevyStage κ α ≃o
      Completion (Joint.PairCondition (internalLevyPoset κ α)
        (anonymousSmallAuxiliaryWithCollapse κ hκ).forcing) :=
  (internalLevyStageAuxIso hκ α).symm.trans
    (Joint.stackIso (internalLevyPoset κ α) (anonymousSmallAuxiliaryWithCollapse κ hκ).forcing)

section AbstractScalarChange
variable {A₀ B₁ B₂ B₃ : Type u} [NontrivialCompleteBooleanAlgebra A₀]
  [NontrivialCompleteBooleanAlgebra B₁] [NontrivialCompleteBooleanAlgebra B₂]
  [NontrivialCompleteBooleanAlgebra B₃]

private theorem injective_completeHom_le_iff' {X Y : Type u}
    [CompleteBooleanAlgebra X] [CompleteBooleanAlgebra Y]
    (f : CompleteLatticeHom X Y) (hinj : Function.Injective f) {x y : X} :
    f x ≤ f y ↔ x ≤ y := by
  constructor
  · intro hle
    have hbot : f (x ⊓ yᶜ) = ⊥ := by
      rw [← sInf_pair, map_sInf, Set.image_pair, sInf_pair, map_compl']
      exact le_bot_iff.mp ((inf_le_inf_right (f y)ᶜ hle).trans inf_compl_eq_bot.le)
    have hx0 : x ⊓ yᶜ = ⊥ := hinj (hbot.trans (BotHomClass.map_bot f).symm)
    exact disjoint_compl_right_iff.mp (disjoint_iff.mpr hx0)
  · exact fun h => OrderHomClass.mono f h

def lowerAux {s₁ : CompleteLatticeHom A₀ B₁} {s₂ : CompleteLatticeHom A₀ B₂}
    (f : CompleteLatticeHom B₁ B₂) (hf : ∀ a, f (s₁ a) = s₂ a) :
    (V : bSet A₀) → Condition (mapNames s₂ V) → Condition (mapNames s₁ V)
  | .mk _ _ w, p =>
    ⟨lowerProjection f p.value,
     lowerProjection_ne_bot f p.nonzero,
     p.index,
     lowerProjection_le f (p.valid.trans_eq (hf (w p.index)).symm)⟩

theorem lowerAux_le_iff {s₁ : CompleteLatticeHom A₀ B₁} {s₂ : CompleteLatticeHom A₀ B₂}
    (f : CompleteLatticeHom B₁ B₂) (hf : ∀ a, f (s₁ a) = s₂ a) (V : bSet A₀)
    (p q : Condition (mapNames s₂ V)) :
    p ≤ q ↔ p.value ≤ q.value ∧ lowerAux f hf V p ≤ lowerAux f hf V q := by
  cases V with
  | mk K X w =>
    let ip : K := p.index
    let iq : K := q.index
    have hsub_eq :
        f (mapNames s₁ (X iq) ⊆ᴮ mapNames s₁ (X ip)) =
          (mapNames s₂ (X iq) ⊆ᴮ mapNames s₂ (X ip)) := by
      rw [← map_subset, ← map_subset, hf]
    constructor
    · rintro ⟨hv, hsub⟩
      refine ⟨hv, lowerProjection_mono f hv, ?_⟩
      change lowerProjection f p.value ≤ mapNames s₁ (X iq) ⊆ᴮ mapNames s₁ (X ip)
      exact (lowerProjection_le_iff f).mpr ((show p.value ≤ mapNames s₂ (X iq) ⊆ᴮ mapNames s₂ (X ip) from hsub).trans_eq hsub_eq.symm)
    · rintro ⟨hv, _, hsub⟩
      refine ⟨hv, ?_⟩
      change p.value ≤ mapNames s₂ (X iq) ⊆ᴮ mapNames s₂ (X ip)
      rw [← hsub_eq]
      exact (lowerProjection_le_iff f).mp hsub

def lowerAuxOrderHom {s₁ : CompleteLatticeHom A₀ B₁} {s₂ : CompleteLatticeHom A₀ B₂}
    (f : CompleteLatticeHom B₁ B₂) (hf : ∀ a, f (s₁ a) = s₂ a) (V : bSet A₀) :
    Condition (mapNames s₂ V) →o Condition (mapNames s₁ V) :=
  ⟨lowerAux f hf V, fun p q hpq => ((lowerAux_le_iff f hf V p q).mp hpq).2⟩

theorem lowerAux_exactLifts {s₁ : CompleteLatticeHom A₀ B₁} {s₂ : CompleteLatticeHom A₀ B₂}
    (f : CompleteLatticeHom B₁ B₂) (hf : ∀ a, f (s₁ a) = s₂ a) (V : bSet A₀) :
    ExactLifts (lowerAuxOrderHom f hf V) := by
  cases V with
  | mk K X w =>
    intro p q hqp
    let b := p.value ⊓ f q.value
    have pos : b ≠ ⊥ := fun h0 =>
      inf_image_lowerProjection_ne_bot f q.nonzero hqp.1 ((inf_comm _ _).trans h0)
    have hval : b ≤ s₂ (w q.index) :=
      inf_le_right.trans ((OrderHomClass.mono f q.valid).trans_eq (hf (w q.index)))
    let r : Condition (mapNames s₂ (.mk K X w)) := ⟨b, pos, q.index, hval⟩
    have heqn : lowerAuxOrderHom f hf (.mk K X w) r = q := by
      rcases q with ⟨v, hv, idx, hvalid⟩
      have hh : lowerProjection f (p.value ⊓ f v) = v :=
        (lowerProjection_inf_image f p.value v).trans (inf_eq_right.mpr hqp.1)
      change (⟨lowerProjection f (p.value ⊓ f v), _, idx, _⟩ : Condition (mapNames s₁ (.mk K X w))) =
        (⟨v, hv, idx, hvalid⟩ : Condition (mapNames s₁ (.mk K X w)))
      congr 1
    exact ⟨r, (lowerAux_le_iff f hf (.mk K X w) r p).mpr ⟨inf_le_left, heqn.le.trans hqp⟩, heqn⟩

private theorem lowerAux_surjective {s₁ : CompleteLatticeHom A₀ B₁} {s₂ : CompleteLatticeHom A₀ B₂}
    (f : CompleteLatticeHom B₁ B₂) (hinj : Function.Injective f)
    (hf : ∀ a, f (s₁ a) = s₂ a) (V : bSet A₀) :
    Function.Surjective (lowerAuxOrderHom f hf V) := by
  cases V with
  | mk K X w =>
    rintro ⟨v, hv, idx, hvalid⟩
    have pos : f v ≠ ⊥ := fun h0 => hv (hinj (h0.trans (BotHomClass.map_bot f).symm))
    have hval : f v ≤ s₂ (w idx) := (OrderHomClass.mono f hvalid).trans_eq (hf (w idx))
    let r : Condition (mapNames s₂ (.mk K X w)) := ⟨f v, pos, idx, hval⟩
    refine ⟨r, ?_⟩
    have heq : lowerProjection f (f v) = v :=
      hinj (le_antisymm
        (OrderHomClass.mono f (lowerProjection_le f le_rfl))
        (le_image_lowerProjection f (f v)))
    change (⟨lowerProjection f (f v), _, idx, _⟩ : Condition (mapNames s₁ (.mk K X w))) =
      (⟨v, hv, idx, hvalid⟩ : Condition (mapNames s₁ (.mk K X w)))
    congr 1

private theorem lowerAux_comp
    {s₁ : CompleteLatticeHom A₀ B₁} {s₂ : CompleteLatticeHom A₀ B₂} {s₃ : CompleteLatticeHom A₀ B₃}
    (f₁ : CompleteLatticeHom B₁ B₂) (hf₁ : ∀ a, f₁ (s₁ a) = s₂ a)
    (f₂ : CompleteLatticeHom B₂ B₃) (hf₂ : ∀ a, f₂ (s₂ a) = s₃ a)
    (f₁₂ : CompleteLatticeHom B₁ B₃) (hf₁₂ : ∀ a, f₁₂ (s₁ a) = s₃ a)
    (hcomp : ∀ x, f₂ (f₁ x) = f₁₂ x) (V : bSet A₀)
    (p : Condition (mapNames s₃ V)) :
    lowerAux f₁ hf₁ V (lowerAux f₂ hf₂ V p) = lowerAux f₁₂ hf₁₂ V p := by
  cases V with
  | mk K X w =>
    rcases p with ⟨c, hc, idx, hvalid⟩
    have hlp : lowerProjection f₁ (lowerProjection f₂ c) = lowerProjection f₁₂ c := by
      apply le_antisymm
      · exact (lowerProjection_le_iff f₁).mpr
          ((lowerProjection_le_iff f₂).mpr
            ((le_image_lowerProjection f₁₂ c).trans_eq (hcomp _).symm))
      · exact (lowerProjection_le_iff f₁₂).mpr
          ((le_image_lowerProjection f₂ c).trans
            ((OrderHomClass.mono f₂ (le_image_lowerProjection f₁ _)).trans_eq (hcomp _)))
    change (⟨lowerProjection f₁ (lowerProjection f₂ c), _, idx, _⟩ : Condition (mapNames s₁ (.mk K X w))) =
      (⟨lowerProjection f₁₂ c, _, idx, _⟩ : Condition (mapNames s₁ (.mk K X w)))
    congr 1

def auxStageHomGen {s₁ : CompleteLatticeHom A₀ B₁} {s₂ : CompleteLatticeHom A₀ B₂}
    (f : CompleteLatticeHom B₁ B₂) (hf : ∀ a, f (s₁ a) = s₂ a) (V : bSet A₀) :
    CompleteLatticeHom
      (Erdos1172BooleanNameIteration.Algebra (mapNames s₁ V))
      (Erdos1172BooleanNameIteration.Algebra (mapNames s₂ V)) :=
  completionHom (lowerAuxOrderHom f hf V) (lowerAux_exactLifts f hf V)

private theorem auxStageHomGen_injective {s₁ : CompleteLatticeHom A₀ B₁} {s₂ : CompleteLatticeHom A₀ B₂}
    (f : CompleteLatticeHom B₁ B₂) (hinj : Function.Injective f)
    (hf : ∀ a, f (s₁ a) = s₂ a) (V : bSet A₀) :
    Function.Injective (auxStageHomGen f hf V) :=
  completionHom_injective (lowerAuxOrderHom f hf V) (lowerAux_exactLifts f hf V)
    (lowerAux_surjective f hinj hf V)

private theorem auxStageHomGen_comp
    {s₁ : CompleteLatticeHom A₀ B₁} {s₂ : CompleteLatticeHom A₀ B₂} {s₃ : CompleteLatticeHom A₀ B₃}
    (f₁ : CompleteLatticeHom B₁ B₂) (hf₁ : ∀ a, f₁ (s₁ a) = s₂ a)
    (f₂ : CompleteLatticeHom B₂ B₃) (hf₂ : ∀ a, f₂ (s₂ a) = s₃ a)
    (f₁₂ : CompleteLatticeHom B₁ B₃) (hf₁₂ : ∀ a, f₁₂ (s₁ a) = s₃ a)
    (hcomp : ∀ x, f₂ (f₁ x) = f₁₂ x) (V : bSet A₀)
    (x : Erdos1172BooleanNameIteration.Algebra (mapNames s₁ V)) :
    auxStageHomGen f₂ hf₂ V (auxStageHomGen f₁ hf₁ V x) = auxStageHomGen f₁₂ hf₁₂ V x := by
  unfold auxStageHomGen
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  rw [← condition_le_iff, ← condition_le_iff, condition_le_completionHom_iff,
    condition_le_completionHom_iff, condition_le_completionHom_iff]
  change condition (lowerAux f₁ hf₁ V (lowerAux f₂ hf₂ V p)) ≤ x ↔
    condition (lowerAux f₁₂ hf₁₂ V p) ≤ x
  rw [lowerAux_comp f₁ hf₁ f₂ hf₂ f₁₂ hf₁₂ hcomp V p]

private theorem exists_auxStageHomGen_condition_le
    {s₁ : CompleteLatticeHom A₀ B₁} {s₂ : CompleteLatticeHom A₀ B₂}
    (f : CompleteLatticeHom B₁ B₂) (hinj : Function.Injective f)
    (hf : ∀ a, f (s₁ a) = s₂ a) (V : bSet A₀)
    (p : Condition (mapNames s₂ V)) (x₀ : B₁) (hx₀_pos : x₀ ≠ ⊥) (hx₀_le : f x₀ ≤ p.value) :
    ∃ p₀ : Condition (mapNames s₁ V), auxStageHomGen f hf V (condition p₀) ≤ condition p := by
  cases V with
  | mk K X w =>
    let ip : K := p.index
    have hvalid_i : x₀ ≤ s₁ (w ip) := by
      apply (injective_completeHom_le_iff' f hinj).mp
      rw [hf]
      exact hx₀_le.trans p.valid
    let p₀ : Condition (mapNames s₁ (.mk K X w)) := ⟨x₀, hx₀_pos, ip, hvalid_i⟩
    refine ⟨p₀, ?_⟩
    intro r hr
    apply (mem_condition_iff p r).mpr
    intro v hvr
    have hv_in : v ∈ (auxStageHomGen f hf (.mk K X w) (condition p₀)).val :=
      condition_le_iff.mp ((condition_mono hvr).trans (condition_le_iff.mpr hr))
    have hv_cone : condition (lowerAuxOrderHom f hf (.mk K X w) v) ≤ condition p₀ :=
      (condition_le_completionHom_iff _ _ v (condition p₀)).mp (condition_le_iff.mpr hv_in)
    obtain ⟨s, hs_v, hs_p₀⟩ := (mem_condition_iff p₀ _).mp (condition_le_iff.mp hv_cone) _ le_rfl
    obtain ⟨t, htv, hts⟩ := lowerAux_exactLifts f hf (.mk K X w) v s hs_v
    have ht_p₀ : lowerAuxOrderHom f hf (.mk K X w) t ≤ p₀ := hts.le.trans hs_p₀
    let it : K := t.index
    have ht_val : t.value ≤ p.value := ((lowerProjection_le_iff f).mp ht_p₀.1).trans hx₀_le
    have hsub_eq :
        f (mapNames s₁ (X ip) ⊆ᴮ mapNames s₁ (X it)) =
          (mapNames s₂ (X ip) ⊆ᴮ mapNames s₂ (X it)) := by
      rw [← map_subset, ← map_subset, hf]
    have ht_sub : t.value ≤ mapNames s₂ (X ip) ⊆ᴮ mapNames s₂ (X it) := by
      rw [← hsub_eq]
      exact (lowerProjection_le_iff f).mp ht_p₀.2
    exact ⟨t, htv, ⟨ht_val, ht_sub⟩⟩

end AbstractScalarChange

abbrev auxStageHom {α β : Ordinal.{u}} (h : α ≤ β) (V : bSet (anonymousAlgebra κ)) :
    CompleteLatticeHom
      (Erdos1172BooleanNameIteration.Algebra (mapNames (sourceHom (internalLevyPoset κ α)) V))
      (Erdos1172BooleanNameIteration.Algebra (mapNames (sourceHom (internalLevyPoset κ β)) V)) :=
  auxStageHomGen (stageStepHom (κ := κ) h) (stageStepHom_sourceHom h) V

private theorem auxStageHom_injective {α β : Ordinal.{u}} (h : α ≤ β) (V : bSet (anonymousAlgebra κ)) :
    Function.Injective (auxStageHom h V) :=
  auxStageHomGen_injective (stageStepHom (κ := κ) h) (stageStepHom_injective h)
    (stageStepHom_sourceHom h) V

private theorem auxStageHom_comp {α β γ : Ordinal.{u}} (h₁ : α ≤ β) (h₂ : β ≤ γ)
    (V : bSet (anonymousAlgebra κ))
    (x : Erdos1172BooleanNameIteration.Algebra (mapNames (sourceHom (internalLevyPoset κ α)) V)) :
    auxStageHom h₂ V (auxStageHom h₁ V x) = auxStageHom (h₁.trans h₂) V x :=
  auxStageHomGen_comp (stageStepHom h₁) (stageStepHom_sourceHom h₁)
    (stageStepHom h₂) (stageStepHom_sourceHom h₂)
    (stageStepHom (h₁.trans h₂)) (stageStepHom_sourceHom (h₁.trans h₂))
    (stageStepHom_comp h₁ h₂) V x

/-- Injective complete stage embedding `AmbientInternalLevyStage κ α → AmbientInternalLevyStage κ β`. -/
def ambientStageStepHom (hκ : κ.IsInaccessible) {α β : Ordinal.{u}} (h : α ≤ β) :
    CompleteLatticeHom (AmbientInternalLevyStage κ α) (AmbientInternalLevyStage κ β) := by
  let T := anonymousSmallAuxiliaryWithCollapse κ hκ
  letI := mappedAuxForcing_nonempty hκ α
  letI := mappedAuxForcing_nonempty hκ β
  letI : NontrivialCompleteBooleanAlgebra
      (Erdos1172BooleanNameIteration.Algebra (mapNames (sourceHom (internalLevyPoset κ α)) T.forcing)) :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  letI : NontrivialCompleteBooleanAlgebra
      (Erdos1172BooleanNameIteration.Algebra (mapNames (sourceHom (internalLevyPoset κ β)) T.forcing)) :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  exact (CompleteLatticeHom.OrderIso.toCompleteLatticeHom (internalLevyStageAuxIso hκ β)).comp
    ((auxStageHom h T.forcing).comp
      (CompleteLatticeHom.OrderIso.toCompleteLatticeHom (internalLevyStageAuxIso hκ α).symm))

theorem ambientStageStepHom_injective (hκ : κ.IsInaccessible) {α β : Ordinal.{u}} (h : α ≤ β) :
    Function.Injective (ambientStageStepHom hκ h) :=
  (internalLevyStageAuxIso hκ β).injective.comp
    ((auxStageHom_injective h _).comp (internalLevyStageAuxIso hκ α).symm.injective)

theorem ambientStageStepHom_comp (hκ : κ.IsInaccessible) {α β γ : Ordinal.{u}}
    (h₁ : α ≤ β) (h₂ : β ≤ γ) (x : AmbientInternalLevyStage κ α) :
    ambientStageStepHom hκ h₂ (ambientStageStepHom hκ h₁ x) =
      ambientStageStepHom hκ (h₁.trans h₂) x := by
  let V := (anonymousSmallAuxiliaryWithCollapse κ hκ).forcing
  change internalLevyStageAuxIso hκ γ
    (auxStageHom h₂ V ((internalLevyStageAuxIso hκ β).symm
      (internalLevyStageAuxIso hκ β (auxStageHom h₁ V ((internalLevyStageAuxIso hκ α).symm x))))) =
    internalLevyStageAuxIso hκ γ (auxStageHom (h₁.trans h₂) V ((internalLevyStageAuxIso hκ α).symm x))
  rw [OrderIso.symm_apply_apply, auxStageHom_comp]

/-- `DenseStageUnion` for `AmbientInternalLevy κ θ`. -/
theorem ambientInternalLevy_denseStageUnion {θ : Cardinal.{u}}
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible) :
    DenseStageUnion (fun i : θ.ord.ToType =>
      ambientStageStepHom (κ := κ) hκ (Order.succ_le_of_lt (toOrd_lt i))) := by
  let T := anonymousSmallAuxiliaryWithCollapse κ hκ
  have := mappedAuxForcing_nonempty hκ θ.ord
  let _ : NontrivialCompleteBooleanAlgebra
      (Erdos1172BooleanNameIteration.Algebra (mapNames (sourceHom (internalLevyPoset κ θ.ord)) T.forcing)) :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  intro z hz
  have hz' : (internalLevyStageAuxIso hκ θ.ord).symm z ≠ ⊥ := fun h0 =>
    hz ((internalLevyStageAuxIso hκ θ.ord).symm.injective
      (h0.trans (internalLevyStageAuxIso hκ θ.ord).symm.map_bot.symm))
  obtain ⟨p, hpz⟩ := exists_condition_le hz'
  obtain ⟨i, x₀, hx₀_ne, hx₀_le⟩ := internalLevy_denseStageUnion hk hκ hθ p.value p.nonzero
  let h_i := Order.succ_le_of_lt (toOrd_lt i)
  have hx₀_pos : x₀ ≠ ⊥ := fun h0 => hx₀_ne ((congrArg (stageStepHom h_i) h0).trans (BotHomClass.map_bot _))
  have := mappedAuxForcing_nonempty hκ (Order.succ i.toOrd.val)
  let _ : NontrivialCompleteBooleanAlgebra
      (Erdos1172BooleanNameIteration.Algebra
        (mapNames (sourceHom (internalLevyPoset κ (Order.succ i.toOrd.val))) T.forcing)) :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  obtain ⟨p₀, hp₀_le⟩ := exists_auxStageHomGen_condition_le
    (stageStepHom h_i) (stageStepHom_injective h_i) (stageStepHom_sourceHom h_i)
    T.forcing p x₀ hx₀_pos hx₀_le
  let y := internalLevyStageAuxIso hκ (Order.succ i.toOrd.val) (condition p₀)
  have hy_ne : ambientStageStepHom hκ h_i y ≠ ⊥ := by
    intro h0
    have hy0 : y = ⊥ := ambientStageStepHom_injective hκ h_i
      (h0.trans (BotHomClass.map_bot (ambientStageStepHom hκ h_i)).symm)
    have hc0 : condition p₀ = ⊥ :=
      (internalLevyStageAuxIso hκ (Order.succ i.toOrd.val)).injective
        (hy0.trans (OrderIso.map_bot _).symm)
    exact condition_ne_bot p₀ hc0
  have hy_le : ambientStageStepHom hκ h_i y ≤ z := by
    change internalLevyStageAuxIso hκ θ.ord
      (auxStageHom h_i T.forcing ((internalLevyStageAuxIso hκ _).symm
        (internalLevyStageAuxIso hκ _ (condition p₀)))) ≤ z
    rw [OrderIso.symm_apply_apply]
    exact (internalLevyStageAuxIso hκ θ.ord).le_symm_apply.mp (hp₀_le.trans hpz)
  exact ⟨i, y, hy_ne, hy_le⟩

private theorem strict_upper_bound_theta {θ : Cardinal.{u}} (hθ : θ.IsRegular)
    {D : Type u} (hD : #D < θ) (f : D → θ.ord.ToType) :
    ∃ b : θ.ord.ToType, ∀ d : D, f d < b := by
  by_contra! h
  have hc : IsCofinal (Set.range f) := fun a => by
    obtain ⟨d, hd⟩ := h a
    exact ⟨f d, Set.mem_range_self d, hd⟩
  have hh := Order.cof_le hc
  rw [Ordinal.cof_toType, hθ.cof_ord] at hh
  exact hD.not_ge (hh.trans Cardinal.mk_range_le)

/-- `StrictCC (AmbientInternalLevy κ θ) θ` reduced directly to `internalLevy_strictCC`
by regular-cardinal pigeonhole on the `≤ 2^κ`-sized `Condition T.forcing` factor. -/
theorem ambientInternalLevy_strictCC {θ : Cardinal.{u}}
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible) :
    StrictCC (AmbientInternalLevy κ θ) θ := by
  classical
  let A := anonymousAlgebra κ
  let T := anonymousSmallAuxiliaryWithCollapse κ hκ
  have hA_le : #A ≤ (2 : Cardinal.{u}) ^ κ :=
    (Cardinal.mk_le_of_injective (inclusion_injective A)).trans (completion_cardinal_le_two_power κ hκ)
  have h2κ_lt : (2 : Cardinal.{u}) ^ κ < θ := hθ.isStrongPrelimit hk
  have hT_cond_le : #(Condition T.forcing) ≤ (2 : Cardinal.{u}) ^ κ := by
    let codeT (s : Condition T.forcing) : A × T.forcing.type := (s.value, s.index)
    have hinjT : Function.Injective codeT := by
      rintro ⟨v₁, _, i₁, _⟩ ⟨v₂, _, i₂, _⟩ h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rfl
    apply (Cardinal.mk_le_of_injective hinjT).trans
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact (mul_le_mul' hA_le (T.size.trans (Cardinal.cantor κ).le)).trans_eq
      (Cardinal.mul_eq_self (hκ.aleph0_lt.le.trans (Cardinal.cantor κ).le))
  have hT_cond_lt : #(Condition T.forcing) < θ := hT_cond_le.trans_lt h2κ_lt
  let iso := ambientStagePairIso hκ θ.ord
  intro J w hpos hdisj
  by_contra! hJ
  obtain ⟨emb⟩ : Nonempty (θ.ord.ToType ↪ J) := (Cardinal.mk_ord_toType θ).le.trans hJ
  have hpos_iso (i : θ.ord.ToType) : iso (w (emb i)) ≠ ⊥ :=
    fun h0 => hpos (emb i) (iso.injective (h0.trans iso.map_bot.symm))
  choose p hp using fun i : θ.ord.ToType => exists_condition_le (hpos_iso i)
  have hex_fiber : ∃ s₀ : Condition T.forcing, θ ≤ #{i : θ.ord.ToType // (p i).second = s₀} := by
    by_contra! hsmall
    choose b hb using fun s : Condition T.forcing =>
      strict_upper_bound_theta hθ.isRegular (hsmall s) (fun x : {i : θ.ord.ToType // (p i).second = s} => x.val)
    obtain ⟨b_top, hb_top⟩ := strict_upper_bound_theta hθ.isRegular hT_cond_lt b
    have hlt1 : b_top < b (p b_top).second := hb (p b_top).second ⟨b_top, rfl⟩
    exact (hlt1.trans (hb_top (p b_top).second)).false
  obtain ⟨s₀, hs₀⟩ := hex_fiber
  let J₀ := {i : θ.ord.ToType // (p i).second = s₀}
  have hdisj₀ (x y : J₀) (hne : x ≠ y) :
      condition (p x.val).first ⊓ condition (p y.val).first = ⊥ := by
    by_contra hmeet
    obtain ⟨r, hrx, hry⟩ := (condition_inf_ne_bot_iff (p x.val).first (p y.val).first).mp hmeet
    have hrv : r.value ≤ s₀.value := by
      rw [← x.property, ← (p x.val).common]
      exact hrx.1
    let s' := shrink s₀ r.value r.nonzero hrv
    have hs'_s₀ : s' ≤ s₀ := shrink_le s₀ r.value r.nonzero hrv
    let z : Joint.PairCondition (internalLevyPoset κ θ.ord) T.forcing := ⟨r, s', rfl⟩
    have hz_x : z ≤ p x.val := ⟨hrx, by change s' ≤ (p x.val).second; rw [x.property]; exact hs'_s₀⟩
    have hz_y : z ≤ p y.val := ⟨hry, by change s' ≤ (p y.val).second; rw [y.property]; exact hs'_s₀⟩
    have hz_both : condition z ≤ iso (w (emb x.val)) ⊓ iso (w (emb y.val)) :=
      le_inf ((condition_mono hz_x).trans (hp x.val)) ((condition_mono hz_y).trans (hp y.val))
    have hxy_ne : emb x.val ≠ emb y.val := fun he => hne (Subtype.ext (emb.injective he))
    have hiso_bot : iso (w (emb x.val)) ⊓ iso (w (emb y.val)) = ⊥ := by
      have h1 := hdisj (emb x.val) (emb y.val) hxy_ne
      apply le_antisymm ?_ bot_le
      apply iso.symm.le_iff_le.mp
      have h2 : iso.symm (iso (w (emb x.val)) ⊓ iso (w (emb y.val))) ≤
          w (emb x.val) ⊓ w (emb y.val) :=
        le_inf ((iso.symm.monotone inf_le_left).trans_eq (iso.symm_apply_apply _))
          ((iso.symm.monotone inf_le_right).trans_eq (iso.symm_apply_apply _))
      exact (h2.trans_eq h1).trans iso.symm.map_bot.symm.le
    exact condition_ne_bot z (le_bot_iff.mp (hz_both.trans_eq hiso_bot))
  exact hs₀.not_gt (internalLevy_strictCC hk hκ hθ
    (fun x : J₀ => condition (p x.val).first) (fun _ => condition_ne_bot _) hdisj₀)

private theorem succ_ord_toType_le {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    #(Order.succ μ.ord).ToType ≤ μ := by
  classical
  let f (x : (Order.succ μ.ord).ToType) : Option μ.ord.ToType :=
    if h : x.toOrd.val < μ.ord then some (Ordinal.ToType.mk ⟨x.toOrd.val, h⟩) else none
  have hinj : Function.Injective f := by
    intro x₁ x₂ heq
    have hx₁_le : x₁.toOrd.val ≤ μ.ord := Order.lt_succ_iff.mp (toOrd_lt x₁)
    have hx₂_le : x₂.toOrd.val ≤ μ.ord := Order.lt_succ_iff.mp (toOrd_lt x₂)
    by_cases h₁ : x₁.toOrd.val < μ.ord <;> by_cases h₂ : x₂.toOrd.val < μ.ord <;>
      simp only [f, dif_pos, dif_neg, h₁, h₂, not_false_eq_true] at heq
    · have hsub := Ordinal.ToType.mk.injective (Option.some.inj heq)
      have hval : x₁.toOrd.val = x₂.toOrd.val := congrArg (fun z : Set.Iio μ.ord => z.val) hsub
      exact Ordinal.ToType.mk.symm.injective (Subtype.ext hval)
    · cases heq
    · cases heq
    · have e₁ : x₁.toOrd.val = μ.ord := le_antisymm hx₁_le (le_of_not_gt h₁)
      have e₂ : x₂.toOrd.val = μ.ord := le_antisymm hx₂_le (le_of_not_gt h₂)
      exact Ordinal.ToType.mk.symm.injective (Subtype.ext (e₁.trans e₂.symm))
  apply (Cardinal.mk_le_of_injective hinj).trans
  rw [Cardinal.mk_option, Cardinal.mk_ord_toType]
  exact (Cardinal.add_one_eq hμ).le

private theorem ambientStage_collapses_kappa (hκ : κ.IsInaccessible) (α : Ordinal.{u}) :
    (⊤ : AmbientInternalLevyStage κ α) ≤ injects_into (check (PSet.ordinalMk κ.ord)) omega := by
  let A_pset := PSet.mk κ.ord.ToType (fun i => PSet.ordinalMk i.toOrd.val)
  have : Nonempty A_pset.Type := Cardinal.mk_ne_zero_iff.mp (show #κ.ord.ToType ≠ 0 from
    (Cardinal.mk_ord_toType κ).trans_ne (Cardinal.aleph0_pos.trans_le hκ.aleph0_lt.le).ne')
  have h₀ : (⊤ : Erdos1172Collapse.Algebra κ.ord.ToType) ≤ larger_than omega (check A_pset) :=
    larger_than_of_surjects_onto (Erdos1172Collapse.forces_countable_surjection A_pset)
  let hom : CompleteLatticeHom (Erdos1172Collapse.Algebra κ.ord.ToType) (AmbientInternalLevyStage κ α) :=
    (sourceHom (mapNames (auxiliaryInclusion κ) (internalLevyPoset κ α))).comp
      (jointCollapseHom (Erdos1172LevyCohen.Algebra κ))
  have h : (⊤ : AmbientInternalLevyStage κ α) ≤
      (mapNames hom omega).larger_than (mapNames hom (check A_pset)) :=
    (TopHomClass.map_top hom).symm.le.trans (map_larger_than_of hom h₀)
  rw [show mapNames hom omega = omega from map_check hom _, map_check] at h
  have hinj : (⊤ : AmbientInternalLevyStage κ α) ≤ injects_into (check A_pset) omega :=
    ErdosCHHartogs.injects_into_of_larger_than_ordinal Ord_omega h
  rw [PSet.ordinalMk_eq_def κ.ord]
  exact hinj

private theorem stack_eq_of_cond_and_index {U V : bSet (anonymousAlgebra κ)} [Nonempty (Condition U)]
    {z₁ z₂ : Joint.PairCondition U V}
    (h1 : condition z₁.first = condition z₂.first)
    (h2 : z₁.second.index = z₂.second.index) :
    Joint.stack U V z₁ = Joint.stack U V z₂ := by
  let _ : NontrivialCompleteBooleanAlgebra (Erdos1172BooleanNameIteration.Algebra U) :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  cases V with
  | mk K Y w =>
    rcases z₁ with ⟨f₁, ⟨v₁, hv₁, i₁, hi₁⟩, c₁⟩
    rcases z₂ with ⟨f₂, ⟨v₂, hv₂, i₂, hi₂⟩, c₂⟩
    dsimp only at h1 h2
    subst h2
    change (⟨condition f₁, _, i₁, _⟩ : Condition (mapNames (sourceHom U) (.mk K Y w))) =
      (⟨condition f₂, _, i₁, _⟩ : Condition (mapNames (sourceHom U) (.mk K Y w)))
    congr 1

/-- `RegularCollapsingStages` for `(fun i : θ.ord.ToType => AmbientInternalLevyStage κ (Order.succ i.toOrd.val))`
without any ground GCH hypothesis, via `tripleSupport_card_le` + `condition_eq_of_tripleSupport_eq`
+ `cofinal_regular_power_closed` at exponent `2^κ < θ`. -/
theorem ambientInternalLevy_regularCollapsingStages {θ : Cardinal.{u}}
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible) :
    RegularCollapsingStages (fun i : θ.ord.ToType =>
      AmbientInternalLevyStage κ (Order.succ i.toOrd.val)) := by
  classical
  let A := anonymousAlgebra κ
  let T := anonymousSmallAuxiliaryWithCollapse κ hκ
  let lam := (2 : Cardinal.{u}) ^ κ
  have hlam_lt : lam < θ := hθ.isStrongPrelimit hk
  have hA_le : #A ≤ lam :=
    (Cardinal.mk_le_of_injective (inclusion_injective A)).trans (completion_cardinal_le_two_power κ hκ)
  intro ξ hξ
  obtain ⟨μ, hm, high, hu, reg, hpow⟩ := cofinal_regular_power_closed hlam_lt hθ ξ hξ
  have hξ_lt : ξ < μ := (le_max_left ξ lam).trans_lt high
  have hlam_μ : lam ≤ μ := ((le_max_right ξ lam).trans_lt high).le
  have hκ_μ : κ ≤ μ := (Cardinal.cantor κ).le.trans hlam_μ
  let i := cardinalStage hm
  have hi_ord : i.toOrd.val = μ.ord := cardinalStage_rank hm
  let α := Order.succ i.toOrd.val
  have hα_eq : α = Order.succ μ.ord := congrArg Order.succ hi_ord
  have := mappedAuxForcing_nonempty hκ α
  let _ : NontrivialCompleteBooleanAlgebra
      (Erdos1172BooleanNameIteration.Algebra (mapNames (sourceHom (internalLevyPoset κ α)) T.forcing)) :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  -- Collapse of `μ` at stage `i`: `μ → κ` in `InternalLevyStage κ α` composed with `κ → ω` in `Col(ω, κ)`.
  have hcol_μ : (⊤ : AmbientInternalLevyStage κ α) ≤
      injects_into (check (PSet.ordinalMk μ.ord)) omega := by
    have hlt_α : μ.ord < α := hα_eq.symm ▸ Order.lt_succ μ.ord
    have hμ_κ_src : (⊤ : InternalLevyStage κ α) ≤
        injects_into (check (PSet.ordinalMk μ.ord)) (check (PSet.ordinalMk κ.ord)) :=
      internalLevyStage_collapses_below hκ hlt_α
    let liftLevy := BaseChange.hom (auxiliaryInclusion κ) (internalLevyPoset κ α)
    have ho : liftLevy ⊤ ≤ Ord (mapNames liftLevy (check (PSet.ordinalMk κ.ord))) := by
      rw [map_check]
      exact check_Ord (PSet.Ord_mk κ.ord)
    have hμ_κ := map_injects_into_of_ordinal liftLevy hμ_κ_src ho
    rw [TopHomClass.map_top, map_check, map_check] at hμ_κ
    exact injects_into_trans hμ_κ (ambientStage_collapses_kappa hκ α)
  -- `≤ μ` dense family in `Positive (AmbientInternalLevyStage κ α)` via `stack` + `tripleSupport`.
  let P_α := levyTriplePSet κ α
  let X := P_α.Type × A
  have hα_card : #α.ToType ≤ μ := hα_eq ▸ succ_ord_toType_le hu.le
  have hP_le : #P_α.Type ≤ μ := by
    change Cardinal.mk (((PSet.ordinalMk α).Type × (PSet.ordinalMk κ.ord).Type) ×
      (PSet.ordinalMk α).Type) ≤ μ
    simp only [Cardinal.mk_prod, Cardinal.lift_id, PSet.ordinalMk_type, Cardinal.mk_ord_toType]
    exact ((mul_le_mul' (mul_le_mul' hα_card hκ_μ) hα_card).trans
      (mul_le_mul' (Cardinal.mul_eq_self hu.le).le le_rfl)).trans_eq (Cardinal.mul_eq_self hu.le)
  have hX_le : #X ≤ μ := by
    change #(P_α.Type × A) ≤ μ
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact (mul_le_mul' hP_le (hA_le.trans hlam_μ)).trans_eq (Cardinal.mul_eq_self hu.le)
  have hshort_le : #{s : Set X // #s ≤ lam} ≤ μ := short_subsets_le hu.le hpow hX_le
  let StackSet : Set (Condition (mapNames (sourceHom (internalLevyPoset κ α)) T.forcing)) :=
    Set.range (Joint.stack (internalLevyPoset κ α) T.forcing)
  have hStack_le : #StackSet ≤ μ := by
    let Code := (A × {s : Set X // #s ≤ lam}) × T.forcing.type
    have hCode_le : #Code ≤ μ := by
      rw [Cardinal.mk_prod, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.lift_id, Cardinal.lift_id]
      exact ((mul_le_mul' (mul_le_mul' (hA_le.trans hlam_μ) hshort_le)
        (T.size.trans hκ_μ)).trans
        (mul_le_mul' (Cardinal.mul_eq_self hu.le).le le_rfl)).trans_eq (Cardinal.mul_eq_self hu.le)
    let pickPair (c : StackSet) : Joint.PairCondition (internalLevyPoset κ α) T.forcing :=
      c.property.choose
    have hpick (c : StackSet) : Joint.stack (internalLevyPoset κ α) T.forcing (pickPair c) = c.val :=
      c.property.choose_spec
    let encode (c : StackSet) : Code :=
      (((pickPair c).first.value,
        ⟨tripleSupport α (pickPair c).first, tripleSupport_card_le hκ α (pickPair c).first⟩),
       (pickPair c).second.index)
    have henc_inj : Function.Injective encode := by
      intro c₁ c₂ heq
      obtain ⟨h1, hidx⟩ := Prod.mk.inj heq
      obtain ⟨hval, hsupp_sub⟩ := Prod.mk.inj h1
      have hsupp : tripleSupport α (pickPair c₁).first = tripleSupport α (pickPair c₂).first :=
        congrArg Subtype.val hsupp_sub
      have hcond : condition (pickPair c₁).first = condition (pickPair c₂).first :=
        condition_eq_of_tripleSupport_eq hval hsupp
      apply Subtype.ext
      rw [← hpick c₁, ← hpick c₂]
      exact stack_eq_of_cond_and_index hcond hidx
    exact (Cardinal.mk_le_of_injective henc_inj).trans hCode_le
  have hStack_nonempty : Nonempty StackSet := by
    obtain ⟨q_T, hq_T⟩ := auxiliary_member T hκ
    obtain ⟨p_U, _, _⟩ := exists_canonical_refinement (top_ne_bot : (⊤ : A) ≠ ⊥)
      (empty_mem_internalLevyCollapse (ordinalCarrier κ.ord) (ordinalCarrier α))
    obtain ⟨s_T, hs_v, _⟩ := exists_canonical_refinement p_U.nonzero (le_top.trans hq_T)
    let z₀ : Joint.PairCondition (internalLevyPoset κ α) T.forcing :=
      ⟨shrink p_U s_T.value s_T.nonzero hs_v, s_T, rfl⟩
    exact ⟨⟨Joint.stack (internalLevyPoset κ α) T.forcing z₀, ⟨z₀, rfl⟩⟩⟩
  obtain ⟨e_stack⟩ : Nonempty (StackSet ↪ μ.ord.ToType) :=
    hStack_le.trans_eq (Cardinal.mk_ord_toType μ).symm
  let iso_α := internalLevyStageAuxIso hκ α
  let d_fam (k : μ.ord.ToType) : Positive (AmbientInternalLevyStage κ α) :=
    let c := Function.invFun e_stack k
    ⟨iso_α (condition c.val),
     fun h0 => condition_ne_bot c.val (iso_α.injective (h0.trans iso_α.map_bot.symm))⟩
  have hd_dense (a : Positive (AmbientInternalLevyStage κ α)) : ∃ k, d_fam k ≤ a := by
    have ha' : iso_α.symm a.val ≠ ⊥ :=
      fun h0 => a.property (iso_α.symm.injective (h0.trans iso_α.symm.map_bot.symm))
    obtain ⟨t, ht⟩ := exists_condition_le ha'
    obtain ⟨z, hz⟩ := Joint.stack_dense (internalLevyPoset κ α) T.forcing t
    let c : StackSet := ⟨Joint.stack (internalLevyPoset κ α) T.forcing z, ⟨z, rfl⟩⟩
    refine ⟨e_stack c, ?_⟩
    change iso_α (condition (Function.invFun e_stack (e_stack c)).val) ≤ a.val
    rw [Function.leftInverse_invFun e_stack.injective c]
    exact iso_α.le_symm_apply.mp ((condition_mono hz).trans ht)
  exact ⟨μ, hm, hξ_lt, hu, reg, ⟨d_fam, hd_dense⟩, hcol_μ⟩

/-- In `AmbientInternalLevy κ θ`, `check θ =ᴮ omegaOne`. -/
theorem ambientInternalLevy_theta_eq_omegaOne {θ : Cardinal.{u}}
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible) :
    (⊤ : AmbientInternalLevy κ θ) ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaOne :=
  source_height_eq_omegaOne
    (fun i : θ.ord.ToType => ambientStageStepHom (κ := κ) hκ (Order.succ_le_of_lt (toOrd_lt i)))
    hθ (ambientInternalLevy_regularCollapsingStages hk hκ hθ)
    (ambientInternalLevy_strictCC hk hκ hθ)

/-- Instantiated Stage-1 bounded-ultrapower anonymous lift over `R := AmbientInternalLevy κ θ`. -/
theorem exists_ambient_stageOne_lift {I : Type u} {θ : Cardinal.{u}}
    (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
    [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    let R := AmbientInternalLevy κ θ
    let u := ambientLevySourceHom κ θ
    ∃ (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne (sourceCohenMaster u))
      (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))
        (LocalizedSourceCohen R (sourceCohenMaster u) hm₀)),
      (∀ b : anonymousAlgebra κ,
        j₀ (value U (fun _ => b)) = localizedFirstStageHom hm₀ (u (inclusion (anonymousAlgebra κ) b))) ∧
      ((⊤ : LocalizedSourceCohen R (sourceCohenMaster u) hm₀) ≤
        mapNames j₀ (Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) =ᴮ
          mapNames (LocalizedBelow.restrict (masterPositive (sourceCohenMaster u) hm₀))
            (Erdos1172CohenIteration.subsetName (B := R) (PSet.ordinalMk θ.ord))) := by
  have hb_hom {i j : θ.ord.ToType} (hij : i ≤ j) :
      Order.succ i.toOrd.val ≤ Order.succ j.toOrd.val :=
    Order.succ_le_succ (Ordinal.ToType.mk.symm.monotone hij)
  exact exists_stageOne_anonymous_lift U a hk hκ hθ hf hn ht (ambientLevySourceHom κ θ)
    (fun {_ _} hij => ambientStageStepHom hκ (hb_hom hij))
    (fun i => ambientStageStepHom hκ (Order.succ_le_of_lt (toOrd_lt i)))
    (ambientInternalLevy_strictCC hk hκ hθ)
    (ambientInternalLevy_denseStageUnion hk hκ hθ)
    (ambientInternalLevy_regularCollapsingStages hk hκ hθ)
    (fun i => ambientStageStepHom_injective hκ (Order.succ_le_of_lt (toOrd_lt i)))
    (fun {_ _} hij x => ambientStageStepHom_comp hκ (hb_hom hij) _ x)
    (ambientLevySourceHom_injective κ θ hκ)

def ambientLevyTopHom (θ : Cardinal.{u}) :
    CompleteLatticeHom (InternalLevyAlgebra κ θ) (AmbientInternalLevy κ θ) :=
  BaseChange.hom (auxiliaryInclusion κ) (internalLevyPoset κ θ.ord)

private theorem ambientLevyTopHom_injective (θ : Cardinal.{u}) :
    Function.Injective (ambientLevyTopHom (κ := κ) θ) :=
  BaseChange.hom_injective (auxiliaryInclusion κ) (internalLevyPoset κ θ.ord)
    (auxiliaryInclusion_injective κ)

private theorem ambientLevyTopHom_sourceHom (θ : Cardinal.{u}) (b : anonymousAlgebra κ) :
    ambientLevyTopHom (κ := κ) θ (sourceHom (internalLevyPoset κ θ.ord) b) =
      ambientLevySourceHom κ θ (inclusion (anonymousAlgebra κ) b) :=
  BaseChange.commutes (auxiliaryInclusion κ) (internalLevyPoset κ θ.ord) b

private theorem internalLevyStageAuxIso_topHom {θ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    (b : InternalLevyAlgebra κ θ) :
    (internalLevyStageAuxIso hκ θ.ord
      (sourceHom (mapNames (sourceHom (internalLevyPoset κ θ.ord))
        (anonymousSmallAuxiliaryWithCollapse κ hκ).forcing) b) : AmbientInternalLevy κ θ) =
      ambientLevyTopHom (κ := κ) θ b :=
  internalLevyStageAuxIso_levy hκ θ.ord b

attribute [irreducible] ambientLevyTopHom

/-- Canonical embedding `InternalLevyStage κ α → AmbientInternalLevy κ θ` for `α ≤ θ.ord`. -/
def ambientLevyStageHom {θ : Cardinal.{u}} {α : Ordinal.{u}} (h : α ≤ θ.ord) :
    CompleteLatticeHom (InternalLevyStage κ α) (AmbientInternalLevy κ θ) :=
  (ambientLevyTopHom (κ := κ) θ).comp (stageStepHom h)

theorem ambientLevyStageHom_injective {θ : Cardinal.{u}} {α : Ordinal.{u}} (h : α ≤ θ.ord) :
    Function.Injective (ambientLevyStageHom (κ := κ) (θ := θ) h) := by
  intro x y hxy
  exact stageStepHom_injective h (ambientLevyTopHom_injective θ hxy)

theorem ambientLevyStageHom_comp {θ : Cardinal.{u}} {α α' : Ordinal.{u}}
    (h₁ : α ≤ α') (h₂ : α' ≤ θ.ord) (x : InternalLevyStage κ α) :
    ambientLevyStageHom h₂ (stageStepHom h₁ x) = ambientLevyStageHom (h₁.trans h₂) x := by
  simp only [ambientLevyStageHom, CompleteLatticeHom.comp_apply, stageStepHom_comp]

theorem ambientLevyStageHom_sourceHom {θ : Cardinal.{u}} {α : Ordinal.{u}}
    (h : α ≤ θ.ord) (b : anonymousAlgebra κ) :
    ambientLevyStageHom h (sourceHom (internalLevyPoset κ α) b) =
      ambientLevySourceHom κ θ (inclusion (anonymousAlgebra κ) b) := by
  simp only [ambientLevyStageHom, CompleteLatticeHom.comp_apply, stageStepHom_sourceHom,
    ambientLevyTopHom_sourceHom]

theorem stageStepHom_refl (α : Ordinal.{u}) (x : InternalLevyStage κ α) :
    stageStepHom (κ := κ) (le_rfl : α ≤ α) x = x :=
  stageStepHom_injective le_rfl (stageStepHom_comp le_rfl le_rfl x)

/-- Relative density `≤ κ` of `AmbientInternalLevy κ θ` over `InternalLevyAlgebra κ θ` via
`anonymousSmallAuxiliaryWithCollapse κ hκ`. -/
theorem ambientLevy_exists_denseOver {θ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    ∃ d : κ.ord.ToType → AmbientInternalLevy κ θ,
      Erdos1172SeedQuotient.denseOver (ambientLevyStageHom (κ := κ) (θ := θ) le_rfl) d := by
  let T := anonymousSmallAuxiliaryWithCollapse κ hκ
  let _ := auxForcing_nonempty hκ
  let _ : NontrivialCompleteBooleanAlgebra (Erdos1172BooleanNameIteration.Algebra T.forcing) :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  let _ := mappedAuxForcing_nonempty hκ θ.ord
  let _ : NontrivialCompleteBooleanAlgebra
      (Erdos1172BooleanNameIteration.Algebra (mapNames (sourceHom (internalLevyPoset κ θ.ord)) T.forcing)) :=
    { toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra, bot_lt_top := bot_lt_top }
  obtain ⟨d₀, hd₀⟩ := exists_denseOver_of_surjection T.forcing
    (T.enumerates.trans inf_le_left) (T.enumerates.trans inf_le_right)
  have hd₁ := BaseChange.denseOver (sourceHom (internalLevyPoset κ θ.ord)) T.forcing d₀ hd₀
  let iso := internalLevyStageAuxIso hκ θ.ord
  have hiso_inf (x y : Erdos1172BooleanNameIteration.Algebra
      (mapNames (sourceHom (internalLevyPoset κ θ.ord)) T.forcing)) :
      iso (x ⊓ y) = iso x ⊓ iso y :=
    le_antisymm (le_inf (iso.monotone inf_le_left) (iso.monotone inf_le_right))
      (iso.symm_apply_le.mp (le_inf
        ((iso.symm.monotone inf_le_left).trans_eq (iso.symm_apply_apply x))
        ((iso.symm.monotone inf_le_right).trans_eq (iso.symm_apply_apply y))))
  let v : (PSet.ordinalMk κ.ord).Type ≃ κ.ord.ToType := Equiv.cast PSet.ordinalMk_type
  let d (i : κ.ord.ToType) : AmbientInternalLevy κ θ :=
    iso (BaseChange.hom (sourceHom (internalLevyPoset κ θ.ord)) T.forcing (d₀ (v.symm i)))
  refine ⟨d, ?_⟩
  intro c hc
  have hc' : iso.symm c ≠ ⊥ := fun h0 => hc (iso.symm.injective (h0.trans iso.symm.map_bot.symm))
  obtain ⟨k, b, hpos, hle⟩ := hd₁ (iso.symm c) hc'
  have hd_vk : d (v k) = iso (BaseChange.hom (sourceHom (internalLevyPoset κ θ.ord)) T.forcing (d₀ k)) :=
    congrArg (fun m => iso (BaseChange.hom (sourceHom (internalLevyPoset κ θ.ord)) T.forcing (d₀ m)))
      (v.symm_apply_apply k)
  have hb_eq : (iso (sourceHom (mapNames (sourceHom (internalLevyPoset κ θ.ord)) T.forcing) b) :
      AmbientInternalLevy κ θ) = ambientLevyStageHom (κ := κ) (θ := θ) le_rfl b :=
    (internalLevyStageAuxIso_topHom hκ b).trans
      ((congrArg (ambientLevyTopHom (κ := κ) θ) (stageStepHom_refl θ.ord b)).symm.trans
        (CompleteLatticeHom.comp_apply _ _ _).symm)
  have himg_eq : (iso (BaseChange.hom (sourceHom (internalLevyPoset κ θ.ord)) T.forcing (d₀ k) ⊓
      sourceHom (mapNames (sourceHom (internalLevyPoset κ θ.ord)) T.forcing) b) : AmbientInternalLevy κ θ) =
      d (v k) ⊓ ambientLevyStageHom (κ := κ) (θ := θ) le_rfl b := by
    have hi : (iso (BaseChange.hom (sourceHom (internalLevyPoset κ θ.ord)) T.forcing (d₀ k) ⊓
        sourceHom (mapNames (sourceHom (internalLevyPoset κ θ.ord)) T.forcing) b) : AmbientInternalLevy κ θ) =
      (iso (BaseChange.hom (sourceHom (internalLevyPoset κ θ.ord)) T.forcing (d₀ k)) : AmbientInternalLevy κ θ) ⊓
        (iso (sourceHom (mapNames (sourceHom (internalLevyPoset κ θ.ord)) T.forcing) b) : AmbientInternalLevy κ θ) :=
      hiso_inf _ _
    exact hi.trans (congrArg₂ (· ⊓ ·) hd_vk.symm hb_eq)
  refine ⟨v k, b, ?_, ?_⟩
  · exact fun h0 => hpos (iso.injective ((himg_eq.trans h0).trans iso.map_bot.symm))
  · exact himg_eq.symm.le.trans ((iso.monotone hle).trans_eq (iso.apply_symm_apply c))

attribute [irreducible] AmbientInternalLevy ambientInternalLevyNCBA ambientLevySourceHom ambientLevyStageHom

end AmbientStages

end Erdos1172AnonymousInternalLevy
