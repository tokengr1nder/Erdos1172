/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OneSuccessorDeepMatrix
public import Erdos1172.Part3TransfiniteArmAPI

@[expose] public section

open Cardinal Ordinal Set Function
open Order

namespace Erdos1172Part3OneSuccessorFullFiberChain

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3CHAsymmetric Erdos1172Part3TransfiniteArmAPI
  Erdos1172Part3OneSuccessorBarrier
  Erdos1172Part3OneSuccessorDeepMatrix

/-- The index type of the full `omegaTwo` chain of red near-target arms. -/
abbrev NearArmIndex : Type 1 := Set.Iio (ω_ 2 : Ordinal.{0})

/-- The canonical copy of the `omegaTwo` initial ordinal inside the arm
index type. -/
noncomputable def nearArmStage (a : W2) : NearArmIndex :=
  ⟨(a : Ordinal), a.toOrd.2⟩

/-- The full failure-fiber obstruction retained by the one-successor
argument.  The same `alephTwo` fiber contains an ordered `omegaTwo`-chain
of red near-target arms, every arm is blue from one fixed earlier center,
and every later point has a blue predecessor in every earlier arm. -/
structure FixedCenterRedNearArmChain
    (red blue : SimpleGraph W2) : Type 1 where
  fiber : Set W2
  center : W2
  arms : NearArmIndex → Set W2
  fiber_card : #fiber = ℵ_ 2
  arm_sub : ∀ i, arms i ⊆ fiber
  arm_red : ∀ i, red.IsClique (arms i)
  arm_type : ∀ i, typeLT (arms i) = RedNearTarget
  center_before : ∀ i, ∀ x ∈ arms i, center < x
  center_blue : ∀ i, ∀ x ∈ arms i, blue.Adj center x
  ordered : ∀ i j, i < j → ∀ x ∈ arms i, ∀ y ∈ arms j, x < y
  cross_blue_failure : ∀ i j, i < j → ∀ y ∈ arms j,
    ∃ x ∈ arms i, blue.Adj x y

/-- The canonical-terminal refinement of the full arm chain.  A blue
`omegaOne + 1` thinning of the terminal spine cannot be extended by a
later terminal.  Its failed extensions freeze one `q` on an
`alephTwo`-sized later fiber, and BHT yields a red near-target arm in that
fiber.  The entire original arm chain and the frozen data are retained. -/
structure BHTConditionalTerminalPrefixObstruction
    (red blue : SimpleGraph W2) : Type 1 where
  chain : FixedCenterRedNearArmChain red blue
  terminal : W2 → W2
  terminal_mem : ∀ a, terminal a ∈ chain.arms (nearArmStage a)
  terminal_max : ∀ a, ∀ x ∈ chain.arms (nearArmStage a), x ≤ terminal a
  terminal_strict : StrictMono terminal
  terminal_range_type : typeLT (Set.range terminal) = ω_ 2
  terminal_center_blue : ∀ a, blue.Adj chain.center (terminal a)
  blueTerminals : Set W2
  blueTerminals_sub : blueTerminals ⊆ Set.range terminal
  blueTerminals_blue : blue.IsClique blueTerminals
  blueTerminals_type : typeLT blueTerminals = ω_ 1 + 1
  blueMaximum : W2
  blueMaximum_mem : blueMaximum ∈ blueTerminals
  blueMaximum_max : ∀ x ∈ blueTerminals, x ≤ blueMaximum
  frozen : W2
  frozen_mem : frozen ∈ blueTerminals
  frozenFiber : Set W2
  frozenFiber_card : #frozenFiber = ℵ_ 2
  frozenFiber_sub : frozenFiber ⊆
    Set.range terminal ∩ Set.Ioi blueMaximum
  frozen_red : ∀ y ∈ frozenFiber, red.Adj frozen y
  finalArm : Set W2
  finalArm_sub : finalArm ⊆ frozenFiber
  finalArm_red : red.IsClique finalArm
  finalArm_type : typeLT finalArm = RedNearTarget
  frozen_before_final : ∀ y ∈ finalArm, frozen < y
  frozen_red_final : ∀ y ∈ finalArm, red.Adj frozen y

/-- Removing a smaller set from an `alephTwo`-sized subset of `W2`
preserves cardinality `alephTwo`. -/
private theorem mk_sdiff_eq_alephTwo
    {s t : Set W2} (hs : #s = ℵ_ 2) (ht : #t < ℵ_ 2) :
    #(s \ t : Set W2) = ℵ_ 2 := by
  apply le_antisymm
  · simpa [hs] using Cardinal.mk_le_mk_of_subset
      (Set.sdiff_subset : s \ t ⊆ s)
  · by_contra h
    have hdiff : #(s \ t : Set W2) < ℵ_ 2 := lt_of_not_ge h
    have hcover : ℵ_ 2 ≤ #(s \ t : Set W2) + #t := by
      simpa [hs] using Cardinal.le_mk_sdiff_add_mk s t
    exact (not_lt_of_ge hcover) <|
      Cardinal.add_lt_of_lt (Cardinal.aleph0_le_aleph 2) hdiff ht

/-- Every tail of an `alephTwo`-sized subset of `W2` still has size
`alephTwo`. -/
theorem mk_inter_Ioi_eq_alephTwo
    {s : Set W2} (hs : #s = ℵ_ 2) (m : W2) :
    #(s ∩ Set.Ioi m : Set W2) = ℵ_ 2 := by
  let _ : Infinite W2 := by
    rw [← Cardinal.aleph0_le_mk_iff]
    simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
    exact Cardinal.aleph0_le_aleph 2
  have hIic : #(Set.Iic m) < ℵ_ 2 := by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using
      Cardinal.mk_Iic_lt m (by simp [W2]) (by
        simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
        exact Cardinal.aleph0_le_aleph 2)
  have hdiff := mk_sdiff_eq_alephTwo hs hIic
  simpa only [Set.sdiff_eq, compl_Iic] using hdiff

/-- BHT supplies a fresh red near-target arm inside the fixed failure
fiber above any family of fewer than `alephTwo` previous points. -/
theorem exists_redNearArm_in_fiber_above_small_family
    (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {fiber : Set W2} (hfiberCard : #fiber = ℵ_ 2)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    {ι : Type} (f : ι → W2) (hι : #ι < ℵ_ 2) :
    ∃ (bound : W2) (arm : Set W2),
      (∀ i, f i < bound) ∧ arm ⊆ fiber ∧ arm ⊆ Set.Ioi bound ∧
      red.IsClique arm ∧ typeLT arm = RedNearTarget := by
  obtain ⟨bound, hbound⟩ :=
    exists_strict_upper_bound_of_mk_lt_alephTwo f hι
  let tail : Set W2 := fiber ∩ Set.Ioi bound
  have htailCard : #tail = ℵ_ 2 :=
    mk_inter_Ioi_eq_alephTwo hfiberCard bound
  have htailType : typeLT tail = ω_ 2 :=
    typeLT_eq_omegaTwo_of_mk_eq htailCard
  obtain ⟨arm, harmSub, harmRed, harmType⟩ |
      ⟨target, _htargetSub, htargetBlue, htargetType⟩ :=
    OrdinalRamsey.on_set_of_type hBHT red blue hcompl tail htailType
  · exact ⟨bound, arm, hbound, harmSub.trans inter_subset_left,
      harmSub.trans inter_subset_right, harmRed, harmType⟩
  · exact (hnoBlue ⟨target, htargetBlue, htargetType⟩).elim

private structure RedNearArmState
    (red : SimpleGraph W2) (fiber : Set W2) where
  arm : Set W2
  arm_sub : arm ⊆ fiber
  arm_red : red.IsClique arm
  arm_type : typeLT arm = RedNearTarget

private structure SuccessorData
    (red : SimpleGraph W2) (fiber : Set W2)
    (state : RedNearArmState red fiber) where
  next : RedNearArmState red fiber
  ordered : ∀ x ∈ state.arm, ∀ y ∈ next.arm, x < y

private theorem successorData_nonempty
    (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {fiber : Set W2} (hfiberCard : #fiber = ℵ_ 2)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (state : RedNearArmState red fiber) :
    Nonempty (SuccessorData red fiber state) := by
  have harmCard : #state.arm = ℵ_ 1 := by
    have hc := congrArg Ordinal.card state.arm_type
    simpa only [Ordinal.card_type, card_redNearTarget] using hc
  have hsmall : #state.arm < ℵ_ 2 := by
    rw [harmCard]
    exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  obtain ⟨bound, next, hbound, hnextSub, hnextTail,
      hnextRed, hnextType⟩ :=
    exists_redNearArm_in_fiber_above_small_family
      hBHT red blue hcompl hfiberCard hnoBlue
        (fun x : state.arm ↦ (x : W2)) hsmall
  refine ⟨{
    next := {
      arm := next
      arm_sub := hnextSub
      arm_red := hnextRed
      arm_type := hnextType }
    ordered := ?_ }⟩
  intro x hx y hy
  exact (hbound ⟨x, hx⟩).trans (hnextTail hy)

private noncomputable def chooseSuccessorData
    (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {fiber : Set W2} (hfiberCard : #fiber = ℵ_ 2)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (state : RedNearArmState red fiber) :
    SuccessorData red fiber state :=
  Classical.choice <|
    successorData_nonempty hBHT red blue hcompl hfiberCard hnoBlue state

private structure LimitData
    (red : SimpleGraph W2) (fiber : Set W2) (o : Ordinal.{0})
    (previous : ∀ o' : Ordinal.{0}, o' < o →
      RedNearArmState red fiber) where
  next : RedNearArmState red fiber
  ordered : ∀ o' (h : o' < o), ∀ x ∈ (previous o' h).arm,
    ∀ y ∈ next.arm, x < y

private theorem limitData_nonempty
    (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {fiber : Set W2} (hfiberCard : #fiber = ℵ_ 2)
    (o : Ordinal.{0}) (ho : o < ω_ 2)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (previous : ∀ o' : Ordinal.{0}, o' < o →
      RedNearArmState red fiber) :
    Nonempty (LimitData red fiber o previous) := by
  let previousSet : Ordinal.{0} → Set W2 := fun j ↦
    if h : j < o then (previous j h).arm else ∅
  let covered : Set W2 := ⋃ j < o, previousSet j
  have hoCardLt : o.card < ℵ_ 2 :=
    Cardinal.lt_omega_iff_card_lt.mp ho
  have halephTwoSucc : (ℵ_ 2 : Cardinal.{0}) = succ (ℵ_ 1) := by
    symm
    simpa only [show (1 : Ordinal.{0}) + 1 = 2 by norm_num] using
      Cardinal.succ_aleph (1 : Ordinal.{0})
  have hoCard : o.card ≤ ℵ_ 1 := by
    rw [halephTwoSucc, lt_succ_iff] at hoCardLt
    exact hoCardLt
  have hpreviousCard (j : Ordinal.{0}) (hj : j < o) :
      #(previousSet j) ≤ ℵ_ 1 := by
    have hcard : #(previous j hj).arm = ℵ_ 1 := by
      have hc := congrArg Ordinal.card (previous j hj).arm_type
      simpa only [Ordinal.card_type, card_redNearTarget] using hc
    simpa only [previousSet, dif_pos hj, hcard] using
      (le_refl (ℵ_ 1 : Cardinal.{0}))
  have hcovered : #covered ≤ ℵ_ 1 := by
    apply Cardinal.mk_biUnion_le_of_le hoCard
      (Cardinal.aleph0_le_aleph 1) previousSet
    exact hpreviousCard
  have hcoveredLt : #covered < ℵ_ 2 :=
    hcovered.trans_lt (Cardinal.aleph_lt_aleph.mpr (by norm_num))
  obtain ⟨bound, next, hbound, hnextSub, hnextTail,
      hnextRed, hnextType⟩ :=
    exists_redNearArm_in_fiber_above_small_family
      hBHT red blue hcompl hfiberCard hnoBlue
        (fun x : covered ↦ (x : W2)) hcoveredLt
  refine ⟨{
    next := {
      arm := next
      arm_sub := hnextSub
      arm_red := hnextRed
      arm_type := hnextType }
    ordered := ?_ }⟩
  intro j hj x hx y hy
  have hxCovered : x ∈ covered := by
    apply Set.mem_iUnion.mpr
    refine ⟨j, Set.mem_iUnion.mpr ⟨hj, ?_⟩⟩
    simpa only [previousSet, dif_pos hj] using hx
  exact (hbound ⟨x, hxCovered⟩).trans (hnextTail hy)

private noncomputable def chooseLimitData
    (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {fiber : Set W2} (hfiberCard : #fiber = ℵ_ 2)
    (o : Ordinal.{0}) (ho : o < ω_ 2)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (previous : ∀ o' : Ordinal.{0}, o' < o →
      RedNearArmState red fiber) :
    LimitData red fiber o previous :=
  Classical.choice <|
    limitData_nonempty hBHT red blue hcompl hfiberCard o ho hnoBlue previous

private noncomputable def buildArmState
    (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {fiber : Set W2} (hfiberCard : #fiber = ℵ_ 2)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (initial : RedNearArmState red fiber) :
    ∀ o : Ordinal.{0}, o < ω_ 2 → RedNearArmState red fiber := fun o ↦
  Ordinal.limitRecOn o
    (fun _ ↦ initial)
    (fun o previous ho ↦
      (chooseSuccessorData hBHT red blue hcompl hfiberCard hnoBlue
        (previous ((lt_add_one o).trans ho))).next)
    (fun o _hoLimit previous ho ↦
      (chooseLimitData hBHT red blue hcompl hfiberCard o ho hnoBlue
        (fun o' h ↦ previous o' h (h.trans ho))).next)

private theorem buildArmState_add_one
    (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {fiber : Set W2} (hfiberCard : #fiber = ℵ_ 2)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (initial : RedNearArmState red fiber)
    (o : Ordinal.{0}) (ho : o + 1 < ω_ 2) :
    buildArmState hBHT red blue hcompl hfiberCard hnoBlue initial
        (o + 1) ho =
      (chooseSuccessorData hBHT red blue hcompl hfiberCard hnoBlue
        (buildArmState hBHT red blue hcompl hfiberCard hnoBlue initial
          o ((lt_add_one o).trans ho))).next := by
  simp only [buildArmState, Ordinal.limitRecOn_add_one]

private theorem buildArmState_limit
    (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {fiber : Set W2} (hfiberCard : #fiber = ℵ_ 2)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (initial : RedNearArmState red fiber)
    (o : Ordinal.{0}) (ho : o < ω_ 2) (hoLimit : IsSuccLimit o) :
    buildArmState hBHT red blue hcompl hfiberCard hnoBlue initial o ho =
      (chooseLimitData hBHT red blue hcompl hfiberCard o ho hnoBlue
        (fun o' h ↦ buildArmState hBHT red blue hcompl hfiberCard
          hnoBlue initial o' (h.trans ho))).next := by
  simp only [buildArmState, Ordinal.limitRecOn_limit o _ _ _ hoLimit]

/-- The fixed `alephTwo` failure fiber of a DoubleFan supports the full
ordered chain of red BHT near-target arms. -/
theorem NearRedOneSuccessorDoubleFan.to_fixedCenterRedNearArmChain
    (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2)
    (hfan : NearRedOneSuccessorDoubleFan red blue)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    Nonempty (FixedCenterRedNearArmChain red blue) := by
  classical
  obtain ⟨base, maximum, center, fiber, _blueArm, redArm,
      _hbaseRed, _hbaseType, _hmaximumMem, hmaximum,
      hcenterMem, _hallTailFailure, hfiberCard, hfiberTail,
      hcenterBlue, _hblueArmSub, _hblueArm, _hblueArmType,
      hredArmSub, hredArm, hredArmType⟩ := hfan
  let initial : RedNearArmState red fiber := {
    arm := redArm
    arm_sub := hredArmSub
    arm_red := hredArm
    arm_type := hredArmType }
  let state : ∀ o : Ordinal.{0}, o < ω_ 2 →
      RedNearArmState red fiber :=
    buildArmState hBHT red blue hcompl hfiberCard hnoBlue initial
  let arms : NearArmIndex → Set W2 := fun i ↦ (state i i.property).arm
  have horderedRaw :
      ∀ (j : Ordinal.{0}) (hj : j < ω_ 2)
        (i : Ordinal.{0}) (hij : i < j),
        ∀ x ∈ (state i (hij.trans hj)).arm,
          ∀ y ∈ (state j hj).arm, x < y := by
    intro j
    induction j using Ordinal.limitRecOn with
    | zero =>
        intro hj i hij
        exact (not_lt_zero hij).elim
    | add_one j ih =>
        intro hj i hij x hx y hy
        have hjω₂ : j < ω_ 2 := (lt_add_one j).trans hj
        let data : SuccessorData red fiber (state j hjω₂) :=
          chooseSuccessorData hBHT red blue hcompl hfiberCard hnoBlue
            (state j hjω₂)
        have hstateSucc : state (j + 1) hj = data.next := by
          exact buildArmState_add_one hBHT red blue hcompl hfiberCard
            hnoBlue initial j hj
        have hyNext : y ∈ data.next.arm := by
          rw [← hstateSucc]
          exact hy
        have hijLe : i ≤ j := (lt_add_one_iff).mp hij
        rcases hijLe.eq_or_lt with hijEq | hijLt
        · subst i
          exact data.ordered x hx y hyNext
        · obtain ⟨middle, _⟩ :=
            exists_max_of_type_redNearTarget (state j hjω₂).arm_type
          exact (ih hjω₂ i hijLt x hx (middle : W2) middle.property).trans
            (data.ordered middle middle.property y hyNext)
    | limit j hjLimit ih =>
        intro hj i hij x hx y hy
        let previous : ∀ o' : Ordinal.{0}, o' < j →
            RedNearArmState red fiber :=
          fun o' h ↦ state o' (h.trans hj)
        let data : LimitData red fiber j previous :=
          chooseLimitData hBHT red blue hcompl hfiberCard j hj hnoBlue
            previous
        have hstateLimit : state j hj = data.next := by
          exact buildArmState_limit hBHT red blue hcompl hfiberCard
            hnoBlue initial j hj hjLimit
        have hyNext : y ∈ data.next.arm := by
          rw [← hstateLimit]
          exact hy
        exact data.ordered i hij x hx y hyNext
  have hcenterBefore : ∀ i, ∀ x ∈ arms i, center < x := by
    intro i x hx
    have hxFiber : x ∈ fiber := (state i i.property).arm_sub hx
    exact (hmaximum center hcenterMem).trans_lt (hfiberTail hxFiber)
  have hcenterArmBlue : ∀ i, ∀ x ∈ arms i, blue.Adj center x := by
    intro i x hx
    exact hcenterBlue x ((state i i.property).arm_sub hx)
  refine ⟨{
    fiber := fiber
    center := center
    arms := arms
    fiber_card := hfiberCard
    arm_sub := fun i ↦ (state i i.property).arm_sub
    arm_red := fun i ↦ (state i i.property).arm_red
    arm_type := fun i ↦ (state i i.property).arm_type
    center_before := hcenterBefore
    center_blue := hcenterArmBlue
    ordered := ?_
    cross_blue_failure := ?_ }⟩
  · intro i j hij x hx y hy
    exact horderedRaw j j.property i hij x hx y hy
  · intro i j hij y hy
    by_contra hnone
    push Not at hnone
    have hlater : ∀ x ∈ arms i, x < y :=
      fun x hx ↦ horderedRaw j j.property i hij x hx y hy
    have hredAdj : ∀ x ∈ arms i, red.Adj x y := by
      intro x hx
      rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
      exact ⟨(hlater x hx).ne, hnone x hx⟩
    obtain ⟨target, htargetRed, htargetType⟩ :=
      red.exists_clique_type_add_one_of_common_later
        (state i i.property).arm_red (state i i.property).arm_type
          hlater hredAdj
    apply hnoRed
    refine ⟨target, htargetRed, ?_⟩
    calc
      typeLT target = RedNearTarget + 1 := htargetType
      _ = RedTarget := by
        norm_num [RedNearTarget, RedCoreTarget, RedTarget, add_assoc]

/-- The range of a strict `W2`-indexed sequence has exact type
`omegaTwo`. -/
private theorem typeLT_range_eq_omegaTwo_of_strictMono
    (f : W2 → W2) (hf : StrictMono f) :
    typeLT (Set.range f) = ω_ 2 := by
  have htype :=
    ((hf.strictMonoOn Set.univ).orderIso f Set.univ).ordinalType_congr
  have himageRange : typeLT (f '' Set.univ) = typeLT (Set.range f) :=
    (OrderIso.setCongr (f '' Set.univ) (Set.range f)
      Set.image_univ).ordinalType_congr
  calc
    typeLT (Set.range f) = typeLT (f '' Set.univ) := himageRange.symm
    _ = typeLT (Set.univ : Set W2) := htype.symm
    _ = typeLT W2 := OrderIso.Set.univ.ordinalType_congr
    _ = ω_ 2 := by
      simpa only [W2] using Ordinal.type_toType (ω_ 2 : Ordinal.{0})

/-- A point placed before a red near-target is absorbed by its limit
core.  This is the exact arithmetic obstruction left after freezing the
terminal failure coordinate. -/
theorem one_add_redNearTarget_eq :
    (1 : Ordinal.{0}) + RedNearTarget = RedNearTarget := by
  have hprincipal : IsPrincipal (· + ·) RedCoreTarget :=
    Ordinal.isPrincipal_add_opow_of_isPrincipal_add
      (Ordinal.isPrincipal_add_omega 1) (ω + 2)
  have honeLt : (1 : Ordinal.{0}) < RedCoreTarget := by
    rw [RedCoreTarget, Ordinal.one_lt_opow]
    exact ⟨one_lt_omega0.trans_le (Ordinal.omega0_le_omega 1), by simp⟩
  rw [RedNearTarget, ← add_assoc, hprincipal.add_eq_right honeLt]

/-- Terminal thinning of the full arm chain produces the frozen
prefix-absorption obstruction. -/
theorem FixedCenterRedNearArmChain.to_bhtConditionalTerminalPrefixObstruction
    (hCH : CH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2)
    (hchain : FixedCenterRedNearArmChain red blue)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    Nonempty (BHTConditionalTerminalPrefixObstruction red blue) := by
  classical
  have hstageStrict : StrictMono nearArmStage := by
    intro a b hab
    change (a : Ordinal) < (b : Ordinal)
    rw [← Ordinal.ToType.mk.apply_symm_apply a,
      ← Ordinal.ToType.mk.apply_symm_apply b] at hab
    exact (Ordinal.ToType.mk.lt_iff_lt).mp hab
  have hterminalExists (a : W2) :
      ∃ maximum : hchain.arms (nearArmStage a), IsMax maximum :=
    exists_max_of_type_redNearTarget (hchain.arm_type (nearArmStage a))
  let maximum (a : W2) : hchain.arms (nearArmStage a) :=
    Classical.choose (hterminalExists a)
  have hmaximumMax (a : W2) : IsMax (maximum a) :=
    Classical.choose_spec (hterminalExists a)
  let terminal : W2 → W2 := fun a ↦ maximum a
  have hterminalMem (a : W2) :
      terminal a ∈ hchain.arms (nearArmStage a) := (maximum a).property
  have hterminalMax (a : W2)
      (x : W2) (hx : x ∈ hchain.arms (nearArmStage a)) :
      x ≤ terminal a := by
    have hxMax :
        (⟨x, hx⟩ : hchain.arms (nearArmStage a)) ≤ maximum a :=
      le_of_not_gt ((isMax_iff_forall_not_lt.mp (hmaximumMax a)) ⟨x, hx⟩)
    exact hxMax
  have hterminalStrict : StrictMono terminal := by
    intro a b hab
    exact hchain.ordered (nearArmStage a) (nearArmStage b)
      (hstageStrict hab) (terminal a) (hterminalMem a)
        (terminal b) (hterminalMem b)
  have hterminalType : typeLT (Set.range terminal) = ω_ 2 :=
    typeLT_range_eq_omegaTwo_of_strictMono terminal hterminalStrict
  have hterminalCard : #(Set.range terminal) = ℵ_ 2 := by
    have hc := congrArg Ordinal.card hterminalType
    simpa only [Ordinal.card_type, Ordinal.card_omega] using hc
  obtain ⟨blueTerminals, hblueSub, hblueClique, hblueType⟩ :=
    exists_blue_omegaOne_add_one_in_every_alephTwo_set
      hCH red blue hcompl hnoRed hterminalCard
  obtain ⟨blueMaximumSub, hblueMaximumMax⟩ :=
    exists_max_of_type_omegaOne_add_one hblueType
  let blueMaximum : W2 := blueMaximumSub
  have hblueMaximumMem : blueMaximum ∈ blueTerminals :=
    blueMaximumSub.property
  have hblueMaximum : ∀ x ∈ blueTerminals, x ≤ blueMaximum := by
    intro x hx
    exact show (⟨x, hx⟩ : blueTerminals) ≤ blueMaximumSub from
      le_of_not_gt
        ((isMax_iff_forall_not_lt.mp hblueMaximumMax) ⟨x, hx⟩)
  let laterTerminals : Set W2 :=
    Set.range terminal ∩ Set.Ioi blueMaximum
  have hlaterCard : #laterTerminals = ℵ_ 2 :=
    mk_inter_Ioi_eq_alephTwo hterminalCard blueMaximum
  have hblueCard : #blueTerminals = ℵ_ 1 := by
    have hc := congrArg Ordinal.card hblueType
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  have hwitness (y : laterTerminals) :
      ∃ q : blueTerminals, red.Adj q y := by
    by_contra hnone
    push Not at hnone
    have hlater : ∀ q ∈ blueTerminals, q < (y : W2) := by
      intro q hq
      exact (hblueMaximum q hq).trans_lt y.property.2
    have hblueAdj : ∀ q ∈ blueTerminals, blue.Adj q y := by
      intro q hq
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      exact ⟨(hlater q hq).ne, hnone ⟨q, hq⟩⟩
    obtain ⟨target, htargetBlue, htargetType⟩ :=
      blue.exists_clique_type_add_one_of_common_later
        hblueClique hblueType hlater hblueAdj
    apply hnoBlue
    refine ⟨target, htargetBlue, ?_⟩
    calc
      typeLT target = (ω_ 1 + 1) + 1 := htargetType
      _ = ω_ 1 + 2 := by norm_num [add_assoc]
  let failure : laterTerminals → blueTerminals :=
    fun y ↦ Classical.choose (hwitness y)
  have hfailure (y : laterTerminals) : red.Adj (failure y) y :=
    Classical.choose_spec (hwitness y)
  obtain ⟨frozen, hlargeFiber⟩ := Cardinal.infinite_pigeonhole failure
    (by rw [hlaterCard]; exact Cardinal.aleph0_le_aleph 2)
    (by
      rw [hblueCard, hlaterCard]
      rw [show (ℵ_ 2 : Cardinal.{0}) =
          ℵ_ ((1 : Ordinal.{0}) + 1) by norm_num,
        (Cardinal.isRegular_aleph_add_one 1).cof_ord]
      exact Cardinal.aleph_lt_aleph.mpr (by norm_num))
  let frozenFiber : Set W2 :=
    Subtype.val '' (failure ⁻¹' {frozen})
  have hfrozenFiberCard : #frozenFiber = ℵ_ 2 := by
    calc
      #frozenFiber = #(failure ⁻¹' {frozen}) :=
        Cardinal.mk_image_eq Subtype.val_injective
      _ = #laterTerminals := hlargeFiber
      _ = ℵ_ 2 := hlaterCard
  have hfrozenFiberSub : frozenFiber ⊆ laterTerminals := by
    rintro y ⟨z, _hz, rfl⟩
    exact z.property
  have hfrozenRed : ∀ y ∈ frozenFiber, red.Adj frozen y := by
    rintro y ⟨z, hz, rfl⟩
    have hzf : failure z = frozen := by
      simpa only [mem_preimage, mem_singleton_iff] using hz
    simpa only [hzf] using hfailure z
  have hfrozenFiberType : typeLT frozenFiber = ω_ 2 :=
    typeLT_eq_omegaTwo_of_mk_eq hfrozenFiberCard
  obtain ⟨finalArm, hfinalSub, hfinalRed, hfinalType⟩ |
      ⟨target, _htargetSub, htargetBlue, htargetType⟩ :=
    OrdinalRamsey.on_set_of_type hBHT red blue hcompl
      frozenFiber hfrozenFiberType
  · have hfrozenBefore : ∀ y ∈ finalArm, (frozen : W2) < y := by
      intro y hy
      have hyLater : y ∈ laterTerminals :=
        hfrozenFiberSub (hfinalSub hy)
      exact (hblueMaximum frozen frozen.property).trans_lt
        hyLater.2
    refine ⟨{
      chain := hchain
      terminal := terminal
      terminal_mem := hterminalMem
      terminal_max := hterminalMax
      terminal_strict := hterminalStrict
      terminal_range_type := hterminalType
      terminal_center_blue := fun a ↦
        hchain.center_blue (nearArmStage a) (terminal a) (hterminalMem a)
      blueTerminals := blueTerminals
      blueTerminals_sub := hblueSub
      blueTerminals_blue := hblueClique
      blueTerminals_type := hblueType
      blueMaximum := blueMaximum
      blueMaximum_mem := hblueMaximumMem
      blueMaximum_max := hblueMaximum
      frozen := frozen
      frozen_mem := frozen.property
      frozenFiber := frozenFiber
      frozenFiber_card := hfrozenFiberCard
      frozenFiber_sub := hfrozenFiberSub
      frozen_red := hfrozenRed
      finalArm := finalArm
      finalArm_sub := hfinalSub
      finalArm_red := hfinalRed
      finalArm_type := hfinalType
      frozen_before_final := hfrozenBefore
      frozen_red_final := fun y hy ↦ hfrozenRed y (hfinalSub hy) }⟩
  · exact (hnoBlue ⟨target, htargetBlue, htargetType⟩).elim

/-- Direct DoubleFan-to-terminal obstruction theorem. -/
theorem NearRedOneSuccessorDoubleFan.to_bhtConditionalTerminalPrefixObstruction
    (hCH : CH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2)
    (hfan : NearRedOneSuccessorDoubleFan red blue)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    Nonempty (BHTConditionalTerminalPrefixObstruction red blue) := by
  obtain ⟨chain⟩ :=
    NearRedOneSuccessorDoubleFan.to_fixedCenterRedNearArmChain
      hBHT red blue hfan hcompl hnoRed hnoBlue
  exact FixedCenterRedNearArmChain.to_bhtConditionalTerminalPrefixObstruction
    hCH hBHT red blue chain hcompl hnoRed hnoBlue

/-- Explicitly BHT-conditional exact-or-obstruction wrapper.  Outside the
exact targets, the full `alephTwo` DoubleFan fiber yields the complete
arm chain and frozen terminal prefix obstruction above. -/
theorem part3_exact_or_bhtConditionalTerminalPrefixObstruction
    (hCH : CH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      Nonempty (BHTConditionalTerminalPrefixObstruction red blue) := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain hexact | hfan :=
      part3_exact_or_nearRedOneSuccessorDoubleFan
        hCH hBHT red blue hcompl
    · exact (htarget hexact).elim
    · exact NearRedOneSuccessorDoubleFan.to_bhtConditionalTerminalPrefixObstruction
        hCH hBHT red blue hfan hcompl hnone.1 hnone.2

end Erdos1172Part3OneSuccessorFullFiberChain
