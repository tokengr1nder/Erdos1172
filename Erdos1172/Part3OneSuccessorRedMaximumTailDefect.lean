/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NearArmFullProfileBarrier
public import Erdos1172.Part3OneSuccessorTerminalSplit

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OneSuccessorRedMaximumTailDefect

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3OneSuccessorBarrier
  Erdos1172Part3OneSuccessorDeepMatrix
  Erdos1172Part3OneSuccessorFullFiberChain
  Erdos1172Part3OneSuccessorTerminalSplit
  Erdos1172Part3OmegaOneRectangleRefinement
  Erdos1172Part3NearArmFullProfileBarrier

/-- The predecessor core of the canonical maximum in arm `a`. -/
def nearArmCore
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2) : Set W2 :=
  redCoreBelow (chain.arms (nearArmStage a))
    (nearArmTerminal chain a)

/-- The blue predecessor section in the exact core of arm `a` belonging
to the canonical terminal at the later stage `b`. -/
noncomputable def coreBlueSection
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2)
    (b : LaterIndex a) : Set (nearArmCore chain a) :=
  blueColumn blue (nearArmCore chain a)
    (nearArmTerminal chain (b : W2))

/-- The canonical maximum selected from an arm agrees with the terminal
already retained by the terminal-prefix obstruction.  Both are maxima of
the same linearly ordered arm. -/
theorem nearArmTerminal_eq_obstructionTerminal
    {red blue : SimpleGraph W2}
    (obs : BHTConditionalTerminalPrefixObstruction red blue) (a : W2) :
    nearArmTerminal obs.chain a = obs.terminal a := by
  apply le_antisymm
  · exact obs.terminal_max a (nearArmTerminal obs.chain a)
      (nearArmTerminal_mem obs.chain a)
  · exact nearArmTerminal_max obs.chain a (obs.terminal a)
      (obs.terminal_mem a)

/-- Each predecessor core retains the exact limit-core order type. -/
theorem typeLT_nearArmCore
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2) :
    typeLT (nearArmCore chain a) = RedCoreTarget := by
  exact typeLT_redCoreBelow
    (chain.arm_type (nearArmStage a))
    (nearArmTerminal_mem chain a)
    (nearArmTerminal_max chain a)

/-- Every strict final segment of a red near-target arm above a point
below its maximum still has the full near-target type. -/
theorem typeLT_nearArm_strictFinalSegment
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2)
    {x₀ : W2} (hx₀Mem : x₀ ∈ chain.arms (nearArmStage a))
    (hx₀lt : x₀ < nearArmTerminal chain a) :
    typeLT {x : W2 |
      x ∈ chain.arms (nearArmStage a) ∧ x₀ < x} = RedNearTarget := by
  classical
  let coreTail : Set W2 :=
    {x | x ∈ chain.arms (nearArmStage a) ∧
      x₀ < x ∧ x < nearArmTerminal chain a}
  have hcoreTailType : typeLT coreTail = RedCoreTarget :=
    typeLT_redCore_finalSegment
      (chain.arm_type (nearArmStage a))
      (nearArmTerminal_mem chain a)
      (nearArmTerminal_max chain a) hx₀Mem hx₀lt
  have hcoreTailBeforeMaximum :
      ∀ x ∈ coreTail, x < nearArmTerminal chain a :=
    fun _ hx ↦ hx.2.2
  have hsegmentEq :
      {x : W2 | x ∈ chain.arms (nearArmStage a) ∧ x₀ < x} =
        Set.insert (nearArmTerminal chain a) coreTail := by
    ext x
    constructor
    · intro hx
      rcases (nearArmTerminal_max chain a x hx.1).eq_or_lt with
        hxm | hxm
      · exact Set.mem_insert_iff.mpr (Or.inl hxm)
      · exact Set.mem_insert_iff.mpr
          (Or.inr ⟨hx.1, hx.2, hxm⟩)
    · intro hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨nearArmTerminal_mem chain a, hx₀lt⟩
      · exact ⟨hx.1, hx.2.1⟩
  calc
    typeLT {x : W2 |
        x ∈ chain.arms (nearArmStage a) ∧ x₀ < x} =
        typeLT (Set.insert (nearArmTerminal chain a) coreTail : Set W2) :=
      congrArg (fun s : Set W2 ↦ typeLT s) hsegmentEq
    _ = typeLT coreTail + 1 :=
      Ordinal.typeLT_insert_of_forall_lt hcoreTailBeforeMaximum
    _ = RedCoreTarget + 1 := by rw [hcoreTailType]
    _ = RedNearTarget := rfl

/-- Sharp pointwise tail-defect law.  For an earlier arm and a later
terminal, either the arm maximum itself is blue, or the blue section in
the predecessor core is strictly cofinal.  If both failed, a final red
near-target segment followed by the later terminal would be the exact
red target. -/
theorem nearArmMaximum_blue_or_strictlyCofinalCoreSection
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (a : W2) (b : LaterIndex a) :
    blue.Adj (nearArmTerminal chain a)
        (nearArmTerminal chain (b : W2)) ∨
      StrictlyCofinalBlueColumn blue (nearArmCore chain a)
        (nearArmTerminal chain (b : W2)) := by
  classical
  by_cases hmaximumBlue :
      blue.Adj (nearArmTerminal chain a)
        (nearArmTerminal chain (b : W2))
  · exact Or.inl hmaximumBlue
  · right
    apply strictlyCofinalBlueColumn_of_not_shallowAt blue
    intro hshallow
    obtain ⟨x₀, hx₀Mem, hx₀lt, hbounded⟩ := hshallow
    let finalSegment : Set W2 :=
      {x | x ∈ chain.arms (nearArmStage a) ∧ x₀ < x}
    have hfinalSegmentType : typeLT finalSegment = RedNearTarget :=
      typeLT_nearArm_strictFinalSegment chain a hx₀Mem hx₀lt
    have hfinalSegmentSub :
        finalSegment ⊆ profileRedComplement chain a
          (fullBlueProfile chain a b) := by
      intro x hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      have hnotBlue :
          ¬ blue.Adj x (nearArmTerminal chain (b : W2)) := by
        rcases (nearArmTerminal_max chain a x hx.1).eq_or_lt with
          hxm | hxm
        · simpa only [hxm] using hmaximumBlue
        · exact hbounded x hx.1 hx.2 hxm
      simpa only [fullBlueProfile, Set.mem_compl_iff,
        Set.mem_ofPred_eq] using hnotBlue
    have hnearLe : RedNearTarget ≤
        typeLT (profileRedComplement chain a
          (fullBlueProfile chain a b)) := by
      rw [← hfinalSegmentType]
      exact Ordinal.type_mono hfinalSegmentSub
    exact (not_lt_of_ge hnearLe)
      (fullProfileComplement_type_lt_redNearTarget
        chain hcompl hnoRed a b)

/-- A strictly cofinal core section is cofinal in the induced core order. -/
theorem coreBlueSection_isCofinal
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue)
    (a : W2) (b : LaterIndex a)
    (hstrict : StrictlyCofinalBlueColumn blue (nearArmCore chain a)
      (nearArmTerminal chain (b : W2))) :
    IsCofinal (coreBlueSection chain a b) :=
  blueColumn_isCofinal blue hstrict

/-- A strictly cofinal predecessor section has exact cardinality
`alephOne`. -/
theorem mk_coreBlueSection_eq_alephOne
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue)
    (a : W2) (b : LaterIndex a)
    (hstrict : StrictlyCofinalBlueColumn blue (nearArmCore chain a)
      (nearArmTerminal chain (b : W2))) :
    #(coreBlueSection chain a b) = ℵ_ 1 :=
  mk_blueColumn_eq_alephOne blue (typeLT_nearArmCore chain a) hstrict

/-- The order type of a cofinal core section is at least the initial
ordinal `omegaOne`. -/
theorem omegaOne_le_typeLT_coreBlueSection
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue)
    (a : W2) (b : LaterIndex a)
    (hstrict : StrictlyCofinalBlueColumn blue (nearArmCore chain a)
      (nearArmTerminal chain (b : W2))) :
    (ω_ 1 : Ordinal.{0}) ≤ typeLT (coreBlueSection chain a b) := by
  have hcard : #(coreBlueSection chain a b) = ℵ_ 1 :=
    mk_coreBlueSection_eq_alephOne chain a b hstrict
  calc
    (ω_ 1 : Ordinal.{0}) = (ℵ_ 1 : Cardinal).ord :=
      (Cardinal.ord_aleph 1).symm
    _ = (#(coreBlueSection chain a b)).ord :=
      congrArg Cardinal.ord hcard.symm
    _ ≤ typeLT (coreBlueSection chain a b) :=
      Cardinal.ord_le_type ((· < ·) :
        (coreBlueSection chain a b) →
          (coreBlueSection chain a b) → Prop)

/-- The order type of any core section is bounded by the exact red core. -/
theorem typeLT_coreBlueSection_le_redCoreTarget
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue)
    (a : W2) (b : LaterIndex a) :
    typeLT (coreBlueSection chain a b) ≤ RedCoreTarget := by
  calc
    typeLT (coreBlueSection chain a b) ≤ typeLT (nearArmCore chain a) :=
      Ordinal.type_set_le (coreBlueSection chain a b)
    _ = RedCoreTarget := typeLT_nearArmCore chain a

/-- Type-valued data extracted from the distinguished red-to-maximum
branch of `TerminalSplit`.  The actual `alephTwo` terminal fiber and its
exact red near-arm are retained.  Reindexing that fiber by later arm
stages makes the maximum-blue alternative impossible, so every exact
core section is strictly cofinal, has cardinality `alephOne`, and has
order type between `omegaOne` and the exact red core. -/
structure DistinguishedRedMaximumCofinalTail
    {red blue : SimpleGraph W2}
    (obs : BHTConditionalTerminalPrefixObstruction red blue) : Type 1 where
  stage : W2
  stage_terminal_eq_blueMaximum :
    nearArmTerminal obs.chain stage = obs.blueMaximum
  terminalFiber : Set W2
  terminalFiber_card : #terminalFiber = ℵ_ 2
  terminalFiber_sub : terminalFiber ⊆
    Set.range obs.terminal ∩ Set.Ioi obs.blueMaximum
  maximum_red_on_terminalFiber :
    ∀ y ∈ terminalFiber, red.Adj obs.blueMaximum y
  redNearArm : Set W2
  redNearArm_sub : redNearArm ⊆ terminalFiber
  redNearArm_red : red.IsClique redNearArm
  redNearArm_type : typeLT redNearArm = RedNearTarget
  maximum_before_redNearArm :
    ∀ y ∈ redNearArm, obs.blueMaximum < y
  maximum_insert_red :
    red.IsClique (Set.insert obs.blueMaximum redNearArm)
  prefix_absorbed :
    (1 : Ordinal.{0}) + typeLT redNearArm = RedNearTarget
  indexFiber : Set (LaterIndex stage)
  indexFiber_card : #indexFiber = ℵ_ 2
  indexed_terminal_image :
    (fun b : LaterIndex stage ↦
      nearArmTerminal obs.chain (b : W2)) '' indexFiber = terminalFiber
  maximum_red : ∀ b ∈ indexFiber,
    red.Adj (nearArmTerminal obs.chain stage)
      (nearArmTerminal obs.chain (b : W2))
  maximum_not_blue : ∀ b ∈ indexFiber,
    ¬ blue.Adj (nearArmTerminal obs.chain stage)
      (nearArmTerminal obs.chain (b : W2))
  ordered : ∀ b ∈ indexFiber,
    ∀ x ∈ obs.chain.arms (nearArmStage stage),
      x < nearArmTerminal obs.chain (b : W2)
  core_type : typeLT (nearArmCore obs.chain stage) = RedCoreTarget
  blueSection_strictlyCofinal : ∀ b ∈ indexFiber,
    StrictlyCofinalBlueColumn blue (nearArmCore obs.chain stage)
      (nearArmTerminal obs.chain (b : W2))
  blueSection_isCofinal : ∀ b ∈ indexFiber,
    IsCofinal (coreBlueSection obs.chain stage b)
  blueSection_card : ∀ b ∈ indexFiber,
    #(coreBlueSection obs.chain stage b) = ℵ_ 1
  blueSection_type_lower : ∀ b ∈ indexFiber,
    (ω_ 1 : Ordinal.{0}) ≤ typeLT (coreBlueSection obs.chain stage b)
  blueSection_type_upper : ∀ b ∈ indexFiber,
    typeLT (coreBlueSection obs.chain stage b) ≤ RedCoreTarget

/-- Extract the reindexed, uniformly core-cofinal tail from the actual
red-to-maximum branch.  No stationary-set or profile-repetition claim is
made. -/
theorem TerminalMaximumRedNearArm.to_distinguishedRedMaximumCofinalTail
    {red blue : SimpleGraph W2}
    {obs : BHTConditionalTerminalPrefixObstruction red blue}
    (hmaximum : TerminalMaximumRedNearArm red blue obs)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget) :
    Nonempty (DistinguishedRedMaximumCofinalTail obs) := by
  classical
  obtain ⟨terminalFiber, redNearArm, hterminalFiberCard,
      hterminalFiberSub, hmaximumRedOnFiber, hredNearArmSub,
      hredNearArmRed, hredNearArmType, hmaximumBeforeRedNearArm,
      hmaximumInsertRed, hprefixAbsorbed⟩ := hmaximum
  obtain ⟨stage, hstageTerminal⟩ :=
    obs.blueTerminals_sub obs.blueMaximum_mem
  have hcanonicalStageTerminal :
      nearArmTerminal obs.chain stage = obs.blueMaximum :=
    (nearArmTerminal_eq_obstructionTerminal obs stage).trans
      hstageTerminal
  have hrawIndexExists (y : terminalFiber) :
      ∃ b : W2, obs.terminal b = (y : W2) :=
    (hterminalFiberSub y.property).1
  let rawIndex (y : terminalFiber) : W2 :=
    Classical.choose (hrawIndexExists y)
  have hrawIndexSpec (y : terminalFiber) :
      obs.terminal (rawIndex y) = (y : W2) :=
    Classical.choose_spec (hrawIndexExists y)
  have hrawIndexLater (y : terminalFiber) : stage < rawIndex y := by
    apply lt_of_not_ge
    intro hle
    have hterminalLe :
        obs.terminal (rawIndex y) ≤ obs.terminal stage :=
      obs.terminal_strict.monotone hle
    have hyLeMaximum : (y : W2) ≤ obs.blueMaximum := by
      rw [← hrawIndexSpec y, ← hstageTerminal]
      exact hterminalLe
    exact (not_le_of_gt (hterminalFiberSub y.property).2) hyLeMaximum
  let laterIndex (y : terminalFiber) : LaterIndex stage :=
    ⟨rawIndex y, hrawIndexLater y⟩
  have hlaterIndexTerminal (y : terminalFiber) :
      nearArmTerminal obs.chain ((laterIndex y : LaterIndex stage) : W2) =
        (y : W2) := by
    change nearArmTerminal obs.chain (rawIndex y) = (y : W2)
    rw [nearArmTerminal_eq_obstructionTerminal obs (rawIndex y)]
    exact hrawIndexSpec y
  have hlaterIndexInjective : Function.Injective laterIndex := by
    intro y z hyz
    apply Subtype.ext
    rw [← hlaterIndexTerminal y, ← hlaterIndexTerminal z]
    exact congrArg
      (fun b : LaterIndex stage ↦ nearArmTerminal obs.chain (b : W2)) hyz
  let indexFiber : Set (LaterIndex stage) := Set.range laterIndex
  have hindexFiberCard : #indexFiber = ℵ_ 2 := by
    calc
      #indexFiber = #terminalFiber :=
        Cardinal.mk_range_eq laterIndex hlaterIndexInjective
      _ = ℵ_ 2 := hterminalFiberCard
  have hindexedTerminalImage :
      (fun b : LaterIndex stage ↦
        nearArmTerminal obs.chain (b : W2)) '' indexFiber =
          terminalFiber := by
    ext y
    constructor
    · rintro ⟨b, ⟨z, rfl⟩, rfl⟩
      change nearArmTerminal obs.chain
        ((laterIndex z : LaterIndex stage) : W2) ∈ terminalFiber
      rw [hlaterIndexTerminal z]
      exact z.property
    · intro hy
      let z : terminalFiber := ⟨y, hy⟩
      refine ⟨laterIndex z, Set.mem_range_self z, ?_⟩
      exact hlaterIndexTerminal z
  have hmaximumRed (b : LaterIndex stage) (hb : b ∈ indexFiber) :
      red.Adj (nearArmTerminal obs.chain stage)
        (nearArmTerminal obs.chain (b : W2)) := by
    obtain ⟨y, rfl⟩ := hb
    rw [hcanonicalStageTerminal, hlaterIndexTerminal y]
    exact hmaximumRedOnFiber y y.property
  have hmaximumNotBlue (b : LaterIndex stage) (hb : b ∈ indexFiber) :
      ¬ blue.Adj (nearArmTerminal obs.chain stage)
        (nearArmTerminal obs.chain (b : W2)) := by
    intro hblue
    let leftVertex : W2 := nearArmTerminal obs.chain stage
    let rightVertex : W2 := nearArmTerminal obs.chain (b : W2)
    change blue.Adj leftVertex rightVertex at hblue
    rw [← hcompl.compl_eq, SimpleGraph.compl_adj] at hblue
    exact hblue.2 (hmaximumRed b hb)
  have hordered (b : LaterIndex stage) (_hb : b ∈ indexFiber) :
      ∀ x ∈ obs.chain.arms (nearArmStage stage),
        x < nearArmTerminal obs.chain (b : W2) := by
    intro x hx
    exact obs.chain.ordered (nearArmStage stage)
      (nearArmStage (b : W2))
      (nearArmStage_strictMono b.property) x hx
      (nearArmTerminal obs.chain (b : W2))
      (nearArmTerminal_mem obs.chain (b : W2))
  have hstrict (b : LaterIndex stage) (hb : b ∈ indexFiber) :
      StrictlyCofinalBlueColumn blue (nearArmCore obs.chain stage)
        (nearArmTerminal obs.chain (b : W2)) := by
    obtain hblue | hcofinal :=
      nearArmMaximum_blue_or_strictlyCofinalCoreSection
        obs.chain hcompl hnoRed stage b
    · exact (hmaximumNotBlue b hb hblue).elim
    · exact hcofinal
  refine ⟨{
    stage := stage
    stage_terminal_eq_blueMaximum := hcanonicalStageTerminal
    terminalFiber := terminalFiber
    terminalFiber_card := hterminalFiberCard
    terminalFiber_sub := hterminalFiberSub
    maximum_red_on_terminalFiber := hmaximumRedOnFiber
    redNearArm := redNearArm
    redNearArm_sub := hredNearArmSub
    redNearArm_red := hredNearArmRed
    redNearArm_type := hredNearArmType
    maximum_before_redNearArm := hmaximumBeforeRedNearArm
    maximum_insert_red := hmaximumInsertRed
    prefix_absorbed := hprefixAbsorbed
    indexFiber := indexFiber
    indexFiber_card := hindexFiberCard
    indexed_terminal_image := hindexedTerminalImage
    maximum_red := hmaximumRed
    maximum_not_blue := hmaximumNotBlue
    ordered := hordered
    core_type := typeLT_nearArmCore obs.chain stage
    blueSection_strictlyCofinal := hstrict
    blueSection_isCofinal := fun b hb ↦
      coreBlueSection_isCofinal obs.chain stage b (hstrict b hb)
    blueSection_card := fun b hb ↦
      mk_coreBlueSection_eq_alephOne obs.chain stage b (hstrict b hb)
    blueSection_type_lower := fun b hb ↦
      omegaOne_le_typeLT_coreBlueSection
        obs.chain stage b (hstrict b hb)
    blueSection_type_upper := fun b _hb ↦
      typeLT_coreBlueSection_le_redCoreTarget obs.chain stage b }⟩

/-- The full red-maximum tail obstruction.  It retains the original BHT
terminal record, the actual distinguished cofinal fiber above, and the
choice-independent full-profile barrier at every arm stage. -/
structure BHTConditionalRedMaximumTailDefectObstruction
    (red blue : SimpleGraph W2) : Type 1 where
  terminalObstruction :
    BHTConditionalTerminalPrefixObstruction red blue
  terminalMaximumRedNearArm :
    TerminalMaximumRedNearArm red blue terminalObstruction
  distinguishedTail :
    DistinguishedRedMaximumCofinalTail terminalObstruction
  fullProfileBarrier : ∀ a : W2,
    NearArmFullProfileBarrier terminalObstruction.chain a
  fullProfileSpace_card : ∀ a : W2,
    #(Set (EarlierArm terminalObstruction.chain a)) = ℵ_ 2

/-- Enrich the red branch of `TerminalSplit` by both the sharp
distinguished tail-defect law and the full-profile barrier.  This theorem
is explicitly BHT-conditional. -/
theorem BHTConditionalTerminalPrefixObstruction.to_redMaximumTailDefectObstruction
    {red blue : SimpleGraph W2} (hGCH : GCH)
    (hBHT : BHTNearPart3Relation)
    (obs : BHTConditionalTerminalPrefixObstruction red blue)
    (hmaximum : TerminalMaximumRedNearArm red blue obs)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    Nonempty (BHTConditionalRedMaximumTailDefectObstruction red blue) := by
  obtain ⟨distinguishedTail⟩ :=
    TerminalMaximumRedNearArm.to_distinguishedRedMaximumCofinalTail
      hmaximum hcompl hnoRed
  refine ⟨{
    terminalObstruction := obs
    terminalMaximumRedNearArm := hmaximum
    distinguishedTail := distinguishedTail
    fullProfileBarrier :=
      FixedCenterRedNearArmChain.forall_nearArmFullProfileBarrier
        hBHT red blue obs.chain hcompl hnoRed hnoBlue
    fullProfileSpace_card := fun a ↦
      mk_fullBlueProfile_space_eq_alephTwo hGCH obs.chain a }⟩

/-- Explicitly BHT-conditional global normal form under GCH.  Outside
the exact targets and the already isolated ordered blue rectangle, the
original terminal obstruction survives together with an `alephTwo`
red-maximum fiber of cofinal `alephOne` blue core sections and the sharp
full-profile repeated-or-injective alternative at every arm stage. -/
theorem part3_exact_or_bhtConditionalRedMaximumTailDefect
    (hGCH : GCH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      OrderedBlueOmegaOneByOmegaOneAddOneRedRectangle red blue ∨
      Nonempty (BHTConditionalRedMaximumTailDefectObstruction red blue) := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · have hnone := not_or.mp htarget
    obtain hexact | ⟨obs, hmaximum | hrectangle⟩ :=
      part3_exact_or_bhtConditionalTerminalMaximumSplit
        hGCH.toCH hBHT red blue hcompl
    · exact (htarget hexact).elim
    · exact Or.inr (Or.inr <|
        BHTConditionalTerminalPrefixObstruction.to_redMaximumTailDefectObstruction
          hGCH hBHT obs hmaximum hcompl hnone.1 hnone.2)
    · exact Or.inr (Or.inl hrectangle)

end Erdos1172Part3OneSuccessorRedMaximumTailDefect
