/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OneSuccessorRedMaximumTailDefect

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3BHTSecondMaximumGap

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3OneSuccessorBarrier
  Erdos1172Part3OneSuccessorDeepMatrix
  Erdos1172Part3OneSuccessorFullFiberChain
  Erdos1172Part3OneSuccessorTerminalSplit
  Erdos1172Part3NearArmFullProfileBarrier
  Erdos1172Part3OneSuccessorRedMaximumTailDefect
  Erdos1172Part3OmegaOneRectangleRefinement

/-- The part of the Baumgartner--Hajnal--Todorčević construction below
its final model ordinal.  In the paper this set is the union of `omegaOne`
successive blocks of type `omegaOne ^ (omega + 1)`, hence has type
`omegaOne ^ (omega + 2)`.  The point `firstMaximum` is the single terminal
point supplied by Theorem 4.1. -/
structure BHTFinalFusionCore (red : SimpleGraph W2) : Type 1 where
  core : Set W2
  firstMaximum : W2
  core_red : red.IsClique core
  core_type : typeLT core = RedCoreTarget
  core_before_first : ∀ x ∈ core, x < firstMaximum
  core_red_first : ∀ x ∈ core, red.Adj x firstMaximum

/-- The `omegaOne` stages of the final BHT fusion. -/
abbrev BHTFusionStage : Type := (ω_ 1 : Ordinal.{0}).ToType

/-- The exact extra assertion which changes the BHT red conclusion from
`omegaOne ^ (omega + 2) + 1` to the open target
`omegaOne ^ (omega + 2) + 2`: there is one further point above the BHT
maximum which is red both to that maximum and to every selected block
(equivalently, to their fused union `core`). -/
def HasSecondMaximumExtension
    (red : SimpleGraph W2) (fusion : BHTFinalFusionCore red) : Prop :=
  ∃ secondMaximum : W2,
    fusion.firstMaximum < secondMaximum ∧
    red.Adj fusion.firstMaximum secondMaximum ∧
    ∀ x ∈ fusion.core, red.Adj x secondMaximum

/-- The same missing assertion in the literal block coordinates of the
BHT proof.  The equality says that the displayed blocks are exactly the
selected `omegaOne`-stage fusion core; the last field is the assertion
which the paper's one-maximum recursion does not preserve. -/
def HasSelectedBlockSecondMaximumExtension
    (red : SimpleGraph W2) (fusion : BHTFinalFusionCore red)
    (blocks : BHTFusionStage → Set W2) : Prop :=
  fusion.core = ⋃ i, blocks i ∧
  ∃ secondMaximum : W2,
    fusion.firstMaximum < secondMaximum ∧
    red.Adj fusion.firstMaximum secondMaximum ∧
    ∀ i, ∀ x ∈ blocks i, red.Adj x secondMaximum

/-- The exact intersection which a stationary/club strengthening of BHT
Claim 4.4 would have to keep nonempty through the `omegaOne` fusion.
Claim 4.4(b) gives a new stationary positive set at an individual step;
it does not put these compatibility sets in the `< omegaTwo`-complete dual
filter, so their `omegaOne`-stage intersection is not supplied by Fodor
or by diagonal intersection of clubs. -/
def selectedBlockSecondMaximumReservoir
    (red : SimpleGraph W2) (fusion : BHTFinalFusionCore red)
    (blocks : BHTFusionStage → Set W2) : Set W2 :=
  {q | fusion.firstMaximum < q ∧
    red.Adj fusion.firstMaximum q ∧
    ∀ i, ∀ x ∈ blocks i, red.Adj x q}

/-- A nonempty final compatibility intersection is precisely the missing
selected-block extension assertion. -/
theorem hasSelectedBlockSecondMaximumExtension_of_reservoir
    {red : SimpleGraph W2} (fusion : BHTFinalFusionCore red)
    (blocks : BHTFusionStage → Set W2)
    (hcore : fusion.core = ⋃ i, blocks i)
    (hreservoir :
      (selectedBlockSecondMaximumReservoir red fusion blocks).Nonempty) :
    HasSelectedBlockSecondMaximumExtension red fusion blocks := by
  obtain ⟨q, hq⟩ := hreservoir
  exact ⟨hcore, q, hq.1, hq.2.1, hq.2.2⟩

/-- Being red to every selected BHT block is exactly being red to their
fused union. -/
theorem hasSecondMaximumExtension_of_selectedBlocks
    {red : SimpleGraph W2} (fusion : BHTFinalFusionCore red)
    (blocks : BHTFusionStage → Set W2)
    (hext : HasSelectedBlockSecondMaximumExtension red fusion blocks) :
    HasSecondMaximumExtension red fusion := by
  obtain ⟨hcore, secondMaximum, hfirstSecond, hfirstRedSecond,
      hblocksRedSecond⟩ := hext
  refine ⟨secondMaximum, hfirstSecond, hfirstRedSecond, ?_⟩
  intro x hx
  rw [hcore] at hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact hblocksRedSecond i x hxi

/-- The missing second-maximum assertion is sufficient for the exact red
target.  This is the ordinal-arithmetic endpoint of any attempted
strengthening of BHT Claim 4.4: the fused block core is followed first by
the model ordinal and then by the new common red point. -/
theorem BHTFinalFusionCore.hasCliqueOfType_redTarget
    {red : SimpleGraph W2} (fusion : BHTFinalFusionCore red)
    (hext : HasSecondMaximumExtension red fusion) :
    OrdinalRamsey.HasCliqueOfType red RedTarget := by
  classical
  obtain ⟨secondMaximum, hfirstSecond, hfirstRedSecond,
      hcoreRedSecond⟩ := hext
  let withFirst : Set W2 := Set.insert fusion.firstMaximum fusion.core
  have hwithFirstRed : red.IsClique withFirst := by
    apply fusion.core_red.insert
    intro x hx _
    rw [red.adj_comm]
    exact fusion.core_red_first x hx
  have hwithFirstType : typeLT withFirst = RedCoreTarget + 1 := by
    calc
      typeLT withFirst = typeLT fusion.core + 1 :=
        Ordinal.typeLT_insert_of_forall_lt fusion.core_before_first
      _ = RedCoreTarget + 1 := by rw [fusion.core_type]
  have hwithFirstBeforeSecond :
      ∀ x ∈ withFirst, x < secondMaximum := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hfirstSecond
    · exact (fusion.core_before_first x hx).trans hfirstSecond
  have hwithFirstRedSecond :
      ∀ x ∈ withFirst, red.Adj x secondMaximum := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hfirstRedSecond
    · exact hcoreRedSecond x hx
  obtain ⟨target, htargetRed, htargetType⟩ :=
    red.exists_clique_type_add_one_of_common_later
      hwithFirstRed hwithFirstType hwithFirstBeforeSecond
        hwithFirstRedSecond
  refine ⟨target, htargetRed, ?_⟩
  calc
    typeLT target = (RedCoreTarget + 1) + 1 := htargetType
    _ = RedTarget := by
      norm_num [RedCoreTarget, RedTarget, add_assoc]

/-- Literal selected-block form of the exact `+2` reduction. -/
theorem BHTFinalFusionCore.hasCliqueOfType_redTarget_of_selectedBlocks
    {red : SimpleGraph W2} (fusion : BHTFinalFusionCore red)
    (blocks : BHTFusionStage → Set W2)
    (hext : HasSelectedBlockSecondMaximumExtension red fusion blocks) :
    OrdinalRamsey.HasCliqueOfType red RedTarget :=
  fusion.hasCliqueOfType_redTarget
    (hasSecondMaximumExtension_of_selectedBlocks fusion blocks hext)

/-- The concrete obstruction left by the published transfinite-arm
analysis, stated in the coordinates of the BHT proof.  There are
`alephTwo` candidate second maxima.  Every candidate is correctly ordered
and red-adjacent to the first maximum, but its blue neighbourhood in the
exact fused predecessor core is strictly cofinal.  A red near-target arm
among the candidates shows that merely reapplying BHT does not repair the
defect: its initial prefix is absorbed by the limit core. -/
structure BHTSecondMaximumGap
    (red blue : SimpleGraph W2) : Type 1 where
  fusion : BHTFinalFusionCore red
  candidates : Set W2
  candidates_card : #candidates = ℵ_ 2
  first_before_candidates :
    ∀ y ∈ candidates, fusion.firstMaximum < y
  first_red_candidates :
    ∀ y ∈ candidates, red.Adj fusion.firstMaximum y
  blue_core_strictlyCofinal :
    ∀ y ∈ candidates,
      StrictlyCofinalBlueColumn blue fusion.core y
  blue_core_card :
    ∀ y ∈ candidates, #(blueColumn blue fusion.core y) = ℵ_ 1
  laterRedArm : Set W2
  laterRedArm_sub : laterRedArm ⊆ candidates
  laterRedArm_red : red.IsClique laterRedArm
  laterRedArm_type : typeLT laterRedArm = RedNearTarget
  prefix_absorbed :
    (1 : Ordinal.{0}) + typeLT laterRedArm = RedNearTarget

theorem nonempty_of_typeLT_eq_redCoreTarget
    {s : Set W2} (htype : typeLT s = RedCoreTarget) : s.Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  rw [hempty] at htype
  have hzero : (0 : Ordinal) = RedCoreTarget := by simpa using htype
  have honeLt : (1 : Ordinal.{0}) < RedCoreTarget := by
    rw [RedCoreTarget, Ordinal.one_lt_opow]
    exact ⟨one_lt_omega0.trans_le (Ordinal.omega0_le_omega 1), by simp⟩
  rw [← hzero] at honeLt
  exact (not_lt_zero honeLt)

/-- Every displayed candidate in the gap really fails the exact
second-maximum predicate.  The failure is stronger than a single bad
edge: blue witnesses occur strictly cofinally in the fused core. -/
theorem BHTSecondMaximumGap.not_secondMaximumExtension_at
    {red blue : SimpleGraph W2} (gap : BHTSecondMaximumGap red blue)
    (hcompl : IsCompl red blue) {y : W2} (hy : y ∈ gap.candidates) :
    ¬ (gap.fusion.firstMaximum < y ∧
      red.Adj gap.fusion.firstMaximum y ∧
      ∀ x ∈ gap.fusion.core, red.Adj x y) := by
  intro hext
  obtain ⟨x₀, hx₀⟩ :=
    nonempty_of_typeLT_eq_redCoreTarget gap.fusion.core_type
  obtain ⟨x, hx, _hx₀x, hblue⟩ :=
    gap.blue_core_strictlyCofinal y hy x₀ hx₀
  have hred : red.Adj x y := hext.2.2 x hx
  rw [← hcompl.compl_eq, SimpleGraph.compl_adj] at hblue
  exact hblue.2 hred

/-- What minimal-block/point freezing actually yields from the failure of
the second-maximum reservoir.  One point of the fused red core is blue to
an `alephTwo` candidate fiber.  CH thins that fiber to a blue
`omegaOne + 1` arm, but the fixed point is earlier than the arm, so the
extra prefix is ordinally absorbed and still does not have type
`omegaOne + 2`. -/
structure BHTFrozenSecondMaximumFailure
    (red blue : SimpleGraph W2) : Type 1 where
  gap : BHTSecondMaximumGap red blue
  center : gap.fusion.core
  failureFiber : Set W2
  failureFiber_card : #failureFiber = ℵ_ 2
  failureFiber_sub : failureFiber ⊆ gap.candidates
  center_blue_failureFiber :
    ∀ y ∈ failureFiber, blue.Adj (center : W2) y
  blueArm : Set W2
  blueArm_sub : blueArm ⊆ failureFiber
  blueArm_blue : blue.IsClique blueArm
  blueArm_type : typeLT blueArm = ω_ 1 + 1
  center_before_blueArm : ∀ y ∈ blueArm, (center : W2) < y
  center_blue_blueArm : ∀ y ∈ blueArm, blue.Adj (center : W2) y
  center_insert_blue : blue.IsClique (Set.insert (center : W2) blueArm)
  prefix_absorbed :
    (1 : Ordinal.{0}) + typeLT blueArm = ω_ 1 + 1

/-- Pigeonhole already freezes the failed BHT extension to one core
point; CH then supplies the strongest blue arm available from the current
asymmetric theorem.  The final arithmetic field records why this familiar
move stops one successor short. -/
noncomputable def BHTSecondMaximumGap.to_frozenFailure
    {red blue : SimpleGraph W2} (gap : BHTSecondMaximumGap red blue)
    (hCH : CH) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget) :
    BHTFrozenSecondMaximumFailure red blue := by
  classical
  have hcoreNonempty : gap.fusion.core.Nonempty :=
    nonempty_of_typeLT_eq_redCoreTarget gap.fusion.core_type
  let anchor := Classical.choose hcoreNonempty
  have hanchor := Classical.choose_spec hcoreNonempty
  have hwitness (y : gap.candidates) :
      ∃ x : gap.fusion.core, blue.Adj x y := by
    obtain ⟨x, hx, _hanchorx, hblue⟩ :=
      gap.blue_core_strictlyCofinal (y : W2) y.property
        anchor hanchor
    exact ⟨⟨x, hx⟩, hblue⟩
  let failure : gap.candidates → gap.fusion.core :=
    fun y ↦ Classical.choose (hwitness y)
  have hfailure (y : gap.candidates) :
      blue.Adj (failure y) y :=
    Classical.choose_spec (hwitness y)
  have hcoreCard : #gap.fusion.core = ℵ_ 1 := by
    have hc := congrArg Ordinal.card gap.fusion.core_type
    simpa only [Ordinal.card_type, card_redCoreTarget] using hc
  have hcenterExists := Cardinal.infinite_pigeonhole failure
    (by
      rw [gap.candidates_card]
      exact Cardinal.aleph0_le_aleph 2)
    (by
      rw [hcoreCard, gap.candidates_card]
      rw [show (ℵ_ 2 : Cardinal.{0}) =
          ℵ_ ((1 : Ordinal.{0}) + 1) by norm_num,
        (Cardinal.isRegular_aleph_add_one 1).cof_ord]
      exact Cardinal.aleph_lt_aleph.mpr (by norm_num))
  let center := Classical.choose hcenterExists
  have hlargeFiber := Classical.choose_spec hcenterExists
  let failureFiber : Set W2 :=
    Subtype.val '' (failure ⁻¹' {center})
  have hfailureFiberCard : #failureFiber = ℵ_ 2 := by
    calc
      #failureFiber = #(failure ⁻¹' {center}) :=
        Cardinal.mk_image_eq Subtype.val_injective
      _ = #gap.candidates := hlargeFiber
      _ = ℵ_ 2 := gap.candidates_card
  have hfailureFiberSub : failureFiber ⊆ gap.candidates := by
    rintro y ⟨z, _hz, rfl⟩
    exact z.property
  have hcenterBlue :
      ∀ y ∈ failureFiber, blue.Adj (center : W2) y := by
    rintro y ⟨z, hz, rfl⟩
    have hzc : failure z = center := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
    simpa only [hzc] using hfailure z
  have hblueArmExists :=
    Erdos1172Part3CHAsymmetric.exists_blue_omegaOne_add_one_in_every_alephTwo_set
      hCH red blue hcompl hnoRed hfailureFiberCard
  let blueArm := Classical.choose hblueArmExists
  have hblueArmSpec := Classical.choose_spec hblueArmExists
  have hblueArmSub := hblueArmSpec.1
  have hblueArmBlue := hblueArmSpec.2.1
  have hblueArmType := hblueArmSpec.2.2
  have hcenterBeforeBlueArm :
      ∀ y ∈ blueArm, (center : W2) < y := by
    intro y hy
    exact (gap.fusion.core_before_first center center.property).trans
      (gap.first_before_candidates y
        (hfailureFiberSub (hblueArmSub hy)))
  have hcenterBlueBlueArm :
      ∀ y ∈ blueArm, blue.Adj (center : W2) y := by
    intro y hy
    exact hcenterBlue y (hblueArmSub hy)
  have hcenterInsertBlue :
      blue.IsClique (Set.insert (center : W2) blueArm) := by
    apply hblueArmBlue.insert
    intro y hy _
    exact hcenterBlueBlueArm y hy
  exact {
    gap := gap
    center := center
    failureFiber := failureFiber
    failureFiber_card := hfailureFiberCard
    failureFiber_sub := hfailureFiberSub
    center_blue_failureFiber := hcenterBlue
    blueArm := blueArm
    blueArm_sub := hblueArmSub
    blueArm_blue := hblueArmBlue
    blueArm_type := hblueArmType
    center_before_blueArm := hcenterBeforeBlueArm
    center_blue_blueArm := hcenterBlueBlueArm
    center_insert_blue := hcenterInsertBlue
    prefix_absorbed := by
      rw [hblueArmType]
      exact one_add_omegaOne_add_one_eq }

/-- The red-maximum branch of the existing terminal obstruction is
exactly a BHT second-maximum gap.  No stationarity or profile repetition
is added here: all fields are projections of the already proved
distinguished tail. -/
noncomputable def
    BHTConditionalRedMaximumTailDefectObstruction.to_bhtSecondMaximumGap
    {red blue : SimpleGraph W2}
    (obstruction :
      BHTConditionalRedMaximumTailDefectObstruction red blue) :
    BHTSecondMaximumGap red blue := by
  let obs := obstruction.terminalObstruction
  let tail := obstruction.distinguishedTail
  let core : Set W2 := nearArmCore obs.chain tail.stage
  let firstMaximum : W2 := nearArmTerminal obs.chain tail.stage
  have hfirstMaximumEq : firstMaximum = obs.blueMaximum := by
    exact tail.stage_terminal_eq_blueMaximum
  let candidateTerminals : Set W2 :=
    (fun b : LaterIndex tail.stage ↦
      nearArmTerminal obs.chain (b : W2)) '' tail.indexFiber
  have hcandidateTerminals : candidateTerminals = tail.terminalFiber := by
    exact tail.indexed_terminal_image
  have hcoreRed : red.IsClique core :=
    (obs.chain.arm_red (nearArmStage tail.stage)).subset
      (fun _ hx ↦ hx.1)
  have hcoreBeforeFirst : ∀ x ∈ core, x < firstMaximum := by
    intro x hx
    exact hx.2
  have hcoreRedFirst : ∀ x ∈ core, red.Adj x firstMaximum := by
    intro x hx
    exact obs.chain.arm_red (nearArmStage tail.stage)
      hx.1 (nearArmTerminal_mem obs.chain tail.stage)
        (hcoreBeforeFirst x hx).ne
  let fusion : BHTFinalFusionCore red := {
    core := core
    firstMaximum := firstMaximum
    core_red := hcoreRed
    core_type := tail.core_type
    core_before_first := hcoreBeforeFirst
    core_red_first := hcoreRedFirst }
  have hcandidatesCard : #candidateTerminals = ℵ_ 2 := by
    rw [hcandidateTerminals]
    exact tail.terminalFiber_card
  have hfirstBefore :
      ∀ y ∈ candidateTerminals, firstMaximum < y := by
    intro y hy
    rw [hcandidateTerminals] at hy
    rw [hfirstMaximumEq]
    change obstruction.terminalObstruction.blueMaximum < y
    exact (tail.terminalFiber_sub hy).2
  have hfirstRed :
      ∀ y ∈ candidateTerminals, red.Adj firstMaximum y := by
    intro y hy
    rw [hcandidateTerminals] at hy
    rw [hfirstMaximumEq]
    change red.Adj obstruction.terminalObstruction.blueMaximum y
    exact tail.maximum_red_on_terminalFiber y hy
  have hstrict :
      ∀ y ∈ candidateTerminals,
        StrictlyCofinalBlueColumn blue core y := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    exact tail.blueSection_strictlyCofinal b hb
  have hblueCard :
      ∀ y ∈ candidateTerminals,
        #(blueColumn blue core y) = ℵ_ 1 := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    exact tail.blueSection_card b hb
  have hlaterRedSub : tail.redNearArm ⊆ candidateTerminals := by
    rw [hcandidateTerminals]
    exact tail.redNearArm_sub
  exact {
    fusion := fusion
    candidates := candidateTerminals
    candidates_card := hcandidatesCard
    first_before_candidates := hfirstBefore
    first_red_candidates := hfirstRed
    blue_core_strictlyCofinal := hstrict
    blue_core_card := hblueCard
    laterRedArm := tail.redNearArm
    laterRedArm_sub := hlaterRedSub
    laterRedArm_red := tail.redNearArm_red
    laterRedArm_type := tail.redNearArm_type
    prefix_absorbed := tail.prefix_absorbed }

/-- Global BHT-conditional reduction exposing the precise `+2` gap.
Outside the two exact targets and the already isolated ordered blue
rectangle, the same coloring carries the second-maximum obstruction above.
This theorem deliberately does not assert that the obstruction is
impossible. -/
theorem part3_exact_or_orderedBlueRectangle_or_bhtSecondMaximumGap
    (hGCH : GCH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      OrderedBlueOmegaOneByOmegaOneAddOneRedRectangle red blue ∨
      Nonempty (BHTSecondMaximumGap red blue) := by
  obtain hexact | hrectangle | hobstruction :=
    part3_exact_or_bhtConditionalRedMaximumTailDefect
      hGCH hBHT red blue hcompl
  · exact Or.inl hexact
  · exact Or.inr (Or.inl hrectangle)
  · obtain ⟨obstruction⟩ := hobstruction
    exact Or.inr (Or.inr
      ⟨BHTConditionalRedMaximumTailDefectObstruction.to_bhtSecondMaximumGap
        obstruction⟩)

end Erdos1172Part3BHTSecondMaximumGap
