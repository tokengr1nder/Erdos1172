/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OneSuccessorFullFiberChain
public import Erdos1172.Part3OmegaOneRectangleRefinement
public import Erdos1172.Part3TransversalPredecessorPattern

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OneSuccessorTerminalSplit

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3CHAsymmetric
  Erdos1172Part3OneSuccessorBarrier
  Erdos1172Part3OneSuccessorFullFiberChain
  Erdos1172Part3OmegaOneRectangleRefinement

/-- The exact predecessor core of the chosen blue terminal maximum. -/
def terminalBlueCore
    {red blue : SimpleGraph W2}
    (obs : BHTConditionalTerminalPrefixObstruction red blue) : Set W2 :=
  {x | x ∈ obs.blueTerminals ∧ x < obs.blueMaximum}

/-- The red-to-maximum alternative in the sharp terminal-color split.
The large later terminal fiber and its BHT red near-arm are retained.
The maximum is a common earlier red neighbor of the arm, but the displayed
left-prefix arithmetic is absorbed at `RedNearTarget`. -/
def TerminalMaximumRedNearArm
    (red blue : SimpleGraph W2)
    (obs : BHTConditionalTerminalPrefixObstruction red blue) : Prop :=
  ∃ (fiber arm : Set W2),
    #fiber = ℵ_ 2 ∧
    fiber ⊆ Set.range obs.terminal ∩ Set.Ioi obs.blueMaximum ∧
    (∀ y ∈ fiber, red.Adj obs.blueMaximum y) ∧
    arm ⊆ fiber ∧ red.IsClique arm ∧
    typeLT arm = RedNearTarget ∧
    (∀ y ∈ arm, obs.blueMaximum < y) ∧
    red.IsClique (Set.insert obs.blueMaximum arm) ∧
    (1 : Ordinal.{0}) + typeLT arm = RedNearTarget

/-- Removing the certified maximum from the blue terminal clique leaves
an exact `omegaOne` core. -/
theorem terminalBlueCore_type
    {red blue : SimpleGraph W2}
    (obs : BHTConditionalTerminalPrefixObstruction red blue) :
    typeLT (terminalBlueCore obs) = ω_ 1 := by
  have hcoreLater :
      ∀ x ∈ terminalBlueCore obs, x < obs.blueMaximum :=
    fun _ hx ↦ hx.2
  have hbaseEq :
      obs.blueTerminals =
        Set.insert obs.blueMaximum (terminalBlueCore obs) := by
    ext x
    constructor
    · intro hx
      rcases (obs.blueMaximum_max x hx).eq_or_lt with hxm | hxm
      · exact Set.mem_insert_iff.mpr (Or.inl hxm)
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨hx, hxm⟩)
    · intro hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact obs.blueMaximum_mem
      · exact hx.1
  have hsucc :
      typeLT (terminalBlueCore obs) + (1 : Ordinal) = ω_ 1 + 1 := by
    calc
      typeLT (terminalBlueCore obs) + 1 =
          typeLT (Set.insert obs.blueMaximum
            (terminalBlueCore obs) : Set W2) :=
        (Ordinal.typeLT_insert_of_forall_lt hcoreLater).symm
      _ = typeLT obs.blueTerminals :=
        congrArg (fun s : Set W2 ↦ typeLT s) hbaseEq.symm
      _ = ω_ 1 + 1 := obs.blueTerminals_type
  apply (Ordinal.add_right_cancel
    (a := typeLT (terminalBlueCore obs)) (b := (ω_ 1 : Ordinal)) 1).mp
  simpa only [Nat.cast_one] using hsucc

/-- The blue predecessor core has cardinality `alephOne`. -/
theorem terminalBlueCore_card
    {red blue : SimpleGraph W2}
    (obs : BHTConditionalTerminalPrefixObstruction red blue) :
    #(terminalBlueCore obs) = ℵ_ 1 := by
  have hc := congrArg Ordinal.card (terminalBlueCore_type obs)
  simpa only [Ordinal.card_type, Ordinal.card_omega] using hc

private theorem mk_sdiff_eq_alephTwo
    {s t : Set W2} (hs : #s = ℵ_ 2) (ht : #t < ℵ_ 2) :
    #(s \ t : Set W2) = ℵ_ 2 := by
  apply le_antisymm
  · simpa only [hs] using Cardinal.mk_le_mk_of_subset
      (Set.sdiff_subset : s \ t ⊆ s)
  · by_contra h
    have hdiff : #(s \ t : Set W2) < ℵ_ 2 := lt_of_not_ge h
    have hcover : ℵ_ 2 ≤ #(s \ t : Set W2) + #t := by
      simpa only [hs] using Cardinal.le_mk_sdiff_add_mk s t
    exact (not_lt_of_ge hcover) <|
      Cardinal.add_lt_of_lt (Cardinal.aleph0_le_aleph 2) hdiff ht

private theorem mk_sdiff_eq_alephOne
    {s t : Set W2} (hs : #s = ℵ_ 1) (ht : #t ≤ ℵ₀) :
    #(s \ t : Set W2) = ℵ_ 1 := by
  have htlt : #t < ℵ_ 1 :=
    ht.trans_lt Cardinal.aleph0_lt_aleph_one
  apply le_antisymm
  · simpa only [hs] using Cardinal.mk_le_mk_of_subset
      (Set.sdiff_subset : s \ t ⊆ s)
  · by_contra h
    have hdiff : #(s \ t : Set W2) < ℵ_ 1 := lt_of_not_ge h
    have hcover : ℵ_ 1 ≤ #(s \ t : Set W2) + #t := by
      simpa only [hs] using Cardinal.le_mk_sdiff_add_mk s t
    exact (not_lt_of_ge hcover) <|
      Cardinal.add_lt_of_lt (Cardinal.aleph0_le_aleph 1) hdiff htlt

private theorem typeLT_eq_omegaOne_of_mk_eq_of_subset
    {small large : Set W2} (hsmallCard : #small = ℵ_ 1)
    (hsmallSub : small ⊆ large) (hlargeType : typeLT large = ω_ 1) :
    typeLT small = ω_ 1 := by
  apply le_antisymm
  · exact (Ordinal.type_mono hsmallSub).trans_eq hlargeType
  · calc
      ω_ 1 = (ℵ_ 1 : Cardinal).ord := (Cardinal.ord_aleph 1).symm
      _ = (#small).ord := congrArg Cardinal.ord hsmallCard.symm
      _ ≤ typeLT small :=
        Cardinal.ord_le_type ((· < ·) : small → small → Prop)

/-- The sharp maximum-color refinement of the BHT terminal obstruction.
Either the chosen terminal maximum is red to a full later terminal fiber,
where BHT supplies an absorbable red near-arm, or CH compresses the
countable blue-neighborhood profiles on its exact `omegaOne` predecessor
core and yields the existing ordered blue-by-blue red rectangle. -/
theorem BHTConditionalTerminalPrefixObstruction.terminalMaximumRedNearArm_or_orderedBlueRectangle
    {red blue : SimpleGraph W2}
    (obs : BHTConditionalTerminalPrefixObstruction red blue)
    (hCH : CH) (hBHT : BHTNearPart3Relation)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    TerminalMaximumRedNearArm red blue obs ∨
      OrderedBlueOmegaOneByOmegaOneAddOneRedRectangle red blue := by
  classical
  let core : Set W2 := terminalBlueCore obs
  have hcoreType : typeLT core = ω_ 1 := terminalBlueCore_type obs
  have hcoreCard : #core = ℵ_ 1 := terminalBlueCore_card obs
  have hcoreSub : core ⊆ obs.blueTerminals := fun _ hx ↦ hx.1
  have hcoreBlue : blue.IsClique core :=
    obs.blueTerminals_blue.subset hcoreSub
  have hcoreBefore : ∀ x ∈ core, x < obs.blueMaximum :=
    fun _ hx ↦ hx.2
  have hcoreNonempty : core.Nonempty := by
    apply Cardinal.mk_set_ne_zero_iff.mp
    rw [hcoreCard]
    exact (Cardinal.aleph_pos 1).ne'
  let _ : Nonempty core := hcoreNonempty.to_subtype
  have hterminalCard : #(Set.range obs.terminal) = ℵ_ 2 := by
    have hc := congrArg Ordinal.card obs.terminal_range_type
    simpa only [Ordinal.card_type, Ordinal.card_omega] using hc
  let later : Set W2 :=
    Set.range obs.terminal ∩ Set.Ioi obs.blueMaximum
  have hlaterCard : #later = ℵ_ 2 :=
    mk_inter_Ioi_eq_alephTwo hterminalCard obs.blueMaximum
  let redFiber : Set W2 :=
    {y | y ∈ later ∧ red.Adj obs.blueMaximum y}
  have hredFiberSub : redFiber ⊆ later := fun _ hy ↦ hy.1
  have hredFiberLe : #redFiber ≤ ℵ_ 2 := by
    simpa only [hlaterCard] using
      Cardinal.mk_le_mk_of_subset hredFiberSub
  by_cases hredFiberCard : #redFiber = ℵ_ 2
  · have hredFiberType : typeLT redFiber = ω_ 2 :=
      typeLT_eq_omegaTwo_of_mk_eq hredFiberCard
    obtain ⟨arm, harmSub, harmRed, harmType⟩ |
        ⟨target, _htargetSub, htargetBlue, htargetType⟩ :=
      OrdinalRamsey.on_set_of_type hBHT red blue hcompl
        redFiber hredFiberType
    · have hmaximumRed :
          ∀ y ∈ redFiber, red.Adj obs.blueMaximum y :=
        fun _ hy ↦ hy.2
      have hmaximumBefore :
          ∀ y ∈ arm, obs.blueMaximum < y := by
        intro y hy
        exact (hredFiberSub (harmSub hy)).2
      have hinsertRed :
          red.IsClique (Set.insert obs.blueMaximum arm) := by
        apply harmRed.insert
        intro y hy _
        exact hmaximumRed y (harmSub hy)
      left
      exact ⟨redFiber, arm, hredFiberCard, hredFiberSub,
        hmaximumRed, harmSub, harmRed, harmType, hmaximumBefore,
        hinsertRed, by
          rw [harmType]
          exact one_add_redNearTarget_eq⟩
    · exact (hnoBlue ⟨target, htargetBlue, htargetType⟩).elim
  · have hredFiberLt : #redFiber < ℵ_ 2 :=
      lt_of_le_of_ne hredFiberLe hredFiberCard
    let blueFiber : Set W2 := later \ redFiber
    have hblueFiberCard : #blueFiber = ℵ_ 2 :=
      mk_sdiff_eq_alephTwo hlaterCard hredFiberLt
    have hblueFiberSub : blueFiber ⊆ later := Set.sdiff_subset
    have hmaximumBlue :
        ∀ y ∈ blueFiber, blue.Adj obs.blueMaximum y := by
      intro y hy
      let maximum : W2 := obs.blueMaximum
      change blue.Adj maximum y
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      exact ⟨(show maximum < y from (hblueFiberSub hy).2).ne,
        fun hred ↦ hy.2 ⟨hblueFiberSub hy,
          show red.Adj obs.blueMaximum y from hred⟩⟩
    let neighborhood : blueFiber → Set core := fun y ↦
      {x | blue.Adj (x : W2) (y : W2)}
    have hneighborhoodSmall (y : blueFiber) :
        #(neighborhood y) ≤ ℵ₀ := by
      apply Cardinal.lt_aleph_one_iff.mp
      apply lt_of_le_of_ne
      · exact (Cardinal.mk_set_le (neighborhood y)).trans_eq hcoreCard
      · intro hneighborCard
        let values : Set W2 :=
          Subtype.val '' (neighborhood y)
        have hvaluesCard : #values = ℵ_ 1 := by
          calc
            #values = #(neighborhood y) :=
              Cardinal.mk_image_eq Subtype.val_injective
            _ = ℵ_ 1 := hneighborCard
        have hvaluesSub : values ⊆ core := by
          rintro _ ⟨x, _hx, rfl⟩
          exact x.property
        have hvaluesType : typeLT values = ω_ 1 :=
          typeLT_eq_omegaOne_of_mk_eq_of_subset
            hvaluesCard hvaluesSub hcoreType
        have hvaluesBlue : blue.IsClique values :=
          hcoreBlue.subset hvaluesSub
        have hvaluesBeforeMaximum :
            ∀ x ∈ values, x < obs.blueMaximum :=
          fun x hx ↦ hcoreBefore x (hvaluesSub hx)
        have hvaluesMaximumBlue :
            ∀ x ∈ values, blue.Adj x obs.blueMaximum := by
          intro x hx
          exact obs.blueTerminals_blue
            (hcoreSub (hvaluesSub hx)) obs.blueMaximum_mem
              (hvaluesBeforeMaximum x hx).ne
        let withMaximum : Set W2 :=
          Set.insert obs.blueMaximum values
        have hwithMaximumBlue : blue.IsClique withMaximum := by
          apply hvaluesBlue.insert
          intro x hx _
          rw [blue.adj_comm]
          exact hvaluesMaximumBlue x hx
        have hwithMaximumType :
            typeLT withMaximum = ω_ 1 + 1 := by
          calc
            typeLT withMaximum = typeLT values + 1 :=
              Ordinal.typeLT_insert_of_forall_lt hvaluesBeforeMaximum
            _ = ω_ 1 + 1 := by rw [hvaluesType]
        have hwithMaximumBeforeY :
            ∀ x ∈ withMaximum, x < (y : W2) := by
          intro x hx
          simp only [withMaximum] at hx
          rcases hx with rfl | hx
          · exact (hblueFiberSub y.property).2
          · exact (hvaluesBeforeMaximum x hx).trans
              (hblueFiberSub y.property).2
        have hwithMaximumAdjY :
            ∀ x ∈ withMaximum, blue.Adj x (y : W2) := by
          intro x hx
          simp only [withMaximum] at hx
          rcases hx with rfl | hx
          · exact hmaximumBlue y y.property
          · rcases hx with ⟨z, hz, rfl⟩
            exact hz
        obtain ⟨target, htargetBlue, htargetType⟩ :=
          blue.exists_clique_type_add_one_of_common_later
            hwithMaximumBlue hwithMaximumType
              hwithMaximumBeforeY hwithMaximumAdjY
        apply hnoBlue
        refine ⟨target, htargetBlue, ?_⟩
        calc
          typeLT target = (ω_ 1 + 1) + 1 := htargetType
          _ = ω_ 1 + 2 := by norm_num [add_assoc]
    have hneighborhoodCountable (y : blueFiber) :
        (neighborhood y).Countable :=
      Cardinal.le_aleph0_iff_set_countable.mp (hneighborhoodSmall y)
    have hprofileExists (y : blueFiber) :
        ∃ profile : ℕ → core,
          neighborhood y ⊆ Set.range profile :=
      Set.countable_iff_exists_subset_range.mp
        (hneighborhoodCountable y)
    let profile : blueFiber → ℕ → core := fun y ↦
      Classical.choose (hprofileExists y)
    have hprofileCovers (y : blueFiber) :
        neighborhood y ⊆ Set.range (profile y) :=
      Classical.choose_spec (hprofileExists y)
    obtain ⟨fixedProfile, hfixedProfileFiberCard⟩ :=
      Erdos1172Part3TransversalPredecessorPattern.exists_alephTwo_fiber_of_countable_alephOne_profile
        hCH (fun _ : ℕ ↦ core) hblueFiberCard
          (fun _ ↦ hcoreCard) profile
    let uniformFiber : Set W2 :=
      Subtype.val '' (profile ⁻¹' {fixedProfile})
    have huniformFiberCard : #uniformFiber = ℵ_ 2 := by
      calc
        #uniformFiber = #(profile ⁻¹' {fixedProfile}) :=
          Cardinal.mk_image_eq Subtype.val_injective
        _ = ℵ_ 2 := hfixedProfileFiberCard
    have huniformFiberSub : uniformFiber ⊆ blueFiber := by
      rintro _ ⟨y, _hy, rfl⟩
      exact y.property
    let deleted : Set W2 :=
      Set.range (fun n : ℕ ↦ (fixedProfile n : W2))
    have hdeletedCard : #deleted ≤ ℵ₀ := by
      simpa [deleted] using Cardinal.mk_range_le_lift
        (f := fun n : ℕ ↦ (fixedProfile n : W2))
    let left : Set W2 := core \ deleted
    have hleftCard : #left = ℵ_ 1 :=
      mk_sdiff_eq_alephOne hcoreCard hdeletedCard
    have hleftSub : left ⊆ core := Set.sdiff_subset
    have hleftBlue : blue.IsClique left :=
      hcoreBlue.subset hleftSub
    have hleftType : typeLT left = ω_ 1 :=
      typeLT_eq_omegaOne_of_mk_eq_of_subset
        hleftCard hleftSub hcoreType
    have hleftBeforeUniform :
        ∀ x ∈ left, ∀ y ∈ uniformFiber, x < y := by
      intro x hx y hy
      exact (hcoreBefore x (hleftSub hx)).trans
        (hblueFiberSub (huniformFiberSub hy)).2
    have hcrossRed :
        ∀ x ∈ left, ∀ y ∈ uniformFiber, red.Adj x y := by
      intro x hx y hy
      have hxy : x < y := hleftBeforeUniform x hx y hy
      have hnblue : ¬ blue.Adj x y := by
        intro hblue
        rcases hy with ⟨z, hz, rfl⟩
        have hprofileEq : profile z = fixedProfile := by
          simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
        let xcore : core := ⟨x, hleftSub hx⟩
        have hxNeighbor : xcore ∈ neighborhood z := hblue
        obtain ⟨n, hn⟩ := hprofileCovers z hxNeighbor
        apply hx.2
        refine ⟨n, ?_⟩
        have hfixedValue : fixedProfile n = xcore := by
          rw [← hprofileEq]
          exact hn
        exact congrArg Subtype.val hfixedValue
      rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
      exact ⟨hxy.ne, hnblue⟩
    obtain ⟨right, hrightSub, hrightBlue, hrightType⟩ :=
      exists_blue_omegaOne_add_one_in_every_alephTwo_set
        hCH red blue hcompl hnoRed huniformFiberCard
    right
    exact ⟨left, right, hleftBlue, hleftType,
      hrightBlue, hrightType,
      (fun x hx y hy ↦ hleftBeforeUniform x hx y (hrightSub hy)),
      fun x hx y hy ↦ hcrossRed x hx y (hrightSub hy)⟩

/-- Explicitly BHT-conditional global wrapper.  Outside the exact Part 3
targets, the whole full-fiber obstruction is retained together with its
sharp terminal maximum split. -/
theorem part3_exact_or_bhtConditionalTerminalMaximumSplit
    (hCH : CH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      ∃ obs : BHTConditionalTerminalPrefixObstruction red blue,
        TerminalMaximumRedNearArm red blue obs ∨
          OrderedBlueOmegaOneByOmegaOneAddOneRedRectangle red blue := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · have hnone := not_or.mp htarget
    obtain hexact | hobs :=
      part3_exact_or_bhtConditionalTerminalPrefixObstruction
        hCH hBHT red blue hcompl
    · exact (htarget hexact).elim
    · obtain ⟨obs⟩ := hobs
      right
      exact ⟨obs,
        Erdos1172Part3OneSuccessorTerminalSplit.BHTConditionalTerminalPrefixObstruction.terminalMaximumRedNearArm_or_orderedBlueRectangle
          obs hCH hBHT hcompl hnone.1 hnone.2⟩

end Erdos1172Part3OneSuccessorTerminalSplit
