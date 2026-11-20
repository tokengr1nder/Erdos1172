/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CHUniformRectangles
public import Erdos1172.Part3CountableLimit

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3BlueRectangleFullLoss

open Erdos1172Part3Failure Erdos1172Part3CHAsymmetric

/-- The unresolved red-color branch of countable profile compression. -/
def UniformRedRectangle (red blue : SimpleGraph W2) : Prop :=
  ∃ (m : W2) (centers : ℕ → W2) (arm fiber : Set W2),
    StrictMono centers ∧ typeLT (Set.range centers) = ω ∧
    blue.IsClique (Set.range centers) ∧
    #fiber = ℵ_ 2 ∧ fiber ⊆ Set.Ioi m ∧
    arm ⊆ fiber ∧ blue.IsClique arm ∧ typeLT arm = ω_ 1 + 1 ∧
    ∀ i, ∀ x ∈ fiber, red.Adj (centers i) x

/-- The complete-blue-rectangle branch, sharpened past its first full
loss.  Besides the original blue `ω`-by-`ℵ₂` rectangle, it contains two
ordered blue arms of type `ω₁ + 1`; one point of the first arm is
red-adjacent to every point of the second. -/
def BlueRectangleFailureChain (red blue : SimpleGraph W2) : Prop :=
  ∃ (m : W2) (centers : ℕ → W2) (firstArm fiber : Set W2),
    StrictMono centers ∧ typeLT (Set.range centers) = ω ∧
    blue.IsClique (Set.range centers) ∧
    #fiber = ℵ_ 2 ∧ fiber ⊆ Set.Ioi m ∧
    firstArm ⊆ fiber ∧ blue.IsClique firstArm ∧
    typeLT firstArm = ω_ 1 + 1 ∧
    (∀ i, ∀ x ∈ fiber, blue.Adj (centers i) x) ∧
    ∃ (maximum witness : W2) (failureFiber secondArm : Set W2),
      maximum ∈ firstArm ∧ witness ∈ firstArm ∧
      #failureFiber = ℵ_ 2 ∧ failureFiber ⊆ Set.Ioi maximum ∧
      secondArm ⊆ failureFiber ∧ blue.IsClique secondArm ∧
      typeLT secondArm = ω_ 1 + 1 ∧
      (∀ z ∈ firstArm, ∀ x ∈ secondArm, z < x) ∧
      ∀ x ∈ secondArm, red.Adj witness x

/-- Infinite version of the complete-blue-rectangle obstruction.  The
initial uniform rectangle is followed by an `ω`-sequence of strictly
ordered blue arms of type `ω₁ + 1`; each consecutive pair contains a
complete red star from a witness in the earlier arm. -/
def InfiniteBlueRectangleFailureChain (red blue : SimpleGraph W2) : Prop :=
  ∃ (m : W2) (centers : ℕ → W2) (firstArm fiber : Set W2)
      (arms : ℕ → Set W2) (maxima witnesses : ℕ → W2)
      (failureFibers : ℕ → Set W2),
    StrictMono centers ∧ typeLT (Set.range centers) = ω ∧
    blue.IsClique (Set.range centers) ∧
    #fiber = ℵ_ 2 ∧ fiber ⊆ Set.Ioi m ∧
    firstArm ⊆ fiber ∧ blue.IsClique firstArm ∧
    typeLT firstArm = ω_ 1 + 1 ∧
    (∀ i, ∀ x ∈ fiber, blue.Adj (centers i) x) ∧
    arms 0 = firstArm ∧
    (∀ n, blue.IsClique (arms n) ∧ typeLT (arms n) = ω_ 1 + 1) ∧
    (∀ n, maxima n ∈ arms n ∧ witnesses n ∈ arms n) ∧
    (∀ n, #(failureFibers n) = ℵ_ 2 ∧
      failureFibers n ⊆ Set.Ioi (maxima n)) ∧
    (∀ n, arms (n + 1) ⊆ failureFibers n) ∧
    (∀ n, ∀ z ∈ arms n, ∀ x ∈ arms (n + 1), z < x) ∧
    ∀ n, ∀ x ∈ arms (n + 1), red.Adj (witnesses n) x

/-- Ordered form of the large failure-fiber theorem.  The fiber lies
above the maximum of the original blue arm, so it lies strictly after
the whole arm. -/
private theorem exists_ordered_large_red_failure_fiber
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    ∃ (m y : W2) (failureFiber : Set W2),
      m ∈ base ∧ y ∈ base ∧
      #failureFiber = ℵ_ 2 ∧ failureFiber ⊆ Set.Ioi m ∧
      (∀ z ∈ base, ∀ x ∈ failureFiber, z < x) ∧
      ∀ x ∈ failureFiber, red.Adj y x := by
  classical
  obtain ⟨m, hmMax⟩ := exists_max_of_type_omegaOne_add_one hbaseType
  have hlater (x : Set.Ioi (m : W2)) : ∀ y ∈ base, y < (x : W2) := by
    intro y hy
    have hym : (⟨y, hy⟩ : base) ≤ m :=
      le_of_not_gt ((isMax_iff_forall_not_lt.mp hmMax) ⟨y, hy⟩)
    change y ≤ (m : W2) at hym
    exact hym.trans_lt x.property
  have hwitness (x : Set.Ioi (m : W2)) : ∃ y : base, red.Adj y x := by
    by_contra hnone
    have hblueAdj : ∀ y ∈ base, blue.Adj y x := by
      intro y hy
      rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
      refine ⟨(hlater x y hy).ne, ?_⟩
      intro hred
      exact hnone ⟨⟨y, hy⟩, hred⟩
    apply hnoBlue
    obtain ⟨t, ht, htType⟩ :=
      blue.exists_clique_type_add_one_of_common_later
        hbase hbaseType (hlater x) hblueAdj
    refine ⟨t, ht, ?_⟩
    calc
      typeLT t = (ω_ 1 + 1) + 1 := htType
      _ = ω_ 1 + 2 := by norm_num [add_assoc]
  let failure : Set.Ioi (m : W2) → base :=
    fun x ↦ Classical.choose (hwitness x)
  have hfailure (x : Set.Ioi (m : W2)) : red.Adj (failure x) x :=
    Classical.choose_spec (hwitness x)
  have htailCard : #(Set.Ioi (m : W2)) = ℵ_ 2 := mk_Ioi_omegaTwo_eq m
  have hbaseCard : #base = ℵ_ 1 := by
    have hc := congrArg Ordinal.card hbaseType
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  obtain ⟨y, hyfiber⟩ := Cardinal.infinite_pigeonhole failure
    (by rw [htailCard]; exact Cardinal.aleph0_le_aleph 2)
    (by
      rw [hbaseCard, htailCard]
      rw [show (ℵ_ 2 : Cardinal.{0}) = ℵ_ ((1 : Ordinal.{0}) + 1) by norm_num,
        (Cardinal.isRegular_aleph_add_one 1).cof_ord]
      exact Cardinal.aleph_lt_aleph.mpr (by norm_num))
  let failureFiber : Set W2 := Subtype.val '' (failure ⁻¹' {y})
  have hfailureCard : #failureFiber = ℵ_ 2 := by
    calc
      #failureFiber = #(failure ⁻¹' {y}) :=
        Cardinal.mk_image_eq Subtype.val_injective
      _ = #(Set.Ioi (m : W2)) := hyfiber
      _ = ℵ_ 2 := htailCard
  have hfailureTail : failureFiber ⊆ Set.Ioi (m : W2) := by
    rintro x ⟨z, -, rfl⟩
    exact z.property
  have hfailureRed : ∀ x ∈ failureFiber, red.Adj y x := by
    rintro x ⟨z, hz, rfl⟩
    have hzy : failure z = y := by
      simpa only [mem_preimage, mem_singleton_iff] using hz
    simpa only [hzy] using hfailure z
  exact ⟨m, y, failureFiber, m.property, y.property,
    hfailureCard, hfailureTail,
    fun z hz x hx ↦ hlater ⟨x, hfailureTail hx⟩ z hz,
    hfailureRed⟩

private structure BlueArmState (blue : SimpleGraph W2) where
  arm : Set W2
  arm_blue : blue.IsClique arm
  arm_type : typeLT arm = ω_ 1 + 1

private structure BlueArmStepData
    (red blue : SimpleGraph W2) (state : BlueArmState blue) where
  maximum : W2
  witness : W2
  failureFiber : Set W2
  next : BlueArmState blue
  maximum_mem : maximum ∈ state.arm
  witness_mem : witness ∈ state.arm
  failure_card : #failureFiber = ℵ_ 2
  failure_tail : failureFiber ⊆ Set.Ioi maximum
  next_sub : next.arm ⊆ failureFiber
  ordered : ∀ z ∈ state.arm, ∀ x ∈ next.arm, z < x
  red_star : ∀ x ∈ next.arm, red.Adj witness x

private theorem blueArmStepData_nonempty
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (state : BlueArmState blue) :
    Nonempty (BlueArmStepData red blue state) := by
  obtain ⟨maximum, witness, failureFiber, hmaximumMem,
      hwitnessMem, hfailureCard, hfailureTail,
      hfailureOrdered, hfailureRed⟩ :=
    exists_ordered_large_red_failure_fiber red blue hcompl
      state.arm_blue state.arm_type hnoBlue
  obtain ⟨nextArm, hnextSub, hnextBlue, hnextType⟩ :=
    exists_blue_omegaOne_add_one_in_every_alephTwo_set
      hCH red blue hcompl hnoRed hfailureCard
  exact ⟨{
    maximum := maximum
    witness := witness
    failureFiber := failureFiber
    next := {
      arm := nextArm
      arm_blue := hnextBlue
      arm_type := hnextType }
    maximum_mem := hmaximumMem
    witness_mem := hwitnessMem
    failure_card := hfailureCard
    failure_tail := hfailureTail
    next_sub := hnextSub
    ordered := fun z hz x hx ↦ hfailureOrdered z hz x (hnextSub hx)
    red_star := fun x hx ↦ hfailureRed x (hnextSub hx) }⟩

private noncomputable def chooseBlueArmStepData
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (state : BlueArmState blue) : BlueArmStepData red blue state :=
  Classical.choice
    (blueArmStepData_nonempty hCH red blue hcompl hnoRed hnoBlue state)

private noncomputable def iterateBlueArmState
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (initial : BlueArmState blue) : ℕ → BlueArmState blue
  | 0 => initial
  | n + 1 =>
      (chooseBlueArmStepData hCH red blue hcompl hnoRed hnoBlue
        (iterateBlueArmState hCH red blue hcompl hnoRed hnoBlue initial n)).next

/-- If both exact targets fail, every blue arm of type `ω₁ + 1`
generates an infinite strictly ordered failure chain.  At each step the
next blue arm again has type `ω₁ + 1`, lies inside an `ℵ₂` failure fiber,
and is completely red-adjacent to one witness in the preceding arm. -/
theorem exists_infinite_ordered_blue_arm_failure_chain
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {firstArm : Set W2} (hfirstBlue : blue.IsClique firstArm)
    (hfirstType : typeLT firstArm = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    ∃ (arms : ℕ → Set W2) (maxima witnesses : ℕ → W2)
        (failureFibers : ℕ → Set W2),
      arms 0 = firstArm ∧
      (∀ n, blue.IsClique (arms n) ∧ typeLT (arms n) = ω_ 1 + 1) ∧
      (∀ n, maxima n ∈ arms n ∧ witnesses n ∈ arms n) ∧
      (∀ n, #(failureFibers n) = ℵ_ 2 ∧
        failureFibers n ⊆ Set.Ioi (maxima n)) ∧
      (∀ n, arms (n + 1) ⊆ failureFibers n) ∧
      (∀ n, ∀ z ∈ arms n, ∀ x ∈ arms (n + 1), z < x) ∧
      ∀ n, ∀ x ∈ arms (n + 1), red.Adj (witnesses n) x := by
  classical
  let initial : BlueArmState blue := {
    arm := firstArm
    arm_blue := hfirstBlue
    arm_type := hfirstType }
  let states : ℕ → BlueArmState blue :=
    iterateBlueArmState hCH red blue hcompl hnoRed hnoBlue initial
  let data (n : ℕ) : BlueArmStepData red blue (states n) :=
    chooseBlueArmStepData hCH red blue hcompl hnoRed hnoBlue (states n)
  let arms : ℕ → Set W2 := fun n ↦ (states n).arm
  let maxima : ℕ → W2 := fun n ↦ (data n).maximum
  let witnesses : ℕ → W2 := fun n ↦ (data n).witness
  let failureFibers : ℕ → Set W2 := fun n ↦ (data n).failureFiber
  have hstatesZero : states 0 = initial := rfl
  have hstatesSucc (n : ℕ) : states (n + 1) = (data n).next := rfl
  refine ⟨arms, maxima, witnesses, failureFibers, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (states 0).arm = firstArm
    rw [hstatesZero]
  · intro n
    exact ⟨(states n).arm_blue, (states n).arm_type⟩
  · intro n
    exact ⟨(data n).maximum_mem, (data n).witness_mem⟩
  · intro n
    exact ⟨(data n).failure_card, (data n).failure_tail⟩
  · intro n
    change (states (n + 1)).arm ⊆ (data n).failureFiber
    rw [hstatesSucc]
    exact (data n).next_sub
  · intro n z hz x hx
    change z ∈ (states n).arm at hz
    change x ∈ (states (n + 1)).arm at hx
    rw [hstatesSucc] at hx
    exact (data n).ordered z hz x hx
  · intro n x hx
    change x ∈ (states (n + 1)).arm at hx
    rw [hstatesSucc] at hx
    exact (data n).red_star x hx

/-- A full loss in a countable red-reservoir tower can be classified one
step further under CH.  If the countable limit is not preserved, the
lost `ℵ₂` set contains a first blue `ω₁ + 1` arm.  Failure to append one
blue point then supplies a second, strictly later blue `ω₁ + 1` arm and
a point of the first arm red-adjacent to the whole second arm. -/
theorem countableRedTower_limit_or_full_loss_failure_chain
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (tower : Erdos1172Part3CountableLimit.CountableRedReservoirTower red)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    (∃ (limitReservoir : Set W2) (limitPoint : W2),
      #limitReservoir = ℵ_ 2 ∧
      limitReservoir ⊆ ⋂ n, tower.reservoirs n ∧
      limitPoint ∈ limitReservoir ∧
      (∀ n, ∀ x ∈ limitReservoir, tower.points n < x) ∧
      ∀ n, ∀ x ∈ limitReservoir, red.Adj (tower.points n) x) ∨
      ∃ (n : ℕ) (firstArm : Set W2)
          (maximum witness : W2) (failureFiber secondArm : Set W2),
        #(tower.reservoirs 0 \ tower.reservoirs n : Set W2) = ℵ_ 2 ∧
        firstArm ⊆ tower.reservoirs 0 \ tower.reservoirs n ∧
        blue.IsClique firstArm ∧ typeLT firstArm = ω_ 1 + 1 ∧
        maximum ∈ firstArm ∧ witness ∈ firstArm ∧
        #failureFiber = ℵ_ 2 ∧ failureFiber ⊆ Set.Ioi maximum ∧
        secondArm ⊆ failureFiber ∧ blue.IsClique secondArm ∧
        typeLT secondArm = ω_ 1 + 1 ∧
        (∀ z ∈ firstArm, ∀ x ∈ secondArm, z < x) ∧
        ∀ x ∈ secondArm, red.Adj witness x := by
  obtain hlimit | ⟨n, hloss⟩ := tower.exists_limit_stage_or_full_loss
  · exact Or.inl hlimit
  · right
    obtain ⟨firstArm, hfirstSub, hfirstBlue, hfirstType⟩ :=
      exists_blue_omegaOne_add_one_in_every_alephTwo_set
        hCH red blue hcompl hnoRed hloss
    obtain ⟨maximum, witness, failureFiber, hmaximumMem,
        hwitnessMem, hfailureCard, hfailureTail,
        hfailureOrdered, hfailureRed⟩ :=
      exists_ordered_large_red_failure_fiber red blue hcompl
        hfirstBlue hfirstType hnoBlue
    obtain ⟨secondArm, hsecondSub, hsecondBlue, hsecondType⟩ :=
      exists_blue_omegaOne_add_one_in_every_alephTwo_set
        hCH red blue hcompl hnoRed hfailureCard
    exact ⟨n, firstArm, maximum, witness, failureFiber, secondArm,
      hloss, hfirstSub, hfirstBlue, hfirstType,
      hmaximumMem, hwitnessMem, hfailureCard, hfailureTail,
      hsecondSub, hsecondBlue, hsecondType,
      fun z hz x hx ↦ hfailureOrdered z hz x (hsecondSub hx),
      fun x hx ↦ hfailureRed x (hsecondSub hx)⟩

/-- Under CH, failure of both exact Part 3 targets has a strictly sharper
normal form than a uniform rectangle alone.  A red uniform rectangle
remains, or a blue uniform rectangle necessarily continues through its
first extension failure to an ordered pair of blue `ω₁ + 1` arms with a
complete red star between them. -/
theorem part3_exact_or_red_rectangle_or_blue_failure_chain
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      UniformRedRectangle red blue ∨
      BlueRectangleFailureChain red blue := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red Erdos1172Part3FiniteStars.RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain hexact | ⟨m, centers, firstArm, fiber, hcentersStrict,
        hcentersType, hcentersBlue, hfiberCard, hfiberTail,
        hfirstArmSub, hfirstArmBlue, hfirstArmType, hrectangle⟩ :=
      Erdos1172Part3CHUniformRectangles.part3_exact_or_ordered_omega_by_alephTwo_uniform_rectangle
        hCH red blue hcompl
    · exact (htarget hexact).elim
    · rcases hrectangle with hredRectangle | hblueRectangle
      · left
        exact ⟨m, centers, firstArm, fiber, hcentersStrict,
          hcentersType, hcentersBlue, hfiberCard, hfiberTail,
          hfirstArmSub, hfirstArmBlue, hfirstArmType, hredRectangle⟩
      · right
        obtain ⟨maximum, witness, failureFiber, hmaximumMem,
            hwitnessMem, hfailureCard, hfailureTail,
            hfailureOrdered, hfailureRed⟩ :=
          exists_ordered_large_red_failure_fiber red blue hcompl
            hfirstArmBlue hfirstArmType hnone.2
        obtain ⟨secondArm, hsecondSub, hsecondBlue, hsecondType⟩ :=
          exists_blue_omegaOne_add_one_in_every_alephTwo_set
            hCH red blue hcompl hnone.1 hfailureCard
        exact ⟨m, centers, firstArm, fiber, hcentersStrict,
          hcentersType, hcentersBlue, hfiberCard, hfiberTail,
          hfirstArmSub, hfirstArmBlue, hfirstArmType, hblueRectangle,
          maximum, witness, failureFiber, secondArm,
          hmaximumMem, hwitnessMem, hfailureCard, hfailureTail,
          hsecondSub, hsecondBlue, hsecondType,
          fun z hz x hx ↦ hfailureOrdered z hz x (hsecondSub hx),
          fun x hx ↦ hfailureRed x (hsecondSub hx)⟩

/-- Strongest global form of the blue-rectangle analysis.  If neither
exact Part 3 target occurs, profile compression leaves a red uniform
rectangle, or the blue uniform rectangle continues through every finite
extension failure to an infinite ordered chain of blue `ω₁ + 1` arms. -/
theorem part3_exact_or_red_rectangle_or_infinite_blue_failure_chain
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      UniformRedRectangle red blue ∨
      InfiniteBlueRectangleFailureChain red blue := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red Erdos1172Part3FiniteStars.RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain hexact | ⟨m, centers, firstArm, fiber, hcentersStrict,
        hcentersType, hcentersBlue, hfiberCard, hfiberTail,
        hfirstArmSub, hfirstArmBlue, hfirstArmType, hrectangle⟩ :=
      Erdos1172Part3CHUniformRectangles.part3_exact_or_ordered_omega_by_alephTwo_uniform_rectangle
        hCH red blue hcompl
    · exact (htarget hexact).elim
    · rcases hrectangle with hredRectangle | hblueRectangle
      · left
        exact ⟨m, centers, firstArm, fiber, hcentersStrict,
          hcentersType, hcentersBlue, hfiberCard, hfiberTail,
          hfirstArmSub, hfirstArmBlue, hfirstArmType, hredRectangle⟩
      · right
        obtain ⟨arms, maxima, witnesses, failureFibers, harmsZero,
            harmsBlueType, hmembers, hfailureFibers,
            hnextSub, hordered, hredStars⟩ :=
          exists_infinite_ordered_blue_arm_failure_chain
            hCH red blue hcompl hfirstArmBlue hfirstArmType
              hnone.1 hnone.2
        exact ⟨m, centers, firstArm, fiber, arms, maxima, witnesses,
          failureFibers, hcentersStrict, hcentersType, hcentersBlue,
          hfiberCard, hfiberTail, hfirstArmSub, hfirstArmBlue,
          hfirstArmType, hblueRectangle, harmsZero, harmsBlueType,
          hmembers, hfailureFibers, hnextSub, hordered, hredStars⟩

end Erdos1172Part3BlueRectangleFullLoss
