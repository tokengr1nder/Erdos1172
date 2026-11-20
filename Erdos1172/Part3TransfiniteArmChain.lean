/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3HomogeneousFailureLadder
public import Erdos1172.Part3TransfiniteArmAPI

@[expose] public section

open Cardinal Ordinal Set Function
open Order

namespace Erdos1172Part3TransfiniteArmChain

open Erdos1172Part3Failure Erdos1172Part3BlueRectangleFullLoss

/-- The precise limit-stage hypothesis needed to continue an ordered
blue-arm recursion below an ordinal `κ`.  Given blue `ω₁ + 1` arms at
every earlier stage of a nonzero limit `o < κ`, it supplies a new blue
arm of the same type strictly after all earlier arms. -/
def HasFreshLimitArmsBelow
    (blue : SimpleGraph W2) (κ : Ordinal.{0}) : Prop :=
  ∀ (o : Ordinal.{0}), o < κ → IsSuccLimit o →
    ∀ previous : ∀ o' : Ordinal.{0}, o' < o → Set W2,
      (∀ o' h, blue.IsClique (previous o' h) ∧
        typeLT (previous o' h) = ω_ 1 + 1) →
      ∃ next : Set W2,
        blue.IsClique next ∧ typeLT next = ω_ 1 + 1 ∧
        ∀ o' (h : o' < o), ∀ z ∈ previous o' h,
          ∀ x ∈ next, z < x

private structure ArmState (blue : SimpleGraph W2) where
  arm : Set W2
  arm_blue : blue.IsClique arm
  arm_type : typeLT arm = ω_ 1 + 1

private structure SuccessorData
    (red blue : SimpleGraph W2) (state : ArmState blue) where
  next : ArmState blue
  witness : W2
  witness_mem : witness ∈ state.arm
  ordered : ∀ z ∈ state.arm, ∀ x ∈ next.arm, z < x
  red_star : ∀ x ∈ next.arm, red.Adj witness x

private theorem successorData_nonempty
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (state : ArmState blue) : Nonempty (SuccessorData red blue state) := by
  obtain ⟨arms, maxima, witnesses, failureFibers, harmsZero,
      harmsBlueType, hmembers, -, -, hordered, hredStars⟩ :=
    exists_infinite_ordered_blue_arm_failure_chain
      hCH red blue hcompl state.arm_blue state.arm_type hnoRed hnoBlue
  let next : ArmState blue := {
    arm := arms 1
    arm_blue := (harmsBlueType 1).1
    arm_type := (harmsBlueType 1).2 }
  refine ⟨{
    next := next
    witness := witnesses 0
    witness_mem := ?_
    ordered := ?_
    red_star := ?_ }⟩
  · simpa only [harmsZero] using (hmembers 0).2
  · intro z hz x hx
    apply hordered 0 z
    · simpa only [harmsZero] using hz
    · simpa only [next, Nat.zero_add, Nat.reduceAdd] using hx
  · intro x hx
    simpa only [next, Nat.zero_add, Nat.reduceAdd] using hredStars 0 x hx

private noncomputable def chooseSuccessorData
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (state : ArmState blue) : SuccessorData red blue state :=
  Classical.choice
    (successorData_nonempty hCH red blue hcompl hnoRed hnoBlue state)

private structure LimitData (blue : SimpleGraph W2) (o : Ordinal.{0})
    (previous : ∀ o' : Ordinal.{0}, o' < o → ArmState blue) where
  next : ArmState blue
  ordered : ∀ o' (h : o' < o), ∀ z ∈ (previous o' h).arm,
    ∀ x ∈ next.arm, z < x

private theorem limitData_nonempty
    (blue : SimpleGraph W2) (κ o : Ordinal.{0}) (ho : o < κ)
    (hoLimit : IsSuccLimit o) (hFresh : HasFreshLimitArmsBelow blue κ)
    (previous : ∀ o' : Ordinal.{0}, o' < o → ArmState blue) :
    Nonempty (LimitData blue o previous) := by
  obtain ⟨next, hnextBlue, hnextType, hordered⟩ :=
    hFresh o ho hoLimit (fun o' h ↦ (previous o' h).arm)
      (fun o' h ↦ ⟨(previous o' h).arm_blue,
        (previous o' h).arm_type⟩)
  exact ⟨{
    next := {
      arm := next
      arm_blue := hnextBlue
      arm_type := hnextType }
    ordered := hordered }⟩

private noncomputable def chooseLimitData
    (blue : SimpleGraph W2) (κ o : Ordinal.{0}) (ho : o < κ)
    (hoLimit : IsSuccLimit o) (hFresh : HasFreshLimitArmsBelow blue κ)
    (previous : ∀ o' : Ordinal.{0}, o' < o → ArmState blue) :
    LimitData blue o previous :=
  Classical.choice
    (limitData_nonempty blue κ o ho hoLimit hFresh previous)

/-- Transfinite recursion of blue arms.  Successor stages use the
large failure-fiber step; limit stages use exactly
`HasFreshLimitArmsBelow`. -/
private noncomputable def buildArmState
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (κ : Ordinal.{0})
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (initial : ArmState blue) (hFresh : HasFreshLimitArmsBelow blue κ) :
    ∀ o : Ordinal.{0}, o < κ → ArmState blue := fun o ↦
  Ordinal.limitRecOn o
    (fun _ ↦ initial)
    (fun o previous ho ↦
      (chooseSuccessorData hCH red blue hcompl hnoRed hnoBlue
        (previous ((lt_add_one o).trans ho))).next)
    (fun o hoLimit previous ho ↦
      (chooseLimitData blue κ o ho hoLimit hFresh
        (fun o' h ↦ previous o' h (h.trans ho))).next)

private theorem buildArmState_add_one
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (κ : Ordinal.{0})
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (initial : ArmState blue) (hFresh : HasFreshLimitArmsBelow blue κ)
    (o : Ordinal.{0}) (ho : o + 1 < κ) :
    buildArmState hCH red blue hcompl κ hnoRed hnoBlue initial hFresh
        (o + 1) ho =
      (chooseSuccessorData hCH red blue hcompl hnoRed hnoBlue
        (buildArmState hCH red blue hcompl κ hnoRed hnoBlue initial
          hFresh o ((lt_add_one o).trans ho))).next := by
  simp only [buildArmState, Ordinal.limitRecOn_add_one]

private theorem buildArmState_limit
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (κ : Ordinal.{0})
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (initial : ArmState blue) (hFresh : HasFreshLimitArmsBelow blue κ)
    (o : Ordinal.{0}) (ho : o < κ) (hoLimit : IsSuccLimit o) :
    buildArmState hCH red blue hcompl κ hnoRed hnoBlue initial hFresh o ho =
      (chooseLimitData blue κ o ho hoLimit hFresh
        (fun o' h ↦ buildArmState hCH red blue hcompl κ hnoRed hnoBlue
          initial hFresh o' (h.trans ho))).next := by
  simp only [buildArmState, Ordinal.limitRecOn_limit o _ _ _ hoLimit]

/-- A transfinite ordered chain of blue `ω₁ + 1` arms.  Every two arms
are strictly ordered, and at every successor stage one point of the
earlier arm is red-adjacent to the entire next arm. -/
def TransfiniteBlueArmChain
    (red blue : SimpleGraph W2) (κ : Ordinal.{0}) : Prop :=
  ∃ arms : Set.Iio κ → Set W2,
    (∀ i, blue.IsClique (arms i) ∧ typeLT (arms i) = ω_ 1 + 1) ∧
    (∀ i j, i < j → ∀ z ∈ arms i, ∀ x ∈ arms j, z < x) ∧
    ∀ (o : Ordinal.{0}) (ho : o + 1 < κ),
      ∃ witness : W2,
        witness ∈ arms ⟨o, (lt_add_one o).trans ho⟩ ∧
        ∀ x ∈ arms ⟨o + 1, ho⟩, red.Adj witness x

/-- Transfinite arm recursion from the exact limit-stage hypothesis.
Successor stages require no extra assumption: failure of both exact
Part 3 targets supplies the next ordered blue arm and its red-star
witness.  Thus proving `HasFreshLimitArmsBelow blue κ` is sufficient for
a full chain of length `κ`. -/
theorem exists_transfiniteBlueArmChain_of_freshLimitArms
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (κ : Ordinal.{0}) {firstArm : Set W2}
    (hfirstBlue : blue.IsClique firstArm)
    (hfirstType : typeLT firstArm = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (hFresh : HasFreshLimitArmsBelow blue κ) :
    TransfiniteBlueArmChain red blue κ := by
  classical
  let initial : ArmState blue := {
    arm := firstArm
    arm_blue := hfirstBlue
    arm_type := hfirstType }
  let state : ∀ o : Ordinal.{0}, o < κ → ArmState blue :=
    buildArmState hCH red blue hcompl κ hnoRed hnoBlue initial hFresh
  let arms : Set.Iio κ → Set W2 := fun i ↦ (state i i.property).arm
  have horderedRaw :
      ∀ (j : Ordinal.{0}) (hj : j < κ) (i : Ordinal.{0}) (hij : i < j),
        ∀ z ∈ (state i (hij.trans hj)).arm,
          ∀ x ∈ (state j hj).arm, z < x := by
    intro j
    induction j using Ordinal.limitRecOn with
    | zero =>
        intro hj i hij
        exact (not_lt_zero hij).elim
    | add_one j ih =>
        intro hj i hij z hz x hx
        have hjκ : j < κ := (lt_add_one j).trans hj
        let data : SuccessorData red blue (state j hjκ) :=
          chooseSuccessorData hCH red blue hcompl hnoRed hnoBlue
            (state j hjκ)
        have hstateSucc : state (j + 1) hj = data.next := by
          exact buildArmState_add_one hCH red blue hcompl κ hnoRed
            hnoBlue initial hFresh j hj
        have hxNext : x ∈ data.next.arm := by
          rw [← hstateSucc]
          exact hx
        have hijLe : i ≤ j := (lt_add_one_iff).mp hij
        rcases hijLe.eq_or_lt with hijEq | hijLt
        · subst i
          exact data.ordered z hz x hxNext
        · exact (ih hjκ i hijLt z hz data.witness data.witness_mem).trans
            (data.ordered data.witness data.witness_mem x hxNext)
    | limit j hjLimit ih =>
        intro hj i hij z hz x hx
        let previous : ∀ o' : Ordinal.{0}, o' < j → ArmState blue :=
          fun o' h ↦ state o' (h.trans hj)
        let data : LimitData blue j previous :=
          chooseLimitData blue κ j hj hjLimit hFresh previous
        have hstateLimit : state j hj = data.next := by
          exact buildArmState_limit hCH red blue hcompl κ hnoRed hnoBlue
            initial hFresh j hj hjLimit
        have hxNext : x ∈ data.next.arm := by
          rw [← hstateLimit]
          exact hx
        exact data.ordered i hij z hz x hxNext
  refine ⟨arms, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(state i i.property).arm_blue, (state i i.property).arm_type⟩
  · intro i j hij z hz x hx
    exact horderedRaw j j.property i hij z hz x hx
  · intro o ho
    have hoκ : o < κ := (lt_add_one o).trans ho
    let data : SuccessorData red blue (state o hoκ) :=
      chooseSuccessorData hCH red blue hcompl hnoRed hnoBlue (state o hoκ)
    have hstateSucc : state (o + 1) ho = data.next := by
      exact buildArmState_add_one hCH red blue hcompl κ hnoRed hnoBlue
        initial hFresh o ho
    refine ⟨data.witness, data.witness_mem, ?_⟩
    intro x hx
    apply data.red_star x
    rw [← hstateSucc]
    exact hx

/-- A blue arm of exact type `ω₁ + 1` has cardinality `ℵ₁`. -/
private theorem mk_eq_alephOne_of_typeLT_eq_omegaOne_add_one
    {s : Set W2} (hs : typeLT s = ω_ 1 + 1) : #s = ℵ_ 1 := by
  have hc := congrArg Ordinal.card hs
  simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc

/-- The limit-stage hypothesis is automatic all the way below `ω₂`.
Indeed, before any stage `o < ω₂` there are at most `ℵ₁` earlier arms,
each of cardinality `ℵ₁`; their union, and then its downward closure in
`ω₂`, still has cardinality at most `ℵ₁`.  A point outside that downward
closure is a strict upper bound, and its `ℵ₂` tail contains a new blue
`ω₁ + 1` arm by the CH asymmetric relation. -/
theorem hasFreshLimitArmsBelow_omegaTwo
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget) :
    HasFreshLimitArmsBelow blue (ω_ 2) := by
  classical
  intro o ho hoLimit previous hprevious
  let previousSet : Ordinal.{0} → Set W2 := fun j ↦
    if h : j < o then previous j h else ∅
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
    have hcard : #(previous j hj) = ℵ_ 1 :=
      mk_eq_alephOne_of_typeLT_eq_omegaOne_add_one (hprevious j hj).2
    simpa only [previousSet, dif_pos hj, hcard] using
      (le_refl (ℵ_ 1 : Cardinal.{0}))
  have hcovered : #covered ≤ ℵ_ 1 := by
    apply Cardinal.mk_biUnion_le_of_le hoCard
      (Cardinal.aleph0_le_aleph 1) previousSet
    exact hpreviousCard
  have hcoveredLt : #covered < ℵ_ 2 :=
    hcovered.trans_lt (Cardinal.aleph_lt_aleph.mpr (by norm_num))
  obtain ⟨bound, next, hcoveredBelow, hnextSub,
      hnextBlue, hnextType⟩ :=
    Erdos1172Part3TransfiniteArmAPI.exists_blue_omegaOne_add_one_above_small_family
      hCH red blue hcompl hnoRed (fun z : covered ↦ (z : W2)) hcoveredLt
  refine ⟨next, hnextBlue, hnextType, ?_⟩
  intro j hj z hz x hx
  have hzCovered : z ∈ covered := by
    apply Set.mem_iUnion.mpr
    refine ⟨j, Set.mem_iUnion.mpr ⟨hj, ?_⟩⟩
    simpa only [previousSet, dif_pos hj] using hz
  exact (hcoveredBelow ⟨z, hzCovered⟩).trans (hnextSub hx)

/-- Under CH and failure of both exact Part 3 targets, there is already
an ordered blue-arm chain of full length `ω₂`.  Every arm has exact type
`ω₁ + 1`, and every successor pair retains a complete red-star witness. -/
theorem exists_transfiniteBlueArmChain_omegaTwo
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {firstArm : Set W2} (hfirstBlue : blue.IsClique firstArm)
    (hfirstType : typeLT firstArm = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red
      Erdos1172Part3FiniteStars.RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    TransfiniteBlueArmChain red blue (ω_ 2) :=
  exists_transfiniteBlueArmChain_of_freshLimitArms
    hCH red blue hcompl (ω_ 2) hfirstBlue hfirstType hnoRed hnoBlue
      (hasFreshLimitArmsBelow_omegaTwo hCH red blue hcompl hnoRed)

/-- Global CH normal form at the full source length.  Either one of the
exact Part 3 targets already occurs, or `ω₂` itself decomposes into an
ordered chain of blue `ω₁ + 1` arms, with a retained complete red-star
witness across every successor pair. -/
theorem part3_exact_or_transfiniteBlueArmChain_omegaTwo
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      TransfiniteBlueArmChain red blue (ω_ 2) := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red
          Erdos1172Part3FiniteStars.RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · right
    have hnone := not_or.mp htarget
    obtain ⟨firstArm, hfirstRed, hfirstType⟩ |
        ⟨firstArm, hfirstBlue, hfirstType⟩ :=
      Erdos1172Part3CHAsymmetric.red_target_or_blue_omegaOne_add_one
        hCH red blue hcompl
    · exact (hnone.1 ⟨firstArm, hfirstRed, hfirstType⟩).elim
    · exact exists_transfiniteBlueArmChain_omegaTwo
        hCH red blue hcompl hfirstBlue hfirstType hnone.1 hnone.2

end Erdos1172Part3TransfiniteArmChain
