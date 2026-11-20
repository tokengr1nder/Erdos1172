/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OneSuccessorFullFiberChain
public import Erdos1172.Part3OmegaOneProfileBarrier

@[expose] public section

open Cardinal Ordinal Set Function
open Order

namespace Erdos1172Part3NearArmFullProfileBarrier

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3OneSuccessorBarrier
  Erdos1172Part3OneSuccessorFullFiberChain
  Erdos1172Part3OmegaOneProfileBarrier

/-- The canonical embedding of the `W2` stages into the full arm-chain
index is strictly increasing. -/
theorem nearArmStage_strictMono : StrictMono nearArmStage := by
  intro a b hab
  change (a : Ordinal) < (b : Ordinal)
  rw [← Ordinal.ToType.mk.apply_symm_apply a,
    ← Ordinal.ToType.mk.apply_symm_apply b] at hab
  exact (Ordinal.ToType.mk.lt_iff_lt).mp hab

/-- The chosen maximum of the red near-target arm at stage `a`. -/
noncomputable def nearArmTerminalSub
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2) :
    chain.arms (nearArmStage a) :=
  Classical.choose <|
    exists_max_of_type_redNearTarget (chain.arm_type (nearArmStage a))

/-- The chosen arm maximum, regarded as a vertex of `W2`. -/
noncomputable def nearArmTerminal
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2) : W2 :=
  nearArmTerminalSub chain a

theorem nearArmTerminal_mem
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2) :
    nearArmTerminal chain a ∈ chain.arms (nearArmStage a) :=
  (nearArmTerminalSub chain a).property

theorem nearArmTerminal_max
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2)
    (x : W2) (hx : x ∈ chain.arms (nearArmStage a)) :
    x ≤ nearArmTerminal chain a := by
  have hmax : IsMax (nearArmTerminalSub chain a) :=
    Classical.choose_spec <|
      exists_max_of_type_redNearTarget (chain.arm_type (nearArmStage a))
  exact show (⟨x, hx⟩ : chain.arms (nearArmStage a)) ≤
      nearArmTerminalSub chain a from
    le_of_not_gt ((isMax_iff_forall_not_lt.mp hmax) ⟨x, hx⟩)

theorem nearArmTerminal_strictMono
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) :
    StrictMono (nearArmTerminal chain) := by
  intro a b hab
  exact chain.ordered (nearArmStage a) (nearArmStage b)
    (nearArmStage_strictMono hab)
    (nearArmTerminal chain a) (nearArmTerminal_mem chain a)
    (nearArmTerminal chain b) (nearArmTerminal_mem chain b)

/-- The earlier arm whose complete incidence profile is recorded. -/
abbrev EarlierArm
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2) : Type :=
  chain.arms (nearArmStage a)

/-- The indices strictly later than the fixed arm stage. -/
abbrev LaterIndex (a : W2) : Type := Set.Ioi a

/-- The exact set of blue neighbors in arm `a` of the chosen terminal at
the later stage `b`.  No representative is selected from this set. -/
noncomputable def fullBlueProfile
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2)
    (b : LaterIndex a) : Set (EarlierArm chain a) :=
  {x | blue.Adj (x : W2) (nearArmTerminal chain (b : W2))}

/-- The vertex set represented by the complement of a profile inside the
fixed earlier arm. -/
def profileRedComplement
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2)
    (profile : Set (EarlierArm chain a)) : Set W2 :=
  Subtype.val '' profileᶜ

theorem profileRedComplement_subset_arm
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2)
    (profile : Set (EarlierArm chain a)) :
    profileRedComplement chain a profile ⊆
      chain.arms (nearArmStage a) := by
  rintro _ ⟨x, _hx, rfl⟩
  exact x.property

theorem profileRedComplement_isClique
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2)
    (profile : Set (EarlierArm chain a)) :
    red.IsClique (profileRedComplement chain a profile) :=
  (chain.arm_red (nearArmStage a)).subset <|
    profileRedComplement_subset_arm chain a profile

/-- Every later terminal has a nonempty exact blue-neighbor profile in
each earlier arm. -/
theorem fullBlueProfile_nonempty
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2)
    (b : LaterIndex a) :
    (fullBlueProfile chain a b).Nonempty := by
  obtain ⟨x, hx, hblue⟩ :=
    chain.cross_blue_failure (nearArmStage a)
      (nearArmStage (b : W2))
      (nearArmStage_strictMono b.property)
      (nearArmTerminal chain (b : W2))
      (nearArmTerminal_mem chain (b : W2))
  exact ⟨⟨x, hx⟩, hblue⟩

theorem fullProfileComplement_before_terminal
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2)
    (b : LaterIndex a) :
    ∀ x ∈ profileRedComplement chain a (fullBlueProfile chain a b),
      x < nearArmTerminal chain (b : W2) := by
  intro x hx
  exact chain.ordered (nearArmStage a) (nearArmStage (b : W2))
    (nearArmStage_strictMono b.property) x
    (profileRedComplement_subset_arm chain a
      (fullBlueProfile chain a b) hx)
    (nearArmTerminal chain (b : W2))
    (nearArmTerminal_mem chain (b : W2))

/-- By global complementarity, the exact complement of the blue profile
is precisely red to its later terminal. -/
theorem fullProfileComplement_redToTerminal
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue)
    (hcompl : IsCompl red blue) (a : W2) (b : LaterIndex a) :
    ∀ x ∈ profileRedComplement chain a (fullBlueProfile chain a b),
      red.Adj x (nearArmTerminal chain (b : W2)) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxNot : x ∉ fullBlueProfile chain a b := by
    simpa only [Set.mem_compl_iff] using hx
  have hnotBlue :
      ¬ blue.Adj (x : W2) (nearArmTerminal chain (b : W2)) := by
    exact hxNot
  let leftVertex : W2 := x
  let rightVertex : W2 := nearArmTerminal chain (b : W2)
  change ¬ blue.Adj leftVertex rightVertex at hnotBlue
  change red.Adj leftVertex rightVertex
  rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
  exact ⟨(fullProfileComplement_before_terminal chain a b
    (x : W2) ⟨x, hx, rfl⟩).ne, hnotBlue⟩

/-- Without the exact red target, every individual red complement is
strictly shorter than the red near-target. -/
theorem fullProfileComplement_type_lt_redNearTarget
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (a : W2) (b : LaterIndex a) :
    typeLT (profileRedComplement chain a (fullBlueProfile chain a b)) <
      RedNearTarget := by
  by_contra hnot
  have hle : RedNearTarget ≤
      typeLT (profileRedComplement chain a (fullBlueProfile chain a b)) :=
    le_of_not_gt hnot
  obtain ⟨near, hnearSub, hnearType⟩ :=
    Ordinal.exists_subset_typeLT_eq
      (profileRedComplement chain a (fullBlueProfile chain a b)) hle
  have hnearRed : red.IsClique near :=
    (profileRedComplement_isClique chain a
      (fullBlueProfile chain a b)).subset hnearSub
  have hnearBefore :
      ∀ x ∈ near, x < nearArmTerminal chain (b : W2) := by
    intro x hx
    exact fullProfileComplement_before_terminal chain a b x (hnearSub hx)
  have hnearAdj :
      ∀ x ∈ near, red.Adj x (nearArmTerminal chain (b : W2)) := by
    intro x hx
    exact fullProfileComplement_redToTerminal chain hcompl a b x
      (hnearSub hx)
  obtain ⟨target, htargetRed, htargetType⟩ :=
    red.exists_clique_type_add_one_of_common_later
      hnearRed hnearType hnearBefore hnearAdj
  apply hnoRed
  refine ⟨target, htargetRed, ?_⟩
  calc
    typeLT target = RedNearTarget + 1 := htargetType
    _ = RedTarget := by
      norm_num [RedNearTarget, RedCoreTarget, RedTarget, add_assoc]

/-- The repeated-profile branch.  On a full `alephTwo` fiber, BHT gives a
later red near-target.  Its common exact red complement in the fixed arm
is then strictly below the red core; otherwise a core and two later red
points form the forbidden exact red target. -/
structure RepeatedFullProfileBranch
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2) : Type 1 where
  fixed : Set (EarlierArm chain a)
  indexFiber : Set (LaterIndex a)
  indexFiber_card : #indexFiber = ℵ_ 2
  profile_fixed : ∀ b ∈ indexFiber, fullBlueProfile chain a b = fixed
  fixed_nonempty : fixed.Nonempty
  complement_red : red.IsClique (profileRedComplement chain a fixed)
  complement_type_lt_core :
    typeLT (profileRedComplement chain a fixed) < RedCoreTarget
  terminalFiber : Set W2
  terminalFiber_eq : terminalFiber =
    (fun b : LaterIndex a ↦ nearArmTerminal chain (b : W2)) '' indexFiber
  terminalFiber_card : #terminalFiber = ℵ_ 2
  laterRed : Set W2
  laterRed_sub : laterRed ⊆ terminalFiber
  laterRed_red : red.IsClique laterRed
  laterRed_type : typeLT laterRed = RedNearTarget
  complement_before_later :
    ∀ x ∈ profileRedComplement chain a fixed,
      ∀ y ∈ laterRed, x < y
  complement_red_later :
    ∀ x ∈ profileRedComplement chain a fixed,
      ∀ y ∈ laterRed, red.Adj x y

/-- The residual branch at the exact profile-space threshold. -/
structure InjectiveFullProfileBranch
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2) : Type 1 where
  residual : Set (LaterIndex a)
  residual_card : #residual = ℵ_ 2
  profile_injective : Set.InjOn (fullBlueProfile chain a) residual

/-- The strongest choice-independent tail full-profile normal form
currently forced by a fixed-center red near-arm chain. -/
structure NearArmFullProfileBarrier
    {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2) : Type 1 where
  terminal_strict : StrictMono (nearArmTerminal chain)
  full_profile_nonempty :
    ∀ b : LaterIndex a, (fullBlueProfile chain a b).Nonempty
  complement_red : ∀ b : LaterIndex a,
    red.IsClique
      (profileRedComplement chain a (fullBlueProfile chain a b))
  complement_type_lt_near : ∀ b : LaterIndex a,
    typeLT (profileRedComplement chain a (fullBlueProfile chain a b)) <
      RedNearTarget
  outcome : Nonempty (RepeatedFullProfileBranch chain a) ∨
    Nonempty (InjectiveFullProfileBranch chain a)

/-- The exact binary profile space of an earlier arm has cardinality
`alephTwo` under GCH.  Thus the injective residual alternative is at the
sharp cardinal threshold, rather than contradicting pigeonhole. -/
theorem mk_fullBlueProfile_space_eq_alephTwo
    (hGCH : GCH) {red blue : SimpleGraph W2}
    (chain : FixedCenterRedNearArmChain red blue) (a : W2) :
    #(Set (EarlierArm chain a)) = ℵ_ 2 := by
  have harmCard : #(EarlierArm chain a) = ℵ_ 1 := by
    have hc := congrArg Ordinal.card (chain.arm_type (nearArmStage a))
    simpa only [Ordinal.card_type, card_redNearTarget] using hc
  rw [Cardinal.mk_set, harmCard]
  exact hGCH.two_power_aleph_one

/-- Full profiles on every fixed arm stage satisfy the sharp
repeated-or-injective dichotomy.  No GCH hypothesis is used: GCH only
identifies the profile space itself with `alephTwo`. -/
noncomputable def FixedCenterRedNearArmChain.to_nearArmFullProfileBarrier
    (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2)
    (chain : FixedCenterRedNearArmChain red blue)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (a : W2) :
    NearArmFullProfileBarrier chain a := by
  classical
  refine {
    terminal_strict := nearArmTerminal_strictMono chain
    full_profile_nonempty := fullBlueProfile_nonempty chain a
    complement_red := fun b ↦
      profileRedComplement_isClique chain a (fullBlueProfile chain a b)
    complement_type_lt_near := fun b ↦
      fullProfileComplement_type_lt_redNearTarget
        chain hcompl hnoRed a b
    outcome := ?_ }
  let profile : LaterIndex a → Set (EarlierArm chain a) :=
    fullBlueProfile chain a
  have hdomainCard : #(LaterIndex a) = ℵ_ 2 :=
    mk_Ioi_omegaTwo_eq a
  obtain ⟨fixed, hfixedFiberCard⟩ |
      ⟨residual, hresidualCard, hresidualInjective⟩ :=
    alephTwo_fiber_or_alephTwo_injective_restriction
      hdomainCard profile
  · let indexFiber : Set (LaterIndex a) := profile ⁻¹' {fixed}
    have hindexFiberCard : #indexFiber = ℵ_ 2 := hfixedFiberCard
    have hprofileFixed (b : LaterIndex a) (hb : b ∈ indexFiber) :
        fullBlueProfile chain a b = fixed := by
      have hb' : profile b = fixed := by
        simpa only [indexFiber, Set.mem_preimage,
          Set.mem_singleton_iff] using hb
      simpa only [profile] using hb'
    have hindexFiberNonempty : indexFiber.Nonempty := by
      apply Cardinal.mk_set_ne_zero_iff.mp
      rw [hindexFiberCard]
      exact (Cardinal.aleph_pos 2).ne'
    obtain ⟨sample, hsample⟩ := hindexFiberNonempty
    have hfixedNonempty : fixed.Nonempty := by
      rw [← hprofileFixed sample hsample]
      exact fullBlueProfile_nonempty chain a sample
    let complement : Set W2 := profileRedComplement chain a fixed
    have hcomplementRed : red.IsClique complement :=
      profileRedComplement_isClique chain a fixed
    let terminalOnTail : LaterIndex a → W2 :=
      fun b ↦ nearArmTerminal chain (b : W2)
    have hterminalOnTailInjective : Function.Injective terminalOnTail :=
      (nearArmTerminal_strictMono chain).injective.comp
        Subtype.val_injective
    let terminalFiber : Set W2 := terminalOnTail '' indexFiber
    have hterminalFiberCard : #terminalFiber = ℵ_ 2 := by
      calc
        #terminalFiber = #indexFiber :=
          Cardinal.mk_image_eq hterminalOnTailInjective
        _ = ℵ_ 2 := hindexFiberCard
    have hterminalFiberType : typeLT terminalFiber = ω_ 2 :=
      typeLT_eq_omegaTwo_of_mk_eq hterminalFiberCard
    obtain ⟨laterRed, hlaterRedSub, hlaterRedRed, hlaterRedType⟩ |
        ⟨target, _htargetSub, htargetBlue, htargetType⟩ :=
      OrdinalRamsey.on_set_of_type hBHT red blue hcompl
        terminalFiber hterminalFiberType
    · have hcomplementBeforeLater :
          ∀ x ∈ complement, ∀ y ∈ laterRed, x < y := by
        intro x hx y hy
        have hyFiber : y ∈ terminalFiber := hlaterRedSub hy
        obtain ⟨b, hb, rfl⟩ := hyFiber
        exact chain.ordered (nearArmStage a)
          (nearArmStage (b : W2))
          (nearArmStage_strictMono b.property) x
          (profileRedComplement_subset_arm chain a fixed hx)
          (nearArmTerminal chain (b : W2))
          (nearArmTerminal_mem chain (b : W2))
      have hcomplementRedLater :
          ∀ x ∈ complement, ∀ y ∈ laterRed, red.Adj x y := by
        rintro _ ⟨x, hx, rfl⟩ y hy
        have hyFiber : y ∈ terminalFiber := hlaterRedSub hy
        obtain ⟨b, hb, rfl⟩ := hyFiber
        have hxNot : x ∉ fixed := by
          simpa only [Set.mem_compl_iff] using hx
        have hnotBlue :
            ¬ blue.Adj (x : W2)
              (nearArmTerminal chain (b : W2)) := by
          intro hblue
          apply hxNot
          rw [← hprofileFixed b hb]
          exact hblue
        let leftVertex : W2 := x
        let rightVertex : W2 := terminalOnTail b
        change ¬ blue.Adj leftVertex rightVertex at hnotBlue
        change red.Adj leftVertex rightVertex
        rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
        exact ⟨(hcomplementBeforeLater (x : W2) ⟨x, hx, rfl⟩
          (nearArmTerminal chain (b : W2))
          hy).ne, hnotBlue⟩
      have hcomplementTypeLtCore : typeLT complement < RedCoreTarget := by
        by_contra hnot
        have hcoreLe : RedCoreTarget ≤ typeLT complement :=
          le_of_not_gt hnot
        obtain ⟨core, hcoreSub, hcoreType⟩ :=
          Ordinal.exists_subset_typeLT_eq complement hcoreLe
        have hcoreRed : red.IsClique core :=
          hcomplementRed.subset hcoreSub
        have honeLtCore : (1 : Ordinal.{0}) < RedCoreTarget := by
          rw [RedCoreTarget, Ordinal.one_lt_opow]
          exact ⟨one_lt_omega0.trans_le
            (Ordinal.omega0_le_omega 1), by simp⟩
        have htwoLeCore : (2 : Ordinal.{0}) ≤ RedCoreTarget := by
          rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]
          exact add_one_le_iff.mpr honeLtCore
        have htwoLeNear : (2 : Ordinal.{0}) ≤ RedNearTarget :=
          htwoLeCore.trans (by
            change RedCoreTarget ≤ RedCoreTarget + 1
            exact le_self_add)
        obtain ⟨pair, hpairSub, hpairType⟩ :=
          Ordinal.exists_subset_typeLT_eq laterRed
            (hlaterRedType ▸ htwoLeNear)
        have hpairRed : red.IsClique pair :=
          hlaterRedRed.subset hpairSub
        obtain ⟨redTarget, hredTargetClique, hredTargetType⟩ :=
          red.exists_clique_type_add_of_later_block
            hcoreRed hpairRed hcoreType hpairType
            (fun x hx y hy ↦ hcomplementBeforeLater
              x (hcoreSub hx) y (hpairSub hy))
            (fun x hx y hy ↦ hcomplementRedLater
              x (hcoreSub hx) y (hpairSub hy))
        apply hnoRed
        refine ⟨redTarget, hredTargetClique, ?_⟩
        simpa only [RedCoreTarget, RedTarget] using hredTargetType
      exact Or.inl ⟨{
        fixed := fixed
        indexFiber := indexFiber
        indexFiber_card := hindexFiberCard
        profile_fixed := hprofileFixed
        fixed_nonempty := hfixedNonempty
        complement_red := hcomplementRed
        complement_type_lt_core := hcomplementTypeLtCore
        terminalFiber := terminalFiber
        terminalFiber_eq := rfl
        terminalFiber_card := hterminalFiberCard
        laterRed := laterRed
        laterRed_sub := hlaterRedSub
        laterRed_red := hlaterRedRed
        laterRed_type := hlaterRedType
        complement_before_later := hcomplementBeforeLater
        complement_red_later := hcomplementRedLater }⟩
    · exact (hnoBlue ⟨target, htargetBlue, htargetType⟩).elim
  · exact Or.inr ⟨{
      residual := residual
      residual_card := hresidualCard
      profile_injective := by
        simpa only [profile] using hresidualInjective }⟩

/-- The full-coordinate barrier holds simultaneously at every arm stage. -/
noncomputable def FixedCenterRedNearArmChain.forall_nearArmFullProfileBarrier
    (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2)
    (chain : FixedCenterRedNearArmChain red blue)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    ∀ a : W2, NearArmFullProfileBarrier chain a := by
  intro a
  exact FixedCenterRedNearArmChain.to_nearArmFullProfileBarrier
    hBHT red blue chain hcompl hnoRed hnoBlue a

end Erdos1172Part3NearArmFullProfileBarrier
