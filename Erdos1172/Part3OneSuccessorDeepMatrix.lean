/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OneSuccessorBarrier
public import Erdos1172.ForMathlib.SetTheory.Ordinal.TerminalClique
public import Mathlib.Order.Hom.Lex
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OneSuccessorDeepMatrix

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3OneSuccessorBarrier

/-- The exact predecessor core below the terminal point of a near-target. -/
def redCoreBelow (base : Set W2) (maximum : W2) : Set W2 :=
  {x | x ∈ base ∧ x < maximum}

/-- A right-hand point is shallow if its blue neighbours in the red core
are bounded below the terminal point. -/
def ShallowAt (blue : SimpleGraph W2) (base : Set W2)
    (maximum y : W2) : Prop :=
  ∃ x₀, x₀ ∈ base ∧ x₀ < maximum ∧
    ∀ x, x ∈ base → x₀ < x → x < maximum → ¬ blue.Adj x y

/-- The blue column of `y`, regarded as a subset of the ordered left core. -/
def blueColumn (blue : SimpleGraph W2) (left : Set W2) (y : W2) : Set left :=
  {x | blue.Adj x y}

/-- A blue column is strictly cofinal in the induced order on the left core. -/
def StrictlyCofinalBlueColumn (blue : SimpleGraph W2)
    (left : Set W2) (y : W2) : Prop :=
  ∀ x₀ ∈ left, ∃ x ∈ left, x₀ < x ∧ blue.Adj x y

/-- The surviving one-successor obstruction as an honest two-core matrix.
Both sides are red copies of the exact limit core.  Every right column has
an `alephOne`-sized cofinal blue neighbourhood on the left, while two
distinct right points never have a full-core common red neighbourhood. -/
def OrderedDeepRedCoreMatrixResidual
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (left right : Set W2),
    red.IsClique left ∧ typeLT left = RedCoreTarget ∧
    red.IsClique right ∧ typeLT right = RedCoreTarget ∧
    (∀ x ∈ left, ∀ y ∈ right, x < y) ∧
    (∀ y ∈ right,
      StrictlyCofinalBlueColumn blue left y ∧
      #(blueColumn blue left y) = ℵ_ 1) ∧
    ∀ y ∈ right, ∀ z ∈ right, y ≠ z →
      typeLT {x : W2 |
        x ∈ left ∧ red.Adj x y ∧ red.Adj x z} < RedCoreTarget

private theorem redCoreTarget_isPrincipal_add :
    IsPrincipal (· + ·) RedCoreTarget := by
  exact Ordinal.isPrincipal_add_opow_of_isPrincipal_add
    (Ordinal.isPrincipal_add_omega 1) (ω + 2)

private theorem one_lt_redCoreTarget :
    (1 : Ordinal.{0}) < RedCoreTarget := by
  rw [RedCoreTarget, Ordinal.one_lt_opow]
  exact ⟨one_lt_omega0.trans_le (Ordinal.omega0_le_omega 1), by simp⟩

/-- The cardinality of the exact predecessor core is `alephOne`. -/
theorem card_redCoreTarget : RedCoreTarget.card = ℵ_ 1 := by
  have hExp : (ω + 2 : Ordinal.{0}).card = ℵ₀ := by
    rw [Ordinal.card_add, Ordinal.card_omega0, Ordinal.card_ofNat,
      Cardinal.add_eq_left]
    · exact le_rfl
    · exact Cardinal.natCast_le_aleph0
  rw [RedCoreTarget, Ordinal.card_opow_eq_of_omega0_le_left,
    Ordinal.card_omega, hExp,
    max_eq_left (Cardinal.aleph0_le_aleph 1)]
  · exact Ordinal.omega0_le_omega 1
  · exact Ordinal.omega0_pos.trans_le (by simp)

/-- The exact predecessor core has cofinality `alephOne`. -/
theorem cof_redCoreTarget : RedCoreTarget.cof = ℵ_ 1 := by
  have hexp : (ω + 2 : Ordinal.{0}) = (ω + 1) + 1 := by
    norm_num [add_assoc]
  have hbase0 : (ω_ 1 : Ordinal.{0}) ≠ 0 :=
    (Ordinal.omega0_pos.trans_le (Ordinal.omega0_le_omega 1)).ne'
  rw [RedCoreTarget, hexp, Ordinal.opow_add_one,
    Ordinal.cof_mul (Ordinal.opow_ne_zero (ω + 1) hbase0)
      (Cardinal.isSuccLimit_omega 1).isSuccPrelimit,
    Cardinal.cof_omega_one]

/-- Removing the terminal point from a near-target leaves exactly its
predecessor core. -/
theorem typeLT_redCoreBelow
    {base : Set W2} {maximum : W2}
    (hbaseType : typeLT base = RedNearTarget)
    (hmaximumMem : maximum ∈ base)
    (hmaximum : ∀ x ∈ base, x ≤ maximum) :
    typeLT (redCoreBelow base maximum) = RedCoreTarget := by
  classical
  have hcoreLater :
      ∀ x ∈ redCoreBelow base maximum, x < maximum :=
    fun _ hx ↦ hx.2
  have hbaseEq : base = insert maximum (redCoreBelow base maximum) := by
    ext x
    constructor
    · intro hx
      rcases (hmaximum x hx).eq_or_lt with hxm | hxm
      · exact Set.mem_insert_iff.mpr (Or.inl hxm)
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨hx, hxm⟩)
    · intro hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hmaximumMem
      · exact hx.1
  have hsucc :
      typeLT (redCoreBelow base maximum) + (1 : Ordinal) =
        RedCoreTarget + 1 := by
    calc
      typeLT (redCoreBelow base maximum) + 1 =
          typeLT (Set.insert maximum
            (redCoreBelow base maximum) : Set W2) :=
        (Ordinal.typeLT_insert_of_forall_lt hcoreLater).symm
      _ = typeLT base :=
        congrArg (fun s : Set W2 ↦ typeLT s) hbaseEq.symm
      _ = RedNearTarget := hbaseType
      _ = RedCoreTarget + 1 := rfl
  apply (Ordinal.add_right_cancel
    (a := typeLT (redCoreBelow base maximum))
    (b := RedCoreTarget) 1).mp
  simpa only [Nat.cast_one] using hsucc

/-- Every strict final segment of the predecessor core of a red
near-target still has the full predecessor order type. -/
theorem typeLT_redCore_finalSegment
    {base : Set W2} {maximum x₀ : W2}
    (hbaseType : typeLT base = RedNearTarget)
    (hmaximumMem : maximum ∈ base)
    (hmaximum : ∀ x ∈ base, x ≤ maximum)
    (hx₀Mem : x₀ ∈ base) (hx₀lt : x₀ < maximum) :
    typeLT {x : W2 | x ∈ base ∧ x₀ < x ∧ x < maximum} =
      RedCoreTarget := by
  classical
  let core : Set W2 := redCoreBelow base maximum
  have hcoreType : typeLT core = RedCoreTarget :=
    typeLT_redCoreBelow hbaseType hmaximumMem hmaximum
  let x₀core : core := ⟨x₀, hx₀Mem, hx₀lt⟩
  have hIicEq : (Set.Iic x₀core : Set core) =
      insert x₀core (Set.Iio x₀core) := by
    ext x
    simp [le_iff_lt_or_eq]
  have hprefixType :
      typeLT (Set.Iic x₀core) =
        Ordinal.typein (α := core) (· < ·) x₀core + 1 := by
    calc
      typeLT (Set.Iic x₀core) =
          typeLT (Set.insert x₀core (Set.Iio x₀core) : Set core) :=
        congrArg (fun s : Set core ↦ typeLT s) hIicEq
      _ = typeLT (Set.Iio x₀core) + 1 :=
        Ordinal.typeLT_insert_of_forall_lt (fun x hx ↦ hx)
      _ = Ordinal.typein (α := core) (· < ·) x₀core + 1 := by
        rw [Ordinal.type_Iio_lt]
  have hprefixLt : typeLT (Set.Iic x₀core) < RedCoreTarget := by
    rw [hprefixType]
    apply redCoreTarget_isPrincipal_add
    · rw [← hcoreType]
      exact Ordinal.typein_lt_type (α := core) (· < ·) x₀core
    · exact one_lt_redCoreTarget
  have hwf_lex : WellFounded (fun a b : Set.Iic x₀core ⊕ₗ Set.Ioi x₀core => a < b) := by
    refine Subrelation.wf (r := InvImage (Sum.Lex (· < ·) (· < ·)) ofLex) (fun h => h) ?_
    exact InvImage.wf ofLex (Sum.lex_wf wellFounded_lt wellFounded_lt)
  letI : WellFoundedLT (Set.Iic x₀core ⊕ₗ Set.Ioi x₀core) := hwf_lex
  have hdecomp :
      typeLT (Set.Iic x₀core) + typeLT (Set.Ioi x₀core) =
        typeLT core := by
    have hsum :
        typeLT (Set.Iic x₀core ⊕ₗ Set.Ioi x₀core) =
          typeLT (Set.Iic x₀core) + typeLT (Set.Ioi x₀core) :=
      Ordinal.type_sum_lex (· < ·) (· < ·)
    calc
      typeLT (Set.Iic x₀core) + typeLT (Set.Ioi x₀core) =
          typeLT (Set.Iic x₀core ⊕ₗ Set.Ioi x₀core) := hsum.symm
      _ = typeLT core :=
        (OrderIso.sumLexIicIoi x₀core).ordinalType_congr
  have htailLe : typeLT (Set.Ioi x₀core) ≤ RedCoreTarget := by
    rw [← hcoreType]
    exact Ordinal.type_set_le (Set.Ioi x₀core)
  have htailType : typeLT (Set.Ioi x₀core) = RedCoreTarget := by
    apply le_antisymm htailLe
    apply le_of_not_gt
    intro htailLt
    have hsumLt :
        typeLT (Set.Iic x₀core) + typeLT (Set.Ioi x₀core) <
          RedCoreTarget :=
      redCoreTarget_isPrincipal_add hprefixLt htailLt
    rw [hdecomp, hcoreType] at hsumLt
    exact (lt_irrefl RedCoreTarget) hsumLt
  let tail : Set W2 :=
    {x : W2 | x ∈ base ∧ x₀ < x ∧ x < maximum}
  let e : Set.Ioi x₀core ≃o tail :=
    { toEquiv :=
        { toFun := fun x ↦ ⟨x.1.1, x.1.2.1, x.2, x.1.2.2⟩
          invFun := fun x ↦ ⟨⟨x.1, x.2.1, x.2.2.2⟩, x.2.2.1⟩
          left_inv := fun x ↦ Subtype.ext rfl
          right_inv := fun x ↦ Subtype.ext rfl }
      map_rel_iff' := by
        intro a b
        rfl }
  change typeLT tail = RedCoreTarget
  exact e.ordinalType_congr.symm.trans htailType

/-- In the absence of the exact red target, two red-adjacent later
vertices have common red left neighbourhood of type strictly below the
full predecessor core. -/
theorem typeLT_commonRedLeft_lt_of_no_red_target
    (red : SimpleGraph W2) {left right : Set W2}
    (hleftRed : red.IsClique left)
    (hrightRed : red.IsClique right)
    (hleftBefore : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    {y z : W2} (hy : y ∈ right) (hz : z ∈ right) (hyz : y ≠ z) :
    typeLT {x : W2 |
      x ∈ left ∧ red.Adj x y ∧ red.Adj x z} < RedCoreTarget := by
  classical
  let common : Set W2 :=
    {x | x ∈ left ∧ red.Adj x y ∧ red.Adj x z}
  have hcommonSub : common ⊆ left := fun _ hx ↦ hx.1
  by_contra hcommonNotLt
  have hcoreLe : RedCoreTarget ≤ typeLT common :=
    le_of_not_gt hcommonNotLt
  obtain ⟨core, hcoreSub, hcoreType⟩ :=
    Ordinal.exists_subset_typeLT_eq common hcoreLe
  have hcoreRed : red.IsClique core :=
    hleftRed.subset (hcoreSub.trans hcommonSub)
  have impossible_of_ordered (low high : W2)
      (hlow : low ∈ right) (hhigh : high ∈ right)
      (hlowHigh : low < high)
      (hcoreLow : ∀ x ∈ core, red.Adj x low)
      (hcoreHigh : ∀ x ∈ core, red.Adj x high) : False := by
    have hcoreBeforeLow : ∀ x ∈ core, x < low := by
      intro x hx
      exact hleftBefore x (hcommonSub (hcoreSub hx)) low hlow
    let withLow : Set W2 := insert low core
    have hwithLowRed : red.IsClique withLow := by
      apply hcoreRed.insert
      intro x hx _
      rw [red.adj_comm]
      exact hcoreLow x hx
    have hwithLowType : typeLT withLow = RedCoreTarget + 1 := by
      calc
        typeLT withLow = typeLT core + 1 :=
          Ordinal.typeLT_insert_of_forall_lt hcoreBeforeLow
        _ = RedCoreTarget + 1 := by rw [hcoreType]
    have hwithLowBeforeHigh : ∀ x ∈ withLow, x < high := by
      intro x hx
      simp only [withLow, mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact hlowHigh
      · exact hleftBefore x (hcommonSub (hcoreSub hx)) high hhigh
    have hwithLowAdjHigh : ∀ x ∈ withLow, red.Adj x high := by
      intro x hx
      simp only [withLow, mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact hrightRed hlow hhigh hlowHigh.ne
      · exact hcoreHigh x hx
    obtain ⟨target, htargetRed, htargetType⟩ :=
      red.exists_clique_type_add_one_of_common_later
        hwithLowRed hwithLowType hwithLowBeforeHigh hwithLowAdjHigh
    apply hnoRed
    refine ⟨target, htargetRed, ?_⟩
    calc
      typeLT target = (RedCoreTarget + 1) + 1 := htargetType
      _ = RedTarget := by
        norm_num [RedCoreTarget, RedTarget, add_assoc]
  rcases lt_or_gt_of_ne hyz with hyzlt | hzylt
  · exact impossible_of_ordered y z hy hz hyzlt
      (fun x hx ↦ (hcoreSub hx).2.1)
      (fun x hx ↦ (hcoreSub hx).2.2)
  · exact impossible_of_ordered z y hz hy hzylt
      (fun x hx ↦ (hcoreSub hx).2.2)
      (fun x hx ↦ (hcoreSub hx).2.1)

/-- Under complementary colouring, the shallow points in a later red
clique form a subsingleton.  Two of them would expose a full final segment
inside their common red left neighbourhood. -/
theorem shallowAt_subsingleton_of_no_red_target
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base right : Set W2} {maximum : W2}
    (hbaseRed : red.IsClique base)
    (hbaseType : typeLT base = RedNearTarget)
    (hmaximumMem : maximum ∈ base)
    (hmaximum : ∀ x ∈ base, x ≤ maximum)
    (hrightRed : red.IsClique right)
    (hbaseBefore : ∀ x ∈ base, ∀ y ∈ right, x < y)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget) :
    ({y : W2 | y ∈ right ∧ ShallowAt blue base maximum y} : Set W2).Subsingleton := by
  classical
  let left : Set W2 := redCoreBelow base maximum
  have hleftRed : red.IsClique left :=
    hbaseRed.subset (fun _ hx ↦ hx.1)
  have hleftType : typeLT left = RedCoreTarget :=
    typeLT_redCoreBelow hbaseType hmaximumMem hmaximum
  have hleftBefore : ∀ x ∈ left, ∀ y ∈ right, x < y := by
    intro x hx y hy
    exact hbaseBefore x hx.1 y hy
  intro y hy z hz
  by_contra hyz
  have hcommonLt := typeLT_commonRedLeft_lt_of_no_red_target
    red hleftRed hrightRed hleftBefore hnoRed
      hy.1 hz.1 hyz
  obtain ⟨y₀, hy₀Mem, hy₀Max, hy₀⟩ := hy.2
  obtain ⟨z₀, hz₀Mem, hz₀Max, hz₀⟩ := hz.2
  have red_of_not_blue {x w : W2} (hxw : x ≠ w)
      (hnotBlue : ¬ blue.Adj x w) : red.Adj x w := by
    rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
    exact ⟨hxw, hnotBlue⟩
  rcases le_total y₀ z₀ with hyz₀ | hzy₀
  · let tail : Set W2 :=
      {x | x ∈ base ∧ z₀ < x ∧ x < maximum}
    have htailType : typeLT tail = RedCoreTarget :=
      typeLT_redCore_finalSegment hbaseType hmaximumMem hmaximum
        hz₀Mem hz₀Max
    have htailSub : tail ⊆
        {x : W2 | x ∈ left ∧ red.Adj x y ∧ red.Adj x z} := by
      intro x hx
      have hxyNotBlue : ¬ blue.Adj x y :=
        hy₀ x hx.1 (hyz₀.trans_lt hx.2.1) hx.2.2
      have hxzNotBlue : ¬ blue.Adj x z :=
        hz₀ x hx.1 hx.2.1 hx.2.2
      refine ⟨⟨hx.1, hx.2.2⟩, ?_, ?_⟩
      · exact red_of_not_blue
          (hbaseBefore x hx.1 y hy.1).ne hxyNotBlue
      · exact red_of_not_blue
          (hbaseBefore x hx.1 z hz.1).ne hxzNotBlue
    have hmono := Ordinal.type_mono htailSub
    rw [htailType] at hmono
    exact (not_le_of_gt hcommonLt) hmono
  · let tail : Set W2 :=
      {x | x ∈ base ∧ y₀ < x ∧ x < maximum}
    have htailType : typeLT tail = RedCoreTarget :=
      typeLT_redCore_finalSegment hbaseType hmaximumMem hmaximum
        hy₀Mem hy₀Max
    have htailSub : tail ⊆
        {x : W2 | x ∈ left ∧ red.Adj x y ∧ red.Adj x z} := by
      intro x hx
      have hxyNotBlue : ¬ blue.Adj x y :=
        hy₀ x hx.1 hx.2.1 hx.2.2
      have hxzNotBlue : ¬ blue.Adj x z :=
        hz₀ x hx.1 (hzy₀.trans_lt hx.2.1) hx.2.2
      refine ⟨⟨hx.1, hx.2.2⟩, ?_, ?_⟩
      · exact red_of_not_blue
          (hbaseBefore x hx.1 y hy.1).ne hxyNotBlue
      · exact red_of_not_blue
          (hbaseBefore x hx.1 z hz.1).ne hxzNotBlue
    have hmono := Ordinal.type_mono htailSub
    rw [htailType] at hmono
    exact (not_le_of_gt hcommonLt) hmono

/-- A near-target right arm with at most one shallow point contains an
exact predecessor-type subarm consisting entirely of deep points. -/
theorem exists_exact_deep_right_of_shallow_subsingleton
    (red blue : SimpleGraph W2)
    {base rightArm : Set W2} {maximum : W2}
    (hrightRed : red.IsClique rightArm)
    (hrightType : typeLT rightArm = RedNearTarget)
    (hshallow :
      ({y : W2 | y ∈ rightArm ∧ ShallowAt blue base maximum y} : Set W2).Subsingleton) :
    ∃ right : Set W2, right ⊆ rightArm ∧
      red.IsClique right ∧ typeLT right = RedCoreTarget ∧
      ∀ y ∈ right, ¬ ShallowAt blue base maximum y := by
  classical
  obtain ⟨armCore, armMaximum, hcoreSub, hmaxMem, hrightEq,
      hcoreType, hcoreBefore⟩ :=
    Ordinal.exists_core_terminal_of_typeLT_eq_add_one
      rightArm hrightType
  have hrightMaximum : ∀ x ∈ rightArm, x ≤ armMaximum := by
    intro x hx
    rw [hrightEq] at hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact le_rfl
    · exact (hcoreBefore x hx).le
  let bad : Set W2 :=
    {y | y ∈ rightArm ∧ ShallowAt blue base maximum y}
  by_cases hbad : bad.Nonempty
  · obtain ⟨s, hs⟩ := hbad
    by_cases hsmax : s = armMaximum
    · refine ⟨armCore, hcoreSub, hrightRed.subset hcoreSub,
        hcoreType, ?_⟩
      intro y hy hyShallow
      have hyBad : y ∈ bad := ⟨hcoreSub hy, hyShallow⟩
      have hys : y = s := hshallow hyBad hs
      rw [hys, hsmax] at hy
      exact (hcoreBefore armMaximum hy).false
    · have hsLt : s < armMaximum := by
        exact (hrightMaximum s hs.1).lt_of_ne hsmax
      let right : Set W2 :=
        {y | y ∈ rightArm ∧ s < y ∧ y < armMaximum}
      have hrightCoreType : typeLT right = RedCoreTarget :=
        typeLT_redCore_finalSegment hrightType hmaxMem hrightMaximum
          hs.1 hsLt
      refine ⟨right, (fun _ hy ↦ hy.1),
        hrightRed.subset (fun _ hy ↦ hy.1), hrightCoreType, ?_⟩
      intro y hy hyShallow
      have hyBad : y ∈ bad := ⟨hy.1, hyShallow⟩
      have hys : y = s := hshallow hyBad hs
      exact (hys ▸ hy.2.1).false
  · refine ⟨armCore, hcoreSub, hrightRed.subset hcoreSub,
      hcoreType, ?_⟩
    intro y hy hyShallow
    exact hbad ⟨y, hcoreSub hy, hyShallow⟩

/-- Non-shallowness is precisely the strict cofinality needed for the
blue column on the predecessor core. -/
theorem strictlyCofinalBlueColumn_of_not_shallowAt
    (blue : SimpleGraph W2) {base : Set W2} {maximum y : W2}
    (hdeep : ¬ ShallowAt blue base maximum y) :
    StrictlyCofinalBlueColumn blue (redCoreBelow base maximum) y := by
  classical
  intro x₀ hx₀
  by_contra hnone
  apply hdeep
  refine ⟨x₀, hx₀.1, hx₀.2, ?_⟩
  intro x hx hx₀x hxmax hxy
  apply hnone
  exact ⟨x, ⟨hx, hxmax⟩, hx₀x, hxy⟩

/-- A strictly cofinal blue column is cofinal in the induced order. -/
theorem blueColumn_isCofinal
    (blue : SimpleGraph W2) {left : Set W2} {y : W2}
    (hstrict : StrictlyCofinalBlueColumn blue left y) :
    IsCofinal (blueColumn blue left y) := by
  intro x₀
  obtain ⟨x, hx, hx₀x, hxy⟩ := hstrict x₀ x₀.property
  exact ⟨⟨x, hx⟩, hxy, hx₀x.le⟩

/-- Every cofinal blue column in an exact predecessor core has cardinality
exactly `alephOne`. -/
theorem mk_blueColumn_eq_alephOne
    (blue : SimpleGraph W2) {left : Set W2} {y : W2}
    (hleftType : typeLT left = RedCoreTarget)
    (hstrict : StrictlyCofinalBlueColumn blue left y) :
    #(blueColumn blue left y) = ℵ_ 1 := by
  have hcofLeft : Order.cof left = ℵ_ 1 := by
    calc
      Order.cof left = (typeLT left).cof :=
        (Ordinal.cof_type left).symm
      _ = RedCoreTarget.cof := congrArg Ordinal.cof hleftType
      _ = ℵ_ 1 := cof_redCoreTarget
  have hlower : ℵ_ 1 ≤ #(blueColumn blue left y) := by
    rw [← hcofLeft]
    exact Order.cof_le (blueColumn_isCofinal blue hstrict)
  have hleftCard : #left = ℵ_ 1 := by
    calc
      #left = (typeLT left).card := (Ordinal.card_type (· < ·)).symm
      _ = RedCoreTarget.card := congrArg Ordinal.card hleftType
      _ = ℵ_ 1 := card_redCoreTarget
  have hupper : #(blueColumn blue left y) ≤ ℵ_ 1 := by
    rw [← hleftCard]
    exact Cardinal.mk_set_le (blueColumn blue left y)
  exact hupper.antisymm hlower

/-- A DoubleFan counterexample to the two exact targets canonically
contains the ordered deep two-core matrix residual. -/
theorem NearRedOneSuccessorDoubleFan.to_orderedDeepRedCoreMatrixResidual
    (red blue : SimpleGraph W2)
    (hfan : NearRedOneSuccessorDoubleFan red blue)
    (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget) :
    OrderedDeepRedCoreMatrixResidual red blue := by
  classical
  obtain ⟨base, maximum, _center, failureFiber, _blueArm, redArm,
      hbaseRed, hbaseType, hmaximumMem, hmaximum,
      _hcenterMem, _hallTailFailure, _hfailureFiberCard,
      hfailureFiberTail, _hcenterBlue, _hblueArmSub,
      _hblueArm, _hblueArmType, hredArmSub,
      hredArm, hredArmType⟩ := hfan
  let left : Set W2 := redCoreBelow base maximum
  have hleftRed : red.IsClique left :=
    hbaseRed.subset (fun _ hx ↦ hx.1)
  have hleftType : typeLT left = RedCoreTarget :=
    typeLT_redCoreBelow hbaseType hmaximumMem hmaximum
  have hbaseBeforeArm : ∀ x ∈ base, ∀ y ∈ redArm, x < y := by
    intro x hx y hy
    exact (hmaximum x hx).trans_lt
      (hfailureFiberTail (hredArmSub hy))
  have hshallow := shallowAt_subsingleton_of_no_red_target
    red blue hcompl hbaseRed hbaseType hmaximumMem hmaximum
      hredArm hbaseBeforeArm hnoRed
  obtain ⟨right, hrightSub, hrightRed, hrightType, hrightDeep⟩ :=
    exists_exact_deep_right_of_shallow_subsingleton
      red blue hredArm hredArmType hshallow
  have hleftBefore : ∀ x ∈ left, ∀ y ∈ right, x < y := by
    intro x hx y hy
    exact hbaseBeforeArm x hx.1 y (hrightSub hy)
  refine ⟨left, right, hleftRed, hleftType,
    hrightRed, hrightType, hleftBefore, ?_, ?_⟩
  · intro y hy
    have hstrict := strictlyCofinalBlueColumn_of_not_shallowAt
      blue (hrightDeep y hy)
    exact ⟨hstrict,
      mk_blueColumn_eq_alephOne blue hleftType hstrict⟩
  · intro y hy z hz hyz
    exact typeLT_commonRedLeft_lt_of_no_red_target
      red hleftRed hrightRed hleftBefore hnoRed hy hz hyz

/-- Conditional BHT wrapper: either one of the exact targets already
occurs, or the surviving DoubleFan yields the honest ordered deep matrix.
The theorem is explicitly conditional on `BHTNearPart3Relation`; it does
not assert that relation unconditionally. -/
theorem part3_exact_or_orderedDeepRedCoreMatrixResidual_conditional
    (hCH : CH) (hBHT : BHTNearPart3Relation)
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      OrderedDeepRedCoreMatrixResidual red blue := by
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
    · exact NearRedOneSuccessorDoubleFan.to_orderedDeepRedCoreMatrixResidual
        red blue hfan hcompl hnone.1

end Erdos1172Part3OneSuccessorDeepMatrix
