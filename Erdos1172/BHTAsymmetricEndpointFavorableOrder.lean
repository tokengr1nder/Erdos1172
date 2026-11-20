/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part2BlockCriterion
public import Erdos1172.ForMathlib.SetTheory.Cardinal.GCHConsequences1172

@[expose] public section

open Cardinal Ordinal Set Function

/-!
# The favorable order at the asymmetric BHT endpoint

This file is a static formalization draft of the one endpoint case of the
Baumgartner--Hajnal--Todorčević argument which does not require freezing a
complete `omegaOne`-long profile.

At the last step of Theorem 3.1, a maximal two-color sequence can produce an
`omegaOne`-by-`omegaOne` good set in either of two orders.  This module treats
the favorable order:

* every block is red-homogeneous of type `omegaOne`;
* distinct blocks are completely joined in blue.

The rows form a positive set for an abstract `alephTwo`-complete derived
ideal.  The only ideal facts assumed below are downward closure, finite
unions, and unions indexed by fewer than `alephTwo` objects.  In particular,
the module does **not** use the past-local `CoverClosureAt` mismatch lemma as
a surrogate for the future profiles occurring in the BHT proof.

Under CH there are only `alephOne` countable block transversals.  If one has
a positive all-blue row fiber, the blue `omegaTwo + omega` target follows.
Otherwise their union is small, so every remaining row is blue on points in
only finitely many blocks.  There are only `alephOne` finite block supports;
one support therefore freezes on a positive fiber, and any block outside it
is wholly red to that fiber.  The red `omegaTwo + omegaOne` target follows.

The reverse order is intentionally absent.  There one obtains a finite blue
set in each of `omegaOne` blue blocks, and the full slalom space
`([omegaOne]^{<omega})^omegaOne` has cardinal `alephTwo` under GCH.  That is
the genuine equality-case premise still needed by this route.
-/

namespace Erdos1172BHTAsymmetricEndpointFavorableOrder

abbrev W3 : Type := (omega 3 : Ordinal.{0}).ToType
abbrev I1 : Type := (omega 1 : Ordinal.{0}).ToType

/-- The exact closure fragment of the local derived ideal used in the
favorable endpoint argument. -/
structure AlephTwoSmallness (V : Type) where
  small : Set V → Prop
  mono : ∀ {s t : Set V}, s ⊆ t → small t → small s
  union_small : ∀ {s t : Set V}, small s → small t → small (s ∪ t)
  iUnion_small : ∀ {A : Type} (s : A → Set V), #A < aleph 2 →
    (∀ a, small (s a)) → small (⋃ a, s a)

namespace AlephTwoSmallness

/-- Removing a small set from a positive set preserves positivity. -/
theorem positive_sdiff
    {V : Type} (J : AlephTwoSmallness V) {x z : Set V}
    (hx : ¬J.small x) (hz : J.small z) :
    ¬J.small (x \ z) := by
  intro hdiff
  apply hx
  apply J.mono (t := (x \ z) ∪ z)
  · intro a ha
    by_cases haz : a ∈ z
    · exact Or.inr haz
    · exact Or.inl ⟨ha, haz⟩
  · exact J.union_small hdiff hz

/-- A partition of a positive set into fewer than `alephTwo` fibers has a
positive fiber. -/
theorem exists_positive_fiber
    {V P : Type} (J : AlephTwoSmallness V) (x : Set V)
    (hx : ¬J.small x) (f : V → P) (hP : #P < aleph 2) :
    ∃ p : P, ¬J.small (x ∩ f ⁻¹' {p}) := by
  by_contra h
  push Not at h
  have hall : J.small (⋃ p : P, x ∩ f ⁻¹' {p}) :=
    J.iUnion_small (fun p : P => x ∩ f ⁻¹' {p}) hP h
  apply hx
  apply J.mono (t := ⋃ p : P, x ∩ f ⁻¹' {p})
  · intro a ha
    apply Set.mem_iUnion.mpr
    exact ⟨f a, ha, by simp⟩
  · exact hall

end AlephTwoSmallness

/-- All points of the left set precede all points of the right set. -/
def BlocksBefore (left right : Set W3) : Prop :=
  ∀ x ∈ left, ∀ y ∈ right, x < y

/-- The local BHT data in the favorable maximal-sequence order.  The
`red_core` and `blue_core` fields are exactly the conclusion of the derived
ideal homogeneous-core lemma (BHT Lemma 3.4) used at the final step. -/
structure FavorableEndpointData
    (red blue : SimpleGraph W3) where
  rows : Set W3
  blocks : I1 → Set W3
  smallness : AlephTwoSmallness W3
  rows_positive : ¬smallness.small rows
  block_red : ∀ i, red.IsClique (blocks i)
  block_type : ∀ i, typeLT (blocks i) = omega 1
  blocks_ordered : ∀ {i j : I1}, i < j →
    BlocksBefore (blocks i) (blocks j)
  distinct_blocks_blue : ∀ {i j : I1}, i ≠ j →
    blue.IsCompleteBetween (blocks i) (blocks j)
  rows_before_blocks : ∀ x ∈ rows, ∀ i, ∀ y ∈ blocks i,
    x < y
  red_core : ∀ x : Set W3, x ⊆ rows →
    ¬smallness.small x →
    ∃ core : Set W3,
      core ⊆ x ∧ red.IsClique core ∧ typeLT core = omega 2
  blue_core : ∀ x : Set W3, x ⊆ rows →
    ¬smallness.small x →
    ∃ core : Set W3,
      core ⊆ x ∧ blue.IsClique core ∧ typeLT core = omega 2

variable {red blue : SimpleGraph W3}

/-- A point tagged by the good block containing it. -/
def BlockPoint (data : FavorableEndpointData red blue) : Type :=
  Sigma fun i : I1 => data.blocks i

/-- A countable transversal through pairwise distinct good blocks. -/
def BlueTransversalCode (data : FavorableEndpointData red blue) : Type :=
  {q : Nat → BlockPoint data //
    Function.Injective (fun n => (q n).1)}

/-- The actual point selected at coordinate `n` by a transversal code. -/
def BlueTransversalCode.point
    {data : FavorableEndpointData red blue}
    (q : BlueTransversalCode data) (n : Nat) : W3 :=
  (q.1 n).2.1

/-- Rows which are blue to every point of one countable transversal. -/
def blueRows (data : FavorableEndpointData red blue)
    (q : BlueTransversalCode data) : Set W3 :=
  {x | x ∈ data.rows ∧ ∀ n, blue.Adj x (q.point n)}

/-- Blocks on which a row has at least one blue neighbor. -/
def blueBlockSupport (data : FavorableEndpointData red blue)
    (x : W3) : Set I1 :=
  {i | ∃ y ∈ data.blocks i, blue.Adj x y}

private theorem block_card
    (data : FavorableEndpointData red blue) (i : I1) :
    #(data.blocks i) = aleph 1 := by
  have h := congrArg Ordinal.card (data.block_type i)
  simpa only [Ordinal.card_type, Ordinal.card_omega] using h

private theorem blockPoint_card
    (data : FavorableEndpointData red blue) :
    #(BlockPoint data) = aleph 1 := by
  rw [BlockPoint, Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun i : I1 => #(data.blocks i)) =
        Cardinal.sum (fun _ : I1 => (aleph 1 : Cardinal.{0})) := by
      congr 1
      funext i
      exact block_card data i
    _ = #I1 * aleph 1 := Cardinal.sum_const' I1 (aleph 1)
    _ = (aleph 1 : Cardinal.{0}) * aleph 1 := by
      simp only [I1, Cardinal.mk_toType, Ordinal.card_omega]
    _ = aleph 1 := by
      rw [Cardinal.aleph_mul_aleph, max_self]

/-- CH puts all countable transversals below the `alephTwo` completeness
threshold. -/
theorem blueTransversalCode_card_lt_alephTwo
    (hCH : CH) (data : FavorableEndpointData red blue) :
    #(BlueTransversalCode data) < aleph 2 := by
  calc
    #(BlueTransversalCode data) ≤ #(Nat → BlockPoint data) :=
      Cardinal.mk_subtype_le _
    _ = #(BlockPoint data) ^ #Nat := by
      rw [Cardinal.mk_arrow]
      simp only [Cardinal.lift_id]
    _ = (aleph 1 : Cardinal.{0}) ^ aleph0 := by
      rw [blockPoint_card data, Cardinal.mk_nat]
    _ = aleph 1 := hCH.aleph_one_power_aleph_zero
    _ < aleph 2 := Cardinal.aleph_lt_aleph.mpr (by norm_num)

private theorem finset_I1_card_lt_alephTwo :
    #(Finset I1) < aleph 2 := by
  let : Infinite I1 := Cardinal.infinite_iff.2 <| by
    simpa only [I1, Cardinal.mk_toType, Ordinal.card_omega] using
      Cardinal.aleph0_le_aleph (1 : Ordinal)
  calc
    #(Finset I1) = #I1 := Cardinal.mk_finset_of_infinite I1
    _ = aleph 1 := by
      simp only [I1, Cardinal.mk_toType, Ordinal.card_omega]
    _ < aleph 2 := Cardinal.aleph_lt_aleph.mpr (by norm_num)

private theorem point_mem_block
    (data : FavorableEndpointData red blue)
    (q : BlueTransversalCode data) (n : Nat) :
    q.point n ∈ data.blocks (q.1 n).1 :=
  (q.1 n).2.2

private theorem transversal_points_injective
    (data : FavorableEndpointData red blue)
    (q : BlueTransversalCode data) :
    Function.Injective q.point := by
  intro m n hmn
  apply q.2
  by_contra hindex
  rcases lt_or_gt_of_ne hindex with hlt | hgt
  · have hp := data.blocks_ordered hlt
      (q.point m) (point_mem_block data q m)
      (q.point n) (point_mem_block data q n)
    exact hp.ne hmn
  · have hp := data.blocks_ordered hgt
      (q.point n) (point_mem_block data q n)
      (q.point m) (point_mem_block data q m)
    exact hp.ne hmn.symm

private theorem transversal_range_blue
    (data : FavorableEndpointData red blue)
    (q : BlueTransversalCode data) :
    blue.IsClique (Set.range q.point) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hne
  have hmn : m ≠ n := fun h => hne (congrArg q.point h)
  have hindex : (q.1 m).1 ≠ (q.1 n).1 := fun h => hmn (q.2 h)
  exact data.distinct_blocks_blue hindex
    (point_mem_block data q m) (point_mem_block data q n)

private theorem exists_blue_tail_of_transversal
    (data : FavorableEndpointData red blue)
    (q : BlueTransversalCode data) :
    ∃ tail : Set W3,
      tail ⊆ Set.range q.point ∧ blue.IsClique tail ∧
        typeLT tail = ω := by
  have hrangeCard : #(Set.range q.point) = aleph0 := by
    rw [Cardinal.mk_range_eq q.point
      (transversal_points_injective data q)]
    exact Cardinal.mk_nat
  have homega : ω ≤ typeLT (Set.range q.point) := by
    simpa only [hrangeCard, Cardinal.ord_aleph0] using
      (Cardinal.ord_le_type
        ((· < ·) : Set.range q.point → Set.range q.point → Prop))
  obtain ⟨tail, htailSub, htailType⟩ :=
    Ordinal.exists_subset_typeLT_eq (Set.range q.point) homega
  exact ⟨tail, htailSub,
    (transversal_range_blue data q).subset htailSub, htailType⟩

private theorem blue_target_of_positive_transversal
    (data : FavorableEndpointData red blue)
    (q : BlueTransversalCode data)
    (hpositive : ¬data.smallness.small (blueRows data q)) :
    OrdinalRamsey.HasCliqueOfType blue (omega 2 + ω) := by
  have hrowSub : blueRows data q ⊆ data.rows := fun _ hx => hx.1
  obtain ⟨core, hcoreSub, hcoreBlue, hcoreType⟩ :=
    data.blue_core (blueRows data q) hrowSub hpositive
  obtain ⟨tail, htailSub, htailBlue, htailType⟩ :=
    exists_blue_tail_of_transversal data q
  have hbefore : BlocksBefore core tail := by
    intro x hx y hy
    have hxRows : x ∈ data.rows := hrowSub (hcoreSub hx)
    obtain ⟨n, rfl⟩ := htailSub hy
    exact data.rows_before_blocks x hxRows (q.1 n).1
      (q.point n) (point_mem_block data q n)
  have hcross : ∀ x ∈ core, ∀ y ∈ tail, blue.Adj x y := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := htailSub hy
    exact (hcoreSub hx).2 n
  apply Erdos1172BlockCriterion.exists_clique_type_omegaTwo_add_of_later_block
    blue hcoreBlue hcoreType
  exact ⟨tail, htailBlue, htailType, hbefore, hcross⟩

private theorem remaining_row_blueSupport_finite
    (data : FavorableEndpointData red blue)
    (bad : Set W3)
    (hbadDef : bad = ⋃ q : BlueTransversalCode data, blueRows data q)
    {x : W3} (hx : x ∈ data.rows \ bad) :
    (blueBlockSupport data x).Finite := by
  classical
  by_contra hinfinite
  have hinf : (blueBlockSupport data x).Infinite := hinfinite
  let indices : Nat ↪ blueBlockSupport data x :=
    hinf.natEmbedding (blueBlockSupport data x)
  have hexists (n : Nat) :
      ∃ y : W3,
        y ∈ data.blocks (indices n).1 ∧ blue.Adj x y :=
    (indices n).2
  let selected (n : Nat) : W3 := Classical.choose (hexists n)
  have hselected (n : Nat) :
      selected n ∈ data.blocks (indices n).1 ∧
        blue.Adj x (selected n) :=
    Classical.choose_spec (hexists n)
  let raw : Nat → BlockPoint data := fun n =>
    ⟨(indices n).1, ⟨selected n, (hselected n).1⟩⟩
  have hrawIndexInjective :
      Function.Injective (fun n => (raw n).1) := by
    intro m n hmn
    apply indices.injective
    exact Subtype.ext hmn
  let q : BlueTransversalCode data := ⟨raw, hrawIndexInjective⟩
  have hxBlue : x ∈ blueRows data q := by
    refine ⟨hx.1, ?_⟩
    intro n
    simpa only [BlueTransversalCode.point, q, raw] using (hselected n).2
  have hxBad : x ∈ bad := by
    rw [hbadDef]
    exact Set.mem_iUnion.mpr ⟨q, hxBlue⟩
  exact hx.2 hxBad

/-- The favorable maximal-sequence order closes the asymmetric endpoint:
either a positive blue countable transversal gives the blue target, or a
positive constant finite block support gives the red target. -/
theorem part2Targets_of_favorableEndpoint
    (hCH : CH) (red blue : SimpleGraph W3) (hcompl : IsCompl red blue)
    (data : FavorableEndpointData red blue) :
    OrdinalRamsey.HasCliqueOfType red (omega 2 + omega 1) ∨
      OrdinalRamsey.HasCliqueOfType blue (omega 2 + ω) := by
  classical
  let : Infinite I1 := Cardinal.infinite_iff.2 <| by
    simpa only [I1, Cardinal.mk_toType, Ordinal.card_omega] using
      Cardinal.aleph0_le_aleph (1 : Ordinal)
  by_cases hblue : ∃ q : BlueTransversalCode data,
      ¬data.smallness.small (blueRows data q)
  · obtain ⟨q, hq⟩ := hblue
    exact Or.inr (blue_target_of_positive_transversal data q hq)
  · have hallSmall (q : BlueTransversalCode data) :
        data.smallness.small (blueRows data q) := by
      by_contra hq
      exact hblue ⟨q, hq⟩
    let bad : Set W3 := ⋃ q : BlueTransversalCode data, blueRows data q
    have hbadSmall : data.smallness.small bad := by
      exact data.smallness.iUnion_small
        (fun q : BlueTransversalCode data => blueRows data q)
        (blueTransversalCode_card_lt_alephTwo hCH data) hallSmall
    let remaining : Set W3 := data.rows \ bad
    have hremainingPositive :
        ¬data.smallness.small remaining := by
      exact data.smallness.positive_sdiff data.rows_positive hbadSmall
    have hsupportFinite : ∀ x ∈ remaining,
        (blueBlockSupport data x).Finite := by
      intro x hx
      exact remaining_row_blueSupport_finite data bad rfl hx
    let supportCode : W3 → Finset I1 := fun x =>
      if hx : x ∈ remaining then
        (hsupportFinite x hx).toFinset
      else ∅
    obtain ⟨fixedSupport, hfixedPositive⟩ :=
      data.smallness.exists_positive_fiber remaining
        hremainingPositive supportCode finset_I1_card_lt_alephTwo
    let fiber : Set W3 :=
      remaining ∩ supportCode ⁻¹' {fixedSupport}
    have hfiberPositive : ¬data.smallness.small fiber := by
      simpa only [fiber] using hfixedPositive
    have hfiberSubRows : fiber ⊆ data.rows := by
      intro x hx
      exact hx.1.1
    obtain ⟨outsideBlock, houtside⟩ :=
      Infinite.exists_notMem_finset fixedSupport
    have hcrossRed : ∀ x ∈ fiber,
        ∀ y ∈ data.blocks outsideBlock, red.Adj x y := by
      intro x hx y hy
      have hxRemaining : x ∈ remaining := hx.1
      have hcodeEq : supportCode x = fixedSupport := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx.2
      have houtsideSupport : outsideBlock ∉ blueBlockSupport data x := by
        intro hs
        have hmemCode : outsideBlock ∈ supportCode x := by
          simp only [supportCode, dif_pos hxRemaining]
          exact (hsupportFinite x hxRemaining).mem_toFinset.mpr hs
        rw [hcodeEq] at hmemCode
        exact houtside hmemCode
      have hnblue : ¬blue.Adj x y := by
        intro hxy
        exact houtsideSupport ⟨y, hy, hxy⟩
      rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
      exact ⟨(data.rows_before_blocks x (hfiberSubRows hx)
        outsideBlock y hy).ne, hnblue⟩
    obtain ⟨core, hcoreSub, hcoreRed, hcoreType⟩ :=
      data.red_core fiber hfiberSubRows hfiberPositive
    have hbefore : BlocksBefore core (data.blocks outsideBlock) := by
      intro x hx y hy
      exact data.rows_before_blocks x (hfiberSubRows (hcoreSub hx))
        outsideBlock y hy
    apply Or.inl
    apply Erdos1172BlockCriterion.exists_clique_type_omegaTwo_add_of_later_block
      red hcoreRed hcoreType
    exact ⟨data.blocks outsideBlock, data.block_red outsideBlock,
      data.block_type outsideBlock, hbefore,
      fun x hx y hy => hcrossRed x (hcoreSub hx) y hy⟩

end Erdos1172BHTAsymmetricEndpointFavorableOrder
