/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FailureFiber
public import Erdos1172.ForMathlib.SetTheory.Ordinal.CliqueBlockExtension

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3FiniteStars

open Erdos1172Part3Failure

noncomputable abbrev RedTarget : Ordinal :=
  (ω_ 1 : Ordinal.{0}) ^ (ω + 2) + 2

/-- Removing a smaller set from a set of infinite cardinality `k` preserves
cardinality.  This local form only uses the cardinal arithmetic already in
the compiled dependency graph. -/
private theorem mk_sdiff_eq_of_mk_eq_of_mk_lt {s t : Set W2} {k : Cardinal.{0}}
    (hk : ℵ₀ ≤ k) (hs : #s = k) (ht : #t < k) : #(s \ t : Set W2) = k := by
  apply le_antisymm
  · simpa [hs] using Cardinal.mk_le_mk_of_subset (Set.sdiff_subset : s \ t ⊆ s)
  · by_contra h
    have hdiff : #(s \ t : Set W2) < k := lt_of_not_ge h
    have hcover : k ≤ #(s \ t : Set W2) + #t := by
      simpa [hs] using Cardinal.le_mk_sdiff_add_mk s t
    exact (not_lt_of_ge hcover) (Cardinal.add_lt_of_lt hk hdiff ht)

/-- Removing finitely many points from a set of cardinality `ℵ₁` preserves
cardinality `ℵ₁`. -/
theorem mk_sdiff_finset_eq_alephOne {s : Set W2} (hs : #s = ℵ_ 1)
    (c : Finset W2) : #(s \ (c : Set W2) : Set W2) = ℵ_ 1 := by
  calc
    #(s \ (c : Set W2) : Set W2) = ℵ_ 1 :=
      mk_sdiff_eq_of_mk_eq_of_mk_lt (k := ℵ_ 1)
        (Cardinal.aleph0_le_aleph 1) hs
          ((Cardinal.finset_card_lt_aleph0 c).trans_le
            (Cardinal.aleph0_le_aleph 1))

/-- A finite set of deleted points leaves an `ω₁`-type subset of a base of
cardinality `ℵ₁`. -/
theorem exists_omegaOne_core_away_from_finset
    (blue : SimpleGraph W2) {base : Set W2}
    (hbase : blue.IsClique base) (hbaseType : typeLT base = ω_ 1 + 1)
    (c : Finset W2) :
    ∃ core : Set W2, core ⊆ base \ (c : Set W2) ∧
      blue.IsClique core ∧ typeLT core = ω_ 1 := by
  have hbaseCard : #base = ℵ_ 1 := by
    have hc := congrArg Ordinal.card hbaseType
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  have hremCard : #(base \ (c : Set W2) : Set W2) = ℵ_ 1 :=
    mk_sdiff_finset_eq_alephOne hbaseCard c
  have hle : (ω_ 1 : Ordinal.{0}) ≤
      typeLT ((base \ (c : Set W2) : Set W2)) := by
    simpa only [hremCard, Cardinal.ord_aleph] using
      (Cardinal.ord_le_type ((· < ·) :
        ((base \ (c : Set W2) : Set W2)) →
        ((base \ (c : Set W2) : Set W2)) → Prop))
  obtain ⟨core, hcoreSub, hcoreType⟩ :=
    Ordinal.exists_subset_typeLT_eq (base \ (c : Set W2) : Set W2) hle
  exact ⟨core, hcoreSub, hbase.subset (hcoreSub.trans sdiff_subset), hcoreType⟩

/-- The vertices in a large reservoir which are blue-adjacent to every
undeleted base point cannot themselves have size `ℵ₂`: a red `ω₂` inside
would contain the Part 3 red target, while a blue `ω+1` supplies two later
points which extend an `ω₁` core to the forbidden blue `ω₁+2`. -/
theorem mk_unwitnessed_lt_alephTwo
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base reservoir : Set W2} {m : W2} (hm : m ∈ base)
    (hmMax : IsMax (⟨m, hm⟩ : base))
    (hbase : blue.IsClique base) (hbaseType : typeLT base = ω_ 1 + 1)
    (hreservoirTail : reservoir ⊆ Set.Ioi m)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (centers : Finset W2) :
    #{x : W2 | x ∈ reservoir ∧
      ∀ y ∈ base \ (centers : Set W2), blue.Adj y x} < ℵ_ 2 := by
  let unwitnessed : Set W2 := {x | x ∈ reservoir ∧
    ∀ y ∈ base \ (centers : Set W2), blue.Adj y x}
  have hle : #unwitnessed ≤ ℵ_ 2 := by
    calc
      #unwitnessed ≤ #W2 := Cardinal.mk_set_le unwitnessed
      _ = ℵ_ 2 := by simp [W2]
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hutype : typeLT unwitnessed = ω_ 2 :=
    typeLT_eq_omegaTwo_of_mk_eq heq
  obtain ⟨t, htSub, htRed, htType⟩ | ⟨t, htSub, htBlue, htType⟩ :=
    OrdinalRamsey.on_set_of_type
      Ordinal.ordinalRamsey_omega_two_omega_two_omega_add_one
      red blue hcompl unwitnessed hutype
  · obtain ⟨z, hzSub, hzType⟩ := Ordinal.exists_subset_typeLT_eq t
      (part3_red_target_lt_omegaTwo.le.trans_eq htType.symm)
    exact hnoRed ⟨z, htRed.subset hzSub, hzType⟩
  · obtain ⟨core, hcoreSub, hcoreBlue, hcoreType⟩ :=
      exists_omegaOne_core_away_from_finset blue hbase hbaseType centers
    have htwo : (2 : Ordinal.{0}) ≤ ω + 1 :=
      (Ordinal.natCast_lt_omega0 2).le.trans le_self_add
    obtain ⟨pair, hpairSub, hpairType⟩ :=
      Ordinal.exists_subset_typeLT_eq t (htType ▸ htwo)
    have hpairBlue : blue.IsClique pair := htBlue.subset hpairSub
    have hlater : ∀ x ∈ core, ∀ y ∈ pair, x < y := by
      intro x hx y hy
      have hxm : x ≤ m := by
        have hxbase : x ∈ base := sdiff_subset (hcoreSub hx)
        have hxle : (⟨x, hxbase⟩ : base) ≤ ⟨m, hm⟩ :=
          le_of_not_gt ((isMax_iff_forall_not_lt.mp hmMax) ⟨x, hxbase⟩)
        exact hxle
      have hyu : y ∈ unwitnessed := htSub (hpairSub hy)
      exact hxm.trans_lt (hreservoirTail hyu.1)
    have hcross : ∀ x ∈ core, ∀ y ∈ pair, blue.Adj x y := by
      intro x hx y hy
      have hyu : y ∈ unwitnessed := htSub (hpairSub hy)
      exact hyu.2 x (hcoreSub hx)
    exact hnoBlue <| blue.exists_clique_type_add_of_later_block
      hcoreBlue hpairBlue hcoreType hpairType hlater hcross

/-- One finite-star extension step.  A finite blue set of centres with an
`ℵ₂` common red neighborhood can be enlarged by a fresh base point while
retaining an `ℵ₂` common red neighborhood. -/
theorem exists_fresh_center_large_common_red_fiber
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base reservoir : Set W2} {m : W2} (hm : m ∈ base)
    (hmMax : IsMax (⟨m, hm⟩ : base))
    (hbase : blue.IsClique base) (hbaseType : typeLT base = ω_ 1 + 1)
    (hreservoirCard : #reservoir = ℵ_ 2)
    (hreservoirTail : reservoir ⊆ Set.Ioi m)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (centers : Finset W2) (_hcentersBase : (centers : Set W2) ⊆ base)
    (hstar : ∀ y ∈ centers, ∀ x ∈ reservoir, red.Adj y x) :
    ∃ (newCenter : W2) (newFiber : Set W2),
      newCenter ∈ base ∧ newCenter ∉ centers ∧
      newFiber ⊆ reservoir ∧ #newFiber = ℵ_ 2 ∧
      (∀ y ∈ insert newCenter centers, ∀ x ∈ newFiber, red.Adj y x) := by
  classical
  let unwitnessed : Set W2 := {x | x ∈ reservoir ∧
    ∀ y ∈ base \ (centers : Set W2), blue.Adj y x}
  have huSmall : #unwitnessed < ℵ_ 2 :=
    mk_unwitnessed_lt_alephTwo red blue hcompl hm hmMax hbase hbaseType
      hreservoirTail hnoRed hnoBlue centers
  let witnessed : Set W2 := reservoir \ unwitnessed
  have hwitnessedCard : #witnessed = ℵ_ 2 := by
    exact mk_sdiff_eq_of_mk_eq_of_mk_lt (k := ℵ_ 2)
      (Cardinal.aleph0_le_aleph 2) hreservoirCard huSmall
  have hwitness (x : witnessed) :
      ∃ y : ((base \ (centers : Set W2) : Set W2)), red.Adj y x := by
    have hxR : (x : W2) ∈ reservoir := x.property.1
    have hxNotU : (x : W2) ∉ unwitnessed := x.property.2
    have hnotall : ¬ ∀ y ∈ base \ (centers : Set W2), blue.Adj y x := by
      intro hall
      exact hxNotU ⟨hxR, hall⟩
    push Not at hnotall
    obtain ⟨y, hyRem, hyNotBlue⟩ := hnotall
    refine ⟨⟨y, hyRem⟩, ?_⟩
    rw [← hcompl.symm.compl_eq, SimpleGraph.compl_adj]
    refine ⟨?_, hyNotBlue⟩
    have hym : y ≤ m := by
      have hybase : y ∈ base := hyRem.1
      have hyle : (⟨y, hybase⟩ : base) ≤ ⟨m, hm⟩ :=
        le_of_not_gt ((isMax_iff_forall_not_lt.mp hmMax) ⟨y, hybase⟩)
      exact hyle
    exact (hym.trans_lt (hreservoirTail hxR)).ne
  let failure : witnessed → ((base \ (centers : Set W2) : Set W2)) :=
    fun x ↦ Classical.choose (hwitness x)
  have hfailure (x : witnessed) : red.Adj (failure x) x :=
    Classical.choose_spec (hwitness x)
  have hbaseCard : #base = ℵ_ 1 := by
    have hc := congrArg Ordinal.card hbaseType
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  have hremainingCard : #(base \ (centers : Set W2) : Set W2) = ℵ_ 1 :=
    mk_sdiff_finset_eq_alephOne hbaseCard centers
  obtain ⟨newCenter, hlargeFiber⟩ := Cardinal.infinite_pigeonhole failure
    (by rw [hwitnessedCard]; exact Cardinal.aleph0_le_aleph 2)
    (by
      rw [hremainingCard, hwitnessedCard]
      rw [show (ℵ_ 2 : Cardinal.{0}) = ℵ_ ((1 : Ordinal.{0}) + 1) by norm_num,
        (Cardinal.isRegular_aleph_add_one 1).cof_ord]
      exact Cardinal.aleph_lt_aleph.mpr (by norm_num))
  let newFiber : Set W2 := Subtype.val '' (failure ⁻¹' {newCenter})
  have hnewFiberSub : newFiber ⊆ reservoir := by
    rintro x ⟨z, hz, rfl⟩
    exact z.property.1
  refine ⟨newCenter, newFiber, newCenter.property.1, newCenter.property.2,
    hnewFiberSub, ?_, ?_⟩
  · calc
      #newFiber = #(failure ⁻¹' {newCenter}) :=
        Cardinal.mk_image_eq Subtype.val_injective
      _ = #witnessed := hlargeFiber
      _ = ℵ_ 2 := hwitnessedCard
  · intro y hy x hx
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · obtain ⟨z, hz, rfl⟩ := hx
      have hzeq : failure z = newCenter := by
        simpa only [mem_preimage, mem_singleton_iff] using hz
      simpa only [hzeq] using hfailure z
    · exact hstar y hy x (hnewFiberSub hx)

/-- Under failure of both exact Part 3 targets, arbitrarily large finite
subsets of the blue base have an `ℵ₂` common red neighborhood above the
maximum of the base. -/
theorem exists_arbitrarily_large_finite_star_reservoirs
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    ∃ m : W2, m ∈ base ∧ ∀ n : ℕ,
      ∃ (centers : Finset W2) (reservoir : Set W2),
        centers.card = n ∧ (centers : Set W2) ⊆ base ∧
        blue.IsClique (centers : Set W2) ∧
        #reservoir = ℵ_ 2 ∧ reservoir ⊆ Set.Ioi m ∧
        ∀ y ∈ centers, ∀ x ∈ reservoir, red.Adj y x := by
  classical
  obtain ⟨m, hmMax⟩ := exists_max_of_type_omegaOne_add_one hbaseType
  refine ⟨m, m.property, fun n ↦ ?_⟩
  induction n with
  | zero =>
      refine ⟨∅, Set.Ioi (m : W2), by simp, by simp, ?_,
        mk_Ioi_omegaTwo_eq m, Subset.rfl, ?_⟩
      · exact hbase.subset (by simp)
      · simp
  | succ n ih =>
      obtain ⟨centers, reservoir, hcard, hcentersBase, hcentersBlue,
        hreservoirCard, hreservoirTail, hstar⟩ := ih
      obtain ⟨newCenter, newFiber, hnewBase, hnewFresh, hnewSub,
        hnewCard, hnewStar⟩ :=
        exists_fresh_center_large_common_red_fiber red blue hcompl
          m.property hmMax hbase hbaseType hreservoirCard hreservoirTail
          hnoRed hnoBlue centers hcentersBase hstar
      refine ⟨insert newCenter centers, newFiber, ?_, ?_, ?_, hnewCard,
        hnewSub.trans hreservoirTail, hnewStar⟩
      · rw [Finset.card_insert_of_notMem hnewFresh, hcard]
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_insert] at hx
        exact hx.elim (fun h ↦ h ▸ hnewBase) (hcentersBase ·)
      · apply hbase.subset
        intro x hx
        rw [Finset.mem_coe, Finset.mem_insert] at hx
        exact hx.elim (fun h ↦ h ▸ hnewBase) (hcentersBase ·)

/-- Main iterated strengthening of the one-star failure-fiber theorem.
If the red target does not already occur, then for every finite size there
is a blue set of that size in the original base with an `ℵ₂` common red
neighborhood above the base maximum. -/
theorem red_target_or_arbitrarily_large_finite_stars
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      ∃ m : W2, m ∈ base ∧ ∀ n : ℕ,
        ∃ (centers : Finset W2) (reservoir : Set W2),
          centers.card = n ∧ (centers : Set W2) ⊆ base ∧
          blue.IsClique (centers : Set W2) ∧
          #reservoir = ℵ_ 2 ∧ reservoir ⊆ Set.Ioi m ∧
          ∀ y ∈ centers, ∀ x ∈ reservoir, red.Adj y x := by
  by_cases hred : OrdinalRamsey.HasCliqueOfType red RedTarget
  · exact Or.inl hred
  · exact Or.inr <|
      exists_arbitrarily_large_finite_star_reservoirs red blue hcompl
        hbase hbaseType hred hnoBlue

/-- In the absence of the exact red target, every `ℵ₂`-sized set contains
a blue clique of type `ω+1`.  This is the hereditary form of the
Erdős--Dushnik--Miller alternative used by the star iteration. -/
theorem exists_blue_omega_add_one_in_every_alephTwo_set
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    {s : Set W2} (hs : #s = ℵ_ 2) :
    ∃ t : Set W2, t ⊆ s ∧ blue.IsClique t ∧ typeLT t = ω + 1 := by
  have hstype : typeLT s = ω_ 2 := typeLT_eq_omegaTwo_of_mk_eq hs
  obtain ⟨t, htSub, htRed, htType⟩ | ⟨t, htSub, htBlue, htType⟩ :=
    OrdinalRamsey.on_set_of_type
      Ordinal.ordinalRamsey_omega_two_omega_two_omega_add_one
      red blue hcompl s hstype
  · obtain ⟨z, hzSub, hzType⟩ := Ordinal.exists_subset_typeLT_eq t
      (part3_red_target_lt_omegaTwo.le.trans_eq htType.symm)
    exact (hnoRed ⟨z, htRed.subset hzSub, hzType⟩).elim
  · exact ⟨t, htSub, htBlue, htType⟩

/-- Fully strengthened failure alternative.  For every finite `n` there is
a blue `n`-point subset of the original base with an `ℵ₂` common red
neighborhood; moreover every `ℵ₂`-sized subreservoir still contains a blue
`ω+1` arm.  Taking `n = 1` and the whole reservoir recovers the earlier
one-star conclusion, while all larger `n` are genuine finite iterations. -/
theorem red_target_or_arbitrarily_large_finite_stars_with_hereditary_blue_arms
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      ∃ m : W2, m ∈ base ∧ ∀ n : ℕ,
        ∃ (centers : Finset W2) (reservoir : Set W2),
          centers.card = n ∧ (centers : Set W2) ⊆ base ∧
          blue.IsClique (centers : Set W2) ∧
          #reservoir = ℵ_ 2 ∧ reservoir ⊆ Set.Ioi m ∧
          (∀ y ∈ centers, ∀ x ∈ reservoir, red.Adj y x) ∧
          ∀ s : Set W2, s ⊆ reservoir → #s = ℵ_ 2 →
            ∃ t : Set W2, t ⊆ s ∧ blue.IsClique t ∧ typeLT t = ω + 1 := by
  by_cases hred : OrdinalRamsey.HasCliqueOfType red RedTarget
  · exact Or.inl hred
  · right
    obtain ⟨m, hm, hfinite⟩ :=
      exists_arbitrarily_large_finite_star_reservoirs red blue hcompl
        hbase hbaseType hred hnoBlue
    refine ⟨m, hm, fun n ↦ ?_⟩
    obtain ⟨centers, reservoir, hcard, hcentersBase, hcentersBlue,
      hreservoirCard, hreservoirTail, hstar⟩ := hfinite n
    exact ⟨centers, reservoir, hcard, hcentersBase, hcentersBlue,
      hreservoirCard, hreservoirTail, hstar,
      fun s _ hs ↦
        exists_blue_omega_add_one_in_every_alephTwo_set red blue hcompl hred hs⟩

/-- Compact biclique form of the iteration.  Unless the exact red target
already exists, for every finite `n` there are a blue `n`-point clique in
the original base and a blue `ω+1` clique above it, with every cross-edge
red.  The case `n = 1` is precisely the old one-centre star alternative. -/
theorem red_target_or_all_finite_by_omega_add_one_bicolored_stars
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      ∀ n : ℕ, ∃ (centers : Finset W2) (arm : Set W2),
        centers.card = n ∧ (centers : Set W2) ⊆ base ∧
        blue.IsClique (centers : Set W2) ∧
        blue.IsClique arm ∧ typeLT arm = ω + 1 ∧
        ∀ y ∈ centers, ∀ x ∈ arm, red.Adj y x := by
  obtain hred | ⟨m, hm, hiterate⟩ :=
    red_target_or_arbitrarily_large_finite_stars_with_hereditary_blue_arms
      red blue hcompl hbase hbaseType hnoBlue
  · exact Or.inl hred
  · right
    intro n
    obtain ⟨centers, reservoir, hcard, hcentersBase, hcentersBlue,
      hreservoirCard, hreservoirTail, hstar, hhereditary⟩ := hiterate n
    obtain ⟨arm, harmSub, harmBlue, harmType⟩ :=
      hhereditary reservoir Subset.rfl hreservoirCard
    exact ⟨centers, arm, hcard, hcentersBase, hcentersBlue,
      harmBlue, harmType,
      fun y hy x hx ↦ hstar y hy x (harmSub hx)⟩

end Erdos1172Part3FiniteStars
