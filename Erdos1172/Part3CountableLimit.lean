/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteCoherence

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3CountableLimit

open Erdos1172Part3Failure

/-- Removing a smaller set from an `ℵ₂`-sized set preserves cardinality. -/
private theorem mk_sdiff_eq_alephTwo_of_mk_lt
    {s t : Set W2} (hs : #s = ℵ_ 2) (ht : #t < ℵ_ 2) :
    #(s \ t : Set W2) = ℵ_ 2 := by
  apply le_antisymm
  · simpa [hs] using
      Cardinal.mk_le_mk_of_subset (Set.sdiff_subset : s \ t ⊆ s)
  · by_contra h
    have hdiff : #(s \ t : Set W2) < ℵ_ 2 := lt_of_not_ge h
    have hcover : ℵ_ 2 ≤ #(s \ t : Set W2) + #t := by
      simpa [hs] using Cardinal.le_mk_sdiff_add_mk s t
    exact (not_lt_of_ge hcover)
      (Cardinal.add_lt_of_lt (Cardinal.aleph0_le_aleph 2) hdiff ht)

/-- `ℵ₂` is regular, in the concrete form needed below. -/
private theorem alephTwo_isRegular :
    Cardinal.IsRegular (ℵ_ 2 : Cardinal.{0}) := by
  simpa only [show (2 : Ordinal.{0}) = 1 + 1 by norm_num] using
    Cardinal.isRegular_aleph_add_one (1 : Ordinal.{0})

/-- A countable family of subsets of `ω₂`, each of cardinality below
`ℵ₂`, has union of cardinality below `ℵ₂`. -/
private theorem mk_iUnion_lt_alephTwo_of_forall_lt
    (sets : ℕ → Set W2) (hsets : ∀ n, #(sets n) < ℵ_ 2) :
    #(⋃ n, sets n) < ℵ_ 2 := by
  have hindex : #ℕ < (ℵ_ 2 : Cardinal.{0}) := by
    rw [Cardinal.mk_nat]
    exact Cardinal.aleph0_lt_aleph.mpr
      (show (0 : Ordinal.{0}) < 2 by norm_num)
  exact (Cardinal.card_iUnion_lt_iff_forall_of_isRegular
    alephTwo_isRegular hindex).2 hsets

/-- Every countable sequence in `ω₂` has a strict upper bound in `ω₂`.
This is the regularity input needed to choose a genuinely later point at
a countable limit. -/
theorem exists_strict_upper_bound_of_nat_sequence (points : ℕ → W2) :
    ∃ bound : W2, ∀ n, points n < bound := by
  let covered : Set W2 := ⋃ n, Set.Iic (points n)
  have hpiece (n : ℕ) : #(Set.Iic (points n)) < ℵ_ 2 := by
    have hlt : #(Set.Iic (points n)) < #W2 :=
      Cardinal.mk_Iic_lt (points n) (by simp [W2]) (by
        simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
        exact Cardinal.aleph0_le_aleph 2)
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using hlt
  have hcovered : #covered < ℵ_ 2 :=
    mk_iUnion_lt_alephTwo_of_forall_lt
      (fun n ↦ Set.Iic (points n)) hpiece
  have hcoveredW2 : #covered < #W2 := by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using hcovered
  obtain ⟨bound, hbound⟩ := Cardinal.compl_nonempty_of_mk_lt_mk hcoveredW2
  refine ⟨bound, fun n ↦ ?_⟩
  have hnot : bound ∉ Set.Iic (points n) := by
    intro hmem
    exact hbound (Set.mem_iUnion.mpr ⟨n, hmem⟩)
  simpa only [Set.mem_Iic, not_le] using hnot

/-- If every member of a countable family loses fewer than `ℵ₂` points
from its zeroth member, then the full diagonal intersection still has
cardinality `ℵ₂`.  No nesting hypothesis is needed. -/
theorem mk_iInter_eq_alephTwo_of_small_losses
    (reservoirs : ℕ → Set W2) (hzero : #(reservoirs 0) = ℵ_ 2)
    (hloss : ∀ n, #(reservoirs 0 \ reservoirs n : Set W2) < ℵ_ 2) :
    #(⋂ n, reservoirs n) = ℵ_ 2 := by
  let lost : Set W2 := ⋃ n, reservoirs 0 \ reservoirs n
  have hlost : #lost < ℵ_ 2 :=
    mk_iUnion_lt_alephTwo_of_forall_lt
      (fun n ↦ reservoirs 0 \ reservoirs n) hloss
  have hinter : (⋂ n, reservoirs n) = reservoirs 0 \ lost := by
    ext x
    constructor
    · intro hx
      have hall := Set.mem_iInter.mp hx
      refine ⟨hall 0, ?_⟩
      intro hxlost
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxlost
      exact hn.2 (hall n)
    · rintro ⟨hxzero, hxnot⟩
      apply Set.mem_iInter.mpr
      intro n
      by_contra hxn
      exact hxnot (Set.mem_iUnion.mpr ⟨n, hxzero, hxn⟩)
  rw [hinter]
  exact mk_sdiff_eq_alephTwo_of_mk_lt hzero hlost

/-- A countable red-reservoir tower: the chosen points form an increasing
red `ω`-clique, reservoirs descend and stay `ℵ₂`, and every later
reservoir is red-adjacent to all earlier chosen points. -/
structure CountableRedReservoirTower (red : SimpleGraph W2) where
  points : ℕ → W2
  reservoirs : ℕ → Set W2
  points_strict : StrictMono points
  points_red : red.IsClique (Set.range points)
  reservoir_large : ∀ n, #(reservoirs n) = ℵ_ 2
  reservoirs_antitone : Antitone reservoirs
  prior_red : ∀ i n, i < n →
    ∀ x ∈ reservoirs n, red.Adj (points i) x

/-- Small losses at every finite stage extend a countable tower through
its limit: there is an `ℵ₂`-sized reservoir inside every previous
reservoir, all of whose points are strictly later than and red-adjacent
to every earlier chosen point.  In particular one may choose the limit
point from that same reservoir. -/
theorem CountableRedReservoirTower.exists_limit_stage_of_small_losses
    {red : SimpleGraph W2} (tower : CountableRedReservoirTower red)
    (hloss : ∀ n,
      #(tower.reservoirs 0 \ tower.reservoirs n : Set W2) < ℵ_ 2) :
    ∃ (limitReservoir : Set W2) (limitPoint : W2),
      #limitReservoir = ℵ_ 2 ∧
      limitReservoir ⊆ ⋂ n, tower.reservoirs n ∧
      limitPoint ∈ limitReservoir ∧
      (∀ n, ∀ x ∈ limitReservoir, tower.points n < x) ∧
      ∀ n, ∀ x ∈ limitReservoir, red.Adj (tower.points n) x := by
  obtain ⟨bound, hbound⟩ :=
    exists_strict_upper_bound_of_nat_sequence tower.points
  let diagonal : Set W2 := ⋂ n, tower.reservoirs n
  have hdiagonal : #diagonal = ℵ_ 2 :=
    mk_iInter_eq_alephTwo_of_small_losses tower.reservoirs
      (tower.reservoir_large 0) hloss
  have hIic : #(Set.Iic bound) < ℵ_ 2 := by
    have hlt : #(Set.Iic bound) < #W2 :=
      Cardinal.mk_Iic_lt bound (by simp [W2]) (by
        simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
        exact Cardinal.aleph0_le_aleph 2)
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using hlt
  let limitReservoir : Set W2 := diagonal \ Set.Iic bound
  have hlimitCard : #limitReservoir = ℵ_ 2 :=
    mk_sdiff_eq_alephTwo_of_mk_lt hdiagonal hIic
  have hlimitNonempty : limitReservoir.Nonempty := by
    apply Cardinal.mk_set_ne_zero_iff.mp
    rw [hlimitCard]
    exact (Cardinal.aleph_pos 2).ne'
  obtain ⟨limitPoint, hlimitPoint⟩ := hlimitNonempty
  have hlimitSub : limitReservoir ⊆ diagonal := Set.sdiff_subset
  have hlater (n : ℕ) (x : W2) (hx : x ∈ limitReservoir) :
      tower.points n < x := by
    have hbx : bound < x := by
      simpa only [Set.mem_Iic, not_le] using hx.2
    exact (hbound n).trans hbx
  have hred (n : ℕ) (x : W2) (hx : x ∈ limitReservoir) :
      red.Adj (tower.points n) x := by
    apply tower.prior_red n (n + 1) (Nat.lt_succ_self n)
    exact Set.mem_iInter.mp (hlimitSub hx) (n + 1)
  exact ⟨limitReservoir, limitPoint, hlimitCard, hlimitSub,
    hlimitPoint, hlater, hred⟩

/-- The limit-stage data supplied by small losses extends the red clique
from exact type `ω` to exact type `ω + 1`. -/
theorem CountableRedReservoirTower.hasCliqueOfType_omega_add_one_of_small_losses
    {red : SimpleGraph W2} (tower : CountableRedReservoirTower red)
    (hloss : ∀ n,
      #(tower.reservoirs 0 \ tower.reservoirs n : Set W2) < ℵ_ 2) :
    OrdinalRamsey.HasCliqueOfType red (ω + 1) := by
  obtain ⟨limitReservoir, limitPoint, -, -, hlimitPoint,
      hlater, hred⟩ := tower.exists_limit_stage_of_small_losses hloss
  have hpointsType : typeLT (Set.range tower.points) = ω := by
    have htype :=
      ((tower.points_strict.strictMonoOn Set.univ).orderIso
        tower.points Set.univ).ordinalType_congr
    have himageRange :
        typeLT (tower.points '' Set.univ) =
          typeLT (Set.range tower.points) :=
      (OrderIso.setCongr (tower.points '' Set.univ)
        (Set.range tower.points) Set.image_univ).ordinalType_congr
    calc
      typeLT (Set.range tower.points) =
          typeLT (tower.points '' Set.univ) := himageRange.symm
      _ = typeLT (Set.univ : Set ℕ) := htype.symm
      _ = typeLT ℕ := OrderIso.Set.univ.ordinalType_congr
      _ = ω := Ordinal.type_nat_lt
  obtain ⟨clique, hclique, hcliqueType⟩ :=
    red.exists_clique_type_add_one_of_common_later tower.points_red
      hpointsType (x := limitPoint)
      (by rintro _ ⟨n, rfl⟩; exact hlater n limitPoint hlimitPoint)
      (by rintro _ ⟨n, rfl⟩; exact hred n limitPoint hlimitPoint)
  exact ⟨clique, hclique, hcliqueType⟩

/-- Exact obstruction classification for countable limit preservation.
Either the tower extends through the countable limit, or some finite
stage has already discarded a full `ℵ₂`-sized subset of the initial
reservoir. -/
theorem CountableRedReservoirTower.exists_limit_stage_or_full_loss
    {red : SimpleGraph W2} (tower : CountableRedReservoirTower red) :
    (∃ (limitReservoir : Set W2) (limitPoint : W2),
      #limitReservoir = ℵ_ 2 ∧
      limitReservoir ⊆ ⋂ n, tower.reservoirs n ∧
      limitPoint ∈ limitReservoir ∧
      (∀ n, ∀ x ∈ limitReservoir, tower.points n < x) ∧
      ∀ n, ∀ x ∈ limitReservoir, red.Adj (tower.points n) x) ∨
      ∃ n, #(tower.reservoirs 0 \ tower.reservoirs n : Set W2) = ℵ_ 2 := by
  by_cases hloss : ∀ n,
      #(tower.reservoirs 0 \ tower.reservoirs n : Set W2) < ℵ_ 2
  · exact Or.inl (tower.exists_limit_stage_of_small_losses hloss)
  · right
    push Not at hloss
    obtain ⟨n, hn⟩ := hloss
    refine ⟨n, le_antisymm ?_ hn⟩
    simpa [tower.reservoir_large 0] using
      Cardinal.mk_le_mk_of_subset
        (Set.sdiff_subset : tower.reservoirs 0 \ tower.reservoirs n ⊆
          tower.reservoirs 0)

end Erdos1172Part3CountableLimit
