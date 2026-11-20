/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Order.WellQuasiOrder
public import Erdos1172.Part3FiniteStars

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3InfiniteStars

open Erdos1172Part3Failure Erdos1172Part3FiniteStars

private structure StarState (red : SimpleGraph W2) (base : Set W2) (m : W2) where
  centers : Finset W2
  reservoir : Set W2
  centersBase : (centers : Set W2) ⊆ base
  reservoirCard : #reservoir = ℵ_ 2
  reservoirTail : reservoir ⊆ Set.Ioi m
  star : ∀ y ∈ centers, ∀ x ∈ reservoir, red.Adj y x

private def initialState (red : SimpleGraph W2) (base : Set W2) (m : W2) :
    StarState red base m where
  centers := ∅
  reservoir := Set.Ioi m
  centersBase := by simp
  reservoirCard := mk_Ioi_omegaTwo_eq m
  reservoirTail := Subset.rfl
  star := by simp

private structure StarStepData (red : SimpleGraph W2) (base : Set W2) (m : W2)
    (s : StarState red base m) where
  center : W2
  fiber : Set W2
  centerBase : center ∈ base
  centerFresh : center ∉ s.centers
  fiberSub : fiber ⊆ s.reservoir
  fiberCard : #fiber = ℵ_ 2
  star : ∀ y ∈ insert center s.centers, ∀ x ∈ fiber, red.Adj y x

private theorem starStepData_nonempty
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (base : Set W2) (m : W2) (hm : m ∈ base)
    (hmMax : IsMax (⟨m, hm⟩ : base))
    (hbase : blue.IsClique base) (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (s : StarState red base m) :
    Nonempty (StarStepData red base m s) := by
  obtain ⟨center, fiber, hcenterBase, hcenterFresh, hfiberSub,
    hfiberCard, hstar⟩ :=
    exists_fresh_center_large_common_red_fiber red blue hcompl
      hm hmMax hbase hbaseType s.reservoirCard s.reservoirTail
      hnoRed hnoBlue s.centers s.centersBase s.star
  exact ⟨{
    center := center
    fiber := fiber
    centerBase := hcenterBase
    centerFresh := hcenterFresh
    fiberSub := hfiberSub
    fiberCard := hfiberCard
    star := hstar }⟩

private noncomputable def chooseStarStepData
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (base : Set W2) (m : W2) (hm : m ∈ base)
    (hmMax : IsMax (⟨m, hm⟩ : base))
    (hbase : blue.IsClique base) (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (s : StarState red base m) : StarStepData red base m s :=
  Classical.choice (starStepData_nonempty red blue hcompl base m hm hmMax
    hbase hbaseType hnoRed hnoBlue s)

private noncomputable def nextState
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    (base : Set W2) (m : W2) (hm : m ∈ base)
    (hmMax : IsMax (⟨m, hm⟩ : base))
    (hbase : blue.IsClique base) (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (s : StarState red base m) : StarState red base m := by
  let d := chooseStarStepData red blue hcompl base m hm hmMax hbase hbaseType
    hnoRed hnoBlue s
  exact {
    centers := insert d.center s.centers
    reservoir := d.fiber
    centersBase := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_insert] at hx
      exact hx.elim (fun h ↦ h ▸ d.centerBase) (s.centersBase ·)
    reservoirCard := d.fiberCard
    reservoirTail := d.fiberSub.trans s.reservoirTail
    star := d.star }

/-- Failure of both exact targets yields one recursively coherent sequence
of distinct blue base centres and nested `ℵ₂` reservoirs.  Reservoir `n`
is red-adjacent to every centre chosen before stage `n`. -/
theorem exists_coherent_infinite_center_reservoir_sequence
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    ∃ (m : W2) (centers : ℕ → W2) (reservoirs : ℕ → Set W2),
      m ∈ base ∧ Function.Injective centers ∧
      (∀ n, centers n ∈ base) ∧ blue.IsClique (Set.range centers) ∧
      (∀ n, #(reservoirs n) = ℵ_ 2 ∧ reservoirs n ⊆ Set.Ioi m) ∧
      (∀ n, reservoirs (n + 1) ⊆ reservoirs n) ∧
      ∀ i n, i < n → ∀ x ∈ reservoirs n, red.Adj (centers i) x := by
  classical
  obtain ⟨m, hmMax⟩ := exists_max_of_type_omegaOne_add_one hbaseType
  let data : ∀ s : StarState red base m, StarStepData red base m s := fun s ↦
    chooseStarStepData red blue hcompl base m m.property hmMax
      hbase hbaseType hnoRed hnoBlue s
  let step : StarState red base m → StarState red base m := fun s ↦
    nextState red blue hcompl base m m.property hmMax
      hbase hbaseType hnoRed hnoBlue s
  let states : ℕ → StarState red base m := fun n ↦ step^[n] (initialState red base m)
  let centers : ℕ → W2 := fun n ↦ (data (states n)).center
  let reservoirs : ℕ → Set W2 := fun n ↦ (states n).reservoir
  have hstatesSucc (n : ℕ) : states (n + 1) = step (states n) := by
    simp only [states, Function.iterate_succ_apply']
  have hcentersSucc (n : ℕ) :
      (states (n + 1)).centers = insert (centers n) (states n).centers := by
    rw [hstatesSucc]
    rfl
  have hreservoirsSucc (n : ℕ) : reservoirs (n + 1) ⊆ reservoirs n := by
    rw [show reservoirs (n + 1) = (states (n + 1)).reservoir by rfl,
      hstatesSucc]
    exact (data (states n)).fiberSub
  have hcenterBase (n : ℕ) : centers n ∈ base :=
    (data (states n)).centerBase
  have hcenterFresh (n : ℕ) : centers n ∉ (states n).centers :=
    (data (states n)).centerFresh
  have hcenterMemSucc (n : ℕ) : centers n ∈ (states (n + 1)).centers := by
    rw [hcentersSucc]
    exact Finset.mem_insert_self _ _
  have hstateCentersStep (n : ℕ) :
      (states n).centers ⊆ (states (n + 1)).centers := by
    rw [hcentersSucc]
    exact Finset.subset_insert _ _
  have hstateCentersMono : Monotone fun n ↦ (states n).centers :=
    monotone_nat_of_le_succ hstateCentersStep
  have hcenterMemOfLt {i n : ℕ} (hin : i < n) :
      centers i ∈ (states n).centers :=
    hstateCentersMono (Nat.succ_le_iff.mpr hin) (hcenterMemSucc i)
  have hcentersInjective : Function.Injective centers := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij' | hji'
    · exact hcenterFresh j (hij ▸ hcenterMemOfLt hij')
    · exact hcenterFresh i (hij.symm ▸ hcenterMemOfLt hji')
  have hcentersClique : blue.IsClique (Set.range centers) := by
    apply hbase.subset
    rintro _ ⟨n, rfl⟩
    exact hcenterBase n
  refine ⟨m, centers, reservoirs, m.property, hcentersInjective,
    hcenterBase, hcentersClique, ?_, hreservoirsSucc, ?_⟩
  · intro n
    exact ⟨(states n).reservoirCard, (states n).reservoirTail⟩
  · intro i n hin x hx
    exact (states n).star (centers i) (hcenterMemOfLt hin) x hx

/-- Every `ℵ₂`-sized subset of `ω₂` has a point above any prescribed
cutoff. -/
private theorem exists_mem_gt_of_mk_eq_alephTwo {s : Set W2}
    (hs : #s = ℵ_ 2) (cutoff : W2) : ∃ x ∈ s, cutoff < x := by
  by_contra h
  push Not at h
  have hsub : s ⊆ Set.Iic cutoff := by
    intro x hx
    exact h x hx
  have hle : #s ≤ #(Set.Iic cutoff) := Cardinal.mk_le_mk_of_subset hsub
  have hIic : #(Set.Iic cutoff) < ℵ_ 2 := by
    have hlt : #(Set.Iic cutoff) < #W2 :=
      Cardinal.mk_Iic_lt cutoff (by simp [W2]) (by
        simp only [W2, Cardinal.mk_toType, Ordinal.card_omega]
        exact Cardinal.aleph0_le_aleph 2)
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using hlt
  rw [hs] at hle
  exact (not_le_of_gt hIic) hle

/-- The range of a strictly increasing sequence has exact order type `ω`. -/
private theorem typeLT_range_eq_omega_of_strictMono (f : ℕ → W2)
    (hf : StrictMono f) : typeLT (Set.range f) = ω := by
  have htype :=
    ((hf.strictMonoOn Set.univ).orderIso f Set.univ).ordinalType_congr
  have himageRange : typeLT (f '' Set.univ) = typeLT (Set.range f) :=
    (OrderIso.setCongr (f '' Set.univ) (Set.range f) Set.image_univ).ordinalType_congr
  calc
    typeLT (Set.range f) = typeLT (f '' Set.univ) := himageRange.symm
    _ = typeLT (Set.univ : Set ℕ) := htype.symm
    _ = typeLT ℕ := OrderIso.Set.univ.ordinalType_congr
    _ = ω := Ordinal.type_nat_lt

/-- Either the exact red target occurs, or there are a blue sequence of
distinct base centres `yᵢ`, a strictly increasing arm sequence `xₙ`, and
nested `ℵ₂` reservoirs such that `yᵢ` is red-adjacent to `xₙ` whenever
`i ≤ n`. -/
theorem red_target_or_infinite_triangular_red_pattern
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      ∃ (m : W2) (centers arms : ℕ → W2) (reservoirs : ℕ → Set W2),
        m ∈ base ∧ Function.Injective centers ∧ StrictMono arms ∧
        (∀ n, centers n ∈ base) ∧ blue.IsClique (Set.range centers) ∧
        (∀ n, #(reservoirs n) = ℵ_ 2 ∧ reservoirs n ⊆ Set.Ioi m) ∧
        (∀ n, reservoirs (n + 1) ⊆ reservoirs n) ∧
        (∀ n, arms n ∈ reservoirs (n + 1)) ∧
        ∀ i n, i ≤ n → red.Adj (centers i) (arms n) := by
  classical
  by_cases hred : OrdinalRamsey.HasCliqueOfType red RedTarget
  · exact Or.inl hred
  · right
    obtain ⟨m, centers, reservoirs, hm, hcentersInjective, hcentersBase,
      hcentersBlue, hreservoirs, hreservoirsNested, hstar⟩ :=
      exists_coherent_infinite_center_reservoir_sequence red blue hcompl
        hbase hbaseType hred hnoBlue
    let above (n : ℕ) (cutoff : W2) : W2 :=
      Classical.choose
        (exists_mem_gt_of_mk_eq_alephTwo (hreservoirs (n + 1)).1 cutoff)
    have haboveMem (n : ℕ) (cutoff : W2) : above n cutoff ∈ reservoirs (n + 1) :=
      (Classical.choose_spec
        (exists_mem_gt_of_mk_eq_alephTwo (hreservoirs (n + 1)).1 cutoff)).1
    have haboveGt (n : ℕ) (cutoff : W2) : cutoff < above n cutoff :=
      (Classical.choose_spec
        (exists_mem_gt_of_mk_eq_alephTwo (hreservoirs (n + 1)).1 cutoff)).2
    let arms : ℕ → W2 := fun n ↦
      Nat.rec (above 0 m) (fun k previous ↦ above (k + 1) previous) n
    have harmsZero : arms 0 = above 0 m := rfl
    have harmsSucc (n : ℕ) : arms (n + 1) = above (n + 1) (arms n) := by
      rfl
    have harmsMem (n : ℕ) : arms n ∈ reservoirs (n + 1) := by
      cases n with
      | zero => rw [harmsZero]; exact haboveMem 0 m
      | succ n => rw [harmsSucc]; exact haboveMem (n + 1) (arms n)
    have harmsLtSucc (n : ℕ) : arms n < arms (n + 1) := by
      rw [harmsSucc]
      exact haboveGt (n + 1) (arms n)
    have harmsStrict : StrictMono arms :=
      strictMono_nat_of_lt_succ harmsLtSucc
    refine ⟨m, centers, arms, reservoirs, hm, hcentersInjective, harmsStrict,
      hcentersBase, hcentersBlue, hreservoirs, hreservoirsNested,
      harmsMem, ?_⟩
    intro i n hin
    exact hstar i (n + 1) (Nat.lt_succ_iff.mpr hin) (arms n) (harmsMem n)

/-- Ordered refinement of the triangular obstruction.  Both the blue
centre sequence and the arm sequence are strictly increasing and hence
have exact order type `ω`; the sampled reservoirs remain nested and of
cardinality `ℵ₂`. -/
theorem red_target_or_ordered_omega_by_omega_triangular_red_pattern
    (red blue : SimpleGraph W2) (hcompl : IsCompl red blue)
    {base : Set W2} (hbase : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) :
    OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      ∃ (m : W2) (centers arms : ℕ → W2) (reservoirs : ℕ → Set W2),
        m ∈ base ∧ StrictMono centers ∧
        typeLT (Set.range centers) = ω ∧
        blue.IsClique (Set.range centers) ∧ StrictMono arms ∧
        typeLT (Set.range arms) = ω ∧
        (∀ n, centers n ∈ base) ∧
        (∀ n, #(reservoirs n) = ℵ_ 2 ∧ reservoirs n ⊆ Set.Ioi m) ∧
        (∀ n, reservoirs (n + 1) ⊆ reservoirs n) ∧
        (∀ n, arms n ∈ reservoirs n) ∧
        ∀ i n, i ≤ n → red.Adj (centers i) (arms n) := by
  classical
  by_cases hred : OrdinalRamsey.HasCliqueOfType red RedTarget
  · exact Or.inl hred
  · right
    obtain ⟨m, originalCenters, originalReservoirs, hm, hcentersInjective,
      hcentersBase, hcentersBlue, hreservoirs, hreservoirsNested, hstar⟩ :=
      exists_coherent_infinite_center_reservoir_sequence red blue hcompl
        hbase hbaseType hred hnoBlue
    obtain ⟨subseq, hsubseqMono⟩ :=
      wellQuasiOrdered_le.exists_monotone_subseq originalCenters
    let centers : ℕ → W2 := fun n ↦ originalCenters (subseq n)
    have hcentersStrict : StrictMono centers := by
      intro i j hij
      have hle : centers i ≤ centers j := hsubseqMono i j hij.le
      exact lt_of_le_of_ne hle fun heq ↦ by
        have hindex : (subseq i : ℕ) = subseq j := hcentersInjective heq
        exact hij.ne (subseq.injective hindex)
    have hcentersRangeSub : Set.range centers ⊆ Set.range originalCenters := by
      rintro _ ⟨n, rfl⟩
      exact ⟨subseq n, rfl⟩
    have hcentersClique : blue.IsClique (Set.range centers) :=
      hcentersBlue.subset hcentersRangeSub
    have hcentersType : typeLT (Set.range centers) = ω :=
      typeLT_range_eq_omega_of_strictMono centers hcentersStrict
    let reservoirs : ℕ → Set W2 := fun n ↦ originalReservoirs (subseq n + 1)
    have horiginalAntitone : Antitone originalReservoirs :=
      antitone_nat_of_succ_le hreservoirsNested
    have hreservoirsSampled (n : ℕ) :
        #(reservoirs n) = ℵ_ 2 ∧ reservoirs n ⊆ Set.Ioi m :=
      hreservoirs (subseq n + 1)
    have hreservoirsSampledNested (n : ℕ) : reservoirs (n + 1) ⊆ reservoirs n := by
      apply horiginalAntitone
      exact Nat.add_le_add_right (subseq.monotone (Nat.le_succ n)) 1
    let above (n : ℕ) (cutoff : W2) : W2 :=
      Classical.choose
        (exists_mem_gt_of_mk_eq_alephTwo (hreservoirsSampled n).1 cutoff)
    have haboveMem (n : ℕ) (cutoff : W2) : above n cutoff ∈ reservoirs n :=
      (Classical.choose_spec
        (exists_mem_gt_of_mk_eq_alephTwo (hreservoirsSampled n).1 cutoff)).1
    have haboveGt (n : ℕ) (cutoff : W2) : cutoff < above n cutoff :=
      (Classical.choose_spec
        (exists_mem_gt_of_mk_eq_alephTwo (hreservoirsSampled n).1 cutoff)).2
    let arms : ℕ → W2 := fun n ↦
      Nat.rec (above 0 m) (fun k previous ↦ above (k + 1) previous) n
    have harmsZero : arms 0 = above 0 m := rfl
    have harmsSucc (n : ℕ) : arms (n + 1) = above (n + 1) (arms n) := by
      rfl
    have harmsMem (n : ℕ) : arms n ∈ reservoirs n := by
      cases n with
      | zero => rw [harmsZero]; exact haboveMem 0 m
      | succ n => rw [harmsSucc]; exact haboveMem (n + 1) (arms n)
    have harmsLtSucc (n : ℕ) : arms n < arms (n + 1) := by
      rw [harmsSucc]
      exact haboveGt (n + 1) (arms n)
    have harmsStrict : StrictMono arms :=
      strictMono_nat_of_lt_succ harmsLtSucc
    have harmsType : typeLT (Set.range arms) = ω :=
      typeLT_range_eq_omega_of_strictMono arms harmsStrict
    refine ⟨m, centers, arms, reservoirs, hm, hcentersStrict, hcentersType,
      hcentersClique, harmsStrict, harmsType, ?_, hreservoirsSampled,
      hreservoirsSampledNested, harmsMem, ?_⟩
    · intro n
      exact hcentersBase (subseq n)
    · intro i n hin
      apply hstar (subseq i) (subseq n + 1)
      · exact (subseq.monotone hin).trans_lt (Nat.lt_succ_self _)
      · exact harmsMem n

end Erdos1172Part3InfiniteStars
