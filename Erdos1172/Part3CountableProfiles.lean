/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FailureFiber
public import Erdos1172.ForMathlib.SetTheory.Cardinal.GCHConsequences1172

@[expose] public section

open Cardinal Ordinal Set

/-!
# Countable adjacency-profile compression for Erdős Problem 1172, Part 3

Under CH there are at most `ℵ₁` Boolean profiles on a countable set.  Hence
an `ℵ₂`-sized reservoir has an `ℵ₂`-sized fiber on which every adjacency to
the countable set is constant.  This is the cardinal compression available
at countable limit stages of the Part 3 reservoir construction.
-/

namespace Erdos1172Part3CountableProfiles

abbrev W2 : Type := Erdos1172Part3Failure.W2

/-- The Boolean adjacency profile of one vertex on a prescribed set. -/
noncomputable def adjacencyProfile
    (G : SimpleGraph W2) (centers : Set W2) (x : W2) : centers → Bool := by
  classical
  exact fun y ↦ decide (G.Adj y x)

/-- Under CH, a countable set supports at most `ℵ₁` Boolean profiles. -/
theorem mk_arrow_bool_le_alephOne_of_mk_le_aleph0
    (hCH : CH) {centers : Set W2} (hcenters : #centers ≤ ℵ₀) :
    #(centers → Bool) ≤ ℵ_ 1 := by
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.lift_id, Cardinal.mk_fintype, Fintype.card_bool,
    Nat.cast_ofNat]
  calc
    (2 : Cardinal.{0}) ^ #centers ≤ (2 : Cardinal.{0}) ^ ℵ₀ :=
      Cardinal.power_le_power_left (by norm_num) hcenters
    _ = ℵ_ 1 := CH_iff.mp hCH

/-- An `ℵ₂` reservoir has an `ℵ₂` subreservoir on which the complete
Boolean adjacency profile to any fixed countable set is constant. -/
theorem exists_alephTwo_uniform_adjacencyProfile
    (hCH : CH) (G : SimpleGraph W2)
    {centers reservoir : Set W2}
    (hcenters : #centers ≤ ℵ₀) (hreservoir : #reservoir = ℵ_ 2) :
    ∃ (profile : centers → Bool) (fiber : Set W2),
      fiber ⊆ reservoir ∧ #fiber = ℵ_ 2 ∧
      ∀ x ∈ fiber, adjacencyProfile G centers x = profile := by
  classical
  let profileMap : reservoir → (centers → Bool) :=
    fun x ↦ adjacencyProfile G centers x
  have hprofileCard : #(centers → Bool) ≤ ℵ_ 1 :=
    mk_arrow_bool_le_alephOne_of_mk_le_aleph0 hCH hcenters
  obtain ⟨profile, hlargeFiber⟩ := Cardinal.infinite_pigeonhole profileMap
    (by
      rw [hreservoir]
      exact Cardinal.aleph0_le_aleph 2)
    (by
      rw [hreservoir]
      rw [show (ℵ_ 2 : Cardinal.{0}) = ℵ_ ((1 : Ordinal.{0}) + 1) by norm_num,
        (Cardinal.isRegular_aleph_add_one 1).cof_ord]
      exact hprofileCard.trans_lt (Cardinal.aleph_lt_aleph.mpr (by norm_num)))
  let fiber : Set W2 := Subtype.val '' (profileMap ⁻¹' {profile})
  refine ⟨profile, fiber, ?_, ?_, ?_⟩
  · rintro x ⟨y, -, rfl⟩
    exact y.property
  · calc
      #fiber = #(profileMap ⁻¹' {profile}) :=
        Cardinal.mk_image_eq Subtype.val_injective
      _ = #reservoir := hlargeFiber
      _ = ℵ_ 2 := hreservoir
  · rintro x ⟨y, hy, rfl⟩
    have hprofile : profileMap y = profile := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hy
    exact hprofile

/-- On the uniform fiber, adjacency to every prescribed centre agrees
pointwise. -/
theorem adjacency_iff_of_mem_uniform_fiber
    {G : SimpleGraph W2} {centers fiber : Set W2}
    {profile : centers → Bool}
    (huniform : ∀ x ∈ fiber, adjacencyProfile G centers x = profile)
    {x z : W2} (hx : x ∈ fiber) (hz : z ∈ fiber) (y : centers) :
    G.Adj y x ↔ G.Adj y z := by
  classical
  have h := congrFun ((huniform x hx).trans (huniform z hz).symm) y
  change decide (G.Adj y x) = decide (G.Adj y z) at h
  constructor
  · intro hyx
    apply of_decide_eq_true
    rw [← h]
    exact decide_eq_true hyx
  · intro hyz
    apply of_decide_eq_true
    rw [h]
    exact decide_eq_true hyz

end Erdos1172Part3CountableProfiles
