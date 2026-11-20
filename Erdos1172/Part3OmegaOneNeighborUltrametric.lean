/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OmegaOneNeighborProfileBridge

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OmegaOneNeighborUltrametric

open Erdos1172Part3Failure Erdos1172Part3StationaryOmegaStars
  Erdos1172Part3StationaryCountablePredecessors
  Erdos1172Part3OmegaOneNeighborProfiles
  Erdos1172Part3OmegaOneNeighborProfileBridge

/-- Countable proposition-valued profiles on an `alephTwo` domain have
an `alephTwo` fiber under CH. -/
theorem exists_alephTwo_fiber_of_countable_prop_profile
    (hCH : CH) {D : Type} (hD : #D = ℵ_ 2)
    (profile : D → ℕ → Prop) :
    ∃ fixed, #(profile ⁻¹' {fixed}) = ℵ_ 2 := by
  have hprofileCard : #(ℕ → Prop) ≤ ℵ_ 1 := by
    rw [Cardinal.mk_pi]
    calc
      Cardinal.prod (fun _ : ℕ ↦ #Prop) =
          (2 : Cardinal.{0}) ^ #ℕ := by
        simpa only [Cardinal.mk_Prop] using
          (Cardinal.prod_const' ℕ (2 : Cardinal.{0}))
      _ = (2 : Cardinal.{0}) ^ ℵ₀ := by simp
      _ ≤ ℵ_ 1 := (Cardinal.CH_iff.mp hCH).le
  obtain ⟨fixed, hlargeFiber⟩ :=
    Cardinal.infinite_pigeonhole profile
      (by rw [hD]; exact Cardinal.aleph0_le_aleph 2)
      (by
        rw [hD]
        rw [show (ℵ_ 2 : Cardinal.{0}) =
            ℵ_ ((1 : Ordinal.{0}) + 1) by norm_num,
          (Cardinal.isRegular_aleph_add_one 1).cof_ord]
        exact hprofileCard.trans_lt
          (Cardinal.aleph_lt_aleph.mpr (by norm_num)))
  exact ⟨fixed, hlargeFiber.trans hD⟩

/-- The first `W2` coordinate at which two unequal proposition-valued
profiles differ. -/
noncomputable def neighborProfileFirstDifference
    {D : Type} (profile : D → W2 → Prop)
    (a b : D) (hab : profile a ≠ profile b) : W2 :=
  wellFounded_lt.min {i | profile a i ≠ profile b i}
    (Function.ne_iff.mp hab)

/-- Unequal profiles differ at their canonical first coordinate. -/
theorem neighborProfileFirstDifference_ne_at
    {D : Type} (profile : D → W2 → Prop)
    {a b : D} (hab : profile a ≠ profile b) :
    profile a (neighborProfileFirstDifference profile a b hab) ≠
      profile b (neighborProfileFirstDifference profile a b hab) := by
  simp only [neighborProfileFirstDifference]
  exact wellFounded_lt.min_mem
    {i | profile a i ≠ profile b i} (Function.ne_iff.mp hab)

/-- Unequal profiles agree strictly below their first difference. -/
theorem neighborProfileFirstDifference_eq_below
    {D : Type} (profile : D → W2 → Prop)
    {a b : D} (hab : profile a ≠ profile b) {i : W2}
    (hi : i < neighborProfileFirstDifference profile a b hab) :
    profile a i = profile b i := by
  simp only [neighborProfileFirstDifference] at hi
  by_contra hne
  exact (wellFounded_lt.not_lt_min
    {j | profile a j ≠ profile b j} hne) hi

/-- Strong triangle laws for a `W2`-valued first-difference operation. -/
def IsW2FirstDifferenceUltrametric {D : Type}
    (difference : (a b : D) → a ≠ b → W2) : Prop :=
  ∀ (a b c : D) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c),
    min (difference a b hab) (difference b c hbc) ≤
        difference a c hac ∧
    (difference a b hab < difference b c hbc →
      difference a c hac = difference a b hab) ∧
    (difference b c hbc < difference a b hab →
      difference a c hac = difference b c hbc)

/-- The least-difference axioms imply the ultrametric lower bound. -/
theorem firstDifference_min_le_of_neAt_eqBelow
    {D : Type} (profile : D → W2 → Prop)
    (difference : (a b : D) → a ≠ b → W2)
    (hneAt : ∀ (a b : D) (hab : a ≠ b),
      profile a (difference a b hab) ≠ profile b (difference a b hab))
    (heqBelow : ∀ (a b : D) (hab : a ≠ b) (i : W2),
      i < difference a b hab → profile a i = profile b i)
    {a b c : D} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    min (difference a b hab) (difference b c hbc) ≤
      difference a c hac := by
  apply le_of_not_gt
  intro houter
  have hout_ab : difference a c hac < difference a b hab :=
    houter.trans_le (min_le_left _ _)
  have hout_bc : difference a c hac < difference b c hbc :=
    houter.trans_le (min_le_right _ _)
  exact hneAt a c hac <|
    (heqBelow a b hab _ hout_ab).trans
      (heqBelow b c hbc _ hout_bc)

/-- If the first consecutive difference is earlier, it is the outer
first difference. -/
theorem firstDifference_eq_left_of_lt_of_neAt_eqBelow
    {D : Type} (profile : D → W2 → Prop)
    (difference : (a b : D) → a ≠ b → W2)
    (hneAt : ∀ (a b : D) (hab : a ≠ b),
      profile a (difference a b hab) ≠ profile b (difference a b hab))
    (heqBelow : ∀ (a b : D) (hab : a ≠ b) (i : W2),
      i < difference a b hab → profile a i = profile b i)
    {a b c : D} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hlt : difference a b hab < difference b c hbc) :
    difference a c hac = difference a b hab := by
  apply le_antisymm
  · apply le_of_not_gt
    intro habOuter
    exact hneAt a b hab <|
      (heqBelow a c hac _ habOuter).trans
        (heqBelow b c hbc _ hlt).symm
  · have hmin := firstDifference_min_le_of_neAt_eqBelow
      profile difference hneAt heqBelow hab hbc hac
    simpa only [min_eq_left hlt.le] using hmin

/-- Symmetric strict-dominance law for least differences. -/
theorem firstDifference_eq_right_of_lt_of_neAt_eqBelow
    {D : Type} (profile : D → W2 → Prop)
    (difference : (a b : D) → a ≠ b → W2)
    (hneAt : ∀ (a b : D) (hab : a ≠ b),
      profile a (difference a b hab) ≠ profile b (difference a b hab))
    (heqBelow : ∀ (a b : D) (hab : a ≠ b) (i : W2),
      i < difference a b hab → profile a i = profile b i)
    {a b c : D} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hlt : difference b c hbc < difference a b hab) :
    difference a c hac = difference b c hbc := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hbcOuter
    exact hneAt b c hbc <|
      (heqBelow a b hab _ hlt).symm.trans
        (heqBelow a c hac _ hbcOuter)
  · have hmin := firstDifference_min_le_of_neAt_eqBelow
      profile difference hneAt heqBelow hab hbc hac
    simpa only [min_eq_right hlt.le] using hmin

/-- Canonical least differences satisfy all strong ultrametric laws. -/
theorem neighborProfileFirstDifference_isUltrametric
    {D : Type} (profile : D → W2 → Prop)
    (hinjective : Function.Injective profile) :
    IsW2FirstDifferenceUltrametric
      (fun a b hab ↦ neighborProfileFirstDifference profile a b
        (fun h ↦ hab (hinjective h))) := by
  intro a b c hab hbc hac
  let difference : (a b : D) → a ≠ b → W2 := fun a b hab ↦
    neighborProfileFirstDifference profile a b
      (fun h ↦ hab (hinjective h))
  have hneAt : ∀ (a b : D) (hab : a ≠ b),
      profile a (difference a b hab) ≠
        profile b (difference a b hab) := by
    intro x y hxy
    exact neighborProfileFirstDifference_ne_at profile
      (fun h ↦ hxy (hinjective h))
  have heqBelow : ∀ (a b : D) (hab : a ≠ b) (i : W2),
      i < difference a b hab → profile a i = profile b i := by
    intro x y hxy i hi
    exact neighborProfileFirstDifference_eq_below profile
      (fun h ↦ hxy (hinjective h)) hi
  exact ⟨firstDifference_min_le_of_neAt_eqBelow
      profile difference hneAt heqBelow hab hbc hac,
    firstDifference_eq_left_of_lt_of_neAt_eqBelow
      profile difference hneAt heqBelow hab hbc hac,
    firstDifference_eq_right_of_lt_of_neAt_eqBelow
      profile difference hneAt heqBelow hab hbc hac⟩

/-- Agreement through a cutoff is the nested equivalence-class relation
associated to a first-difference ultrametric. -/
def NeighborhoodProfilesAgreeThrough {D : Type}
    (profile : D → W2 → Prop) (cutoff : W2) (a b : D) : Prop :=
  ∀ i, i ≤ cutoff → profile a i = profile b i

theorem neighborhoodProfilesAgreeThrough_refl
    {D : Type} (profile : D → W2 → Prop) (cutoff : W2) (a : D) :
    NeighborhoodProfilesAgreeThrough profile cutoff a a := by
  intro i hi
  rfl

theorem neighborhoodProfilesAgreeThrough_symm
    {D : Type} {profile : D → W2 → Prop} {cutoff : W2} {a b : D}
    (h : NeighborhoodProfilesAgreeThrough profile cutoff a b) :
    NeighborhoodProfilesAgreeThrough profile cutoff b a := by
  intro i hi
  exact (h i hi).symm

theorem neighborhoodProfilesAgreeThrough_trans
    {D : Type} {profile : D → W2 → Prop} {cutoff : W2} {a b c : D}
    (hab : NeighborhoodProfilesAgreeThrough profile cutoff a b)
    (hbc : NeighborhoodProfilesAgreeThrough profile cutoff b c) :
    NeighborhoodProfilesAgreeThrough profile cutoff a c := by
  intro i hi
  exact (hab i hi).trans (hbc i hi)

theorem neighborhoodProfilesAgreeThrough_anti
    {D : Type} {profile : D → W2 → Prop} {small large : W2}
    (hcutoff : small ≤ large) {a b : D}
    (h : NeighborhoodProfilesAgreeThrough profile large a b) :
    NeighborhoodProfilesAgreeThrough profile small a b := by
  intro i hi
  exact h i (hi.trans hcutoff)

/-- For unequal profiles, agreement through a cutoff is equivalent to
their first difference lying strictly above that cutoff. -/
theorem cutoff_lt_neighborProfileFirstDifference_iff
    {D : Type} (profile : D → W2 → Prop)
    {a b : D} (hab : profile a ≠ profile b) (cutoff : W2) :
    cutoff < neighborProfileFirstDifference profile a b hab ↔
      NeighborhoodProfilesAgreeThrough profile cutoff a b := by
  constructor
  · intro hcutoff i hi
    exact neighborProfileFirstDifference_eq_below profile hab
      (hi.trans_lt hcutoff)
  · intro hagree
    apply lt_of_not_ge
    intro hle
    exact neighborProfileFirstDifference_ne_at profile hab
      (hagree _ hle)

/-- The rich surviving Part 3 obstruction: the complete neighbourhood
profiles form a bounded `W2`-valued first-difference ultrametric.  Every
countable coordinate family, and hence every countable initial cutoff,
has an `alephTwo` equivalence class.  All stationary fan and countable
arm-predecessor data are retained. -/
def LocallyCompactUltrametricOmegaOneBaseNeighborhoodResidualWithFan
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (spine : W2 → W2) (base : Set W2) (anchor baseCenter : W2)
      (centerArms : ℕ → Set W2) (armCenters : ℕ → W2)
      (indexFiber representativeFiber fan : Set W2)
      (residual : Set indexFiber)
      (difference : (a b : residual) → a ≠ b → W2),
    StrictMono spine ∧ typeLT (Set.range spine) = ω_ 2 ∧
    base ⊆ Set.range spine ∧ blue.IsClique base ∧
    typeLT base = ω_ 1 + 1 ∧ spine anchor ∈ base ∧
    (∀ y ∈ base, y ≤ spine anchor) ∧ baseCenter ∈ base ∧
    (∀ n, blue.IsClique (centerArms n) ∧
      typeLT (centerArms n) = ω_ 1 + 1) ∧
    (∀ n, armCenters n ∈ centerArms n) ∧
    (∀ i j, i < j → ∀ x ∈ centerArms i,
      ∀ y ∈ centerArms j, x < y) ∧
    StrictMono armCenters ∧ typeLT (Set.range armCenters) = ω ∧
    (red.IsClique (Set.range armCenters) ∨
      blue.IsClique (Set.range armCenters)) ∧
    IsStationary indexFiber ∧ #indexFiber = ℵ_ 2 ∧
    typeLT indexFiber = ω_ 2 ∧
    indexFiber ⊆ Set.Ioi anchor ∩ Set.Ioi omegaOneCutoff ∧
    (∀ b ∈ indexFiber,
      #(baseRedNeighborIndices red spine base b) = ℵ_ 1) ∧
    representativeFiber = spine '' indexFiber ∧
    #representativeFiber = ℵ_ 2 ∧
    typeLT representativeFiber = ω_ 2 ∧
    fan ⊆ representativeFiber ∧ blue.IsClique fan ∧
    typeLT fan = ω_ 1 + 1 ∧
    (∀ b ∈ indexFiber,
      baseCenter < spine b ∧ red.Adj baseCenter (spine b)) ∧
    (∀ n, ∀ b ∈ indexFiber,
      armCenters n < spine b ∧ red.Adj (armCenters n) (spine b)) ∧
    #residual = ℵ_ 2 ∧
    Set.InjOn
      (fun b : indexFiber ↦
        baseRedNeighborIndices red spine base b)
      residual ∧
    (∀ a b : residual, ∀ hab : a ≠ b,
      difference a b hab ≤ anchor ∧
      ((difference a b hab ∈
          baseRedNeighborIndices red spine base (a : indexFiber)) ≠
        (difference a b hab ∈
          baseRedNeighborIndices red spine base (b : indexFiber))) ∧
      ∀ i, i < difference a b hab →
        ((i ∈ baseRedNeighborIndices red spine base (a : indexFiber)) =
          (i ∈ baseRedNeighborIndices red spine base (b : indexFiber)))) ∧
    IsW2FirstDifferenceUltrametric difference ∧
    (∀ coordinates : ℕ → W2,
      ∃ (fixed : ℕ → Prop) (subresidual : Set residual),
        #subresidual = ℵ_ 2 ∧
        ∀ b ∈ subresidual, ∀ n,
          (coordinates n ∈ baseRedNeighborIndices red spine base
            (b : indexFiber)) = fixed n) ∧
    ∀ cutoff : W2, (Set.Iic cutoff).Countable →
      ∃ subresidual : Set residual,
        #subresidual = ℵ_ 2 ∧
        ∀ a ∈ subresidual, ∀ b ∈ subresidual, ∀ hab : a ≠ b,
          cutoff < difference a b hab

/-- CH upgrades the rich injective neighbourhood residual to its bounded
locally compact first-difference ultrametric normal form. -/
theorem StationaryInjectiveOmegaOneBaseNeighborhoodResidualWithFan.to_locallyCompactUltrametric
    (hCH : CH) {red blue : SimpleGraph W2}
    (h : StationaryInjectiveOmegaOneBaseNeighborhoodResidualWithFan
      red blue) :
    LocallyCompactUltrametricOmegaOneBaseNeighborhoodResidualWithFan
      red blue := by
  classical
  obtain ⟨spine, base, anchor, baseCenter, centerArms, armCenters,
    indexFiber, representativeFiber, fan, residual, hspine,
    hspineType, hbaseSub, hbaseBlue, hbaseType, hanchorMem,
    hanchorMax, hbaseCenterMem, hcenterArms, harmCentersMem,
    hcenterArmsOrdered, harmCentersStrict, harmCentersType,
    harmCentersHomogeneous, hindexStationary, hindexCard,
    hindexType, hindexTail, hneighborCard, hrepresentativeEq,
    hrepresentativeCard, hrepresentativeType, hfanSub, hfanBlue,
    hfanType, hbaseCenterCross, harmCentersCross, hresidualCard,
    hresidualInjective⟩ := h
  let profile : residual → W2 → Prop := fun b i ↦
    i ∈ baseRedNeighborIndices red spine base (b : indexFiber)
  have hprofileInjective : Function.Injective profile := by
    intro a b hab
    apply Subtype.ext
    apply hresidualInjective a.property b.property
    ext i
    have hi := congrFun hab i
    change (i ∈ baseRedNeighborIndices red spine base (a : indexFiber)) =
      (i ∈ baseRedNeighborIndices red spine base (b : indexFiber)) at hi
    rw [hi]
  let difference : (a b : residual) → a ≠ b → W2 := fun a b hab ↦
    neighborProfileFirstDifference profile a b
      (fun h ↦ hab (hprofileInjective h))
  have hfirstDifference (a b : residual) (hab : a ≠ b) :
      difference a b hab ≤ anchor ∧
      ((difference a b hab ∈
          baseRedNeighborIndices red spine base (a : indexFiber)) ≠
        (difference a b hab ∈
          baseRedNeighborIndices red spine base (b : indexFiber))) ∧
      ∀ i, i < difference a b hab →
        ((i ∈ baseRedNeighborIndices red spine base (a : indexFiber)) =
          (i ∈ baseRedNeighborIndices red spine base (b : indexFiber))) := by
    have hprofilesNe : profile a ≠ profile b :=
      fun h ↦ hab (hprofileInjective h)
    have hneAt :=
      neighborProfileFirstDifference_ne_at profile hprofilesNe
    have hmem :
        difference a b hab ∈
            baseRedNeighborIndices red spine base (a : indexFiber) ∨
          difference a b hab ∈
            baseRedNeighborIndices red spine base (b : indexFiber) := by
      by_contra hnone
      push Not at hnone
      apply hneAt
      apply propext
      exact iff_of_false hnone.1 hnone.2
    have hbaseMem : spine (difference a b hab) ∈ base := by
      rcases hmem with ha | hb
      · exact ha.1
      · exact hb.1
    have hbound : difference a b hab ≤ anchor :=
      hspine.le_iff_le.mp (hanchorMax _ hbaseMem)
    exact ⟨hbound, hneAt, fun i hi ↦
      neighborProfileFirstDifference_eq_below profile hprofilesNe hi⟩
  have hultrametric : IsW2FirstDifferenceUltrametric difference :=
    neighborProfileFirstDifference_isUltrametric profile hprofileInjective
  have hlocal : ∀ coordinates : ℕ → W2,
      ∃ (fixed : ℕ → Prop) (subresidual : Set residual),
        #subresidual = ℵ_ 2 ∧
        ∀ b ∈ subresidual, ∀ n,
          (coordinates n ∈ baseRedNeighborIndices red spine base
            (b : indexFiber)) = fixed n := by
    intro coordinates
    let restrictedProfile : residual → ℕ → Prop := fun b n ↦
      coordinates n ∈
        baseRedNeighborIndices red spine base (b : indexFiber)
    obtain ⟨fixed, hfixedFiber⟩ :=
      exists_alephTwo_fiber_of_countable_prop_profile
        hCH hresidualCard restrictedProfile
    refine ⟨fixed, restrictedProfile ⁻¹' {fixed}, hfixedFiber, ?_⟩
    intro b hb n
    have hprofileEq : restrictedProfile b = fixed := by
      simpa only [mem_preimage, mem_singleton_iff] using hb
    exact congrFun hprofileEq n
  have hcutoff : ∀ cutoff : W2, (Set.Iic cutoff).Countable →
      ∃ subresidual : Set residual,
        #subresidual = ℵ_ 2 ∧
        ∀ a ∈ subresidual, ∀ b ∈ subresidual, ∀ hab : a ≠ b,
          cutoff < difference a b hab := by
    intro cutoff hcountable
    let _ : Countable (Set.Iic cutoff) := hcountable
    let _ : Nonempty (Set.Iic cutoff) := ⟨⟨cutoff, Set.mem_Iic.mpr le_rfl⟩⟩
    obtain ⟨enumerate, henumerate⟩ :=
      exists_surjective_nat (Set.Iic cutoff)
    let coordinates : ℕ → W2 := fun n ↦ enumerate n
    obtain ⟨fixed, subresidual, hsubresidualCard,
      hsubresidualFixed⟩ := hlocal coordinates
    refine ⟨subresidual, hsubresidualCard, ?_⟩
    intro a ha b hb hab
    apply lt_of_not_ge
    intro hle
    obtain ⟨n, hn⟩ := henumerate ⟨difference a b hab, hle⟩
    have hcoordinate : coordinates n = difference a b hab :=
      congrArg Subtype.val hn
    have haFixed := hsubresidualFixed a ha n
    have hbFixed := hsubresidualFixed b hb n
    have heq :
        (difference a b hab ∈
            baseRedNeighborIndices red spine base (a : indexFiber)) =
          (difference a b hab ∈
            baseRedNeighborIndices red spine base (b : indexFiber)) := by
      rw [← hcoordinate, haFixed, hbFixed]
    exact (hfirstDifference a b hab).2.1 heq
  exact ⟨spine, base, anchor, baseCenter, centerArms, armCenters,
    indexFiber, representativeFiber, fan, residual, difference,
    hspine, hspineType, hbaseSub, hbaseBlue, hbaseType, hanchorMem,
    hanchorMax, hbaseCenterMem, hcenterArms, harmCentersMem,
    hcenterArmsOrdered, harmCentersStrict, harmCentersType,
    harmCentersHomogeneous, hindexStationary, hindexCard,
    hindexType, hindexTail, hneighborCard, hrepresentativeEq,
    hrepresentativeCard, hrepresentativeType, hfanSub, hfanBlue,
    hfanType, hbaseCenterCross, harmCentersCross, hresidualCard,
    hresidualInjective, hfirstDifference, hultrametric, hlocal,
    hcutoff⟩

/-- Global CH split with the injective neighbourhood branch sharpened to
its bounded locally compact ultrametric, while retaining all fan data. -/
theorem part3_exact_or_omegaOneByOmegaTwoRedRectangle_or_neighborhoodUltrametric
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      HasOmegaOneByOmegaTwoRedRectangle red blue ∨
      LocallyCompactUltrametricOmegaOneBaseNeighborhoodResidualWithFan
        red blue := by
  obtain htarget | hrectangle | hresidual :=
    part3_exact_or_omegaOneByOmegaTwoRedRectangle_or_injectiveNeighborhoodResidual
      hCH red blue hcompl
  · exact Or.inl htarget
  · exact Or.inr (Or.inl hrectangle)
  · exact Or.inr (Or.inr
      (StationaryInjectiveOmegaOneBaseNeighborhoodResidualWithFan.to_locallyCompactUltrametric
        hCH hresidual))

end Erdos1172Part3OmegaOneNeighborUltrametric
