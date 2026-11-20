/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OmegaOneFinalBarrier

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OmegaOneNeighborDeepBlue

open Erdos1172Part3Failure Erdos1172Part3FiniteStars
  Erdos1172Part3CHAsymmetric
  Erdos1172Part3StationaryOmegaStars
  Erdos1172Part3OmegaOneRectangleRefinement
  Erdos1172Part3OmegaOneNeighborProfiles
  Erdos1172Part3OmegaOneNeighborUltrametric
  Erdos1172Part3OmegaOneFinalBarrier

/-- If two distinct later vertices are blue-adjacent and each lies after
a blue `omegaOne + 1` base, their common blue neighbourhood in that base
has size below `alephOne` whenever the exact blue Part 3 target is absent.
Otherwise an exact `omegaOne` core followed by those two vertices gives
`omegaOne + 2`. -/
theorem mk_commonBlueBase_lt_alephOne_of_no_blue_target
    (blue : SimpleGraph W2) {base later : Set W2}
    (hbaseBlue : blue.IsClique base)
    (hbaseType : typeLT base = ω_ 1 + 1)
    (hlaterBlue : blue.IsClique later)
    (hbaseBefore : ∀ x ∈ base, ∀ y ∈ later, x < y)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    {y z : W2} (hy : y ∈ later) (hz : z ∈ later) (hyz : y ≠ z) :
    #{x : W2 | x ∈ base ∧ blue.Adj x y ∧ blue.Adj x z} < ℵ_ 1 := by
  classical
  let common : Set W2 :=
    {x | x ∈ base ∧ blue.Adj x y ∧ blue.Adj x z}
  have hcommonSub : common ⊆ base := fun _ hx ↦ hx.1
  have hbaseCard : #base = ℵ_ 1 := by
    have hc := congrArg Ordinal.card hbaseType
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  have hcommonLe : #common ≤ ℵ_ 1 := by
    rw [← hbaseCard]
    exact Cardinal.mk_le_mk_of_subset hcommonSub
  refine lt_of_le_of_ne hcommonLe ?_
  intro hcommonCard
  have homegaOneLe : (ω_ 1 : Ordinal.{0}) ≤ typeLT common := by
    calc
      (ω_ 1 : Ordinal.{0}) = (#common).ord := by
        rw [hcommonCard, Cardinal.ord_aleph]
      _ ≤ typeLT common :=
        Cardinal.ord_le_type ((· < ·) : common → common → Prop)
  obtain ⟨core, hcoreSub, hcoreType⟩ :=
    Ordinal.exists_subset_typeLT_eq common homegaOneLe
  have hcoreBlue : blue.IsClique core :=
    hbaseBlue.subset (hcoreSub.trans hcommonSub)
  have impossible_of_ordered (low high : W2)
      (hlow : low ∈ later) (hhigh : high ∈ later) (hlowHigh : low < high)
      (hcoreLow : ∀ x ∈ core, blue.Adj x low)
      (hcoreHigh : ∀ x ∈ core, blue.Adj x high) : False := by
    have hcoreBeforeLow : ∀ x ∈ core, x < low := by
      intro x hx
      exact hbaseBefore x (hcommonSub (hcoreSub hx)) low hlow
    let withLow : Set W2 := insert low core
    have hwithLowBlue : blue.IsClique withLow := by
      apply hcoreBlue.insert
      intro x hx _
      rw [blue.adj_comm]
      exact hcoreLow x hx
    have hwithLowType : typeLT withLow = ω_ 1 + 1 := by
      calc
        typeLT withLow = typeLT core + 1 :=
          Ordinal.typeLT_insert_of_forall_lt hcoreBeforeLow
        _ = ω_ 1 + 1 := by rw [hcoreType]
    have hwithLowBeforeHigh : ∀ x ∈ withLow, x < high := by
      intro x hx
      simp only [withLow, mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact hlowHigh
      · exact hbaseBefore x (hcommonSub (hcoreSub hx)) high hhigh
    have hwithLowAdjHigh : ∀ x ∈ withLow, blue.Adj x high := by
      intro x hx
      simp only [withLow, mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact hlaterBlue hlow hhigh hlowHigh.ne
      · exact hcoreHigh x hx
    obtain ⟨target, htargetBlue, htargetType⟩ :=
      blue.exists_clique_type_add_one_of_common_later
        hwithLowBlue hwithLowType hwithLowBeforeHigh hwithLowAdjHigh
    apply hnoBlue
    refine ⟨target, htargetBlue, ?_⟩
    calc
      typeLT target = (ω_ 1 + 1) + 1 := htargetType
      _ = ω_ 1 + 2 := by norm_num [add_assoc]
  rcases lt_or_gt_of_ne hyz with hyzlt | hzylt
  · exact impossible_of_ordered y z hy hz hyzlt
      (fun x hx ↦ (hcoreSub hx).2.1)
      (fun x hx ↦ (hcoreSub hx).2.2)
  · exact impossible_of_ordered z y hz hy hzylt
      (fun x hx ↦ (hcoreSub hx).2.2)
      (fun x hx ↦ (hcoreSub hx).2.1)

/-- A graph-synchronised version of the surviving neighbourhood tree.
The domain has size `alephTwo`, its points have distinct `alephOne`-sized
red-neighbour profiles in one blue `omegaOne + 1` base.  Every countable
coordinate pattern, and in particular every countable-depth equivalence
class, can be frozen on `alephTwo` points while still containing a blue
clique of exact type `omegaOne + 1` among the corresponding later
vertices.  Every pair in each such clique has fewer than `alephOne`
common blue base-neighbours; equivalently, its two red-neighbour profiles
cover all but fewer than `alephOne` base indices. -/
def DeepBlueOmegaOneAddOneNeighborhoodUltrametricObstruction
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (D : Type) (spine : W2 → W2) (index : D → W2)
      (base : Set W2) (anchor : W2)
      (difference : (a b : D) → a ≠ b → W2),
    StrictMono spine ∧ base ⊆ Set.range spine ∧
    Function.Injective index ∧ #D = ℵ_ 2 ∧
    blue.IsClique base ∧ typeLT base = ω_ 1 + 1 ∧
    (∀ b : D, ∀ y ∈ base, y < spine (index b)) ∧
    (∀ b : D,
      #(baseRedNeighborIndices red spine base (index b)) = ℵ_ 1) ∧
    (∀ a b : D, ∀ hab : a ≠ b,
      difference a b hab ≤ anchor ∧
      ((difference a b hab ∈
          baseRedNeighborIndices red spine base (index a)) ≠
        (difference a b hab ∈
          baseRedNeighborIndices red spine base (index b))) ∧
      ∀ i, i < difference a b hab →
        ((i ∈ baseRedNeighborIndices red spine base (index a)) =
          (i ∈ baseRedNeighborIndices red spine base (index b)))) ∧
    IsW2FirstDifferenceUltrametric difference ∧
    (∀ coordinates : ℕ → W2,
      ∃ (fixed : ℕ → Prop) (largeFiber blueLocal : Set D),
        #largeFiber = ℵ_ 2 ∧
        blueLocal ⊆ largeFiber ∧
        (∀ b ∈ largeFiber, ∀ n,
          (coordinates n ∈
            baseRedNeighborIndices red spine base (index b)) = fixed n) ∧
        blue.IsClique ((fun b : D ↦ spine (index b)) '' blueLocal) ∧
        typeLT ((fun b : D ↦ spine (index b)) '' blueLocal) =
          ω_ 1 + 1 ∧
        ∀ a ∈ blueLocal, ∀ b ∈ blueLocal, a ≠ b →
          #{x : W2 | x ∈ base ∧
            blue.Adj x (spine (index a)) ∧
            blue.Adj x (spine (index b))} < ℵ_ 1 ∧
          #{i : W2 | spine i ∈ base ∧
            i ∉ baseRedNeighborIndices red spine base (index a) ∧
            i ∉ baseRedNeighborIndices red spine base (index b)} <
              ℵ_ 1) ∧
    ∀ cutoff : W2, (Set.Iic cutoff).Countable →
      ∃ (largeFiber blueLocal : Set D),
        #largeFiber = ℵ_ 2 ∧
        blueLocal ⊆ largeFiber ∧
        (∀ a ∈ largeFiber, ∀ b ∈ largeFiber, ∀ hab : a ≠ b,
          cutoff < difference a b hab) ∧
        blue.IsClique ((fun b : D ↦ spine (index b)) '' blueLocal) ∧
        typeLT ((fun b : D ↦ spine (index b)) '' blueLocal) =
          ω_ 1 + 1 ∧
        ∀ a ∈ blueLocal, ∀ b ∈ blueLocal, a ≠ b →
          #{x : W2 | x ∈ base ∧
            blue.Adj x (spine (index a)) ∧
            blue.Adj x (spine (index b))} < ℵ_ 1 ∧
          #{i : W2 | spine i ∈ base ∧
            i ∉ baseRedNeighborIndices red spine base (index a) ∧
            i ∉ baseRedNeighborIndices red spine base (index b)} <
              ℵ_ 1

/-- Under CH and failure of the red target, local compactness is not
merely cardinal-theoretic: every countable-depth class can be thinned,
inside that very class, to a blue `omegaOne + 1` clique. -/
theorem LocallyCompactUltrametricOmegaOneBaseNeighborhoodResidualWithFan.to_deepBlue
    (hCH : CH) {red blue : SimpleGraph W2} (hcompl : IsCompl red blue)
    (hnoRed : ¬ OrdinalRamsey.HasCliqueOfType red RedTarget)
    (hnoBlue : ¬ OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2))
    (h : LocallyCompactUltrametricOmegaOneBaseNeighborhoodResidualWithFan
      red blue) :
    DeepBlueOmegaOneAddOneNeighborhoodUltrametricObstruction red blue := by
  classical
  obtain ⟨spine, base, anchor, baseCenter, centerArms, armCenters,
    indexFiber, representativeFiber, fan, residual, difference,
    hspine, _hspineType, hbaseSub, hbaseBlue, hbaseType,
    _hanchorMem, hanchorMax, _hbaseCenterMem, _hcenterArms,
    _harmCentersMem, _hcenterArmsOrdered, _harmCentersStrict,
    _harmCentersType, _harmCentersHomogeneous, _hindexStationary,
    _hindexCard, _hindexType, hindexTail, hneighborCard,
    _hrepresentativeEq, _hrepresentativeCard, _hrepresentativeType,
    _hfanSub, _hfanBlue, _hfanType, _hbaseCenterCross,
    _harmCentersCross, hresidualCard, _hresidualInjective,
    hfirstDifference, hultrametric, hcountableProfiles, hcutoff⟩ := h
  let index : residual → W2 := fun b ↦ (b : indexFiber)
  have hindexInjective : Function.Injective index :=
    Subtype.val_injective.comp Subtype.val_injective
  have hbaseBefore : ∀ b : residual, ∀ y ∈ base,
      y < spine (index b) := by
    intro b y hy
    have hanchorIndex : anchor < (b : indexFiber) :=
      (hindexTail b.val.property).1
    exact (hanchorMax y hy).trans_lt (hspine hanchorIndex)
  have hprofileCard : ∀ b : residual,
      #(baseRedNeighborIndices red spine base (index b)) = ℵ_ 1 := by
    intro b
    exact hneighborCard (b : indexFiber) b.val.property
  have hfirstDifference' : ∀ a b : residual, ∀ hab : a ≠ b,
      difference a b hab ≤ anchor ∧
      ((difference a b hab ∈
          baseRedNeighborIndices red spine base (index a)) ≠
        (difference a b hab ∈
          baseRedNeighborIndices red spine base (index b))) ∧
      ∀ i, i < difference a b hab →
        ((i ∈ baseRedNeighborIndices red spine base (index a)) =
          (i ∈ baseRedNeighborIndices red spine base (index b))) := by
    simpa only [index] using hfirstDifference
  let vertex : residual → W2 := fun b ↦ spine (index b)
  have hvertexInjective : Function.Injective vertex :=
    hspine.injective.comp hindexInjective
  have hblueInLarge (largeFiber : Set residual)
      (hlocalCard : #largeFiber = ℵ_ 2) :
      ∃ blueLocal : Set residual,
        blueLocal ⊆ largeFiber ∧ blue.IsClique (vertex '' blueLocal) ∧
        typeLT (vertex '' blueLocal) = ω_ 1 + 1 ∧
        ∀ a ∈ blueLocal, ∀ b ∈ blueLocal, a ≠ b →
          #{x : W2 | x ∈ base ∧ blue.Adj x (vertex a) ∧
            blue.Adj x (vertex b)} < ℵ_ 1 ∧
          #{i : W2 | spine i ∈ base ∧
            i ∉ baseRedNeighborIndices red spine base (index a) ∧
            i ∉ baseRedNeighborIndices red spine base (index b)} <
              ℵ_ 1 := by
    have hvertexCard : #(vertex '' largeFiber) = ℵ_ 2 := by
      calc
        #(vertex '' largeFiber) = #largeFiber :=
          Cardinal.mk_image_eq hvertexInjective
        _ = ℵ_ 2 := hlocalCard
    obtain ⟨clique, hcliqueSub, hcliqueBlue, hcliqueType⟩ :=
      exists_blue_omegaOne_add_one_in_every_alephTwo_set
        hCH red blue hcompl hnoRed hvertexCard
    let blueLocal : Set residual := largeFiber ∩ vertex ⁻¹' clique
    have himage : vertex '' blueLocal = clique := by
      ext x
      constructor
      · rintro ⟨b, ⟨hbLocal, hbClique⟩, rfl⟩
        exact hbClique
      · intro hx
        obtain ⟨b, hbLocal, hbx⟩ := hcliqueSub hx
        refine ⟨b, ⟨hbLocal, ?_⟩, hbx⟩
        simpa only [mem_preimage, hbx] using hx
    have hblueLocalBlue : blue.IsClique (vertex '' blueLocal) := by
      rw [himage]
      exact hcliqueBlue
    have hblueLocalType : typeLT (vertex '' blueLocal) = ω_ 1 + 1 := by
      rw [himage]
      exact hcliqueType
    have hbaseBeforeBlueLocal :
        ∀ x ∈ base, ∀ y ∈ vertex '' blueLocal, x < y := by
      rintro x hx _ ⟨b, _hb, rfl⟩
      exact hbaseBefore b x hx
    have hpairSmall : ∀ a ∈ blueLocal, ∀ b ∈ blueLocal, a ≠ b →
        #{x : W2 | x ∈ base ∧ blue.Adj x (vertex a) ∧
          blue.Adj x (vertex b)} < ℵ_ 1 := by
      intro a ha b hb hab
      exact mk_commonBlueBase_lt_alephOne_of_no_blue_target
        blue hbaseBlue hbaseType hblueLocalBlue hbaseBeforeBlueLocal
          hnoBlue ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
            (fun h ↦ hab (hvertexInjective h))
    have hprofileCover : ∀ a ∈ blueLocal, ∀ b ∈ blueLocal, a ≠ b →
        #{i : W2 | spine i ∈ base ∧
          i ∉ baseRedNeighborIndices red spine base (index a) ∧
          i ∉ baseRedNeighborIndices red spine base (index b)} <
            ℵ_ 1 := by
      intro a ha b hb hab
      let missing : Set W2 := {i | spine i ∈ base ∧
        i ∉ baseRedNeighborIndices red spine base (index a) ∧
        i ∉ baseRedNeighborIndices red spine base (index b)}
      have himageSub : spine '' missing ⊆
          {x : W2 | x ∈ base ∧ blue.Adj x (vertex a) ∧
            blue.Adj x (vertex b)} := by
        rintro _ ⟨i, hi, rfl⟩
        have hnotRedA : ¬red.Adj (spine i) (vertex a) := by
          intro hred
          exact hi.2.1 ⟨hi.1, hred⟩
        have hnotRedB : ¬red.Adj (spine i) (vertex b) := by
          intro hred
          exact hi.2.2 ⟨hi.1, hred⟩
        have hblueA : blue.Adj (spine i) (vertex a) := by
          rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
          exact ⟨(hbaseBefore a (spine i) hi.1).ne, hnotRedA⟩
        have hblueB : blue.Adj (spine i) (vertex b) := by
          rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
          exact ⟨(hbaseBefore b (spine i) hi.1).ne, hnotRedB⟩
        exact ⟨hi.1, hblueA, hblueB⟩
      calc
        #missing = #(spine '' missing) :=
          (Cardinal.mk_image_eq hspine.injective).symm
        _ ≤ #{x : W2 | x ∈ base ∧ blue.Adj x (vertex a) ∧
            blue.Adj x (vertex b)} :=
          Cardinal.mk_le_mk_of_subset himageSub
        _ < ℵ_ 1 := hpairSmall a ha b hb hab
    have hpairData : ∀ a ∈ blueLocal, ∀ b ∈ blueLocal, a ≠ b →
        #{x : W2 | x ∈ base ∧ blue.Adj x (vertex a) ∧
          blue.Adj x (vertex b)} < ℵ_ 1 ∧
        #{i : W2 | spine i ∈ base ∧
          i ∉ baseRedNeighborIndices red spine base (index a) ∧
          i ∉ baseRedNeighborIndices red spine base (index b)} <
            ℵ_ 1 := by
      intro a ha b hb hab
      exact ⟨hpairSmall a ha b hb hab, hprofileCover a ha b hb hab⟩
    exact ⟨blueLocal, inter_subset_left, hblueLocalBlue,
      hblueLocalType, hpairData⟩
  refine ⟨residual, spine, index, base, anchor, difference,
    hspine, hbaseSub, hindexInjective, hresidualCard, hbaseBlue, hbaseType,
    hbaseBefore, hprofileCard, hfirstDifference', hultrametric, ?_, ?_⟩
  · intro coordinates
    obtain ⟨fixed, largeFiber, hlocalCard, hlocalFixed⟩ :=
      hcountableProfiles coordinates
    obtain ⟨blueLocal, hblueLocalSub, hblueLocalBlue,
      hblueLocalType, hpairSmall⟩ :=
      hblueInLarge largeFiber hlocalCard
    exact ⟨fixed, largeFiber, blueLocal, hlocalCard, hblueLocalSub,
      by simpa only [index] using hlocalFixed,
      by simpa only [vertex] using hblueLocalBlue,
      by simpa only [vertex] using hblueLocalType,
      by simpa only [vertex] using hpairSmall⟩
  · intro cutoff hcountable
    obtain ⟨largeFiber, hlocalCard, hlocalDeep⟩ :=
      hcutoff cutoff hcountable
    obtain ⟨blueLocal, hblueLocalSub, hblueLocalBlue,
      hblueLocalType, hpairSmall⟩ :=
      hblueInLarge largeFiber hlocalCard
    exact ⟨largeFiber, blueLocal, hlocalCard, hblueLocalSub, hlocalDeep,
      by simpa only [vertex] using hblueLocalBlue,
      by simpa only [vertex] using hblueLocalType,
      by simpa only [vertex] using hpairSmall⟩

/-- Sharp global Part 3 normal form with the ultrametric branch
synchronised to the graph at every countable depth.  The original rich
stationary-fan residual is retained alongside the new deep-blue
consequence. -/
theorem part3_exact_or_orderedBlueRectangle_or_deepBlueNeighborhoodUltrametric
    (hCH : CH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      OrderedBlueOmegaOneByOmegaOneAddOneRedRectangle red blue ∨
      (LocallyCompactUltrametricOmegaOneBaseNeighborhoodResidualWithFan
          red blue ∧
        DeepBlueOmegaOneAddOneNeighborhoodUltrametricObstruction
          red blue) := by
  classical
  by_cases htarget :
      OrdinalRamsey.HasCliqueOfType red RedTarget ∨
        OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)
  · exact Or.inl htarget
  · have hnone := not_or.mp htarget
    obtain hexact | hrectangle | hresidual :=
      part3_exact_or_orderedBlueRectangle_or_neighborhoodUltrametric
        hCH red blue hcompl
    · exact (htarget hexact).elim
    · exact Or.inr (Or.inl hrectangle)
    · exact Or.inr (Or.inr ⟨hresidual,
        LocallyCompactUltrametricOmegaOneBaseNeighborhoodResidualWithFan.to_deepBlue
          hCH hcompl hnone.1 hnone.2 hresidual⟩)

end Erdos1172Part3OmegaOneNeighborDeepBlue
