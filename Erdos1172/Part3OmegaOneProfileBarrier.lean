/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3TransfiniteIncidence
public import Erdos1172.ForMathlib.SetTheory.Cardinal.GCHConsequences1172

@[expose] public section

open Cardinal Ordinal Set Function

namespace Erdos1172Part3OmegaOneProfileBarrier

open Erdos1172Part3Failure Erdos1172Part3TransfiniteIncidence

abbrev W1 : Type := (ω_ 1 : Ordinal.{0}).ToType

/-- Under GCH, a dependent product of `ω₁` many types, each of
cardinality `ℵ₁`, has cardinality exactly `ℵ₂`. -/
theorem mk_pi_W1_eq_alephTwo_of_forall_mk_eq_alephOne
    (hGCH : GCH) (A : W1 → Type) (hA : ∀ i, #(A i) = ℵ_ 1) :
    #(∀ i, A i) = ℵ_ 2 := by
  rw [Cardinal.mk_pi]
  calc
    Cardinal.prod (fun i : W1 ↦ #(A i)) =
        Cardinal.prod (fun _ : W1 ↦ (ℵ_ 1 : Cardinal.{0})) := by
      congr 1
      funext i
      exact hA i
    _ = (ℵ_ 1 : Cardinal.{0}) ^ #W1 :=
      Cardinal.prod_const' W1 (ℵ_ 1)
    _ = (ℵ_ 1 : Cardinal.{0}) ^ ℵ_ 1 := by
      simp only [W1, Cardinal.mk_toType, Ordinal.card_omega]
    _ = ((2 : Cardinal.{0}) ^ ℵ₀) ^ ℵ_ 1 :=
      congrArg (fun k : Cardinal.{0} ↦ k ^ (ℵ_ 1))
        hGCH.two_power_aleph_zero |>.symm
    _ = (2 : Cardinal.{0}) ^ (ℵ₀ * ℵ_ 1) :=
      (@Cardinal.power_mul 2 ℵ₀ (ℵ_ 1)).symm
    _ = (2 : Cardinal.{0}) ^ ℵ_ 1 := by
      rw [Cardinal.aleph0_mul_aleph]
    _ = ℵ_ 2 := hGCH.two_power_aleph_one

/-- At a regular `ℵ₂` domain, every map has either a full-size constant
fiber or a full-size restriction on which it is injective. -/
theorem alephTwo_fiber_or_alephTwo_injective_restriction
    {D P : Type} (hD : #D = ℵ_ 2) (f : D → P) :
    (∃ p : P, #(f ⁻¹' {p}) = ℵ_ 2) ∨
      ∃ residual : Set D, #residual = ℵ_ 2 ∧ Set.InjOn f residual := by
  classical
  let rangeMap : D → Set.range f := fun x ↦ ⟨f x, Set.mem_range_self x⟩
  by_cases hsmall : #(Set.range f) < ℵ_ 2
  · obtain ⟨value, hvalue⟩ := Cardinal.infinite_pigeonhole rangeMap
      (by rw [hD]; exact Cardinal.aleph0_le_aleph 2)
      (by
        rw [hD]
        rw [show (ℵ_ 2 : Cardinal.{0}) =
            ℵ_ ((1 : Ordinal.{0}) + 1) by norm_num,
          (Cardinal.isRegular_aleph_add_one 1).cof_ord]
        simpa only [show (1 : Ordinal.{0}) + 1 = 2 by norm_num]
          using hsmall)
    left
    refine ⟨value, ?_⟩
    have hfiber : rangeMap ⁻¹' {value} = f ⁻¹' {(value : P)} := by
      ext x
      change rangeMap x = value ↔ f x = (value : P)
      constructor
      · exact fun h ↦ congrArg Subtype.val h
      · exact fun h ↦ Subtype.ext h
    rw [← hfiber, hvalue, hD]
  · have hrangeCard : #(Set.range f) = ℵ_ 2 := by
      apply le_antisymm
      · exact Cardinal.mk_range_le.trans_eq hD
      · exact le_of_not_gt hsmall
    have hpickExists (value : Set.range f) :
        ∃ x : D, f x = value := value.property
    let pick : Set.range f → D := fun value ↦
      Classical.choose (hpickExists value)
    have hpickSpec (value : Set.range f) : f (pick value) = value :=
      Classical.choose_spec (hpickExists value)
    have hpickInjective : Function.Injective pick := by
      intro a b hab
      apply Subtype.ext
      rw [← hpickSpec a, ← hpickSpec b, hab]
    let residual : Set D := Set.range pick
    have hresidualCard : #residual = ℵ_ 2 := by
      calc
        #residual = #(Set.range f) :=
          Cardinal.mk_range_eq pick hpickInjective
        _ = ℵ_ 2 := hrangeCard
    right
    refine ⟨residual, hresidualCard, ?_⟩
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ hxy
    have hab : a = b := by
      apply Subtype.ext
      simpa only [hpickSpec] using hxy
    exact congrArg pick hab

/-- The exact `ω₁`-profile threshold left by full cross-arm incidence.
The earlier arms are blue copies of `ω₁ + 1`; later representatives form
a strictly increasing `ω₂` spine.  Every later representative carries a
complete red-predecessor profile through all earlier arms.  The profile
space itself has cardinality `ℵ₂`, and either one profile has a full
`ℵ₂` fiber or the profile map is injective on a full `ℵ₂` residual. -/
def OmegaOnePredecessorProfileBarrier
    (red blue : SimpleGraph W2) : Prop :=
  ∃ (earlierArms : W1 → Set W2) (laterRepresentative : W2 → W2)
      (domain : Set W2) (profile : domain → ∀ i, earlierArms i),
    (∀ i, blue.IsClique (earlierArms i) ∧
      typeLT (earlierArms i) = ω_ 1 + 1) ∧
    (∀ i j, i < j → ∀ x ∈ earlierArms i,
      ∀ y ∈ earlierArms j, x < y) ∧
    StrictMono laterRepresentative ∧
    typeLT (Set.range laterRepresentative) = ω_ 2 ∧
    #domain = ℵ_ 2 ∧
    #(∀ i, earlierArms i) = ℵ_ 2 ∧
    (∀ b : domain, ∀ i,
      (profile b i : W2) < laterRepresentative b ∧
      red.Adj (profile b i) (laterRepresentative b)) ∧
    ((∃ (fixed : ∀ i, earlierArms i) (fiber : Set domain),
        #fiber = ℵ_ 2 ∧
        ∀ b ∈ fiber, profile b = fixed) ∨
      ∃ residual : Set domain,
        #residual = ℵ_ 2 ∧ Set.InjOn profile residual)

private theorem typeLT_range_eq_omegaTwo_of_strictMono
    (f : W2 → W2) (hf : StrictMono f) :
    typeLT (Set.range f) = ω_ 2 := by
  have htype :=
    ((hf.strictMonoOn Set.univ).orderIso f Set.univ).ordinalType_congr
  have himageRange :
      typeLT (f '' Set.univ) = typeLT (Set.range f) :=
    (OrderIso.setCongr (f '' Set.univ) (Set.range f)
      Set.image_univ).ordinalType_congr
  calc
    typeLT (Set.range f) = typeLT (f '' Set.univ) := himageRange.symm
    _ = typeLT (Set.univ : Set W2) := htype.symm
    _ = typeLT W2 := OrderIso.Set.univ.ordinalType_congr
    _ = ω_ 2 := by
      simpa only [W2] using Ordinal.type_toType (ω_ 2 : Ordinal.{0})

/-- Full cross-arm incidence produces the exact `ω₁` predecessor-profile
barrier under GCH. -/
theorem fullOmegaTwoIncidence_has_omegaOnePredecessorProfileBarrier
    (hGCH : GCH) (red blue : SimpleGraph W2)
    (hobs : FullOmegaTwoIncidenceObstruction red blue) :
    OmegaOnePredecessorProfileBarrier red blue := by
  classical
  obtain ⟨arms, harms, hordered, hsuccessor, hincidence⟩ := hobs
  let stage : W2 → ArmIndex := fun a ↦ ⟨(a : Ordinal), a.toOrd.2⟩
  have hstageStrict : StrictMono stage := by
    intro a b hab
    change (a : Ordinal) < (b : Ordinal)
    rw [← Ordinal.ToType.mk.apply_symm_apply a,
      ← Ordinal.ToType.mk.apply_symm_apply b] at hab
    exact (Ordinal.ToType.mk.lt_iff_lt).mp hab
  have homegaOneTwo : (ω_ 1 : Ordinal.{0}) < ω_ 2 :=
    Ordinal.omega_lt_omega.mpr one_lt_two
  let cutoff : W2 := Ordinal.ToType.mk ⟨ω_ 1, homegaOneTwo⟩
  let earlyPoint (i : W1) : W2 :=
    Ordinal.ToType.mk ⟨(i : Ordinal), by
      change (i : Ordinal) < ω_ 2
      exact i.toOrd.2.trans homegaOneTwo⟩
  let early (i : W1) : ArmIndex := stage (earlyPoint i)
  have hearlyPointLtCutoff (i : W1) : earlyPoint i < cutoff := by
    apply Ordinal.ToType.mk.lt_iff_lt.mpr
    exact i.toOrd.2
  have hearlyPointStrict : StrictMono earlyPoint := by
    intro i j hij
    apply Ordinal.ToType.mk.lt_iff_lt.mpr
    change (i : Ordinal) < (j : Ordinal)
    rw [← Ordinal.ToType.mk.apply_symm_apply i,
      ← Ordinal.ToType.mk.apply_symm_apply j] at hij
    exact (Ordinal.ToType.mk.lt_iff_lt).mp hij
  have hearlyStrict : StrictMono early :=
    hstageStrict.comp hearlyPointStrict
  have hearlyBeforeTail (i : W1) (b : Set.Ioi cutoff) :
      early i < stage (b : W2) :=
    hstageStrict ((hearlyPointLtCutoff i).trans b.property)
  have hrepresentativeExists (a : W2) :
      ∃ x : arms (stage a), IsMax x :=
    exists_max_of_type_omegaOne_add_one (harms (stage a)).2
  let representative (a : W2) : arms (stage a) :=
    Classical.choose (hrepresentativeExists a)
  have hrepresentativeStrict : StrictMono
      (fun a : W2 ↦ (representative a : W2)) := by
    intro a b hab
    exact hordered (stage a) (stage b) (hstageStrict hab)
      (representative a) (representative a).property
      (representative b) (representative b).property
  let earlierArms : W1 → Set W2 := fun i ↦ arms (early i)
  have hearlierArms (i : W1) :
      blue.IsClique (earlierArms i) ∧
        typeLT (earlierArms i) = ω_ 1 + 1 :=
    harms (early i)
  have hearlierOrdered (i j : W1) (hij : i < j) :
      ∀ x ∈ earlierArms i, ∀ y ∈ earlierArms j, x < y :=
    hordered (early i) (early j) (hearlyStrict hij)
  have hpredecessorExists (b : Set.Ioi cutoff) (i : W1) :
      ∃ x : earlierArms i,
        red.Adj x (representative (b : W2)) := by
    obtain ⟨x, hx, hred⟩ :=
      hincidence (early i) (stage (b : W2))
        (hearlyBeforeTail i b)
        (representative (b : W2)) (representative (b : W2)).property
    exact ⟨⟨x, hx⟩, hred⟩
  let profile (b : Set.Ioi cutoff) : ∀ i, earlierArms i :=
    fun i ↦ Classical.choose (hpredecessorExists b i)
  have hprofileRed (b : Set.Ioi cutoff) (i : W1) :
      red.Adj (profile b i) (representative (b : W2)) :=
    Classical.choose_spec (hpredecessorExists b i)
  have hprofileEarlier (b : Set.Ioi cutoff) (i : W1) :
      (profile b i : W2) < representative (b : W2) :=
    hordered (early i) (stage (b : W2)) (hearlyBeforeTail i b)
      (profile b i) (profile b i).property
      (representative (b : W2)) (representative (b : W2)).property
  have hearlierCard (i : W1) : #(earlierArms i) = ℵ_ 1 := by
    have hc := congrArg Ordinal.card (hearlierArms i).2
    simpa only [Ordinal.card_type, Cardinal.card_omega_one_add_one] using hc
  have hprofileSpace : #(∀ i, earlierArms i) = ℵ_ 2 :=
    mk_pi_W1_eq_alephTwo_of_forall_mk_eq_alephOne
      hGCH (fun i ↦ earlierArms i) hearlierCard
  have hdomainCard : #(Set.Ioi cutoff) = ℵ_ 2 :=
    mk_Ioi_omegaTwo_eq cutoff
  obtain ⟨fixed, hfixed⟩ | ⟨residual, hresidualCard,
      hresidualInjective⟩ :=
    alephTwo_fiber_or_alephTwo_injective_restriction
      hdomainCard profile
  · refine ⟨earlierArms, (fun a ↦ representative a), Set.Ioi cutoff,
      profile, hearlierArms, hearlierOrdered, hrepresentativeStrict,
      typeLT_range_eq_omegaTwo_of_strictMono _ hrepresentativeStrict,
      hdomainCard, hprofileSpace, ?_, Or.inl ?_⟩
    · exact fun b i ↦ ⟨hprofileEarlier b i, hprofileRed b i⟩
    · exact ⟨fixed, profile ⁻¹' {fixed}, hfixed,
        fun b hb ↦ by
          simpa only [mem_preimage, mem_singleton_iff] using hb⟩
  · refine ⟨earlierArms, (fun a ↦ representative a), Set.Ioi cutoff,
      profile, hearlierArms, hearlierOrdered, hrepresentativeStrict,
      typeLT_range_eq_omegaTwo_of_strictMono _ hrepresentativeStrict,
      hdomainCard, hprofileSpace, ?_, Or.inr ?_⟩
    · exact fun b i ↦ ⟨hprofileEarlier b i, hprofileRed b i⟩
    · exact ⟨residual, hresidualCard, hresidualInjective⟩

/-- Global exact-target-or-`ω₁`-profile-barrier normal form under GCH. -/
theorem part3_exact_or_omegaOnePredecessorProfileBarrier
    (hGCH : GCH) (red blue : SimpleGraph W2) (hcompl : IsCompl red blue) :
    (OrdinalRamsey.HasCliqueOfType red
        Erdos1172Part3FiniteStars.RedTarget ∨
      OrdinalRamsey.HasCliqueOfType blue (ω_ 1 + 2)) ∨
      OmegaOnePredecessorProfileBarrier red blue := by
  obtain htarget | hobs :=
    part3_exact_or_fullOmegaTwoIncidenceObstruction
      hGCH.toCH red blue hcompl
  · exact Or.inl htarget
  · exact Or.inr <|
      fullOmegaTwoIncidence_has_omegaOnePredecessorProfileBarrier
        hGCH red blue hobs

end Erdos1172Part3OmegaOneProfileBarrier
