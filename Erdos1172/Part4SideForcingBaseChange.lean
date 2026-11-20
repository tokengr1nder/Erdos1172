/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ResidualNameDensity

@[expose] public section

/-! # Base change for a Boolean-valued forcing of partial graphs -/

noncomputable section
set_option autoImplicit false
universe u
open bSet ErdosNameTransport Erdos1172BooleanFactor Erdos1172PosetProjection Erdos1172PosetCompletion
open scoped Flypitch
namespace Erdos1172BooleanNameIteration.BaseChange
variable {A B : Type u} [NontrivialCompleteBooleanAlgebra A] [NontrivialCompleteBooleanAlgebra B]
variable (j : CompleteLatticeHom A B) (Q : bSet A)
local notation "Q'" => mapNames j Q

/-- The new Boolean value is projected to the old algebra, with the
canonical label preserved even when the old condition's name is mixed. -/
def lower : (Q : bSet A) → Condition (mapNames j Q) → Condition Q
  | .mk _ _ _, p => ⟨lowerProjection j p.value,lowerProjection_ne_bot j p.nonzero,p.index,lowerProjection_le j p.valid⟩

theorem lower_value (p : Condition Q') : (lower j Q p).value = lowerProjection j p.value := by cases Q; rfl
theorem lower_name (p : Condition Q') : mapNames j (name (lower j Q p)) = name p := by cases Q; rfl

theorem lower_le_iff (p q : Condition Q') :
    p ≤ q ↔ p.value ≤ q.value ∧ lower j Q p ≤ lower j Q q := by
  have subset : j (name (lower j Q q) ⊆ᴮ name (lower j Q p)) = name q ⊆ᴮ name p := by
    rw [map_subset,lower_name,lower_name]
  constructor
  · intro h
    exact ⟨h.1,(lower_value j Q p).le.trans ((lowerProjection_mono j h.1).trans_eq (lower_value j Q q).symm),
      (lower_value j Q p).le.trans (lowerProjection_le j (h.2.trans_eq subset.symm))⟩
  · rintro ⟨hv,h⟩
    exact ⟨hv,((lowerProjection_le_iff j).mp ((lower_value j Q p).ge.trans h.2)).trans_eq subset⟩

def projection : Condition Q' →o Condition Q :=
  ⟨lower j Q,fun p q h => ((lower_le_iff j Q p q).mp h).2⟩

theorem exactLifts : ExactLifts (projection j Q) := by
  cases Q with
  | mk K f w =>
    intro p q qp
    let b := p.value ⊓ j q.value
    have pos : b ≠ ⊥ := fun h => inf_image_lowerProjection_ne_bot j q.nonzero qp.1 ((inf_comm _ _).trans h)
    let r : Condition (mapNames j (.mk K f w)) :=
      ⟨b,pos,q.index,inf_le_right.trans (OrderHomClass.mono j q.valid)⟩
    have eqn : projection j (.mk K f w) r = q := by
      rcases q with ⟨v,hv,i,hi⟩
      have hh : lowerProjection j (p.value ⊓ j v) = v := (lowerProjection_inf_image j _ _).trans (inf_eq_right.mpr qp.1)
      change (⟨lowerProjection j (p.value ⊓ j v),_,i,_⟩ : Condition _) = ⟨v,hv,i,hi⟩
      congr
    exact ⟨r,(lower_le_iff j _ _ _).mpr ⟨inf_le_left,eqn.le.trans qp⟩,eqn⟩

def hom : CompleteLatticeHom (Algebra Q) (Algebra Q') := completionHom (projection j Q) (exactLifts j Q)

theorem hom_injective (inj : Function.Injective j) : Function.Injective (hom j Q) := by
  apply completionHom_injective (projection j Q) (exactLifts j Q)
  cases Q with
  | mk K f w =>
    rintro ⟨v,hv,i,hi⟩
    have pos : j v ≠ ⊥ := fun h => hv (inj (h.trans (map_bot j).symm))
    let r : Condition (mapNames j (.mk K f w)) := ⟨j v,pos,i,OrderHomClass.mono j hi⟩
    refine ⟨r,?_⟩
    have eqn : lowerProjection j (j v) = v := inj (le_antisymm
      (OrderHomClass.mono j (lowerProjection_le j le_rfl)) (le_image_lowerProjection j (j v)))
    change (⟨lowerProjection j (j v),_,i,_⟩ : Condition _) = ⟨v,hv,i,hi⟩
    congr

theorem cone_le_hom (p : Condition Q') (x : Algebra Q) :
    condition p ≤ hom j Q x ↔ condition (lower j Q p) ≤ x :=
  condition_le_completionHom_iff _ _ _ _

theorem commutes (x : A) : hom j Q (sourceHom Q x) = sourceHom Q' (j x) := by
  apply Heyting.Regular.coe_injective
  apply SetLike.ext
  intro p
  rw [← condition_le_iff,← condition_le_iff,cone_le_hom,condition_le_source,condition_le_source,lower_value,lowerProjection_le_iff]

/-- The cone of a transported condition is its old cone localized at
its actual enlarged Boolean value. -/
theorem localized_cone (p : Condition Q') :
    hom j Q (condition (lower j Q p)) ⊓ sourceHom Q' p.value = condition p := by
  apply le_antisymm
  · intro t ht
    have h₁ : t ∈ (hom j Q (condition (lower j Q p))).val := ht.1
    have h₂ : t ∈ (sourceHom Q' p.value).val := ht.2
    have tv := (condition_le_source Q' t _).mp (condition_le_iff.mpr h₂)
    have hp := condition_le_iff.mp ((cone_le_hom j Q t _).mp (condition_le_iff.mpr h₁))
    apply (mem_condition_iff p t).mpr
    intro v vt
    obtain ⟨s,sv,sp⟩ := (mem_condition_iff _ _).mp hp (lower j Q v) ((projection j Q).monotone vt)
    obtain ⟨r,rv,eqn⟩ := exactLifts j Q v s sv
    exact ⟨r,rv,(lower_le_iff j Q r p).mpr ⟨(rv.trans vt).1.trans tv,eqn.le.trans sp⟩⟩
  · exact le_inf ((cone_le_hom j Q p _).mpr le_rfl) ((condition_le_source Q' p _).mpr le_rfl)

local instance itAlgebra {U : Type u} [NontrivialCompleteBooleanAlgebra U] (S : bSet U)
    [Nonempty (Condition S)] : NontrivialCompleteBooleanAlgebra (Algebra S) where
  toCompleteBooleanAlgebra := completionCompleteBooleanAlgebra
  bot_lt_top := bot_lt_top

private theorem hom_inf {X Y : Type u} [CompleteLattice X] [CompleteLattice Y] (f : CompleteLatticeHom X Y)
    (x y : X) : f (x ⊓ y) = f x ⊓ f y := by rw [← sInf_pair,map_sInf,Set.image_pair,sInf_pair]

variable [Nonempty (Condition Q)] [Nonempty (Condition (mapNames j Q))]

/-- A family dense over the old scalar algebra is dense over the enlarged
scalar algebra after transporting the same side forcing. -/
theorem denseOver {K : Type u} (d : K → Algebra Q) (dense : Erdos1172SeedQuotient.denseOver (sourceHom Q) d) :
    Erdos1172SeedQuotient.denseOver (sourceHom Q') (fun k => hom j Q (d k)) := by
  intro x pos
  obtain ⟨p,px⟩ := exists_condition_le pos
  obtain ⟨k,b,hb,old⟩ := dense _ (condition_ne_bot (lower j Q p))
  obtain ⟨s,hs⟩ := exists_condition_le hb
  have hp := condition_le_iff.mp (hs.trans old)
  obtain ⟨t,ts,tp⟩ := (mem_condition_iff _ _).mp hp s le_rfl
  obtain ⟨r,rp,hrt⟩ := exactLifts j Q p t tp
  have rt : condition (lower j Q r) ≤ d k ⊓ sourceHom Q b :=
    (condition_mono (hrt.le.trans ts)).trans hs
  have rv : r.value ≤ j b := (lowerProjection_le_iff j).mp ((lower_value j Q r).ge.trans
    ((condition_le_source Q (lower j Q r) b).mp (rt.trans inf_le_right)))
  let v := p.value ⊓ j b
  refine ⟨k,v,fun h => condition_ne_bot r (bot_unique ((le_inf
    ((cone_le_hom j Q r _).mpr (rt.trans inf_le_left)) ((condition_le_source Q' r v).mpr (le_inf rp.1 rv))).trans_eq h)),?_⟩
  have both : hom j Q (d k) ⊓ sourceHom Q' v ≤ hom j Q (d k ⊓ sourceHom Q b) := by
    exact (inf_le_inf_left _ ((OrderHomClass.mono (sourceHom Q') (show v ≤ j b from inf_le_right)).trans_eq
      (commutes j Q b).symm)).trans_eq (hom_inf (hom j Q) (d k) (sourceHom Q b)).symm
  exact (le_inf (both.trans (OrderHomClass.mono _ old)) (inf_le_right.trans (OrderHomClass.mono _ (show v ≤ p.value from inf_le_left)))).trans
    ((localized_cone j Q p).le.trans px)

end Erdos1172BooleanNameIteration.BaseChange
