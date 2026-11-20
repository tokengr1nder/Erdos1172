/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedStationaryTail
public import Erdos1172.Part3IteratedHechlerClosure
public import Erdos1172.Part3CenteredStationaryLoss
public import Erdos1172.Part3SupportedCoverRealization

@[expose] public section

/-!
# Stationary initial profiles for names of covering functions

The earlier function names need not be ground functions. Their values on
the countable initial segment can be decided after strengthening the base
condition. CH and the omegaTwo chain condition then retain a stationary
set of possible indices with one common initial profile.

Splicing this profile with the new Hechler coordinate function supplies
one upper function name. At every actual profile member it is pointwise
above that member's earlier function name. Finite supported cover
membership therefore transfers to the common upper cover.

The result does not assume a ground total dominator and does not assert
that arbitrary small loss names already have dense cover certificates.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3NamedCoverProfile

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3StationaryDecisions
open Erdos1172Part3IteratedHechlerOrder (Condition base_le liftBase liftBase_le liftFunction)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NamedStationaryTail (TailMembers)
open Erdos1172Part3SupportedCoverRealization
open Erdos1172Part3RegularMembership (RegularName regularize)

variable {P : Type} [Preorder P]

def ProfileMembers (U : P → W2 → Prop)
    (F : W2 → FunctionDecisions P W1 W1) (bound : W1)
    (profile : Set.Iic bound → W1) (p : Condition P) (a : W2) : Prop :=
  TailMembers U F bound p a ∧
    ∀ i : Set.Iic bound, (F a).decides p.base i.val (profile i)

theorem profileMembers_persistent (U : P → W2 → Prop) (hU : Persistent U)
    (F : W2 → FunctionDecisions P W1 W1) (bound : W1)
    (profile : Set.Iic bound → W1) : Persistent (ProfileMembers U F bound profile) := by
  intro p q a hqp ha
  exact ⟨Erdos1172Part3NamedStationaryTail.tailMembers_persistent U hU F bound hqp ha.1,
    fun i => (F a).persistent (base_le hqp) (ha.2 i)⟩

/-- Only the countable prefix is decided simultaneously. The same new
condition preserves every already actual tail-membership assertion. -/
theorem exists_prefix_deciding_extension
    (hclosed : CountablyClosed P) (p : Condition P)
    (F : FunctionDecisions P W1 W1) (bound : W1) :
    ∃ q : Condition P, q ≤ p ∧ ∃ profile : Set.Iic bound → W1,
      ∀ i : Set.Iic bound, F.decides q.base i.val (profile i) := by
  classical
  let prefixDecisions : FunctionDecisions P (Set.Iic bound) W1 :=
    ⟨fun p i v => F.decides p i.val v,
      fun p i => F.dense p i.val,
      fun {_ _ _ _} hqp hv => F.persistent hqp hv,
      fun {_ _ _ _} hv hw => F.unique hv hw⟩
  have hcount : #(Set.Iic bound) ≤ ℵ₀ :=
    Cardinal.lt_aleph_one_iff.mp (Erdos1172Part3ConvergentCore.mk_Iic_W1_lt bound)
  obtain ⟨base, hbase, hvalues⟩ := prefixDecisions.exists_simultaneous hclosed p.base hcount
  exact ⟨liftBase p base, liftBase_le p hbase,
    fun i => (hvalues i).choose, fun i => (hvalues i).choose_spec⟩

theorem profileSpace_card_lt (hCH : CH) (bound : W1) :
    #(Set.Iic bound → W1) < ℵ_ 2 := by
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
  have hcount : #(Set.Iic bound) ≤ ℵ₀ :=
    Cardinal.lt_aleph_one_iff.mp (Erdos1172Part3ConvergentCore.mk_Iic_W1_lt bound)
  exact ((Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le
    (Cardinal.aleph0_le_aleph 1)).ne' hcount).trans_eq
      hCH.aleph_one_power_aleph_zero).trans_lt
        (Cardinal.aleph_lt_aleph.mpr (by norm_num : (1 : Ordinal.{0}) < 2))

/-- Initial-profile freezing for genuine earlier-stage function names.
The stationary set consists of persistent possibilities below a condition;
no completed omegaOne descending sequence is used to preserve it. -/
theorem exists_stationary_uniform_profile
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P) (hCH : CH)
    (p0 : Condition P) (U : P → W2 → Prop) (hU : Persistent U)
    (hs : IsStationary (possible U p0.base))
    (F : W2 → FunctionDecisions P W1 W1) :
    ∃ bound : W1, ∃ profile : Set.Iic bound → W1,
      ∃ p : Condition P, p ≤ p0 ∧ StationaryAt (ProfileMembers U F bound profile) p := by
  classical
  obtain ⟨bound, p, hpp0, hp⟩ :=
    Erdos1172Part3NamedStationaryTail.exists_stationary_uniform_tail
      center hCH p0 U hU hs F
  have witness (a : possible (TailMembers U F bound) p) :
      ∃ profile : Set.Iic bound → W1, ∃ q : Condition P,
        q ≤ p ∧ ProfileMembers U F bound profile q a.val := by
    obtain ⟨q, hqp, hq⟩ := a.property
    obtain ⟨r, hrq, profile, hprofile⟩ :=
      exists_prefix_deciding_extension hclosed q (F a.val) bound
    exact ⟨profile, r, hrq.trans hqp,
      Erdos1172Part3NamedStationaryTail.tailMembers_persistent U hU F bound hrq hq,
      hprofile⟩
  let chosen (a : possible (TailMembers U F bound) p) : Set.Iic bound → W1 :=
    (witness a).choose
  obtain ⟨profile, hfiber⟩ :=
    Erdos1172Part3CenteredStationaryLoss.exists_stationary_fiber_of_small
      (profileSpace_card_lt hCH bound) (hp p le_rfl) chosen
  have hpossible : IsStationary (possible (ProfileMembers U F bound profile) p) := by
    apply hfiber.mono
    rintro a ⟨ha, heq⟩
    obtain ⟨q, hqp, hq⟩ := (witness ⟨a, ha⟩).choose_spec
    change (witness ⟨a, ha⟩).choose = profile at heq
    rw [heq] at hq
    exact ⟨q, hqp, hq⟩
  obtain ⟨q, hqp, hq⟩ := exists_stationary_refinement (center.extend hCH).omegaTwoCC
    (ProfileMembers U F bound profile) (profileMembers_persistent U hU F bound profile)
    p hpossible
  exact ⟨bound, profile, q, hqp.trans hpp0, hq⟩

/-- The fixed countable prefix followed by the new Hechler coordinates. -/
noncomputable def upperFunction (hclosed : CountablyClosed P) (bound : W1)
    (profile : Set.Iic bound → W1) : FunctionDecisions (Condition P) W1 W1 := by
  classical
  let coordinate := Erdos1172Part3IteratedHechlerClosure.coordinateFunction hclosed
  exact {
    decides := fun p i v => if hi : i ≤ bound then profile ⟨i, hi⟩ = v
      else coordinate.decides p i v
    dense := by
      intro p i
      by_cases hi : i ≤ bound
      · exact ⟨p, le_rfl, profile ⟨i, hi⟩, by simp only [dif_pos hi]⟩
      · obtain ⟨q, hqp, v, hv⟩ := coordinate.dense p i
        exact ⟨q, hqp, v, by simpa only [dif_neg hi] using hv⟩
    persistent := by
      intro p q i v hqp hv
      by_cases hi : i ≤ bound
      · simpa only [dif_pos hi] using hv
      · simp only [dif_neg hi] at hv ⊢
        exact coordinate.persistent hqp hv
    unique := by
      intro p i v w hv hw
      by_cases hi : i ≤ bound
      · simp only [dif_pos hi] at hv hw
        exact hv.symm.trans hw
      · simp only [dif_neg hi] at hv hw
        exact coordinate.unique hv hw }

/-- Actual profile membership gives a comparison of names on the full
domain, combining decided prefix values with the named tail domination. -/
theorem pointwiseBelow_of_profileMember
    (hclosed : CountablyClosed P) (U : P → W2 → Prop)
    (F : W2 → FunctionDecisions P W1 W1) (bound : W1)
    (profile : Set.Iic bound → W1) {p : Condition P} {a : W2}
    (ha : ProfileMembers U F bound profile p a) :
    PointwiseBelow (liftFunction (F a)) (upperFunction hclosed bound profile) p := by
  intro q hqp i v w hv hw
  change (F a).decides q.base i v at hv
  by_cases hi : i ≤ bound
  · have hprefix := (F a).persistent (base_le hqp) (ha.2 ⟨i, hi⟩)
    have hvprofile : v = profile ⟨i, hi⟩ := (F a).unique hv hprefix
    have hprofilew : profile ⟨i, hi⟩ = w := by
      simpa only [upperFunction, dif_pos hi] using hw
    exact (hvprofile.trans hprofilew).le
  · have hstem : q.stem i = some w := by
      simpa only [upperFunction, dif_neg hi,
        Erdos1172Part3IteratedHechlerClosure.coordinateFunction] using hw
    exact (ha.1.2 q hqp i (lt_of_not_ge hi) w hstem q.base le_rfl v hv).le

/-- Dense regularization supplies a regular future membership name. -/
def profileName (U : P → W2 → Prop)
    (F : W2 → FunctionDecisions P W1 W1) (bound : W1)
    (profile : Set.Iic bound → W1) : RegularName (Condition P) W2 :=
  regularize (ProfileMembers U F bound profile)

/-- A dense family of actual profile witnesses suffices for the same
comparison at the original condition. -/
theorem pointwiseBelow_of_regularized_profileMember
    (hclosed : CountablyClosed P) (U : P → W2 → Prop)
    (F : W2 → FunctionDecisions P W1 W1) (bound : W1)
    (profile : Set.Iic bound → W1) {p : Condition P} {a : W2}
    (ha : (profileName U F bound profile).holds p a) :
    PointwiseBelow (liftFunction (F a)) (upperFunction hclosed bound profile) p := by
  apply pointwiseBelow_of_dense
  intro q hqp
  obtain ⟨r, hrq, hr⟩ := ha q hqp
  exact ⟨r, hrq, pointwiseBelow_of_profileMember hclosed U F bound profile hr⟩

/-- A certificate-backed loss cover transfers to the single upper cover
at each actual profile member. Density of certificates for the intended
loss names remains an independent, explicit requirement. -/
theorem upper_cover_holds_of_profileMember {X : Type}
    (hclosed : CountablyClosed P) (U : P → W2 → Prop)
    (F : W2 → FunctionDecisions P W1 W1) (bound : W1)
    (profile : Set.Iic bound → W1) (C : (W1 → W1) → Set X)
    {p : Condition P} {a : W2} (ha : ProfileMembers U F bound profile p a)
    {x : X} (hx : (coverName (liftFunction (F a)) C).holds p x) :
    (coverName (upperFunction hclosed bound profile) C).holds p x :=
  coverName_mono_of_pointwiseBelow
    (pointwiseBelow_of_profileMember hclosed U F bound profile ha) hx

/-- The regularized stationary profile can be used directly with the
regular neighborhood algebra without losing the upper-cover comparison. -/
theorem upper_cover_holds_of_regularized_profileMember {X : Type}
    (hclosed : CountablyClosed P) (U : P → W2 → Prop)
    (F : W2 → FunctionDecisions P W1 W1) (bound : W1)
    (profile : Set.Iic bound → W1) (C : (W1 → W1) → Set X)
    {p : Condition P} {a : W2} (ha : (profileName U F bound profile).holds p a)
    {x : X} (hx : (coverName (liftFunction (F a)) C).holds p x) :
    (coverName (upperFunction hclosed bound profile) C).holds p x :=
  coverName_mono_of_pointwiseBelow
    (pointwiseBelow_of_regularized_profileMember hclosed U F bound profile ha) hx

end Erdos1172Part3NamedCoverProfile
