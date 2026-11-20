/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3FiniteSupport
public import Erdos1172.Part3FunctionDecisions
public import Erdos1172.Part3RegularMembership

@[expose] public section

/-!
# Ground realization of actual members of a supported cover

A finite membership certificate records the function decisions needed for
one point to belong to a monotone cover. Its dense regularization is an
actual membership predicate, not a predicate of possible membership.

For at most omegaOne many actual members, countable closure builds a
descending omegaOne sequence meeting their certificates and deciding each
function coordinate. Its compatible decisions give one ground comparison
function covering all the members. There is no lower bound after the
completed omegaOne sequence and no ground domination assumption.

Consequently a uniform whole-set order-type bound on the ground covers
also bounds their actual members at a fixed condition. The corresponding
assertion about the union of all possible members is not asserted.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3SupportedCoverRealization

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ClosedDecisionSystem
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName regularize ground)
open Erdos1172Part3CofinalCoverSupport (FinitelySupported)

variable {P X : Type} [Preorder P]

/-- A finite lower-bound witness whose values have actually been decided. -/
def Certificate (F : FunctionDecisions P W1 W1)
    (C : (W1 → W1) → Set X) (p : P) (x : X) : Prop :=
  ∃ f : W1 → W1, ∃ support : Finset W1,
    (∀ i ∈ support, F.decides p i (f i)) ∧
    ∀ g : W1 → W1, (∀ i ∈ support, f i ≤ g i) → x ∈ C g

theorem certificate_persistent {F : FunctionDecisions P W1 W1}
    {C : (W1 → W1) → Set X} {p q : P} {x : X}
    (hqp : q ≤ p) (h : Certificate F C p x) : Certificate F C q x := by
  obtain ⟨f, support, hdec, hcover⟩ := h
  exact ⟨f, support, fun i hi => F.persistent hqp (hdec i hi), hcover⟩

/-- Membership certificates are required densely below the current
condition. A single compatible certificate would only give possibility. -/
def coverName (F : FunctionDecisions P W1 W1)
    (C : (W1 → W1) → Set X) : RegularName P X :=
  regularize (Certificate F C)

theorem holds_of_certificate {F : FunctionDecisions P W1 W1}
    {C : (W1 → W1) → Set X} {p : P} {x : X}
    (h : Certificate F C p x) : (coverName F C).holds p x :=
  fun q hqp => ⟨q, le_rfl, certificate_persistent hqp h⟩

/-- Ground functions recover precisely the original supported cover. -/
theorem coverName_ofFunction (C : (W1 → W1) → Set X)
    (hC : FinitelySupported C) (f : W1 → W1) :
    coverName (FunctionDecisions.ofFunction (P := P) f) C = ground (C f) := by
  apply RegularName.ext
  intro p x
  constructor
  · intro h
    obtain ⟨q, -, g, support, hdec, hcover⟩ := h p le_rfl
    exact hcover f (fun i hi => (hdec i hi).symm.le)
  · intro hx
    obtain ⟨support, hsupport⟩ := hC f x hx
    apply holds_of_certificate
    exact ⟨f, support, fun _ _ => rfl, hsupport⟩

/-- Finitely many coordinates can be decided with no closure assumption. -/
theorem exists_finite_decisions (F : FunctionDecisions P W1 W1)
    (support : Finset W1) (p : P) :
    ∃ q : P, q ≤ p ∧ ∀ i ∈ support, ∃ v, F.decides q i v := by
  classical
  induction support using Finset.induction_on generalizing p with
  | empty => exact ⟨p, le_rfl, by simp⟩
  | @insert i support hi ih =>
      obtain ⟨q, hqp, hvalues⟩ := ih p
      obtain ⟨r, hrq, v, hv⟩ := F.dense q i
      refine ⟨r, hrq.trans hqp, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨v, hv⟩
      · obtain ⟨w, hw⟩ := hvalues j hj
        exact ⟨w, F.persistent hrq hw⟩

/-- A pointwise comparison of names is tested at common decisions.
It does not decide the total functions at the displayed condition. -/
def PointwiseBelow (F H : FunctionDecisions P W1 W1) (p : P) : Prop :=
  ∀ q : P, q ≤ p → ∀ i v w,
    F.decides q i v → H.decides q i w → v ≤ w

theorem pointwiseBelow_mono {F H : FunctionDecisions P W1 W1}
    {p q : P} (h : PointwiseBelow F H p) (hqp : q ≤ p) :
    PointwiseBelow F H q :=
  fun r hr i v w hv hw => h r (hr.trans hqp) i v w hv hw

/-- Shared decisions persist to a dense comparison witness, so the
pointwise comparison itself is stable under dense refinement. -/
theorem pointwiseBelow_of_dense {F H : FunctionDecisions P W1 W1} {p : P}
    (h : ∀ q : P, q ≤ p → ∃ r : P, r ≤ q ∧ PointwiseBelow F H r) :
    PointwiseBelow F H p := by
  intro q hqp i v w hv hw
  obtain ⟨r, hrq, hr⟩ := h q hqp
  exact hr r le_rfl i v w (F.persistent hrq hv) (H.persistent hrq hw)

/-- Decide the upper function only on the finite support of one lower
certificate. Thus a pointwise comparison transfers membership densely. -/
theorem upper_holds_of_certificate
    {F H : FunctionDecisions P W1 W1} {C : (W1 → W1) → Set X}
    {p : P} {x : X} (hbelow : PointwiseBelow F H p)
    (hcert : Certificate F C p x) : (coverName H C).holds p x := by
  classical
  obtain ⟨f, support, hdec, hcover⟩ := hcert
  intro q hqp
  obtain ⟨r, hrq, hvalues⟩ := exists_finite_decisions H support q
  let value (i : support) : W1 := (hvalues i.val i.property).choose
  let g (i : W1) : W1 := if hi : i ∈ support then value ⟨i, hi⟩ else f i
  have hg (i : W1) (hi : i ∈ support) : H.decides r i (g i) := by
    simpa only [g, dif_pos hi, value] using (hvalues i hi).choose_spec
  have hfg (i : W1) (hi : i ∈ support) : f i ≤ g i :=
    hbelow r (hrq.trans hqp) i (f i) (g i)
      (F.persistent (hrq.trans hqp) (hdec i hi)) (hg i hi)
  refine ⟨r, hrq, g, support, hg, ?_⟩
  intro k hk
  exact hcover k (fun i hi => (hfg i hi).trans (hk i hi))

/-- Actual supported-cover membership is monotone under pointwise
comparison of function names. No countable or omegaOne fusion is needed. -/
theorem coverName_mono_of_pointwiseBelow
    {F H : FunctionDecisions P W1 W1} {C : (W1 → W1) → Set X}
    {p : P} (hbelow : PointwiseBelow F H p) {x : X}
    (hx : (coverName F C).holds p x) : (coverName H C).holds p x := by
  apply (coverName H C).of_dense p x
  intro q hqp
  obtain ⟨r, hrq, hr⟩ := hx q hqp
  exact ⟨r, hrq, upper_holds_of_certificate
    (pointwiseBelow_mono hbelow (hrq.trans hqp)) hr⟩

/-- Realize a small set of actual members in one ground cover. Only
countable proper stages of the omegaOne sequence take lower bounds. -/
theorem exists_ground_cover_of_actual_members
    (F : FunctionDecisions P W1 W1) (C : (W1 → W1) → Set X)
    (hclosed : CountablyClosed P) (p0 : P)
    (A : Set X) (hA : #A ≤ ℵ_ 1)
    (hactual : ∀ x ∈ A, (coverName F C).holds p0 x) :
    ∃ f : W1 → W1, A ⊆ C f := by
  classical
  obtain ⟨index⟩ : Nonempty (A ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using hA)
  let D (j : W1) : Set P := {p |
    (∃ v, F.decides p j v) ∧
      (p ≤ p0 → ∀ x : A, index x = j → Certificate F C p x.val)}
  have hD : ∀ j, DenseBelow (D j) := by
    intro j p
    obtain ⟨q, hqp, v, hv⟩ := F.dense p j
    by_cases hq0 : q ≤ p0
    · by_cases hrequest : ∃ x : A, index x = j
      · obtain ⟨r, hrq, hcert⟩ :=
          hactual hrequest.choose.val hrequest.choose.property q hq0
        refine ⟨r, ⟨⟨v, F.persistent hrq hv⟩, ?_⟩, hrq.trans hqp⟩
        intro _ x hx
        have heq : x = hrequest.choose :=
          index.injective (hx.trans hrequest.choose_spec.symm)
        subst x
        exact hcert
      · exact ⟨q, ⟨⟨v, hv⟩, fun _ x hx => (hrequest ⟨x, hx⟩).elim⟩, hqp⟩
    · exact ⟨q, ⟨⟨v, hv⟩, fun h => (hq0 h).elim⟩, hqp⟩
  obtain ⟨conditions, hanti, hstart, hmeet⟩ :=
    exists_antitone_dense_sequence hclosed p0 D hD
  have hvalues (i : W1) : ∃ v, F.decides (conditions i) i v :=
    (hmeet i).1
  let f (i : W1) : W1 := (hvalues i).choose
  have hf (i : W1) : F.decides (conditions i) i (f i) :=
    (hvalues i).choose_spec
  refine ⟨f, ?_⟩
  intro x hx
  let a : A := ⟨x, hx⟩
  obtain ⟨g, support, hdec, hcover⟩ :=
    (hmeet (index a)).2 (hstart (index a)) a rfl
  apply hcover f
  intro i hi
  have heq : g i = f i := F.unique
    (F.persistent (hanti (le_max_left (index a) i)) (hdec i hi))
    (F.persistent (hanti (le_max_right (index a) i)) (hf i))
  exact heq.le

variable [LinearOrder X] [WellFoundedLT X]

/-- Uniform bounds on entire ground covers transfer to actual members,
not just to each finite or countable trace separately. -/
theorem typeLT_actual_members_le
    (F : FunctionDecisions P W1 W1) (C : (W1 → W1) → Set X)
    (hclosed : CountablyClosed P) (p0 : P) (hX : #X ≤ ℵ_ 1)
    (bound : Ordinal.{0}) (hbound : ∀ f, typeLT (C f) ≤ bound) :
    typeLT {x : X | (coverName F C).holds p0 x} ≤ bound := by
  obtain ⟨f, hf⟩ := exists_ground_cover_of_actual_members F C hclosed p0
    {x : X | (coverName F C).holds p0 x}
    ((Cardinal.mk_subtype_le _).trans hX) (fun _ hx => hx)
  exact (Ordinal.type_mono hf).trans (hbound f)

/-- The strict version needed for genuine small-order-type loss sets. -/
theorem typeLT_actual_members_lt
    (F : FunctionDecisions P W1 W1) (C : (W1 → W1) → Set X)
    (hclosed : CountablyClosed P) (p0 : P) (hX : #X ≤ ℵ_ 1)
    (bound : Ordinal.{0}) (hbound : ∀ f, typeLT (C f) < bound) :
    typeLT {x : X | (coverName F C).holds p0 x} < bound := by
  obtain ⟨f, hf⟩ := exists_ground_cover_of_actual_members F C hclosed p0
    {x : X | (coverName F C).holds p0 x}
    ((Cardinal.mk_subtype_le _).trans hX) (fun _ hx => hx)
  exact (Ordinal.type_mono hf).trans_lt (hbound f)

end Erdos1172Part3SupportedCoverRealization
