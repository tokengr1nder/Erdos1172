/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableHechlerLimitCentering

@[expose] public section

/-!
# A countable Hechler extension over an arbitrary verified base

Each successor uses function names over the entire preceding order.
The limit keeps exact base agreement. Its countable fusion can be
performed with a prescribed strengthening in the original base.
Unlike a product of ground orders, this construction can be repeated
over an earlier limit without freezing its function names.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3CountableHechlerOverBase

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3FiniteHechlerStages (SmallClosedCenteredOrder extend initial)
open Erdos1172Part3IteratedHechlerOrder (Condition emptyOver liftBase liftBase_le)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3CountableHechlerLimitCentering (profileRank)

noncomputable def stageOver (hGCH : GCH) (R : SmallClosedCenteredOrder) :
    ℕ → SmallClosedCenteredOrder
  | 0 => R
  | n + 1 => extend hGCH (stageOver hGCH R n)

abbrev At (hGCH : GCH) (R : SmallClosedCenteredOrder) (n : ℕ) :=
  (stageOver hGCH R n).Carrier

structure LimitOver (hGCH : GCH) (R : SmallClosedCenteredOrder) where
  point : ∀ n : ℕ, At hGCH R n
  coherent : ∀ n : ℕ, (point (n + 1)).base = point n

variable {hGCH : GCH} {R : SmallClosedCenteredOrder}

instance : Preorder (LimitOver hGCH R) where
  le p q := ∀ n, p.point n ≤ q.point n
  le_refl _ _ := le_rfl
  le_trans _ _ _ hpq hqr n := (hpq n).trans (hqr n)

theorem limit_ext {p q : LimitOver hGCH R} (h : p.point = q.point) : p = q := by
  cases p
  cases q
  cases h
  rfl

def atMap (n : ℕ) : LimitOver hGCH R →o At hGCH R n :=
  ⟨fun p => p.point n, fun _ _ h => h n⟩

theorem exists_limit_starting_with (Good : ∀ n : ℕ, At hGCH R n → Prop)
    (first : R.Carrier) (hfirst : Good 0 first)
    (hstep : ∀ n (p : At hGCH R n), Good n p →
      ∃ q : At hGCH R (n + 1), q.base = p ∧ Good (n + 1) q) :
    ∃ q : LimitOver hGCH R, q.point 0 = first ∧ ∀ n, Good n (q.point n) := by
  classical
  let Entry (n : ℕ) := {p : At hGCH R n // Good n p}
  let next (n : ℕ) (p : Entry n) : Entry (n + 1) :=
    ⟨(hstep n p.val p.property).choose, (hstep n p.val p.property).choose_spec.2⟩
  let branch : ∀ n : ℕ, Entry n := fun n => Nat.rec (⟨first, hfirst⟩ : Entry 0) next n
  let q : LimitOver hGCH R :=
    { point n := (branch n).val
      coherent n := (hstep n (branch n).val (branch n).property).choose_spec.1 }
  exact ⟨q, rfl, fun n => (branch n).property⟩

/-- The supplied base remains exactly the zeroth projection. -/
noncomputable def emptyLimitOver (hGCH : GCH) (R : SmallClosedCenteredOrder)
    (p : R.Carrier) : LimitOver hGCH R :=
  (exists_limit_starting_with (fun _ _ => True) p trivial
    (fun _ q _ => ⟨emptyOver q, rfl, trivial⟩)).choose

theorem emptyLimitOver_base (p : R.Carrier) :
    (emptyLimitOver hGCH R p).point 0 = p :=
  (exists_limit_starting_with (fun _ _ => True) p trivial
    (fun _ q _ => ⟨emptyOver q, rfl, trivial⟩)).choose_spec.1

theorem exists_lift_base (p : LimitOver hGCH R) (q : R.Carrier) (hqp : q ≤ p.point 0) :
    ∃ s : LimitOver hGCH R, s ≤ p ∧ s.point 0 = q := by
  obtain ⟨s, hsbase, hs⟩ := exists_limit_starting_with
    (fun n r => r ≤ p.point n) q hqp (by
      intro n r hr
      refine ⟨liftBase (p.point (n + 1)) r, rfl, liftBase_le _ ?_⟩
      rwa [p.coherent n])
  exact ⟨s, hs, hsbase⟩

theorem exists_lift_one (p : LimitOver hGCH R) (q : Condition R.Carrier)
    (hqp : q ≤ p.point 1) :
    ∃ s : LimitOver hGCH R, s ≤ p ∧ s.point 1 = q := by
  let next : ∀ n : ℕ, At hGCH R n → At hGCH R (n + 1)
    | 0, _ => q
    | n + 1, previous => liftBase (p.point (n + 2)) previous
  let branch : ∀ n : ℕ, At hGCH R n := fun n => Nat.rec q.base next n
  have hcoherent : ∀ n, (branch (n + 1)).base = branch n := by
    intro n
    cases n <;> rfl
  have hbelow : ∀ n, branch n ≤ p.point n := by
    intro n
    induction n with
    | zero =>
      have h := Erdos1172Part3IteratedHechlerOrder.base_le hqp
      rwa [p.coherent 0] at h
    | succ n ih =>
      cases n with
      | zero => exact hqp
      | succ n =>
        apply liftBase_le
        rwa [p.coherent (n + 1)]
  exact ⟨⟨branch, hcoherent⟩, hbelow, rfl⟩

/-- Countable chains are fused coordinate by coordinate over the given
base lower bound, rather than by unrelated coordinatewise choices. -/
theorem exists_chain_lower_with_base (C : Set (LimitOver hGCH R)) (hC : C.Countable)
    (hchain : IsChain (· ≤ ·) C) (lower : R.Carrier)
    (hlower : ∀ p ∈ C, lower ≤ p.point 0) :
    ∃ q : LimitOver hGCH R, q.point 0 = lower ∧ ∀ p ∈ C, q ≤ p := by
  obtain ⟨q, hqbase, hq⟩ := exists_limit_starting_with
    (fun n r => ∀ p ∈ C, r ≤ p.point n) lower hlower (by
      intro n r hr
      have hbase : ∀ p ∈ (atMap (n + 1)) '' C, r ≤ p.base := by
        rintro _ ⟨p, hp, rfl⟩
        change r ≤ (p.point (n + 1)).base
        rw [p.coherent n]
        exact hr p hp
      obtain ⟨s, hsbase, hs⟩ :=
        Erdos1172Part3PrescribedBaseFusion.exists_chain_lower_with_base
          ((atMap (n + 1)) '' C) (hC.image (atMap (n + 1)))
          (hchain.image (atMap (n + 1))) r hbase
      exact ⟨s, hsbase, fun p hp => hs (p.point (n + 1)) ⟨p, hp, rfl⟩⟩)
  exact ⟨q, hqbase, fun p hp n => hq n p hp⟩

theorem countablyClosed : CountablyClosed (LimitOver hGCH R) := by
  intro C hne hC hchain
  obtain ⟨first, hfirst⟩ := R.closed ((atMap 0) '' C)
    (hne.image (atMap 0)) (hC.image (atMap 0)) (hchain.image (atMap 0))
  obtain ⟨q, _, hq⟩ := exists_chain_lower_with_base C hC hchain first
    (fun p hp => hfirst (p.point 0) ⟨p, hp, rfl⟩)
  exact ⟨q, hq⟩

noncomputable def profile (p : LimitOver hGCH R) : ℕ → W1 :=
  fun n => (stageOver hGCH R n).centered.code (p.point n)

theorem exists_same_profile_lower_with_base (p0 : LimitOver hGCH R)
    (C : Set (LimitOver hGCH R)) (hC : C.Countable)
    (hprofile : ∀ p ∈ C, profile p = profile p0)
    (lower : R.Carrier) (hlower : ∀ p ∈ C, lower ≤ p.point 0) :
    ∃ q : LimitOver hGCH R, q.point 0 = lower ∧ ∀ p ∈ C, q ≤ p := by
  obtain ⟨q, hqbase, hq⟩ := exists_limit_starting_with
    (fun n r => ∀ p ∈ C, r ≤ p.point n) lower hlower (by
      intro n r hr
      have hstem : ∀ p ∈ (atMap (n + 1)) '' C,
          p.stem = (p0.point (n + 1)).stem := by
        rintro _ ⟨p, hp, rfl⟩
        exact Erdos1172Part3PrescribedBaseFusion.same_stem_of_extend_code_eq
          (stageOver hGCH R n).centered hGCH.toCH (congrFun (hprofile p hp) (n + 1))
      have hbase : ∀ p ∈ (atMap (n + 1)) '' C, r ≤ p.base := by
        rintro _ ⟨p, hp, rfl⟩
        change r ≤ (p.point (n + 1)).base
        rw [p.coherent n]
        exact hr p hp
      obtain ⟨s, hsbase, hs⟩ :=
        Erdos1172Part3PrescribedBaseFusion.exists_same_stem_lower_with_base
          (p0.point (n + 1)) ((atMap (n + 1)) '' C)
          (hC.image (atMap (n + 1))) hstem r hbase
      exact ⟨s, hsbase, fun p hp => hs (p.point (n + 1)) ⟨p, hp, rfl⟩⟩)
  exact ⟨q, hqbase, fun p hp n => hq n p hp⟩

noncomputable def centered : CountablyCenteredCode (LimitOver hGCH R) where
  code p := profileRank hGCH.toCH (profile p)
  lower := by
    intro C hC value hvalue
    by_cases hne : C.Nonempty
    · obtain ⟨p0, hp0⟩ := hne
      have hprofile : ∀ p ∈ C, profile p = profile p0 := by
        intro p hp
        exact (profileRank hGCH.toCH).injective ((hvalue p hp).trans (hvalue p0 hp0).symm)
      obtain ⟨first, hfirst⟩ := R.centered.lower ((atMap 0) '' C)
        (hC.image (atMap 0)) (R.centered.code (p0.point 0)) (by
          rintro _ ⟨p, hp, rfl⟩
          exact congrFun (hprofile p hp) 0)
      obtain ⟨q, _, hq⟩ := exists_same_profile_lower_with_base p0 C hC hprofile first
        (fun p hp => hfirst (p.point 0) ⟨p, hp, rfl⟩)
      exact ⟨q, hq⟩
    · obtain ⟨first, _⟩ := R.centered.lower ∅ Set.countable_empty value
        (fun _ h => h.elim)
      exact ⟨emptyLimitOver hGCH R first, fun _ hp => (hne ⟨_, hp⟩).elim⟩

theorem mk_LimitOver_le : #(LimitOver hGCH R) ≤ ℵ_ 2 := by
  classical
  have emb (n : ℕ) : Nonempty (At hGCH R n ↪ W2) := (Cardinal.le_def _ _).mp (by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using (stageOver hGCH R n).small)
  let codes (n : ℕ) : At hGCH R n ↪ W2 := Classical.choice (emb n)
  let encode (p : LimitOver hGCH R) : ℕ → W2 := fun n => codes n (p.point n)
  have hinj : Injective encode := by
    intro p q h
    apply limit_ext
    funext n
    exact (codes n).injective (congrFun h n)
  apply (Cardinal.mk_le_of_injective hinj).trans
  simp only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_nat, W2,
    Cardinal.mk_toType, Ordinal.card_omega, hGCH.aleph_two_power_aleph_zero, le_refl]

/-- A new, verified order, including the actual earlier-order function
names at every successor coordinate. -/
noncomputable def extensionOrder (hGCH : GCH) (R : SmallClosedCenteredOrder) :
    SmallClosedCenteredOrder where
  Carrier := LimitOver hGCH R
  order := inferInstance
  closed := countablyClosed
  centered := centered
  small := mk_LimitOver_le

/-- Repeated countable blocks, each based on the preceding limit order. -/
noncomputable def omegaBlocks (hGCH : GCH) : ℕ → SmallClosedCenteredOrder
  | 0 => initial hGCH
  | n + 1 => extensionOrder hGCH (omegaBlocks hGCH n)

theorem omegaBlocks_countablyClosed (hGCH : GCH) (n : ℕ) :
    CountablyClosed (omegaBlocks hGCH n).Carrier := (omegaBlocks hGCH n).closed

theorem omegaBlocks_omegaTwoCC (hGCH : GCH) (n : ℕ) :
    Erdos1172Part3StationaryDecisions.OmegaTwoCC (omegaBlocks hGCH n).Carrier :=
  (omegaBlocks hGCH n).centered.omegaTwoCC

theorem omegaBlocks_card_le (hGCH : GCH) (n : ℕ) :
    #(omegaBlocks hGCH n).Carrier ≤ ℵ_ 2 := (omegaBlocks hGCH n).small

end Erdos1172Part3CountableHechlerOverBase
