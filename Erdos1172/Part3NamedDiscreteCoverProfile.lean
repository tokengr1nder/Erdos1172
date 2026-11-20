/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedShortCofinalCover
public import Erdos1172.Part3SupportedCoverConditionalMixing
public import Erdos1172.Part3StationaryDecisions
public import Erdos1172.Part3CenteredStationaryLoss

@[expose] public section

/-!
# Freezing a discrete cover profile on a stationary regular name

Local coverability persists under strengthening, by restricting a function
name and flattening the nested cone. A small set of profile parameters
therefore admits one stationary fiber of persistent local witnesses.

Regularizing that fiber gives a genuine source subname. Guarded mixing
then chooses one global function name for each source index, covering
all actual loss members whenever that index actually belongs to the
profile subname. No union of possible loss members is used as a cover.
-/

open Cardinal Set Order

namespace Erdos1172Part3NamedDiscreteCoverProfile

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName regularize reindex)
open Erdos1172Part3NamedLocalRowCover (onConeDecisions)
open Erdos1172Part3NamedCofinalRowCovers
  (nestCone flattenDecisions coverName_flatten_iff)
open Erdos1172Part3NamedShortCofinalCover (coverName_onCone_iff)
open Erdos1172Part3SupportedCoverRealization (coverName)
open Erdos1172Part3SupportedCoverConditionalMixing (exists_guarded_cover_of_local)
open Erdos1172Part3StationaryDecisions
  (Persistent possible StationaryAt OmegaTwoCC exists_stationary_refinement)
open Erdos1172Part3CenteredStationaryLoss (exists_stationary_fiber_of_small)

variable {P X E : Type} [Preorder P]

/-- A single cone-local function covers every actual member of the name
throughout the cone, with the specified fixed ground cover family. -/
def CoveredAt (U : RegularName P X) (C : (W1 → W1) → Set X) (p : P) : Prop :=
  ∃ F : FunctionDecisions (Iic p) W1 W1,
    ∀ q : Iic p, ∀ x : X, U.holds q.val x → (coverName F C).holds q x

/-- Restriction of a local covering function, followed by exact cone
flattening, preserves local coverability. -/
theorem coveredAt_persistent {U : RegularName P X} {C : (W1 → W1) → Set X}
    {p q : P} (hqp : q ≤ p) (hp : CoveredAt U C p) : CoveredAt U C q := by
  obtain ⟨F, hF⟩ := hp
  let r : Iic p := ⟨q, hqp⟩
  let Fcone : FunctionDecisions (Iic r) W1 W1 := onConeDecisions F r
  refine ⟨flattenDecisions r Fcone, ?_⟩
  intro s x hx
  apply (coverName_flatten_iff r Fcone C s x).mpr
  apply (coverName_onCone_iff r F C (nestCone r s) x).mpr
  exact hF (nestCone r s).val x hx

/-- A persistent witness for one selected discrete cover parameter. -/
def ProfileWitness (U : RegularName P W2) (loss : W2 → RegularName P X)
    (C : E → (W1 → W1) → Set X) (e : E) (p : P) (b : W2) : Prop :=
  U.holds p b ∧ CoveredAt (loss b) (C e) p

theorem profileWitness_persistent (U : RegularName P W2)
    (loss : W2 → RegularName P X) (C : E → (W1 → W1) → Set X) (e : E) :
    Persistent (ProfileWitness U loss C e) :=
  fun hqp hp => ⟨U.persistent hqp hp.1, coveredAt_persistent hqp hp.2⟩

/-- Actual profile membership requires local covering witnesses densely
below the current condition, not merely at one compatible condition. -/
def profileName (U : RegularName P W2) (loss : W2 → RegularName P X)
    (C : E → (W1 → W1) → Set X) (e : E) : RegularName P W2 :=
  regularize (ProfileWitness U loss C e)

theorem profileName_holds_of_witness (U : RegularName P W2)
    (loss : W2 → RegularName P X) (C : E → (W1 → W1) → Set X) (e : E)
    {p : P} {b : W2} (h : ProfileWitness U loss C e p b) :
    (profileName U loss C e).holds p b :=
  fun q hqp => ⟨q, le_rfl, profileWitness_persistent U loss C e hqp h⟩

/-- The profile regularization stays inside the original regular source. -/
theorem profileName_le_source (U : RegularName P W2)
    (loss : W2 → RegularName P X) (C : E → (W1 → W1) → Set X) (e : E) :
    ∀ p b, (profileName U loss C e).holds p b → U.holds p b := by
  intro p b hb
  apply U.of_dense p b
  intro q hqp
  obtain ⟨r, hrq, hr⟩ := hb q hqp
  exact ⟨r, hrq, hr.1⟩

/-- For a fixed profile, guarded antichain mixing globalizes the local
covering functions separately for each source point. -/
theorem exists_profile_functionNames (U : RegularName P W2)
    (loss : W2 → RegularName P X) (C : E → (W1 → W1) → Set X) (e : E) :
    ∃ F : W2 → FunctionDecisions P W1 W1,
      ∀ p b x, (profileName U loss C e).holds p b → (loss b).holds p x →
        (coverName (F b) (C e)).holds p x := by
  classical
  have hfunctions (b : W2) : ∃ H : FunctionDecisions P W1 W1,
      ∀ p x, (profileName U loss C e).holds p b → (loss b).holds p x →
        (coverName H (C e)).holds p x := by
    apply exists_guarded_cover_of_local
      (reindex (profileName U loss C e) (fun _ : Unit => b)) (loss b) (C e)
    intro p hp
    obtain ⟨q, hqp, hq⟩ := hp p le_rfl
    exact ⟨q, hqp, hq.2⟩
  choose F hF using hfunctions
  exact ⟨F, fun p b x hb hx => hF b p x hb hx⟩

/-- Freeze one small discrete profile on a stationary regular subname,
and produce global function names covering its actual loss members.
The only local mathematical input is the displayed cone coverability. -/
theorem exists_stationary_cover_profile
    (hE : #E < ℵ_ 2) (hcc : OmegaTwoCC P)
    (U : RegularName P W2) (p0 : P) (hs : IsStationary (possible U.holds p0))
    (loss : W2 → RegularName P X) (C : E → (W1 → W1) → Set X)
    (hlocal : ∀ p : P, p ≤ p0 → ∀ b : W2, U.holds p b →
      ∃ q : P, q ≤ p ∧ ∃ e : E, CoveredAt (loss b) (C e) q) :
    ∃ e : E, ∃ p : P, p ≤ p0 ∧ ∃ T : RegularName P W2,
      StationaryAt T.holds p ∧ (∀ q b, T.holds q b → U.holds q b) ∧
        ∃ F : W2 → FunctionDecisions P W1 W1,
          ∀ q b x, T.holds q b → (loss b).holds q x →
            (coverName (F b) (C e)).holds q x := by
  classical
  have witness (b : possible U.holds p0) :
      ∃ e : E, ∃ q : P, q ≤ p0 ∧ ProfileWitness U loss C e q b.val := by
    obtain ⟨p, hpp0, hp⟩ := b.property
    obtain ⟨q, hqp, e, hq⟩ := hlocal p hpp0 b.val hp
    exact ⟨e, q, hqp.trans hpp0, U.persistent hqp hp, hq⟩
  let chosen (b : possible U.holds p0) : E := (witness b).choose
  obtain ⟨e, hfiber⟩ := exists_stationary_fiber_of_small hE hs chosen
  have hpossible : IsStationary (possible (ProfileWitness U loss C e) p0) := by
    apply hfiber.mono
    rintro b ⟨hb, heq⟩
    obtain ⟨q, hqp0, hq⟩ := (witness ⟨b, hb⟩).choose_spec
    change (witness ⟨b, hb⟩).choose = e at heq
    rw [heq] at hq
    exact ⟨q, hqp0, hq⟩
  obtain ⟨p, hpp0, hp⟩ := exists_stationary_refinement hcc
    (ProfileWitness U loss C e) (profileWitness_persistent U loss C e) p0 hpossible
  have hstationary : StationaryAt (profileName U loss C e).holds p := by
    intro q hqp
    apply (hp q hqp).mono
    rintro b ⟨r, hrq, hr⟩
    exact ⟨r, hrq, profileName_holds_of_witness U loss C e hr⟩
  obtain ⟨F, hF⟩ := exists_profile_functionNames U loss C e
  exact ⟨e, p, hpp0, profileName U loss C e, hstationary,
    profileName_le_source U loss C e, F, hF⟩

end Erdos1172Part3NamedDiscreteCoverProfile
