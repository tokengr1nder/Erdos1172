/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3HechlerCentering

@[expose] public section

/-!
# Coding countable-support stem profiles

Under CH, countably supported profiles on at most omegaOne coordinates,
with at most omegaOne labels, admit an injective omegaOne code. An active
coordinate is tagged with `some`, even when its stem is empty. Thus the
code retains the support as well as the stems.

This is a coding theorem, not a construction or preservation theorem
for a longer Hechler iteration.
-/

open Cardinal Ordinal Set Function

namespace Erdos1172Part3CountableSupportProfiles

open ErdosRadoCHAsym (W1)
open Erdos1172Part3HechlerCentering (Stem mk_Stem_le)

abbrev Profile (I V : Type) := {f : I → Option V // {i | f i ≠ none}.Countable}

variable {I V : Type}

def support (p : Profile I V) : Set I := {i | p.val i ≠ none}

def graph (p : Profile I V) : Set (I × V) := {z | p.val z.1 = some z.2}

theorem graph_countable (p : Profile I V) : #(graph p) ≤ ℵ₀ := by
  have hinj : Injective (fun z : graph p =>
      (⟨z.val.1, by
        have hz := z.property
        change p.val z.val.1 = some z.val.2 at hz
        change p.val z.val.1 ≠ none
        rw [hz]
        intro h
        cases h⟩ : support p)) := by
    intro z w h
    apply Subtype.ext
    have hfirst : z.val.1 = w.val.1 := congrArg Subtype.val h
    apply Prod.ext hfirst
    have hz := z.property
    have hw := w.property
    change p.val z.val.1 = some z.val.2 at hz
    change p.val w.val.1 = some w.val.2 at hw
    rw [hfirst] at hz
    exact Option.some.inj (hz.symm.trans hw)
  exact (Cardinal.mk_le_of_injective hinj).trans
    (Cardinal.le_aleph0_iff_set_countable.mpr p.property)

theorem graph_injective : Injective (graph (I := I) (V := V)) := by
  intro p q hpq
  apply Subtype.ext
  funext i
  cases hp : p.val i with
  | none =>
    cases hq : q.val i with
    | none => rfl
    | some v =>
      have h : (i, v) ∈ graph p := by rw [hpq]; exact hq
      change p.val i = some v at h
      rw [hp] at h
      cases h
  | some v =>
    have h : (i, v) ∈ graph q := by rw [← hpq]; exact hp
    exact h.symm

theorem mk_Profile_le (hCH : CH) (hI : #I ≤ ℵ_ 1) (hV : #V ≤ ℵ_ 1) :
    #(Profile I V) ≤ ℵ_ 1 := by
  let graphCode (p : Profile I V) : {s : Set (I × V) // #s ≤ ℵ₀} :=
    ⟨graph p, graph_countable p⟩
  have hgraph : #(Profile I V) ≤ #{s : Set (I × V) // #s ≤ ℵ₀} :=
    Cardinal.mk_le_of_injective (f := graphCode)
      (fun _ _ h => graph_injective (congrArg Subtype.val h))
  have hprod : #(I × V) ≤ ℵ_ 1 := by
    rw [Cardinal.mk_prod]
    simp only [Cardinal.lift_id]
    exact (mul_le_mul' hI hV).trans_eq
      (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1))
  apply hgraph.trans
  apply (Cardinal.mk_bounded_set_le (I × V) ℵ₀).trans
  exact (Cardinal.power_le_power_right (max_le hprod (Cardinal.aleph0_le_aleph 1))).trans_eq
    hCH.aleph_one_power_aleph_zero

noncomputable def rank (hCH : CH) (hI : #I ≤ ℵ_ 1) (hV : #V ≤ ℵ_ 1) :
    Profile I V ↪ W1 :=
  Classical.choice ((Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_Profile_le hCH hI hV))

theorem same_rank_iff (hCH : CH) (hI : #I ≤ ℵ_ 1) (hV : #V ≤ ℵ_ 1)
    (p q : Profile I V) : rank hCH hI hV p = rank hCH hI hV q ↔ ∀ i, p.val i = q.val i := by
  constructor
  · intro h i
    exact congrArg (fun p : Profile I V => p.val i) ((rank hCH hI hV).injective h)
  · intro h
    exact congrArg (rank hCH hI hV) (Subtype.ext (funext h))

theorem support_eq_of_same_rank (hCH : CH) (hI : #I ≤ ℵ_ 1) (hV : #V ≤ ℵ_ 1)
    (p q : Profile I V) (h : rank hCH hI hV p = rank hCH hI hV q) :
    support p = support q :=
  congrArg support ((rank hCH hI hV).injective h)

/-- The extra option is intentional: an absent coordinate and a present
coordinate with an empty Hechler stem are different profiles. -/
abbrev StemProfile (I : Type) := Profile I Stem

theorem mk_StemProfile_le (hCH : CH) (hI : #I ≤ ℵ_ 1) :
    #(StemProfile I) ≤ ℵ_ 1 := mk_Profile_le hCH hI (mk_Stem_le hCH)

noncomputable def stemProfileRank (hCH : CH) (hI : #I ≤ ℵ_ 1) :
    StemProfile I ↪ W1 := rank hCH hI (mk_Stem_le hCH)

theorem active_inactive_codes_ne (hCH : CH) (hI : #I ≤ ℵ_ 1)
    (p q : StemProfile I) (i : I) (s : Stem)
    (hp : p.val i = some s) (hq : q.val i = none) :
    stemProfileRank hCH hI p ≠ stemProfileRank hCH hI q := by
  intro h
  have heq := congrArg (fun p : StemProfile I => p.val i)
    ((stemProfileRank hCH hI).injective h)
  rw [hp, hq] at heq
  cases heq

/-- Every prospective iteration length below omegaTwo has at most
omegaOne countable-support stem profiles under CH. This discharges the
coordinate-cardinality premise; it does not construct that iteration. -/
theorem mk_ordinal_StemProfile_le (hCH : CH) {α : Ordinal.{0}} (hα : α < ω_ 2) :
    #(StemProfile α.ToType) ≤ ℵ_ 1 := by
  apply mk_StemProfile_le hCH
  rw [Cardinal.mk_toType, Cardinal.card_le_iff]
  simpa only [Cardinal.succ_aleph, Cardinal.ord_aleph,
    show (1 : Ordinal) + 1 = 2 by norm_num] using hα

noncomputable def ordinalStemProfileRank (hCH : CH) {α : Ordinal.{0}} (hα : α < ω_ 2) :
    StemProfile α.ToType ↪ W1 :=
  Classical.choice ((Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_ordinal_StemProfile_le hCH hα))

end Erdos1172Part3CountableSupportProfiles
