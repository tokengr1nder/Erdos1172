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

/-- The extra option is intentional: an absent coordinate and a present
coordinate with an empty Hechler stem are different profiles. -/
abbrev StemProfile (I : Type) := Profile I Stem

end Erdos1172Part3CountableSupportProfiles
