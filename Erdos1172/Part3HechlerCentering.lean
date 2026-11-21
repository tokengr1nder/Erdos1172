/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3HechlerOrder

@[expose] public section

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3HechlerCentering

open ErdosRadoCHAsym (W1)
open Erdos1172Part3HechlerOrder

abbrev Stem : Type := {s : W1 → Option W1 // {i | s i ≠ none}.Countable}

def stemGraph (s : Stem) : Set (W1 × W1) := {p | s.val p.1 = some p.2}

theorem stemGraph_countable (s : Stem) : #(stemGraph s) ≤ ℵ₀ := by
  have hinj : Injective (fun p : stemGraph s =>
      (⟨p.val.1, by
        have h := p.property
        change s.val p.val.1 = some p.val.2 at h
        change s.val p.val.1 ≠ none
        rw [h]
        intro heq
        cases heq⟩ : {i | s.val i ≠ none})) := by
    intro p q heq
    apply Subtype.ext
    have hfst : p.val.1 = q.val.1 := congrArg Subtype.val heq
    apply Prod.ext hfst
    have hp := p.property
    have hq := q.property
    change s.val p.val.1 = some p.val.2 at hp
    change s.val q.val.1 = some q.val.2 at hq
    rw [hfst] at hp
    exact Option.some.inj (hp.symm.trans hq)
  exact (Cardinal.mk_le_of_injective hinj).trans
    (Cardinal.le_aleph0_iff_set_countable.mpr s.property)

theorem stemGraph_injective : Injective stemGraph := by
  intro s t heq
  apply Subtype.ext
  funext i
  cases hs : s.val i with
  | none =>
    cases ht : t.val i with
    | none => rfl
    | some v =>
      have hmem : (i, v) ∈ stemGraph s := by rw [heq]; exact ht
      change s.val i = some v at hmem
      rw [hs] at hmem
      cases hmem
  | some v =>
    have hmem : (i, v) ∈ stemGraph t := by rw [← heq]; exact hs
    exact hmem.symm

theorem mk_Stem_le (hCH : CH) : #Stem ≤ ℵ_ 1 := by
  let graphCode (s : Stem) : {t : Set (W1 × W1) // #t ≤ ℵ₀} := ⟨stemGraph s, stemGraph_countable s⟩
  have hgraph : #Stem ≤ #{t : Set (W1 × W1) // #t ≤ ℵ₀} :=
    Cardinal.mk_le_of_injective (f := graphCode)
      (fun _ _ h => stemGraph_injective (congrArg Subtype.val h))
  have hprod : #(W1 × W1) = ℵ_ 1 := by
    simp only [Cardinal.mk_prod, Cardinal.lift_id, W1, Cardinal.mk_toType,
      Ordinal.card_omega, Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)]
  apply hgraph.trans
  simpa only [hprod, max_eq_left (Cardinal.aleph0_le_aleph 1), hCH.aleph_one_power_aleph_zero]
    using Cardinal.mk_bounded_set_le (W1 × W1) ℵ₀

noncomputable def stemRank (hCH : CH) : Stem ↪ W1 := by
  exact Classical.choice ((Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_Stem_le hCH))

end Erdos1172Part3HechlerCentering
