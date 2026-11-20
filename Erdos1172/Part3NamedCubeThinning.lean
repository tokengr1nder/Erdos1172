/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CubeDominationCoding

@[expose] public section

/-!
# Coherent two-level tail selection inside a named cube

The stem at an outer row chooses a middle tail. The stem at the code of
that row and middle coordinate chooses an inner tail. Compatible stem
decisions fix both choices, preserving the exact cubic lexicographic
order as well as all earlier clique edges.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedCubeThinning

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3IteratedHechlerOrder (Condition liftBase liftBase_le base_le)
open Erdos1172Part3StationarySquareDecisions (Square tail tail_strict)
open Erdos1172Part3FullSourceCubes (Cube)
open Erdos1172Part3CubeDominationCoding (pairEquiv)

noncomputable def selectedPair (row : W1 → W1) (v : W1) (z : Cube) : Square :=
  toLex (row (ofLex z).1, tail v (ofLex (ofLex z).2).1)

noncomputable def selectedIndex (row : W1 → W1) (v w : W1) (z : Cube) : Cube :=
  toLex (row (ofLex z).1, toLex (tail v (ofLex (ofLex z).2).1, tail w (ofLex (ofLex z).2).2))

variable {P : Type} [Preorder P]

theorem selectedIndex_lt {row : W1 → W1} (hrow : StrictMono row)
    {p : Condition P} {i j : Cube} {v w v' w' : W1} (hij : i < j)
    (hv : p.stem (row (ofLex i).1) = some v) (hv' : p.stem (row (ofLex j).1) = some v')
    (hw : p.stem (pairEquiv (selectedPair row v i)) = some w)
    (hw' : p.stem (pairEquiv (selectedPair row v' j)) = some w') :
    selectedIndex row v w i < selectedIndex row v' w' j := by
  rw [Prod.Lex.lt_iff] at hij ⊢
  rcases hij with hfirst | ⟨hfirst, hsecond⟩
  · exact Or.inl (hrow hfirst)
  · have heq : v = v' := Option.some.inj (by rw [hfirst] at hv; exact hv.symm.trans hv')
    subst v'
    refine Or.inr ⟨congrArg row hfirst, ?_⟩
    rw [Prod.Lex.lt_iff] at hsecond ⊢
    rcases hsecond with hmiddle | ⟨hmiddle, hlast⟩
    · exact Or.inl (tail_strict v hmiddle)
    · have hpair : selectedPair row v i = selectedPair row v j := by
        simp only [selectedPair, hfirst, hmiddle]
      have heq : w = w' := Option.some.inj (by rw [hpair] at hw; exact hw.symm.trans hw')
      subst w'
      exact Or.inr ⟨congrArg (tail v) hmiddle, tail_strict w hlast⟩

def thinningClique (hclosed : CountablyClosed P) {G : SimpleGraph W2}
    (core : CliqueDecisions P Cube W2 G) (row : W1 → W1) (hrow : StrictMono row) :
    CliqueDecisions (Condition P) Cube W2 G where
  decides p z x := ∃ v : W1, p.stem (row (ofLex z).1) = some v ∧
    ∃ w : W1, p.stem (pairEquiv (selectedPair row v z)) = some w ∧
      core.decides p.base (selectedIndex row v w z) x
  dense := by
    intro p z
    obtain ⟨q, ⟨v, hv⟩, hqp⟩ :=
      Erdos1172Part3IteratedHechlerClosure.coordinate_dense hclosed (row (ofLex z).1) p
    obtain ⟨s, ⟨w, hw⟩, hsq⟩ := Erdos1172Part3IteratedHechlerClosure.coordinate_dense
      hclosed (pairEquiv (selectedPair row v z)) q
    obtain ⟨base, hbase, x, hx⟩ := core.dense s.base (selectedIndex row v w z)
    exact ⟨liftBase s base, (liftBase_le s hbase).trans (hsq.trans hqp), x,
      v, hsq.2.1 _ _ hv, w, hw, hx⟩
  persistent := by
    rintro p q i x hqp ⟨v, hv, w, hw, hx⟩
    exact ⟨v, hqp.2.1 _ _ hv, w, hqp.2.1 _ _ hw, core.persistent (base_le hqp) hx⟩
  unique := by
    rintro p i x y ⟨v, hv, w, hw, hx⟩ ⟨v', hv', w', hw', hy⟩
    have heq : v = v' := Option.some.inj (hv.symm.trans hv')
    subst v'
    have heq : w = w' := Option.some.inj (hw.symm.trans hw')
    subst w'
    exact core.unique hx hy
  ordered := by
    rintro p i j x y hij ⟨v, hv, w, hw, hx⟩ ⟨v', hv', w', hw', hy⟩
    exact core.ordered (selectedIndex_lt hrow hij hv hv' hw hw') hx hy
  adjacent := by
    rintro p i j x y hij ⟨v, hv, w, hw, hx⟩ ⟨v', hv', w', hw', hy⟩
    have hne : selectedIndex row v w i ≠ selectedIndex row v' w' j := by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact (selectedIndex_lt hrow hlt hv hv' hw hw').ne
      · exact (selectedIndex_lt hrow hgt hv' hv hw' hw).ne.symm
    exact core.adjacent hne hx hy

theorem thinningClique_origin (hclosed : CountablyClosed P) {G : SimpleGraph W2}
    (core : CliqueDecisions P Cube W2 G) (row : W1 → W1) (hrow : StrictMono row) :
    ∀ p z x, (thinningClique hclosed core row hrow).decides p z x →
      ∃ old : Cube, core.decides p.base old x := by
  rintro p z x ⟨v, _, w, _, hx⟩
  exact ⟨selectedIndex row v w z, hx⟩

end Erdos1172Part3NamedCubeThinning
