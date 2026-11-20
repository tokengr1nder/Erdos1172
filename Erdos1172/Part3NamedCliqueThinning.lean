/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedStationaryTail
public import Erdos1172.Part3StationarySquareDecisions

@[expose] public section

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedCliqueThinning

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3IteratedHechlerOrder (Condition liftBase liftBase_le base_le)
open Erdos1172Part3StationarySquareDecisions (Square tail tail_strict)
open Erdos1172Part3StationaryDecisions (Persistent StationaryAt)

/-- A clique and a stationarily possible common future over any earlier
decision order. This does not assert a fixed ground stationary future. -/
structure StationaryCliqueDecisions (P I : Type) [Preorder P] [LinearOrder I]
    (G : SimpleGraph W2) where
  start : P
  clique : CliqueDecisions P I W2 G
  future : P → W2 → Prop
  persistent : Persistent future
  stationary : StationaryAt future start
  cross : ∀ p a, future p a → ∀ i x, clique.decides p i x → x < a ∧ G.Adj x a

variable {P : Type} [Preorder P]

noncomputable def selectedIndex (row : W1 → W1) (v : W1) (z : Square) : Square :=
  toLex (row (ofLex z).1, tail v (ofLex z).2)

theorem selectedIndex_lt {row : W1 → W1} (hrow : StrictMono row)
    {p : Condition P} {i j : Square} {v w : W1} (hij : i < j)
    (hv : p.stem (row (ofLex i).1) = some v) (hw : p.stem (row (ofLex j).1) = some w) :
    selectedIndex row v i < selectedIndex row w j := by
  rw [Prod.Lex.lt_iff] at hij ⊢
  rcases hij with hfirst | ⟨hfirst, hsecond⟩
  · exact Or.inl (hrow hfirst)
  · have heq : v = w := Option.some.inj (by rw [hfirst] at hv; exact hv.symm.trans hw)
    subst w
    exact Or.inr ⟨congrArg row hfirst, tail_strict v hsecond⟩

/-- New stem decisions select tails inside an earlier square name.
Both the stem value and the earlier clique point are decided densely. -/
def thinningClique (hclosed : CountablyClosed P) {G : SimpleGraph W2}
    (core : CliqueDecisions P Square W2 G) (row : W1 → W1) (hrow : StrictMono row) :
    CliqueDecisions (Condition P) Square W2 G where
  decides p i x := ∃ v : W1, p.stem (row (ofLex i).1) = some v ∧
    core.decides p.base (selectedIndex row v i) x
  dense := by
    intro p i
    obtain ⟨q, ⟨v, hv⟩, hqp⟩ :=
      Erdos1172Part3IteratedHechlerClosure.coordinate_dense hclosed (row (ofLex i).1) p
    obtain ⟨base, hbase, x, hx⟩ := core.dense q.base (selectedIndex row v i)
    exact ⟨liftBase q base, (liftBase_le q hbase).trans hqp, x, v, hv, hx⟩
  persistent := by
    rintro p q i x hqp ⟨v, hv, hx⟩
    exact ⟨v, hqp.2.1 _ _ hv, core.persistent (base_le hqp) hx⟩
  unique := by
    rintro p i x y ⟨v, hv, hx⟩ ⟨w, hw, hy⟩
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    subst w
    exact core.unique hx hy
  ordered := by
    rintro p i j x y hij ⟨v, hv, hx⟩ ⟨w, hw, hy⟩
    exact core.ordered (selectedIndex_lt hrow hij hv hw) hx hy
  adjacent := by
    rintro p i j x y hij ⟨v, hv, hx⟩ ⟨w, hw, hy⟩
    have hne : selectedIndex row v i ≠ selectedIndex row w j := by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact (selectedIndex_lt hrow hlt hv hw).ne
      · exact (selectedIndex_lt hrow hgt hw hv).ne.symm
    exact core.adjacent hne hx hy

end Erdos1172Part3NamedCliqueThinning
