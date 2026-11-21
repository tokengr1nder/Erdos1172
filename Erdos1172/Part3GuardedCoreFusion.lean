/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedNeighborhoodStep

@[expose] public section

/-!
# A single guarded core across all conditions

The positive branch uses actual source membership and controlled
extension. The negative branch uses one fixed ground fallback clique.
Only conditions deciding the guard enter point decisions. This permits
one name to satisfy the source and convergence laws at every condition
where the guard holds, not merely in one chosen starting cone.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3GuardedCoreFusion

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal (smallName)
open Erdos1172Part3NamedNeighborhoodStep (exists_extension_controlled)
open Erdos1172Part3CountableRankClosure (Local)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3ConstrainedDecisionFusion (ControlledExtension exists_controlled_clique)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {P I : Type} [Preorder P] [LinearOrder I]
variable {G H : SimpleGraph W2} {r : Code P I G ↪ W2}
variable {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2} {a : W2}

def GuardedPoint (T : RegularName P Unit) (U : RegularName P W2)
    (f : W1 → W2) (a : W2) (G : SimpleGraph W2) (p : P) (x : W2) : Prop :=
  x < a ∧ G.Adj x a ∧
    ((T.holds p () ∧ U.holds p x) ∨ ((neg T).holds p () ∧ x ∈ Set.range f))

theorem guardedPoint_persistent (T : RegularName P Unit) (U : RegularName P W2)
    (f : W1 → W2) (a : W2) (G : SimpleGraph W2) {p q : P} {x : W2}
    (hqp : q ≤ p) (h : GuardedPoint T U f a G p x) : GuardedPoint T U f a G q x := by
  refine ⟨h.1, h.2.1, ?_⟩
  rcases h.2.2 with h | h
  · exact Or.inl ⟨T.persistent hqp h.1, U.persistent hqp h.2⟩
  · exact Or.inr ⟨(neg T).persistent hqp h.1, h.2⟩

def GuardedControl (H : SimpleGraph W2) (T : RegularName P Unit)
    (index : Local r a ↪ W1) (i : W1) (p : P) (x : W2) : Prop :=
  ∀ c : Local r a, index c < i → ∀ q : P, q ≤ p → T.holds q () →
    (eval G H c.val).holds q a → (eval G H c.val).holds q x

theorem guardedControl_persistent {T : RegularName P Unit} {index : Local r a ↪ W1}
    {i : W1} {p q : P} {x : W2} (hqp : q ≤ p)
    (h : GuardedControl H T index i p x) : GuardedControl H T index i q x :=
  fun c hc s hsq => h c hc s (hsq.trans hqp)

theorem exists_guarded_core_with_fallback (hclosed : CountablyClosed P)
    (ha : GoodCut r σ H source a) (T : RegularName P Unit) (U : RegularName P W2)
    (index : Local r a ↪ W1)
    (hpositive : ∀ p : P, T.holds p () → (neg (smallName r H a)).holds p U)
    (hcolor : ∀ p : P, T.holds p () → ∀ x, U.holds p x → G.Adj x a)
    (f : W1 → W2) (hf : StrictMono f) (hclique : G.IsClique (Set.range f))
    (hgeometry : ∀ i : W1, f i < a ∧ G.Adj (f i) a) :
    ∃ core : CliqueDecisions P W1 W2 G, ∀ p i x, core.decides p i x →
      GuardedPoint T U f a G p x ∧ GuardedControl H T index i p x := by
  classical
  let R := GuardedPoint T U f a G
  let K := GuardedControl H T index
  have hR : ∀ {p q : P} {x}, q ≤ p → R p x → R q x :=
    fun hqp h => guardedPoint_persistent T U f a G hqp h
  have hK : ∀ {i} {p q : P} {x}, q ≤ p → K i p x → K i q x :=
    fun hqp h => guardedControl_persistent hqp h
  have hextend : ControlledExtension G R K := by
    intro i p selected hcount hselected
    obtain ⟨q, hqp, hT | hnT⟩ := exists_deciding_refinement T p ()
    · obtain ⟨s, hsq, y, hya, hUy, hcontrol, hcross⟩ := exists_extension_controlled
        hclosed ha true U index i q (hpositive q hT) selected hcount
        (fun x hx => (hselected x hx).1) (fun x hx => (hselected x hx).2.1)
      have hTs : T.holds s () := T.persistent hsq hT
      refine ⟨s, hsq.trans hqp, y, ⟨hya, hcolor s hTs y hUy, Or.inl ⟨hTs, hUy⟩⟩, ?_, hcross⟩
      intro c hc t hts hTt hct
      exact hcontrol c hc t hts hct
    · have hselectedFallback : ∀ x ∈ selected, x ∈ Set.range f := by
        intro x hx
        have h := hR hqp (hselected x hx)
        rcases h.2.2 with h | h
        · exact (hnT q le_rfl h.1).elim
        · exact h.2
      let indexOf (x : selected) : W1 := (hselectedFallback x.val x.property).choose
      have hindexOf (x : selected) : f (indexOf x) = x.val :=
        (hselectedFallback x.val x.property).choose_spec
      have hindexCount : (Set.range indexOf).Countable :=
        Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.mk_range_le.trans
          (Cardinal.le_aleph0_iff_set_countable.mpr hcount))
      obtain ⟨bound, hbound⟩ := exists_bound_of_countable (Set.range indexOf) hindexCount
      refine ⟨q, hqp, f bound,
        ⟨(hgeometry bound).1, (hgeometry bound).2, Or.inr ⟨hnT, ⟨bound, rfl⟩⟩⟩, ?_, ?_⟩
      · intro c hc t htq hTt hct
        exact (hnT t htq hTt).elim
      · intro x hx
        have hlt : x < f bound := by
          calc
            x = f (indexOf ⟨x, hx⟩) := (hindexOf ⟨x, hx⟩).symm
            _ < f bound := hf (hbound _ ⟨⟨x, hx⟩, rfl⟩)
        exact ⟨hlt, hclique (hselectedFallback x hx) ⟨bound, rfl⟩ hlt.ne⟩
  exact exists_controlled_clique hclosed G R K
    (fun hqp h => hR hqp h) (fun hqp h => hK hqp h) hextend

end Erdos1172Part3GuardedCoreFusion
