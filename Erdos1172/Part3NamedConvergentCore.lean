/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedNeighborhoodStep
public import Erdos1172.Part3CliqueConeExtension

@[expose] public section

/-!
# Convergent core names

Every local neighborhood has a ground cutoff after which its truth at
the cut transfers to every actual point decision. The cutoff is uniform
over conditions below the start. The whole produced name need not be
locally coded, and its possible-value cover is not asserted to be a clique.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedConvergentCore

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3NamedPositiveExtension (colorGraph)
open Erdos1172Part3NamedNeighborhoodStep
open Erdos1172Part3ConstrainedDecisionFusion (ControlledExtension exists_controlled_clique)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)
open Erdos1172Part3CountableRankClosure (Local mk_local_le)

variable {P I : Type} [Preorder P] [LinearOrder I]
variable {G H : SimpleGraph W2} {r : Code P I G ↪ W2}
variable {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2} {a : W2}

def ConvergesBelow {K : SimpleGraph W2} (r : Code P I G ↪ W2) (H : SimpleGraph W2)
    (a : W2) (p0 : P) (core : CliqueDecisions P W1 W2 K) : Prop :=
  ∀ c : Code P I G, r c < a → ∃ bound : W1,
    ∀ p : P, p ≤ p0 → (eval G H c).holds p a →
      ∀ i : W1, bound < i → ∀ x : W2, core.decides p i x → (eval G H c).holds p x

theorem exists_controlled_cone_core (hclosed : CountablyClosed P)
    (ha : GoodCut r σ H source a) (b : Bool) (U : RegularName P W2)
    (index : Local r a ↪ W1) (p0 : P)
    (hpositive : (neg (smallName r H a)).holds p0 U)
    (hcolor : ∀ p : P, p ≤ p0 → ∀ x, U.holds p x → (colorGraph G H b).Adj x a) :
    ∃ core : CliqueDecisions (Set.Iic p0) W1 W2 (colorGraph G H b),
      ∀ p i x, core.decides p i x →
        (U.holds p.val x ∧ x < a ∧ (colorGraph G H b).Adj x a) ∧ Control H index i p.val x := by
  let R (p : Set.Iic p0) (x : W2) : Prop :=
    U.holds p.val x ∧ x < a ∧ (colorGraph G H b).Adj x a
  let K (i : W1) (p : Set.Iic p0) (x : W2) : Prop := Control H index i p.val x
  have hR : ∀ {p q : Set.Iic p0} {x}, q ≤ p → R p x → R q x :=
    fun hqp h => ⟨U.persistent hqp h.1, h.2⟩
  have hK : ∀ {i} {p q : Set.Iic p0} {x}, q ≤ p → K i p x → K i q x :=
    fun hqp h => control_persistent hqp h
  have hextend : ControlledExtension (colorGraph G H b) R K := by
    intro i p selected hcount hselected
    obtain ⟨q, hqp, y, hya, hqy, hcontrol, hcross⟩ := exists_extension_controlled hclosed ha b U
      index i p.val ((neg (smallName r H a)).persistent p.property hpositive)
        selected hcount (fun x hx => (hselected x hx).2.1)
          (fun x hx => (hselected x hx).2.2)
    exact ⟨⟨q, hqp.trans p.property⟩, hqp, y,
      ⟨hqy, hya, hcolor q (hqp.trans p.property) y hqy⟩, hcontrol, hcross⟩
  exact exists_controlled_clique
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed p0)
    (colorGraph G H b) R K (fun hqp h => hR hqp h) (fun hqp h => hK hqp h) hextend

theorem exists_convergent_color_name (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (ha : GoodCut r σ H source a) (b : Bool) (U : RegularName P W2)
    (p0 : P) (hpositive : (neg (smallName r H a)).holds p0 U)
    (hcolor : ∀ p : P, p ≤ p0 → ∀ x, U.holds p x → (colorGraph G H b).Adj x a) :
    ∃ N : NiceCliqueName P W1 W2 (colorGraph G H b),
      (∀ p i x, N.toClique.decides p i x → x < a ∧ (colorGraph G H b).Adj x a ∧
        ∃ q : P, q ≤ p0 ∧ U.holds q x) ∧
      (∀ p : P, p ≤ p0 → ∀ i x, N.toClique.decides p i x → U.holds p x) ∧
      ConvergesBelow r H a p0 N.toClique := by
  obtain ⟨index⟩ : Nonempty (Local r a ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_local_le r a)
  obtain ⟨core, hcore⟩ := exists_controlled_cone_core hclosed ha b U index p0 hpositive hcolor
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed p0 core
      (by simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl])
  obtain ⟨N, hN⟩ := exists_nice_clique_name hcc global
  refine ⟨N, ?_, ?_, ?_⟩
  · intro p i x hx
    obtain ⟨q, hq⟩ := horigin p i x (hN p i x hx)
    exact ⟨(hcore q i x hq).1.2.1, (hcore q i x hq).1.2.2,
      q.val, q.property, (hcore q i x hq).1.1⟩
  · intro p hpp0 i x hx
    exact (hcore ⟨p, hpp0⟩ i x ((hbelow p hpp0 i x).mp (hN p i x hx))).1.1
  · intro c hc
    refine ⟨index ⟨c, hc⟩, ?_⟩
    intro p hpp0 hca i hi x hx
    have h := (hcore ⟨p, hpp0⟩ i x ((hbelow p hpp0 i x).mp (hN p i x hx))).2
    exact h ⟨c, hc⟩ hi p le_rfl hca

end Erdos1172Part3NamedConvergentCore
