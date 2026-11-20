/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableDecisionFusion
public import Erdos1172.Part3NamedPositiveExtension
public import Erdos1172.Part3CliqueConeExtension

@[expose] public section

/-!
# Constructed clique names in positive named color fibers

The local smallness theorem supplies the countable extension premise;
the coherent decision recursion constructs the core. Extending from a
cone preserves actual source membership below its starting condition.
All possible values remain below the cut in its selected color fiber.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedColorCore

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3NamedPositiveExtension
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)

variable {P I : Type} [Preorder P] [LinearOrder I]
variable {G H : SimpleGraph W2} {r : Code P I G ↪ W2}
variable {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2} {a : W2}

theorem exists_cone_color_core (hclosed : CountablyClosed P)
    (ha : GoodCut r σ H source a) (b : Bool) (U : RegularName P W2)
    (p0 : P) (hpositive : (neg (smallName r H a)).holds p0 U)
    (hcolor : ∀ p : P, p ≤ p0 → ∀ x, U.holds p x → (colorGraph G H b).Adj x a) :
    ∃ core : CliqueDecisions (Set.Iic p0) W1 W2 (colorGraph G H b),
      ∀ p i x, core.decides p i x → U.holds p.val x ∧ x < a ∧ (colorGraph G H b).Adj x a := by
  let R (p : Set.Iic p0) (x : W2) : Prop :=
    U.holds p.val x ∧ x < a ∧ (colorGraph G H b).Adj x a
  have hR : ∀ {p q : Set.Iic p0} {x}, q ≤ p → R p x → R q x :=
    fun hqp h => ⟨U.persistent hqp h.1, h.2⟩
  have hextend : Erdos1172Part3CountableDecisionFusion.CountableExtension
      (colorGraph G H b) R := by
    intro p selected hcount hselected
    obtain ⟨q, hqp, y, hya, hqy, hcross⟩ := exists_actual_extension hclosed ha b U
      p.val (hpositive p.val p.property) selected hcount
      (fun x hx => (hselected x hx).2.1) (fun x hx => (hselected x hx).2.2)
    exact ⟨⟨q, hqp.trans p.property⟩, hqp, y,
      ⟨hqy, hya, hcolor q (hqp.trans p.property) y hqy⟩, hcross⟩
  exact Erdos1172Part3CountableDecisionFusion.exists_clique_decisions_of_countable_extension
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed p0)
    (colorGraph G H b) R (fun hqp h => hR hqp h) hextend

noncomputable def colorFiber (G H : SimpleGraph W2) (U : RegularName P W2)
    (a : W2) (b : Bool) : RegularName P W2 :=
  meet U (ground {x | x < a ∧ (colorGraph G H b).Adj x a})

end Erdos1172Part3NamedColorCore
