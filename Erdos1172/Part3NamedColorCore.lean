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

theorem exists_named_color_core (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (ha : GoodCut r σ H source a) (b : Bool) (U : RegularName P W2)
    (p0 : P) (hpositive : (neg (smallName r H a)).holds p0 U)
    (hcolor : ∀ p : P, p ≤ p0 → ∀ x, U.holds p x → (colorGraph G H b).Adj x a) :
    ∃ N : NiceCliqueName P W1 W2 (colorGraph G H b),
      (∀ p i x, N.toClique.decides p i x → x < a ∧ (colorGraph G H b).Adj x a ∧
        ∃ q : P, q ≤ p0 ∧ U.holds q x) ∧
      (∀ p : P, p ≤ p0 → ∀ i x, N.toClique.decides p i x → U.holds p x) := by
  obtain ⟨core, hcore⟩ := exists_cone_color_core hclosed ha b U p0 hpositive hcolor
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed p0 core
      (by simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl])
  obtain ⟨N, hN⟩ := exists_nice_clique_name hcc global
  refine ⟨N, ?_, ?_⟩
  · intro p i x hx
    obtain ⟨q, hq⟩ := horigin p i x (hN p i x hx)
    exact ⟨(hcore q i x hq).2.1, (hcore q i x hq).2.2,
      q.val, q.property, (hcore q i x hq).1⟩
  · intro p hpp0 i x hx
    exact (hcore ⟨p, hpp0⟩ i x ((hbelow p hpp0 i x).mp (hN p i x hx))).1

noncomputable def colorFiber (G H : SimpleGraph W2) (U : RegularName P W2)
    (a : W2) (b : Bool) : RegularName P W2 :=
  meet U (ground {x | x < a ∧ (colorGraph G H b).Adj x a})

/-- The positive color is selected from the actual two-color partition,
not supplied as an additional geometric premise. -/
theorem exists_positive_color_fiber (hclosed : CountablyClosed P)
    (ha : GoodCut r σ H source a) (hcompl : IsCompl G H)
    (U : RegularName P W2) (p0 : P)
    (hpositive : (neg (smallName r H a)).holds p0 U) :
    ∃ b : Bool, ∃ q : P, q ≤ p0 ∧
      (neg (smallName r H a)).holds q (colorFiber G H U a b) := by
  classical
  let red := colorFiber G H U a true
  let blue := colorFiber G H U a false
  by_cases hred : (smallName r H a).holds p0 red
  · have hblue : ¬(smallName r H a).holds p0 blue := by
      intro hblue
      let family (n : ℕ) : RegularName P W2 := if n = 0 then red else blue
      have hfamily : (smallName r H a).holds p0 (join family) :=
        smallName_countable_join hclosed ha p0 family (by
          intro n
          dsimp only [family]
          split_ifs <;> assumption)
      apply hpositive p0 le_rfl
      apply smallName_mono_set (V := join family) (p := p0) (U := U) ?_ hfamily
      intro x hx p hpp0 hp
      by_cases hG : G.Adj x a
      · exact join_of_holds family 0 ⟨hp, hx, hG⟩
      · have hH : H.Adj x a := by
          rw [← hcompl.compl_eq, SimpleGraph.compl_adj]
          exact ⟨hx.ne, hG⟩
        exact join_of_holds family 1 ⟨hp, hx, hH⟩
    obtain ⟨q, hqp0, hq⟩ := (not_holds_iff_exists_neg (smallName r H a) p0 blue).mp hblue
    exact ⟨false, q, hqp0, hq⟩
  · obtain ⟨q, hqp0, hq⟩ := (not_holds_iff_exists_neg (smallName r H a) p0 red).mp hred
    exact ⟨true, q, hqp0, hq⟩

/-- Source truth at the cut yields a homogeneous omegaOne core name in
one color after strengthening. The color remains an explicit alternative. -/
theorem exists_named_homogeneous_core (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (ha : GoodCut r σ H source a) (hcompl : IsCompl G H)
    (p0 : P) (hp0 : source.holds p0 a) :
    ∃ b : Bool, ∃ q : P, q ≤ p0 ∧
      ∃ N : NiceCliqueName P W1 W2 (colorGraph G H b),
        (∀ p i x, N.toClique.decides p i x → x < a ∧ (colorGraph G H b).Adj x a) ∧
        (∀ p : P, p ≤ q → ∀ i x, N.toClique.decides p i x → source.holds p x) := by
  obtain ⟨b, q, hqp0, hq⟩ := exists_positive_color_fiber hclosed ha hcompl source p0
    (source_not_small ha p0 hp0)
  obtain ⟨N, hN, hsource⟩ := exists_named_color_core hclosed hcc ha b
    (colorFiber G H source a b) q hq (fun p hp x hx => hx.2.2)
  exact ⟨b, q, hqp0, N, fun p i x hx => ⟨(hN p i x hx).1, (hN p i x hx).2.1⟩,
    fun p hp i x hx => (hsource p hp i x hx).1⟩

end Erdos1172Part3NamedColorCore
