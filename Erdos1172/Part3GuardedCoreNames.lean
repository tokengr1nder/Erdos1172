/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3GuardedCoreFusion
public import Erdos1172.Part3NamedColorCore
public import Erdos1172.Part3NamedConvergentCore

@[expose] public section

/-!
# Uniform guarded convergent core names

The fallback and the countable extension law are constructed. The output
is one nice clique name whose source membership and convergence hold at
every condition satisfying the guard. No local rank for the whole output
name is asserted.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3GuardedCoreNames

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal (smallName)
open Erdos1172Part3GuardedCoreFusion (exists_guarded_core_with_fallback)
open Erdos1172Part3NamedColorCore (exists_cone_color_core)
open Erdos1172Part3NamedConvergentCore (ConvergesBelow)
open Erdos1172Part3CountableRankClosure (Local mk_local_le)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)

variable {P I : Type} [Preorder P] [LinearOrder I]
variable {G H : SimpleGraph W2} {r : Code P I G ↪ W2}
variable {σ : NiceCliqueName P I W2 G ↪ W2} {source : RegularName P W2} {a : W2}

def GuardedConverges (r : Code P I G ↪ W2) (H : SimpleGraph W2) (a : W2)
    (T : RegularName P Unit) (core : CliqueDecisions P W1 W2 G) : Prop :=
  ∀ c : Code P I G, r c < a → ∃ bound : W1,
    ∀ p : P, T.holds p () → (eval G H c).holds p a →
      ∀ i : W1, bound < i → ∀ x : W2, core.decides p i x → (eval G H c).holds p x

theorem guardedConverges_below {T : RegularName P Unit} {core : CliqueDecisions P W1 W2 G}
    (hconv : GuardedConverges r H a T core) (p0 : P) (hT : T.holds p0 ()) :
    ConvergesBelow r H a p0 core := by
  intro c hc
  obtain ⟨bound, hbound⟩ := hconv c hc
  exact ⟨bound, fun p hpp0 hca i hi x hx =>
    hbound p (T.persistent hpp0 hT) hca i hi x hx⟩

theorem exists_guarded_name (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (ha : GoodCut r σ H source a) (T : RegularName P Unit) (U : RegularName P W2)
    (hpossible : ∃ p : P, T.holds p ())
    (hpositive : ∀ p : P, T.holds p () → (neg (smallName r H a)).holds p U)
    (hcolor : ∀ p : P, T.holds p () → ∀ x, U.holds p x → G.Adj x a) :
    ∃ N : NiceCliqueName P W1 W2 G,
      (∀ p i x, N.toClique.decides p i x → x < a ∧ G.Adj x a) ∧
      (∀ p : P, T.holds p () → ∀ i x, N.toClique.decides p i x → U.holds p x) ∧
      GuardedConverges r H a T N.toClique := by
  obtain ⟨p0, hT0⟩ := hpossible
  obtain ⟨localCore, hlocal⟩ := exists_cone_color_core hclosed ha true U p0
    (hpositive p0 hT0) (fun p hpp0 x hx => hcolor p (T.persistent hpp0 hT0) x hx)
  obtain ⟨f, hf, hclique, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_clique_map_with_origins localCore
      (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed p0)
      ⟨p0, (show p0 ≤ p0 from le_rfl)⟩
      (by simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl])
  have hgeometry (i : W1) : f i < a ∧ G.Adj (f i) a := by
    obtain ⟨q, _, hq⟩ := horigin i
    exact (hlocal q i (f i) hq).2
  obtain ⟨index⟩ : Nonempty (Local r a ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_local_le r a)
  obtain ⟨core, hcore⟩ := exists_guarded_core_with_fallback hclosed ha T U index
    hpositive hcolor f hf hclique hgeometry
  obtain ⟨N, hN⟩ := exists_nice_clique_name hcc core
  refine ⟨N, ?_, ?_, ?_⟩
  · intro p i x hx
    have h := (hcore p i x (hN p i x hx)).1
    exact ⟨h.1, h.2.1⟩
  · intro p hT i x hx
    rcases (hcore p i x (hN p i x hx)).1.2.2 with h | h
    · exact h.2
    · exact (h.1 p le_rfl hT).elim
  · intro c hc
    refine ⟨index ⟨c, hc⟩, ?_⟩
    intro p hT hca i hi x hx
    exact (hcore p i x (hN p i x hx)).2 ⟨c, hc⟩ hi p le_rfl hT hca

end Erdos1172Part3GuardedCoreNames
