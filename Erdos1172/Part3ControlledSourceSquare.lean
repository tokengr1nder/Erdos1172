/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedSourceSquare
public import Erdos1172.Part3ControlledBlockExtension

@[expose] public section

/-!
# Convergent red square names in regular sources

Each outer row follows all earlier local neighborhood requirements which
are true at the cut. Every sufficiently late whole row therefore follows
each fixed local neighborhood, uniformly under all conditions below the
starting point.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3ControlledSourceSquare

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularBlockEnvironment (GoodBlockCut exists_club_goodBlockCut_of_gch)
open Erdos1172Part3CountableBlockExtension (BlockAt blockAt_persistent joinedName)
open Erdos1172Part3ControlledBlockExtension
open Erdos1172Part3NamedBlockFlattening (joinedCores onConeCore joinedCores_onCone flatten)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3CliqueNameCoding (mk_square_le)
open Erdos1172Part3CountableRankClosure (Local mk_local_le)
open Erdos1172Part3RelationalDecisionFusion (RelationalExtension exists_relational_decisions)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G H : SimpleGraph W2}
variable {r : Code P W1 G ↪ W2} {σ : NiceCliqueName P W1 W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

def SquareConvergesBelow (r : Code P W1 G ↪ W2) (H : SimpleGraph W2) (a : W2)
    (p0 : P) (core : CliqueDecisions P Square W2 G) : Prop :=
  ∀ c : Code P W1 G, r c < a → ∃ bound : W1,
    ∀ p : P, p ≤ p0 → (eval G H c).holds p a →
      ∀ z : Square, bound < (ofLex z).1 → ∀ x : W2,
        core.decides p z x → (eval G H c).holds p x

theorem exists_controlled_block_sequence (hclosed : CountablyClosed P)
    (ha : GoodBlockCut r σ H source a) (index : Local r a ↪ W1)
    (p0 : P) (hp0 : source.holds p0 a) :
    ∃ F : FunctionDecisions (Set.Iic p0) W1 (NiceCliqueName P W1 W2 G),
      (∀ p i N, F.decides p i N → BlockAt σ source a p.val N ∧ BlockControl H index i p.val N) ∧
      ∀ p i j N M, i < j → F.decides p i N → F.decides p j M →
        (joinedName N M).holds p.val () := by
  let R (p : Set.Iic p0) (N : NiceCliqueName P W1 W2 G) := BlockAt σ source a p.val N
  let K (i : W1) (p : Set.Iic p0) (N : NiceCliqueName P W1 W2 G) := BlockControl H index i p.val N
  let J (p : Set.Iic p0) (N M : NiceCliqueName P W1 W2 G) := (joinedName N M).holds p.val ()
  have hextend : RelationalExtension R K J := by
    intro i p selected hcount hselected
    obtain ⟨q, hqp, M, hM, hjoined, hcontrol⟩ := exists_controlled_block_extension hclosed ha index i
      p.val (source.persistent p.property hp0) selected hcount hselected
    exact ⟨⟨q, hqp.trans p.property⟩, hqp, M, hM, hcontrol, hjoined⟩
  exact exists_relational_decisions
    (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed p0) R K J
    (fun hqp h => blockAt_persistent hqp h) (fun hqp h => blockControl_persistent hqp h)
    (fun {p q N M} hqp h => (joinedName N M).persistent hqp h) hextend

theorem exists_cone_convergent_square (hclosed : CountablyClosed P)
    (ha : GoodBlockCut r σ H source a) (p0 : P) (hp0 : source.holds p0 a) :
    ∃ core : CliqueDecisions (Set.Iic p0) Square W2 G,
      (∀ p z x, core.decides p z x → source.holds p.val x ∧ x < a ∧ G.Adj x a) ∧
      ∀ c : Code P W1 G, r c < a → ∃ bound : W1,
        ∀ p : Set.Iic p0, (eval G H c).holds p.val a →
          ∀ z : Square, bound < (ofLex z).1 → ∀ x : W2,
            core.decides p z x → (eval G H c).holds p.val x := by
  obtain ⟨index⟩ : Nonempty (Local r a ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_local_le r a)
  obtain ⟨F, hF, hcross⟩ := exists_controlled_block_sequence hclosed ha index p0 hp0
  let blocks (N : NiceCliqueName P W1 W2 G) := onConeCore p0 N.toClique
  have hj : ∀ p i j N M, i < j → F.decides p i N → F.decides p j M →
      (joinedCores (blocks N) (blocks M)).holds p () :=
    fun p i j N M hij hN hM => joinedCores_onCone p0 N.toClique M.toClique p
      (hcross p i j N M hij hN hM)
  refine ⟨flatten blocks F hj, ?_, ?_⟩
  · rintro p z x ⟨N, hN, hx⟩
    have h := (hF p (ofLex z).1 N hN).1
    exact ⟨h.2.2.1 p.val le_rfl (ofLex z).2 x hx,
      h.2.2.2 p.val le_rfl (ofLex z).2 x hx⟩
  · intro c hc
    refine ⟨index ⟨c, hc⟩, ?_⟩
    rintro p hca z hz x ⟨N, hN, hx⟩
    exact (hF p (ofLex z).1 N hN).2 ⟨c, hc⟩ hz p.val le_rfl hca
      p.val le_rfl (ofLex z).2 x hx

theorem exists_nice_convergent_square (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (ha : GoodBlockCut r σ H source a) (p0 : P) (hp0 : source.holds p0 a) :
    ∃ N : NiceCliqueName P Square W2 G,
      (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
      (∀ p : P, p ≤ p0 → ∀ z x, N.toClique.decides p z x → source.holds p x) ∧
      SquareConvergesBelow r H a p0 N.toClique := by
  obtain ⟨core, hcore, hconv⟩ := exists_cone_convergent_square hclosed ha p0 hp0
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed p0 core mk_square_le
  obtain ⟨N, hN⟩ := exists_nice_clique_name hcc global
  refine ⟨N, ?_, ?_, ?_⟩
  · intro p z x hx
    obtain ⟨q, hq⟩ := horigin p z x (hN p z x hx)
    exact (hcore q z x hq).2
  · intro p hpp0 z x hx
    exact (hcore ⟨p, hpp0⟩ z x ((hbelow p hpp0 z x).mp (hN p z x hx))).1
  · intro c hc
    obtain ⟨bound, hbound⟩ := hconv c hc
    refine ⟨bound, ?_⟩
    intro p hpp0 hca z hz x hx
    exact hbound ⟨p, hpp0⟩ hca z hz x ((hbelow p hpp0 z x).mp (hN p z x hx))

theorem exists_club_convergent_source_squares (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName P W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a) :
    ∃ r : Code P W1 G ↪ W2, ∃ club : Set W2, IsClub club ∧
      ∀ a ∈ club, ∀ p0 : P, source.holds p0 a →
        ∃ N : NiceCliqueName P Square W2 G,
          (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
          (∀ p : P, p ≤ p0 → ∀ z x, N.toClique.decides p z x → source.holds p x) ∧
          SquareConvergesBelow r H a p0 N.toClique := by
  obtain ⟨r, σ, club, hclub, hcuts⟩ := exists_club_goodBlockCut_of_gch hGCH hP hclosed center
    G H hcompl hred hblue source hsup
  exact ⟨r, club, hclub, fun a ha p0 hp0 =>
    exists_nice_convergent_square hclosed center.omegaTwoCC (hcuts a ha (hsup p0 a hp0)) p0 hp0⟩

end Erdos1172Part3ControlledSourceSquare
