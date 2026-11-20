/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedBlockFlattening

@[expose] public section

/-!
# Red square names in condition-dependent sources

The outer block sequence and all its countable extension premises are
constructed. The flattened square retains actual source membership and
red adjacency to its cut. Its nice-name extension has no unbounded rank
claim below that same cut and no stationary future conclusion here.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedSourceSquare

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularBlockEnvironment (GoodBlockCut exists_club_goodBlockCut_of_gch)
open Erdos1172Part3NamedBlockFlattening (joinedCores onConeCore joinedCores_onCone flatten)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3CliqueNameCoding (mk_square_le)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G H : SimpleGraph W2}
variable {r : Code P W1 G ↪ W2} {σ : NiceCliqueName P W1 W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

theorem exists_cone_source_square (hclosed : CountablyClosed P)
    (ha : GoodBlockCut r σ H source a) (p0 : P) (hp0 : source.holds p0 a) :
    ∃ core : CliqueDecisions (Set.Iic p0) Square W2 G,
      ∀ p z x, core.decides p z x → source.holds p.val x ∧ x < a ∧ G.Adj x a := by
  obtain ⟨F, hF, hcross⟩ := Erdos1172Part3NamedBlockSequence.exists_block_sequence hclosed ha p0 hp0
  let blocks (N : NiceCliqueName P W1 W2 G) := onConeCore p0 N.toClique
  have hj : ∀ p i j N M, i < j → F.decides p i N → F.decides p j M →
      (joinedCores (blocks N) (blocks M)).holds p () :=
    fun p i j N M hij hN hM => joinedCores_onCone p0 N.toClique M.toClique p
      (hcross p i j N M hij hN hM)
  refine ⟨flatten blocks F hj, ?_⟩
  rintro p z x ⟨N, hN, hx⟩
  have h := hF p (ofLex z).1 N hN
  exact ⟨h.2.2.1 p.val le_rfl (ofLex z).2 x hx,
    h.2.2.2 p.val le_rfl (ofLex z).2 x hx⟩

theorem exists_nice_source_square (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (ha : GoodBlockCut r σ H source a) (p0 : P) (hp0 : source.holds p0 a) :
    ∃ N : NiceCliqueName P Square W2 G,
      (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
      (∀ p : P, p ≤ p0 → ∀ z x, N.toClique.decides p z x → source.holds p x) := by
  obtain ⟨core, hcore⟩ := exists_cone_source_square hclosed ha p0 hp0
  obtain ⟨global, hbelow, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_global_clique_from_cone hclosed p0 core mk_square_le
  obtain ⟨N, hN⟩ := exists_nice_clique_name hcc global
  refine ⟨N, ?_, ?_⟩
  · intro p z x hx
    obtain ⟨q, hq⟩ := horigin p z x (hN p z x hx)
    exact (hcore q z x hq).2
  · intro p hpp0 z x hx
    exact (hcore ⟨p, hpp0⟩ z x ((hbelow p hpp0 z x).mp (hN p z x hx))).1

theorem exists_club_named_source_squares (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName P W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ∀ p0 : P, source.holds p0 a →
      ∃ N : NiceCliqueName P Square W2 G,
        (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
        (∀ p : P, p ≤ p0 → ∀ z x, N.toClique.decides p z x → source.holds p x) := by
  obtain ⟨r, σ, club, hclub, hcuts⟩ := exists_club_goodBlockCut_of_gch hGCH hP hclosed center
    G H hcompl hred hblue source hsup
  exact ⟨club, hclub, fun a ha p0 hp0 =>
    exists_nice_source_square hclosed center.omegaTwoCC (hcuts a ha (hsup p0 a hp0)) p0 hp0⟩

end Erdos1172Part3NamedSourceSquare
