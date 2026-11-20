/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedSquareTraceIdeal
public import Erdos1172.Part3NamedCliqueMixing

@[expose] public section

/-!
# One guarded square name at each eligible cut

Predense mixing combines the condition-specific convergent squares.
Convergence bounds are obtained densely below an actual source condition;
they are not asserted to be uniform over all antichain branches.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3GuardedSourceSquare

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3RegularBlockEnvironment (GoodBlockCut exists_club_goodBlockCut_of_gch)
open Erdos1172Part3ControlledSourceSquare (SquareConvergesBelow exists_nice_convergent_square)
open Erdos1172Part3NamedSquareTraceIdeal
open Erdos1172Part3NamedTraceIdeal (traceName_of_bound)
open Erdos1172Part3NamedCliqueMixing (mixCore decides_on_branch)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions DenseBelow)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC exists_predense_antichain)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3StationarySquareDecisions (Square)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G H : SimpleGraph W2}
variable {r : Code P W1 G ↪ W2} {σ : NiceCliqueName P W1 W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

def GuardedSquareConverges (r : Code P W1 G ↪ W2) (H : SimpleGraph W2)
    (source : RegularName P W2) (a : W2) (core : CliqueDecisions P Square W2 G) : Prop :=
  ∀ c : Code P W1 G, r c < a → ∀ p : P,
    source.holds p a → (eval G H c).holds p a → ∀ q : P, q ≤ p →
      ∃ s : P, s ≤ q ∧ ∃ bound : W1, ∀ t : P, t ≤ s →
        ∀ z : Square, bound < (ofLex z).1 → ∀ x : W2,
          core.decides t z x → (eval G H c).holds t x

structure SquareData (r : Code P W1 G ↪ W2) (H : SimpleGraph W2)
    (source : RegularName P W2) (a : W2) where
  name : NiceCliqueName P Square W2 G
  geometry : ∀ p z x, name.toClique.decides p z x → x < a ∧ G.Adj x a
  actual_source : ∀ p : P, source.holds p a → ∀ z x,
    name.toClique.decides p z x → source.holds p x
  converges : GuardedSquareConverges r H source a name.toClique

theorem exists_guarded_source_square (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (ha : GoodBlockCut r σ H source a) (hpossible : ∃ p : P, source.holds p a) :
    Nonempty (SquareData r H source a) := by
  classical
  obtain ⟨p0, hp0⟩ := hpossible
  obtain ⟨fallback, hgeometry, _⟩ := exists_nice_convergent_square hclosed hcc ha p0 hp0
  let D : Set P := {p | source.holds p a ∨ (neg source).holds p a}
  have hD : DenseBelow D := by
    intro p
    obtain ⟨q, hqp, hq⟩ := exists_deciding_refinement source p a
    exact ⟨q, hq, hqp⟩
  obtain ⟨A, hAD, hA, hpredense⟩ := exists_predense_antichain D hD
  have hex (b : A) : ∃ N : NiceCliqueName P Square W2 G,
      (∀ p z x, N.toClique.decides p z x → x < a ∧ G.Adj x a) ∧
      (source.holds b.val a →
        (∀ p : P, p ≤ b.val → ∀ z x, N.toClique.decides p z x → source.holds p x) ∧
        SquareConvergesBelow r H a b.val N.toClique) := by
    by_cases hb : source.holds b.val a
    · obtain ⟨N, hg, hs, hc⟩ := exists_nice_convergent_square hclosed hcc ha b.val hb
      exact ⟨N, hg, fun _ => ⟨hs, hc⟩⟩
    · exact ⟨fallback, hgeometry, fun h => (hb h).elim⟩
  choose names hnames using hex
  let blocks (b : A) := (names b).toClique
  let core := mixCore hA hpredense blocks
  have hpositive (b : A) (p : P) (hpb : p ≤ b.val) (hp : source.holds p a) :
      source.holds b.val a :=
    (hAD b.property).resolve_right (fun hn => hn p hpb hp)
  obtain ⟨N, hN⟩ := exists_nice_clique_name hcc core
  refine ⟨⟨N, ?_, ?_, ?_⟩⟩
  · intro p z x hx
    obtain ⟨b, _, hb⟩ := hN p z x hx
    exact (hnames b).1 p z x hb
  · intro p hp z x hx
    obtain ⟨b, hpb, hb⟩ := hN p z x hx
    exact ((hnames b).2 (hpositive b p hpb hp)).1 p hpb z x hb
  · intro c hc p hp hca q hqp
    obtain ⟨b, hbA, s, hsq, hsb⟩ := hpredense q
    let branch : A := ⟨b, hbA⟩
    have hb : source.holds b a := hpositive branch s hsb
      (source.persistent (hsq.trans hqp) hp)
    obtain ⟨bound, hbound⟩ := ((hnames branch).2 hb).2 c hc
    refine ⟨s, hsq, bound, ?_⟩
    intro t hts z hz x hx
    exact hbound t (hts.trans hsb)
      ((eval G H c).persistent ((hts.trans hsq).trans hqp) hca) z hz x
      (decides_on_branch hA blocks branch t (hts.trans hsb) z x (hN t z x hx))

theorem base_small_to_square_trace (data : SquareData r H source a)
    (ha : GoodCut r σ H source a) (p : P) (hp : source.holds p a)
    (U : RegularName P W2) (hU : (smallName r H a).holds p U) :
    (squareTraceName data.name.toClique).holds p U := by
  intro q hqp
  obtain ⟨s, hsq, c, hc, hn, hcover⟩ := hU q hqp
  have hca : (eval G H (SmallUnionCode.compl c)).holds s a := by
    rw [eval_compl]
    exact hn
  obtain ⟨t, hts, bound, hbound⟩ := data.converges (SmallUnionCode.compl c)
    (ha.compl_lt c hc) s (source.persistent (hsq.trans hqp) hp) hca s le_rfl
  obtain ⟨innerBound, _⟩ := exists_bound_of_countable (∅ : Set W1) Set.countable_empty
  refine ⟨t, hts.trans hsq, bound,
    fun i hi => traceName_of_bound (rowCore data.name.toClique i) t U innerBound ?_⟩
  intro v hvt j _ x hx hUx
  have hcx := hbound v hvt (toLex (i, j)) hi x hx
  rw [eval_compl] at hcx
  exact hcx v le_rfl (hcover x (data.geometry v (toLex (i, j)) x hx).1 v
    (hvt.trans hts) hUx)

theorem prior_source_square_positive (data : SquareData r H source a)
    (p : P) (hp : source.holds p a) :
    (neg (squareTraceName data.name.toClique)).holds p
      (Erdos1172Part3GuardedTraceFamily.priorSource source a) := by
  apply named_cover_not_square_small data.name.toClique p
    (Erdos1172Part3GuardedTraceFamily.priorSource source a)
  intro q hqp z x hx
  exact ⟨data.actual_source q (source.persistent hqp hp) z x hx, (data.geometry q z x hx).1⟩

theorem exists_club_guarded_source_squares (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName P W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a) :
    ∃ r : Code P W1 G ↪ W2, ∃ σ : NiceCliqueName P W1 W2 G ↪ W2,
      ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club,
        ErdosRadoCHAsym.IsOmegaOneSup a → GoodBlockCut r σ H source a ∧
          ((∃ p : P, source.holds p a) → Nonempty (SquareData r H source a)) := by
  obtain ⟨r, σ, club, hclub, hcuts⟩ := exists_club_goodBlockCut_of_gch hGCH hP hclosed center
    G H hcompl hred hblue source hsup
  exact ⟨r, σ, club, hclub, fun a ha hasup => ⟨hcuts a ha hasup,
    exists_guarded_source_square hclosed center.omegaTwoCC (hcuts a ha hasup)⟩⟩

end Erdos1172Part3GuardedSourceSquare
