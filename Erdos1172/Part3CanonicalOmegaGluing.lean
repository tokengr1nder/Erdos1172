/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularTruthExtension
public import Erdos1172.Part3OmegaPowerIndex

@[expose] public section

/-!
# A canonical omega-core name from its finite block names

The gluing operation depends only on the sequence of input names. It
preserves their decisions at every condition satisfying all cross-joins,
not only below one chosen condition. This distinction permits countable
rank closure without imposing a rank bound on that condition.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CanonicalOmegaGluing

open ErdosRadoCHAsym (W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique containedIn cliqueFunction)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3RegularTruthExtension (TruthOrder exists_global_clique_from_truth)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName exists_nice_clique_name)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)
open Erdos1172Part3FiniteTraceSchemes (Index)
open Erdos1172Part3OmegaPowerIndex (OmegaIndex mk_omegaIndex_le)
open Erdos1172Part3RankedWitnessRestriction (RankedWitness)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

abbrev Blocks (P : Type) [Preorder P] (G : SimpleGraph W2) :=
  ∀ n : ℕ, NiceCliqueName P (Index n) W2 G

abbrev IncreasingPair := {mn : ℕ × ℕ // mn.1 < mn.2}

noncomputable def allJoined (blocks : Blocks P G) : RegularName P Unit :=
  all (fun mn : IncreasingPair =>
    containedIn (cliqueFunction (blocks mn.val.2).toClique) (afterClique (blocks mn.val.1).toClique))

theorem allJoined_cross (blocks : Blocks P G) {p : P} (hp : (allJoined blocks).holds p ())
    {m n : ℕ} (hmn : m < n) {i : Index m} {j : Index n} {x y : W2}
    (hx : (blocks m).toClique.decides p i x) (hy : (blocks n).toClique.decides p j y) :
    x < y ∧ G.Adj x y :=
  hp ⟨(m, n), hmn⟩ p le_rfl j y hy p le_rfl i x hx

def sumDecides (blocks : Blocks P G) (p : TruthOrder (allJoined blocks))
    (z : OmegaIndex) (x : W2) : Prop :=
  (blocks (ofLex z).1).toClique.decides p.val (ofLex z).2 x

theorem sum_ordered_pair (blocks : Blocks P G)
    {p : TruthOrder (allJoined blocks)} {i j : OmegaIndex} {x y : W2} (hij : i < j)
    (hx : sumDecides blocks p i x) (hy : sumDecides blocks p j y) : x < y ∧ G.Adj x y := by
  cases hij with
  | left k l hmn => exact allJoined_cross blocks p.property hmn hx hy
  | right k l hkl => exact ⟨(blocks _).toClique.ordered hkl hx hy,
      (blocks _).toClique.adjacent hkl.ne hx hy⟩

def sumClique (blocks : Blocks P G) :
    CliqueDecisions (TruthOrder (allJoined blocks)) OmegaIndex W2 G where
  decides := sumDecides blocks
  dense := by
    intro p z
    obtain ⟨q, hqp, x, hx⟩ := (blocks (ofLex z).1).toClique.dense p.val (ofLex z).2
    exact ⟨⟨q, (allJoined blocks).persistent hqp p.property⟩, hqp, x, hx⟩
  persistent := by
    intro p q z x hqp hx
    exact (blocks (ofLex z).1).toClique.persistent hqp hx
  unique := by
    intro p z x y hx hy
    exact (blocks (ofLex z).1).toClique.unique hx hy
  ordered hij hx hy := (sum_ordered_pair blocks hij hx hy).1
  adjacent := by
    intro p i j x y hij hx hy
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (sum_ordered_pair blocks hlt hx hy).2
    · exact (sum_ordered_pair blocks hgt hy hx).2.symm

structure GluingSpec (blocks : Blocks P G) (N : NiceCliqueName P OmegaIndex W2 G) : Prop where
  atTruth : ∀ p, (allJoined blocks).holds p () → ∀ z x, N.toClique.decides p z x →
    (blocks (ofLex z).1).toClique.decides p (ofLex z).2 x
  origin : ∀ p z x, N.toClique.decides p z x →
    ∃ q : P, (blocks (ofLex z).1).toClique.decides q (ofLex z).2 x

theorem exists_glued_name (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (blocks : Blocks P G) (hne : ∃ p, (allJoined blocks).holds p ()) :
    ∃ N : NiceCliqueName P OmegaIndex W2 G, GluingSpec blocks N := by
  obtain ⟨out, htruth, horigin⟩ := exists_global_clique_from_truth hclosed (allJoined blocks)
    (sumClique blocks) mk_omegaIndex_le hne
  obtain ⟨N, hN⟩ := exists_nice_clique_name hcc out
  refine ⟨N, ⟨?_, ?_⟩⟩
  · intro p hp z x hx
    exact (htruth p hp z x).mp (hN p z x hx)
  · intro p z x hx
    obtain ⟨q, hq⟩ := horigin p z x (hN p z x hx)
    exact ⟨q.val, hq⟩

noncomputable def glue? (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (blocks : Blocks P G) : Option (NiceCliqueName P OmegaIndex W2 G) := by
  classical
  exact if h : ∃ p, (allJoined blocks).holds p () then
    some (exists_glued_name hclosed hcc blocks h).choose else none

theorem exists_glue_some (hclosed : CountablyClosed P) (hcc : OmegaTwoCC P)
    (blocks : Blocks P G) (hne : ∃ p, (allJoined blocks).holds p ()) :
    ∃ N, glue? hclosed hcc blocks = some N ∧ GluingSpec blocks N := by
  refine ⟨(exists_glued_name hclosed hcc blocks hne).choose, ?_,
    (exists_glued_name hclosed hcc blocks hne).choose_spec⟩
  simp only [glue?, dif_pos hne]

theorem GluingSpec.preserves_containment {blocks : Blocks P G} {N : NiceCliqueName P OmegaIndex W2 G}
    (spec : GluingSpec blocks N) (source : RegularName P W2) {p : P}
    (hp : (allJoined blocks).holds p ())
    (hsource : ∀ n, (containedIn (cliqueFunction (blocks n).toClique) source).holds p ()) :
    (containedIn (cliqueFunction N.toClique) source).holds p () := by
  intro q hqp z x hx
  exact hsource (ofLex z).1 q hqp (ofLex z).2 x
    (spec.atTruth q ((allJoined blocks).persistent hqp hp) z x hx)

theorem GluingSpec.preserves_after {blocks : Blocks P G} {N : NiceCliqueName P OmegaIndex W2 G}
    (spec : GluingSpec blocks N) {p : P} {a : W2} (hp : (allJoined blocks).holds p ())
    (hafter : ∀ n, (afterClique (blocks n).toClique).holds p a) :
    (afterClique N.toClique).holds p a := by
  intro q hqp z x hx
  exact hafter (ofLex z).1 q hqp (ofLex z).2 x
    (spec.atTruth q ((allJoined blocks).persistent hqp hp) z x hx)

theorem GluingSpec.below {blocks : Blocks P G} {N : NiceCliqueName P OmegaIndex W2 G}
    (spec : GluingSpec blocks N) {a : W2}
    (hbelow : ∀ n q i x, (blocks n).toClique.decides q i x → x < a) :
    ∀ q z x, N.toClique.decides q z x → x < a := by
  intro q z x hx
  obtain ⟨p, hp⟩ := spec.origin q z x hx
  exact hbelow (ofLex z).1 p (ofLex z).2 x hp

theorem GluingSpec.rankedWitness {blocks : Blocks P G} {N : NiceCliqueName P OmegaIndex W2 G}
    (spec : GluingSpec blocks N) (rank : NiceCliqueName P OmegaIndex W2 G ↪ W2)
    (source : RegularName P W2) {p : P} {a : W2} (hrank : rank N < a)
    (hp : (allJoined blocks).holds p ())
    (hbelow : ∀ n q i x, (blocks n).toClique.decides q i x → x < a)
    (hsource : ∀ n, (containedIn (cliqueFunction (blocks n).toClique) source).holds p ())
    (hafter : ∀ n, (afterClique (blocks n).toClique).holds p a) :
    RankedWitness rank source p a :=
  ⟨N, hrank, spec.below hbelow, spec.preserves_containment source hp hsource, spec.preserves_after hp hafter⟩

end Erdos1172Part3CanonicalOmegaGluing
