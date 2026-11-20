/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3GuardedRedCore
public import Erdos1172.Part3NamedTraceSubsequence

@[expose] public section

/-!
# A condition-compatible family of regular red trace ideals

One guarded core is chosen per eligible cut. At every condition where
the source holds at that cut, its trace ideal extends base smallness,
keeps the prior source positive, and extracts actual red omegaOne cliques
with source and trace membership witnessed at the same conditions.
Outside the eligible domain the assigned ideal is the improper ideal.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3GuardedTraceFamily

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal (smallName)
open Erdos1172Part3GuardedRedCore (CoreData exists_club_guarded_red_cores_of_gch)
open Erdos1172Part3GuardedCoreNames (guardedConverges_below)
open Erdos1172Part3NamedTraceIdeal
open Erdos1172Part3NamedTraceSubsequence (named_cover_not_small)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G H : SimpleGraph W2}
variable {r : Code P W1 G ↪ W2} {σ : NiceCliqueName P W1 W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

noncomputable def priorSource (source : RegularName P W2) (a : W2) : RegularName P W2 :=
  meet source (ground {x | x < a})

theorem base_small_to_trace (data : CoreData r H source a) (ha : GoodCut r σ H source a)
    (p : P) (hp : source.holds p a) (U : RegularName P W2)
    (hU : (smallName r H a).holds p U) : (traceName data.name.toClique).holds p U :=
  traceName_of_base_small ha data.name.toClique p
    (fun q i x hx => (data.geometry q i x hx).1)
    (guardedConverges_below data.converges p hp) p le_rfl U hU

theorem prior_source_positive (data : CoreData r H source a)
    (p : P) (hp : source.holds p a) :
    (neg (traceName data.name.toClique)).holds p (priorSource source a) := by
  apply named_cover_not_small data.name.toClique p (priorSource source a)
  intro q hqp i x hx
  exact ⟨data.actual_source q (source.persistent hqp hp) i x hx, (data.geometry q i x hx).1⟩

end Erdos1172Part3GuardedTraceFamily
