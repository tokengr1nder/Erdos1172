/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3GuardedCoreNames
public import Erdos1172.Part3NamedRedReflection
public import Erdos1172.Part3HechlerStagesAfterLimit

@[expose] public section

/-!
# One red core name for every condition at a cut

The reflection club supplies red positivity under every condition where
the source holds at the cut. Guarded fusion turns those extensions into
one nice core name. Its source membership and convergence are guarded by
that actual cut membership; no local rank for the whole name is asserted.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3GuardedRedCore

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3NamedColorCore (colorFiber)
open Erdos1172Part3GuardedCoreNames (GuardedConverges exists_guarded_name)
open Erdos1172Part3NamedRedReflection
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

structure CoreData (r : Code P W1 G ↪ W2) (H : SimpleGraph W2)
    (source : RegularName P W2) (a : W2) where
  name : NiceCliqueName P W1 W2 G
  geometry : ∀ p i x, name.toClique.decides p i x → x < a ∧ G.Adj x a
  actual_source : ∀ p : P, source.holds p a → ∀ i x,
    name.toClique.decides p i x → source.holds p x
  converges : GuardedConverges r H a (reindex source (fun _ : Unit => a)) name.toClique

theorem exists_club_guarded_red_cores (hCH : CH) (hclosed : CountablyClosed P)
    (center : CountablyCenteredCode P) (G H : SimpleGraph W2)
    (r : Code P W1 G ↪ W2) (σ : NiceCliqueName P W1 W2 G ↪ W2)
    (hcompl : IsCompl G H) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName P W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club,
      ErdosRadoCHAsym.IsOmegaOneSup a →
        GoodCut r σ H source a ∧
        ((∃ p : P, source.holds p a) → Nonempty (CoreData r H source a)) := by
  have hI : #W1 ≤ ℵ_ 1 := by
    simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl]
  obtain ⟨closed, hclosedClub, hgood⟩ := exists_club_goodCut hCH center.omegaTwoCC hI
    G H r σ source
  let family (_ : Code P W1 G) : RegularName P W2 := source
  obtain ⟨positive, hpositiveClub, hpositive⟩ :=
    exists_club_red_positive_family_of_no_blue_target center r H hcompl hblue r family
  refine ⟨closed ∩ positive, hclosedClub.inter alephZero_lt_cof_W2.ne' hpositiveClub, ?_⟩
  intro a ha hasup
  have hg : GoodCut r σ H source a := hgood a ha.1 hasup
  refine ⟨hg, ?_⟩
  intro hpossible
  let c0 : Code P W1 G := SmallUnionCode.empty
  have hpos : ∀ p : P, source.holds p a →
      (neg (Erdos1172Part3RegularNamedIdeal.smallName r H a)).holds p
        (colorFiber G H source a true) :=
    fun p hp => hpositive a ha.2 c0 hg.empty_lt p hp
  obtain ⟨N, hgeometry, hsource, hconv⟩ := exists_guarded_name hclosed center.omegaTwoCC hg
    (reindex source (fun _ : Unit => a)) (colorFiber G H source a true)
    hpossible hpos (fun p hp x hx => hx.2.2)
  exact ⟨⟨N, hgeometry, fun p hp i x hx => (hsource p hp i x hx).1, hconv⟩⟩

theorem exists_club_guarded_red_cores_of_gch (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) (source : RegularName P W2) :
    ∃ r : Code P W1 G ↪ W2, ∃ σ : NiceCliqueName P W1 W2 G ↪ W2,
      ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club,
        ErdosRadoCHAsym.IsOmegaOneSup a →
          GoodCut r σ H source a ∧
          ((∃ p : P, source.holds p a) → Nonempty (CoreData r H source a)) := by
  have hI : #W1 ≤ ℵ_ 1 := by
    simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl]
  exact ⟨rank hGCH hP hI G, blockRank hGCH hP hI G,
    exists_club_guarded_red_cores hGCH.toCH hclosed center G H
      (rank hGCH hP hI G) (blockRank hGCH hP hI G) hcompl hblue source⟩

theorem guarded_red_cores_after_limit (hGCH : GCH) (n : ℕ)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName
      (Erdos1172Part3HechlerStagesAfterLimit.afterLimit hGCH n).Carrier W2) :
    let P := (Erdos1172Part3HechlerStagesAfterLimit.afterLimit hGCH n).Carrier
    ∃ r : Code P W1 G ↪ W2, ∃ σ : NiceCliqueName P W1 W2 G ↪ W2,
      ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club,
        ErdosRadoCHAsym.IsOmegaOneSup a →
          GoodCut r σ H source a ∧
          ((∃ p : P, source.holds p a) → Nonempty (CoreData r H source a)) := by
  let order := Erdos1172Part3HechlerStagesAfterLimit.afterLimit hGCH n
  exact exists_club_guarded_red_cores_of_gch hGCH order.small order.closed order.centered
    G H hcompl hblue source

end Erdos1172Part3GuardedRedCore
