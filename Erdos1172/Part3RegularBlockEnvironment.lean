/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularLocalReflection

@[expose] public section

/-!
# Constructed local environments for red block recursion

The same cut is closed under the neighborhood algebra and supports
locally ranked red blocks in each actual coded source neighborhood.
The source can depend on the condition, and all conditions are covered.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RegularBlockEnvironment

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularLocalBlock (localBlockName)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3IteratedHechlerCentering (CountablyCenteredCode)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)
open OrdinalRamsey (HasCliqueOfType)

variable {P : Type} [Preorder P] {G : SimpleGraph W2}

structure GoodBlockCut (r : Code P W1 G ↪ W2) (σ : NiceCliqueName P W1 W2 G ↪ W2)
    (H : SimpleGraph W2) (source : RegularName P W2) (a : W2) : Prop where
  goodCut : GoodCut r σ H source a
  blocks : ∀ c : Code P W1 G, r c < a → ∀ p : P,
    source.holds p a → (eval G H c).holds p a →
      (localBlockName σ (meet source (eval G H c))).holds p a

theorem exists_club_goodBlockCut (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (r : Code P W1 G ↪ W2) (σ : NiceCliqueName P W1 W2 G ↪ W2)
    (source : RegularName P W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ErdosRadoCHAsym.IsOmegaOneSup a →
      GoodBlockCut r σ H source a := by
  obtain ⟨closed, hclosedClub, hgood⟩ := exists_club_goodCut hGCH.toCH center.omegaTwoCC
    (by simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl]) G H r σ source
  obtain ⟨blocksClub, hlocalClub, hlocal⟩ :=
    Erdos1172Part3RegularLocalReflection.exists_club_local_block_family
      hGCH hP hclosed center G H hcompl hred hblue r σ
      (fun c => meet source (eval G H c)) (fun c p a ha => hsup p a ha.1)
  refine ⟨closed ∩ blocksClub, hclosedClub.inter alephZero_lt_cof_W2.ne' hlocalClub, ?_⟩
  intro a ha hasup
  exact ⟨hgood a ha.1 hasup, fun c hc p hp he => hlocal a ha.2 c hc p ⟨hp, he⟩⟩

theorem exists_club_goodBlockCut_of_gch (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hred : ¬HasCliqueOfType G (ω_ 2)) (hblue : ¬HasCliqueOfType H (ω_ 1 + 2))
    (source : RegularName P W2)
    (hsup : ∀ p a, source.holds p a → ErdosRadoCHAsym.IsOmegaOneSup a) :
    ∃ r : Code P W1 G ↪ W2, ∃ σ : NiceCliqueName P W1 W2 G ↪ W2,
      ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club, ErdosRadoCHAsym.IsOmegaOneSup a →
        GoodBlockCut r σ H source a := by
  have hI : #W1 ≤ ℵ_ 1 := by
    simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl]
  exact ⟨rank hGCH hP hI G, blockRank hGCH hP hI G,
    exists_club_goodBlockCut hGCH hP hclosed center G H hcompl hred hblue
      (rank hGCH hP hI G) (blockRank hGCH hP hI G) source hsup⟩

end Erdos1172Part3RegularBlockEnvironment
