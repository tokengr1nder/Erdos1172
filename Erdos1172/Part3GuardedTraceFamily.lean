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

theorem red_core_in_positive_trace (hclosed : CountablyClosed P)
    (data : CoreData r H source a) (p : P) (hp : source.holds p a)
    (U : RegularName P W2) (hU : ¬(traceName data.name.toClique).holds p U) :
    ∃ C : Set W2, G.IsClique C ∧ typeLT C = ω_ 1 ∧
      ∀ x ∈ C, x < a ∧ G.Adj x a ∧ ∃ q : P, q ≤ p ∧ U.holds q x ∧ source.holds q x := by
  obtain ⟨C, hC, hCt, hmem⟩ :=
    Erdos1172Part3NamedTraceExtraction.exists_ground_clique_in_positive_trace
      hclosed data.name.toClique p U hU
  refine ⟨C, hC, hCt, ?_⟩
  intro x hx
  obtain ⟨q, hqp, hUx, i, hi⟩ := hmem x hx
  exact ⟨(data.geometry q i x hi).1, (data.geometry q i x hi).2,
    q, hqp, hUx, data.actual_source q (source.persistent hqp hp) i x hi⟩

/-- No input core family or ideal family is assumed. Their construction
uses GCH and the exact blue-target exclusion. The resulting positive
extraction has type omegaOne, not the large Part 3 target. -/
theorem exists_regular_red_trace_family (hGCH : GCH) (hP : #P ≤ ℵ_ 2)
    (hclosed : CountablyClosed P) (center : CountablyCenteredCode P)
    (G H : SimpleGraph W2) (hcompl : IsCompl G H)
    (hblue : ¬HasCliqueOfType H (ω_ 1 + 2)) (source : RegularName P W2) :
    ∃ r : Code P W1 G ↪ W2, ∃ σ : NiceCliqueName P W1 W2 G ↪ W2,
      ∃ club : Set W2, ∃ J : W2 → RegularName P (RegularName P W2),
        IsClub club ∧
        (∀ a p, (J a).holds p (ground ∅)) ∧
        (∀ a p U V, (∀ x, (implication U V).holds p x) →
          (J a).holds p V → (J a).holds p U) ∧
        (∀ a p (U : ℕ → RegularName P W2), (∀ n, (J a).holds p (U n)) →
          (J a).holds p (join U)) ∧
        ∀ a ∈ club, ErdosRadoCHAsym.IsOmegaOneSup a → ∀ p : P, source.holds p a →
          GoodCut r σ H source a ∧
          (∀ U : RegularName P W2, (smallName r H a).holds p U → (J a).holds p U) ∧
          (neg (J a)).holds p (priorSource source a) ∧
          ∀ U : RegularName P W2, ¬(J a).holds p U →
            ∃ C : Set W2, G.IsClique C ∧ typeLT C = ω_ 1 ∧
              ∀ x ∈ C, x < a ∧ G.Adj x a ∧
                ∃ q : P, q ≤ p ∧ U.holds q x ∧ source.holds q x := by
  classical
  obtain ⟨r, σ, club, hclub, hcores⟩ := exists_club_guarded_red_cores_of_gch
    hGCH hP hclosed center G H hcompl hblue source
  let D : Set W2 := {a | a ∈ club ∧ ErdosRadoCHAsym.IsOmegaOneSup a ∧
    ∃ p : P, source.holds p a}
  let data (a : D) : CoreData r H source a.val :=
    Classical.choice ((hcores a.val a.property.1 a.property.2.1).2 a.property.2.2)
  let J (a : W2) : RegularName P (RegularName P W2) :=
    if ha : a ∈ D then traceName (data ⟨a, ha⟩).name.toClique else ground Set.univ
  refine ⟨r, σ, club, J, hclub, ?_, ?_, ?_, ?_⟩
  · intro a p
    by_cases ha : a ∈ D
    · simpa only [J, dif_pos ha] using traceName_empty (data ⟨a, ha⟩).name.toClique p
    · simp only [J, dif_neg ha]
      trivial
  · intro a p U V hsub hV
    by_cases ha : a ∈ D
    · simp only [J, dif_pos ha] at hV ⊢
      exact traceName_mono (data ⟨a, ha⟩).name.toClique p U V hsub hV
    · simp only [J, dif_neg ha]
      trivial
  · intro a p U hU
    by_cases ha : a ∈ D
    · simp only [J, dif_pos ha] at hU ⊢
      exact traceName_countable_join hclosed (data ⟨a, ha⟩).name.toClique p U hU
    · simp only [J, dif_neg ha]
      trivial
  · intro a hac hasup p hp
    let d : D := ⟨a, hac, hasup, ⟨p, hp⟩⟩
    have hJa : J a = traceName (data d).name.toClique := dif_pos d.property
    rw [hJa]
    have hg : GoodCut r σ H source a := (hcores a hac hasup).1
    exact ⟨hg, fun U hU => base_small_to_trace (data d) hg p hp U hU,
      prior_source_positive (data d) p hp,
      fun U hU => red_core_in_positive_trace hclosed (data d) p hp U hU⟩

end Erdos1172Part3GuardedTraceFamily
