/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NiceNameSupport
public import Erdos1172.Part3RegularNeighborhoodCode

@[expose] public section

/-!
# Earlier-stage locality of regular neighborhood codes

Complete restrictions preserve complements and dense unions. Consequently
the whole well-founded countable neighborhood algebra localizes whenever
small clique names have bounded support. A club then localizes every code
ranked below the cut at that cut's stage, uniformly in the condition.

The actual stage system and its bounded-support inclusion property remain
explicit inputs. This is not a construction of the uncountable iteration
or a proof that locally ranked higher cores already exist.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3RegularStageLocality

open ErdosRadoCHAsym (W2)
open Erdos1172Part3CompleteRestriction (CompleteRestriction Supported restrictClique)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods (afterClique)
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3RegularNeighborhoodCode (Code eval)

variable {P Q X : Type} [Preorder P] [Preorder Q]

theorem liftRegular_neg (r : CompleteRestriction P Q) (U : RegularName Q X) :
    r.liftRegular (neg U) = neg (r.liftRegular U) := by
  apply RegularName.ext
  intro p x
  constructor
  · intro h q hqp hq
    exact h (r.restrict q) (r.restrict.monotone hqp) hq
  · intro h q hqp hq
    obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
    apply h s hsp
    change U.holds (r.restrict s) x
    rwa [hs]

theorem liftRegular_join {J : Type} (r : CompleteRestriction P Q)
    (U : J → RegularName Q X) : r.liftRegular (join U) = join (fun j => r.liftRegular (U j)) := by
  apply RegularName.ext
  intro p x
  constructor
  · intro h q hqp
    obtain ⟨s, hsq, j, hs⟩ := h (r.restrict q) (r.restrict.monotone hqp)
    obtain ⟨t, htq, ht⟩ := r.lift q s hsq
    refine ⟨t, htq, j, ?_⟩
    change (U j).holds (r.restrict t) x
    rwa [ht]
  · intro h q hqp
    obtain ⟨s, hsp, hs⟩ := r.lift p q hqp
    obtain ⟨t, hts, j, ht⟩ := h s hsp
    refine ⟨r.restrict t, ?_, j, ht⟩
    have hle := r.restrict.monotone hts
    rwa [hs] at hle

def Factors (r : CompleteRestriction P Q) (U : RegularName P X) : Prop :=
  ∃ V : RegularName Q X, r.liftRegular V = U

theorem factors_ground (r : CompleteRestriction P Q) (s : Set X) :
    Factors r (ground s) := ⟨ground s, rfl⟩

theorem factors_neg (r : CompleteRestriction P Q) {U : RegularName P X}
    (h : Factors r U) : Factors r (neg U) := by
  obtain ⟨V, rfl⟩ := h
  exact ⟨neg V, liftRegular_neg r V⟩

theorem factors_join {J : Type} (r : CompleteRestriction P Q)
    (U : J → RegularName P X) (h : ∀ j, Factors r (U j)) : Factors r (join U) := by
  classical
  choose V hV using h
  refine ⟨join V, ?_⟩
  rw [liftRegular_join]
  exact congrArg join (funext hV)

variable {I V : Type} [LinearOrder I] [LinearOrder V] {G : SimpleGraph V}

theorem factors_afterClique (r : CompleteRestriction P Q) (N : NiceCliqueName P I V G)
    (hs : Supported r N.function) : Factors r (afterClique N.toClique) := by
  refine ⟨afterClique (restrictClique r N hs).toClique, ?_⟩
  exact RegularName.ext (Erdos1172Part3CompleteRestriction.restrictClique_after_iff r N hs)

variable (Stage : W2 → Type) [∀ a, Preorder (Stage a)]
variable (restriction : ∀ a, CompleteRestriction P (Stage a))

def EventuallyLocal (U : RegularName P X) : Prop :=
  ∃ bound : W2, ∀ a : W2, bound ≤ a → Factors (restriction a) U

theorem eventuallyLocal_ground (s : Set X) : EventuallyLocal Stage restriction (ground s) := by
  let start : W2 := Classical.choice (Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos 2).ne')
  exact ⟨start, fun a _ => factors_ground (restriction a) s⟩

theorem eventuallyLocal_neg {U : RegularName P X} (h : EventuallyLocal Stage restriction U) :
    EventuallyLocal Stage restriction (neg U) := by
  obtain ⟨bound, hb⟩ := h
  exact ⟨bound, fun a ha => factors_neg (restriction a) (hb a ha)⟩

theorem eventuallyLocal_join (U : ℕ → RegularName P X)
    (h : ∀ n, EventuallyLocal Stage restriction (U n)) :
    EventuallyLocal Stage restriction (join U) := by
  classical
  choose bound hb using h
  obtain ⟨top, htop⟩ := Erdos1172Part3CoreObjectCode.exists_objectBound
    ⟨Set.range bound, Cardinal.mk_range_le.trans (by
      simpa only [Cardinal.mk_nat] using Cardinal.aleph0_le_aleph 1)⟩
  refine ⟨top, ?_⟩
  intro a ha
  exact factors_join (restriction a) U (fun n => hb n a ((htop _ ⟨n, rfl⟩).le.trans ha))

variable (conditionSupport : P → Set W2) (hsmall : ∀ p, (conditionSupport p).Countable)
variable (hlocal : ∀ a p, (∀ b ∈ conditionSupport p, b < a) →
  p ∈ Set.range (restriction a).embed)

include conditionSupport hsmall hlocal

theorem eventuallyLocal_afterClique (N : NiceCliqueName P I V G) (hI : #I ≤ ℵ_ 1) :
    EventuallyLocal Stage restriction (afterClique N.toClique) := by
  obtain ⟨bound, hb⟩ := Erdos1172Part3NiceNameSupport.exists_support_bound
    conditionSupport hsmall N.function hI
  refine ⟨bound, ?_⟩
  intro a hba
  apply factors_afterClique
  intro i p v hp
  exact hlocal a p (fun b hbp => (hb i p v hp b hbp).trans_le hba)

theorem eventuallyLocal_eval (G H : SimpleGraph W2) (hI : #I ≤ ℵ_ 1)
    (c : Code P I G) : EventuallyLocal Stage restriction (eval G H c) := by
  induction c using WType.rec with
  | mk head children ih =>
    cases head with
    | inl k =>
      fin_cases k
      · change EventuallyLocal Stage restriction (ground ∅)
        exact eventuallyLocal_ground Stage restriction ∅
      · change EventuallyLocal Stage restriction (neg (eval G H (children ())))
        exact eventuallyLocal_neg Stage restriction (ih ())
      · change EventuallyLocal Stage restriction (join (fun n => eval G H (children n)))
        exact eventuallyLocal_join Stage restriction _ ih
    | inr atom =>
      cases atom with
      | inl point =>
        rcases point with ⟨k, x⟩
        fin_cases k
        · change EventuallyLocal Stage restriction (ground {y | G.Adj x y})
          exact eventuallyLocal_ground Stage restriction _
        · change EventuallyLocal Stage restriction (ground {y | H.Adj x y})
          exact eventuallyLocal_ground Stage restriction _
        · change EventuallyLocal Stage restriction (ground (Set.Iic x))
          exact eventuallyLocal_ground Stage restriction _
      | inr N =>
        change EventuallyLocal Stage restriction (afterClique N.toClique)
        exact eventuallyLocal_afterClique Stage restriction conditionSupport hsmall hlocal N hI

end Erdos1172Part3RegularStageLocality
