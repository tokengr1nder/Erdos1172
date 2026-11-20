/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3HechlerCentering
public import Erdos1172.Part3RedPredecessorReflection
public import Mathlib.Order.Zorn

@[expose] public section

/-!
# Stationary sets of possible decisions

The omegaTwo chain condition turns stationary many possible decisions into
a condition below which they remain stationary. All predicates live in the
original types; no generic filter or forcing extension is postulated.
This is a preservation ingredient for constructing the BHT clique decisions,
not a construction of those decisions or a proof of the large core.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3StationaryDecisions

open Erdos1172Part3NeighborhoodCode (W2 cof_W2 alephZero_lt_cof_W2)
open Erdos1172Part3ClosedDecisionSystem (DenseBelow)

variable {P : Type} [Preorder P]

def Compatible (p q : P) : Prop := ∃ r : P, r ≤ p ∧ r ≤ q

theorem compatible_symm {p q : P} (h : Compatible p q) : Compatible q p := by
  obtain ⟨r, hrp, hrq⟩ := h
  exact ⟨r, hrq, hrp⟩

def IncompatibleFamily (A : Set P) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p ≠ q → ¬Compatible p q

def OmegaTwoCC (P : Type) [Preorder P] : Prop :=
  ∀ A : Set P, IncompatibleFamily A → #A < ℵ_ 2

/-- Every dense set contains a maximal antichain which is predense in
the whole order. The conditions in the antichain retain their dense-set
membership, which is needed for intersecting their associated clubs. -/
theorem exists_predense_antichain (D : Set P) (hD : DenseBelow D) :
    ∃ A : Set P, A ⊆ D ∧ IncompatibleFamily A ∧
      ∀ p : P, ∃ q ∈ A, Compatible p q := by
  classical
  obtain ⟨A, _, hA⟩ := zorn_subset_nonempty
    {A : Set P | A ⊆ D ∧ IncompatibleFamily A} (fun chain hchain hordered _ => by
      refine ⟨⋃₀ chain, ⟨?_, ?_⟩, ?_⟩
      · rintro p ⟨s, hs, hps⟩
        exact (hchain hs).1 hps
      · rintro p ⟨s, hs, hps⟩ q ⟨t, ht, hqt⟩ hpq
        rcases hordered.total hs ht with hst | hts
        · exact (hchain ht).2 p (hst hps) q hqt hpq
        · exact (hchain hs).2 p hps q (hts hqt) hpq
      · exact fun s hs => Set.subset_sUnion_of_mem hs)
    ∅ ⟨Set.empty_subset _, by intro p hp; exact hp.elim⟩
  refine ⟨A, hA.1.1, hA.1.2, ?_⟩
  intro p
  by_contra h
  push Not at h
  obtain ⟨q, hqD, hqp⟩ := hD p
  have hqA : q ∉ A := fun hq => h q hq ⟨q, hqp, le_rfl⟩
  have hinsert : IncompatibleFamily (insert q A) := by
    intro x hx y hy hxy
    by_cases hxq : x = q
    · subst x
      have hyA : y ∈ A := (Set.mem_insert_iff.mp hy).resolve_left hxy.symm
      rintro ⟨r, hrq, hry⟩
      exact h y hyA ⟨r, hrq.trans hqp, hry⟩
    · have hxA : x ∈ A := (Set.mem_insert_iff.mp hx).resolve_left hxq
      by_cases hyq : y = q
      · subst y
        rintro ⟨r, hrx, hrq⟩
        exact h x hxA ⟨r, hrq.trans hqp, hrx⟩
      · exact hA.1.2 x hxA y ((Set.mem_insert_iff.mp hy).resolve_left hyq) hxy
  exact hqA (hA.2 ⟨Set.insert_subset hqD hA.1.1, hinsert⟩
    (Set.subset_insert _ _) (Set.mem_insert _ _))

def Persistent (U : P → W2 → Prop) : Prop :=
  ∀ {p q a}, q ≤ p → U p a → U q a

def possible (U : P → W2 → Prop) (p : P) : Set W2 :=
  {a | ∃ q : P, q ≤ p ∧ U q a}

/-- Every strengthening still has stationary many possible members. This
definition alone does not assert stationarity in an external universe. -/
def StationaryAt (U : P → W2 → Prop) (p : P) : Prop :=
  ∀ q : P, q ≤ p → IsStationary (possible U q)

theorem possible_mono (U : P → W2 → Prop) {p q : P} (hpq : p ≤ q) :
    possible U p ⊆ possible U q := by
  rintro a ⟨r, hrp, hra⟩
  exact ⟨r, hrp.trans hpq, hra⟩

theorem stationaryAt_mono {U : P → W2 → Prop} {p q : P}
    (h : StationaryAt U p) (hqp : q ≤ p) : StationaryAt U q :=
  fun r hrq => h r (hrq.trans hqp)

/-- The small-antichain argument. If every condition could destroy
stationarity, a maximal antichain of such conditions would give fewer
than omegaTwo clubs whose intersection contradicts the original
stationary set of possible members. -/
theorem exists_stationary_condition (hcc : OmegaTwoCC P)
    (U : P → W2 → Prop) (hU : Persistent U)
    (hstat : IsStationary {a : W2 | ∃ p : P, U p a}) :
    ∃ p : P, StationaryAt U p := by
  classical
  by_contra h
  simp only [StationaryAt] at h
  push Not at h
  let D : Set P := {p | ¬IsStationary (possible U p)}
  have hD : DenseBelow D := by
    intro p
    obtain ⟨q, hqp, hq⟩ := h p
    exact ⟨q, hq, hqp⟩
  obtain ⟨A, hAD, hA, hpredense⟩ := exists_predense_antichain D hD
  choose clubs hclubs hdisjoint using
    fun q : A => not_isStationary_iff.mp (hAD q.property)
  have hclub : IsClub (⋂ q : A, clubs q) := IsClub.iInter alephZero_lt_cof_W2.ne'
    (by simpa only [Cardinal.lift_id, cof_W2] using hcc A hA) hclubs
  obtain ⟨a, ⟨p, hpa⟩, hac⟩ := hstat hclub
  obtain ⟨q, hqA, r, hrp, hrq⟩ := hpredense p
  exact Set.disjoint_left.mp (hdisjoint ⟨q, hqA⟩)
    ⟨r, hrq, hU hrp hpa⟩ (Set.mem_iInter.mp hac ⟨q, hqA⟩)

/-- The preservation condition can be chosen below any given condition
whose possible members form a stationary set. -/
theorem exists_stationary_refinement (hcc : OmegaTwoCC P)
    (U : P → W2 → Prop) (hU : Persistent U) (p0 : P)
    (hstat : IsStationary (possible U p0)) :
    ∃ p : P, p ≤ p0 ∧ StationaryAt U p := by
  let restricted (p : P) (a : W2) : Prop := p ≤ p0 ∧ U p a
  have hrestricted : Persistent restricted :=
    fun hpq h => ⟨hpq.trans h.1, hU hpq h.2⟩
  have hs : IsStationary {a : W2 | ∃ p : P, restricted p a} := hstat
  obtain ⟨p, hp⟩ := exists_stationary_condition hcc restricted hrestricted hs
  obtain ⟨a, q, hqp, hq0, hqa⟩ := (hp p le_rfl).nonempty
  refine ⟨q, hq0, ?_⟩
  intro r hrq
  exact ((stationaryAt_mono hp hqp) r hrq).mono
    (by rintro b ⟨s, hsr, hs0, hsb⟩; exact ⟨s, hsr, hsb⟩)

/-- A concrete instance supplied by the previously constructed order. -/
theorem hechler_omegaTwoCC (hCH : CH) :
    OmegaTwoCC Erdos1172Part3HechlerOrder.Condition := by
  intro A hA
  exact (Erdos1172Part3HechlerCentering.antichain_card_le hCH A hA).trans_lt
    (Cardinal.aleph_lt_aleph.mpr (by norm_num : (1 : Ordinal.{0}) < 2))

end Erdos1172Part3StationaryDecisions
