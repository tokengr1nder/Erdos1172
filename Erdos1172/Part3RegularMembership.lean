/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3DecisionSelection

@[expose] public section

/-!
# Membership that is stable under dense refinement

A name is a persistent predicate which holds whenever it holds densely
below the current condition. Negation rules out every strengthening;
unions have dense witnesses. Neither operation uses possible membership
as actual membership. All definitions remain in the ground types.
-/

open Set

namespace Erdos1172Part3RegularMembership

variable {P X : Type} [Preorder P]

def DenseTruth (U : P → X → Prop) (p : P) (x : X) : Prop :=
  ∀ q : P, q ≤ p → ∃ r : P, r ≤ q ∧ U r x

structure RegularName (P X : Type) [Preorder P] where
  holds : P → X → Prop
  persistent : ∀ {p q x}, q ≤ p → holds p x → holds q x
  of_dense : ∀ p x, DenseTruth holds p x → holds p x

theorem RegularName.ext {U V : RegularName P X}
    (h : ∀ p x, U.holds p x ↔ V.holds p x) : U = V := by
  have hh : U.holds = V.holds := funext fun p => funext fun x => propext (h p x)
  cases U
  cases V
  cases hh
  rfl

def ground (s : Set X) : RegularName P X where
  holds _ x := x ∈ s
  persistent _ h := h
  of_dense p _ h := (h p le_rfl).choose_spec.2

def regularize (U : P → X → Prop) : RegularName P X where
  holds := DenseTruth U
  persistent hqp h r hrq := h r (hrq.trans hqp)
  of_dense p x h q hqp := by
    obtain ⟨r, hrq, hr⟩ := h q hqp
    obtain ⟨s, hsr, hs⟩ := hr r le_rfl
    exact ⟨s, hsr.trans hrq, hs⟩

def neg (U : RegularName P X) : RegularName P X where
  holds p x := ∀ q : P, q ≤ p → ¬U.holds q x
  persistent hqp h r hrq := h r (hrq.trans hqp)
  of_dense p x h q hqp hq := by
    obtain ⟨r, hrq, hr⟩ := h q hqp
    exact hr r le_rfl (U.persistent hrq hq)

def meet (U V : RegularName P X) : RegularName P X where
  holds p x := U.holds p x ∧ V.holds p x
  persistent hqp h := ⟨U.persistent hqp h.1, V.persistent hqp h.2⟩
  of_dense p x h := by
    constructor
    · apply U.of_dense p x
      intro q hqp
      obtain ⟨r, hrq, hr⟩ := h q hqp
      exact ⟨r, hrq, hr.1⟩
    · apply V.of_dense p x
      intro q hqp
      obtain ⟨r, hrq, hr⟩ := h q hqp
      exact ⟨r, hrq, hr.2⟩

def all {I : Type} (U : I → RegularName P X) : RegularName P X where
  holds p x := ∀ i, (U i).holds p x
  persistent hqp h i := (U i).persistent hqp (h i)
  of_dense p x h i := by
    apply (U i).of_dense p x
    intro q hqp
    obtain ⟨r, hrq, hr⟩ := h q hqp
    exact ⟨r, hrq, hr i⟩

def join {I : Type} (U : I → RegularName P X) : RegularName P X :=
  regularize (fun p x => ∃ i, (U i).holds p x)

def implication (U V : RegularName P X) : RegularName P X where
  holds p x := ∀ q : P, q ≤ p → U.holds q x → V.holds q x
  persistent hqp h r hrq := h r (hrq.trans hqp)
  of_dense p x h q hqp hq := by
    apply V.of_dense q x
    intro r hrq
    obtain ⟨s, hsr, hs⟩ := h r (hrq.trans hqp)
    exact ⟨s, hsr, hs s le_rfl (U.persistent (hsr.trans hrq) hq)⟩

def reindex {Y : Type} (U : RegularName P X) (f : Y → X) : RegularName P Y where
  holds p y := U.holds p (f y)
  persistent := U.persistent
  of_dense p y := U.of_dense p (f y)

theorem not_holds_iff_exists_neg (U : RegularName P X) (p : P) (x : X) :
    ¬U.holds p x ↔ ∃ q : P, q ≤ p ∧ (neg U).holds q x := by
  classical
  constructor
  · intro h
    have hd : ¬DenseTruth U.holds p x := fun hd => h (U.of_dense p x hd)
    unfold DenseTruth at hd
    push Not at hd
    exact hd
  · rintro ⟨q, hqp, hq⟩ hp
    exact hq q le_rfl (U.persistent hqp hp)

theorem neg_neg (U : RegularName P X) : neg (neg U) = U := by
  apply RegularName.ext
  intro p x
  constructor
  · intro h
    by_contra hp
    obtain ⟨q, hqp, hq⟩ := (not_holds_iff_exists_neg U p x).mp hp
    exact h q hqp hq
  · intro hp q hqp hq
    exact hq q le_rfl (U.persistent hqp hp)

theorem exists_deciding_refinement (U : RegularName P X) (p : P) (x : X) :
    ∃ q : P, q ≤ p ∧ (U.holds q x ∨ (neg U).holds q x) := by
  classical
  by_cases hp : U.holds p x
  · exact ⟨p, le_rfl, Or.inl hp⟩
  · obtain ⟨q, hqp, hq⟩ := (not_holds_iff_exists_neg U p x).mp hp
    exact ⟨q, hqp, Or.inr hq⟩

theorem join_of_holds {I : Type} (U : I → RegularName P X) {p : P} {x : X}
    (i : I) (h : (U i).holds p x) : (join U).holds p x :=
  fun q hqp => ⟨q, le_rfl, i, (U i).persistent hqp h⟩

theorem neg_join {I : Type} (U : I → RegularName P X) :
    neg (join U) = all (fun i => neg (U i)) := by
  apply RegularName.ext
  intro p x
  constructor
  · intro h i q hqp hq
    exact h q hqp (join_of_holds U i hq)
  · intro h q hqp hq
    obtain ⟨r, hrq, i, hr⟩ := hq q le_rfl
    exact h i r (hrq.trans hqp) hr

theorem ground_join {I : Type} (s : I → Set X) :
    join (fun i => ground (P := P) (s i)) = ground (⋃ i, s i) := by
  apply RegularName.ext
  intro p x
  constructor
  · intro h
    obtain ⟨q, _, i, hi⟩ := h p le_rfl
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact join_of_holds _ i hi

end Erdos1172Part3RegularMembership
