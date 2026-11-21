/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularLeastMember

@[expose] public section

/-!
# Greedy enumeration of a regular subname of a well-order

At each stage take the least-or-empty selector of the part of the source
above all earlier selected values. An empty earlier outcome makes this
residue empty. These are regular predicates, so no simultaneous decision
of all earlier values is needed at a limit stage.

At a stopped stage, every actual source point is densely equal to an
earlier selected point. The proof uses the least possible earlier outcome
which is empty or not below that point. Thus absence of a full ordered
decision embedding on a condition cone gives a shorter complete named
enumeration on a strengthening. This does not yet construct function
names witnessing membership in the canonical finite/omega cover families.
-/

open Cardinal Ordinal Set Order Function

namespace Erdos1172Part3RegularGreedyEnumeration

open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName meet all)
open Erdos1172Part3RegularLeastMember

variable {P I V : Type} [Preorder P] [LinearOrder V]

def valueBelow : Option V → V → Prop
  | none, _ => False
  | some y, x => y < x

/-- A point lies above a selected value at every common refinement.
An empty selector outcome rules the point out. -/
def aboveRegular (E : FunctionDecisions P Unit (Option V)) : RegularName P V where
  holds p x := ∀ q : P, q ≤ p → ∀ v : Option V,
    E.decides q () v → valueBelow v x
  persistent hqp h r hrq v hv := h r (hrq.trans hqp) v hv
  of_dense p x h q hqp v hv := by
    obtain ⟨r, hrq, hr⟩ := h q hqp
    exact hr r le_rfl v (E.persistent hrq hv)

theorem aboveRegular_lt {E : FunctionDecisions P Unit (Option V)} {p : P} {x y : V}
    (h : (aboveRegular E).holds p x) (hy : E.decides p () (some y)) : y < x :=
  h p le_rfl (some y) hy

variable [LinearOrder I] [WellFoundedLT I] [WellFoundedLT V]

/-- Transfinite recursion takes a total least-or-empty selector at every
stage, including stages where the selected residue has become empty. -/
noncomputable def stage (U : RegularName P V) : I → FunctionDecisions P Unit (Option V) :=
  WellFoundedLT.fix (fun i previous =>
    leastMember (meet U (all (fun j : Set.Iio i => aboveRegular (previous j.val j.property)))))

noncomputable def residueAt (U : RegularName P V) (i : I) : RegularName P V :=
  meet U (all (fun j : Set.Iio i => aboveRegular (stage U j.val)))

theorem stage_eq (U : RegularName P V) (i : I) : stage U i = leastMember (residueAt U i) := by
  rw [stage, WellFoundedLT.fix_eq]
  rfl

theorem stage_decides_iff (U : RegularName P V) (i : I) (p : P) (v : Option V) :
    (stage U i).decides p () v ↔ LeastDecision (residueAt U i) p v := by
  rw [stage_eq]
  rfl

theorem selected_actual {U : RegularName P V} {i : I} {p : P} {x : V}
    (h : (stage U i).decides p () (some x)) : U.holds p x :=
  ((stage_decides_iff U i p (some x)).mp h).1.1

theorem selected_ordered {U : RegularName P V} {i j : I} {p : P} {x y : V}
    (hij : i < j) (hx : (stage U i).decides p () (some x))
    (hy : (stage U j).decides p () (some y)) : x < y := by
  have hres := ((stage_decides_iff U j p (some y)).mp hy).1
  exact aboveRegular_lt (hres.2 ⟨i, hij⟩) hx

theorem stopped_no_residue {U : RegularName P V} {i : I} {p q : P}
    (hstop : (stage U i).decides p () none) (hqp : q ≤ p) (x : V) :
    ¬(residueAt U i).holds q x :=
  (stage_decides_iff U i p none).mp hstop q hqp x

/-- At a stopped residue, membership has a dense exact enumeration
witness. This is stronger than bounding the fixed-condition actual set. -/
theorem stopped_covers {U : RegularName P V} {i : I} {p : P}
    (hstop : (stage U i).decides p () none) :
    ∀ q : P, q ≤ p → ∀ x : V, U.holds q x →
      ∃ r : P, r ≤ q ∧ ∃ j : Set.Iio i, (stage U j.val).decides r () (some x) := by
  classical
  intro q hqp x hx
  let bad : Set (Set.Iio i) := {j | ∃ r : P, r ≤ q ∧ ∃ v : Option V,
    (stage U j.val).decides r () v ∧ ¬valueBelow v x}
  have hbad : bad.Nonempty := by
    by_contra hnone
    have hprior : ∀ j : Set.Iio i, (aboveRegular (stage U j.val)).holds q x := by
      intro j r hrq v hv
      by_contra hnot
      exact hnone ⟨j, r, hrq, v, hv, hnot⟩
    exact stopped_no_residue hstop hqp x ⟨hx, hprior⟩
  let j : Set.Iio i := wellFounded_lt.min bad hbad
  have hj : j ∈ bad := wellFounded_lt.min_mem bad hbad
  obtain ⟨r, hrq, v, hv, hnot⟩ := hj
  have hprior : ∀ k : Set.Iio j.val, (aboveRegular (stage U k.val)).holds r x := by
    intro k t htr w hw
    by_contra hn
    let k' : Set.Iio i := ⟨k.val, k.property.trans j.property⟩
    have hk : k' ∈ bad := ⟨t, htr.trans hrq, w, hw, hn⟩
    have hjk : j ≤ k' := wellFounded_lt.min_le (s := bad) hk
    have hkj : k' < j := k.property
    exact hkj.not_ge hjk
  have hres : (residueAt U j.val).holds r x := ⟨U.persistent hrq hx, hprior⟩
  cases v with
  | none => exact (stopped_no_residue hv le_rfl x hres).elim
  | some y =>
      have hleast : LeastDecision (residueAt U j.val) r (some y) :=
        (stage_decides_iff U j.val r (some y)).mp hv
      have hyx : y ≤ x := le_of_not_gt (fun hxy => hleast.2 r le_rfl x hxy hres)
      have hxy : x ≤ y := by
        change ¬y < x at hnot
        exact le_of_not_gt hnot
      have heq : y = x := le_antisymm hyx hxy
      subst y
      exact ⟨r, hrq, j, hv⟩

/-- Remove the empty outcome on a cone where it is impossible at each
requested index. This constructs decisions, not a ground enumeration. -/
def someOnCone {J : Type} (U : RegularName P V) (p0 : P) (index : J → I)
    (hno : ∀ j : J, ∀ p : P, p ≤ p0 → ¬(stage U (index j)).decides p () none) :
    FunctionDecisions (Set.Iic p0) J V where
  decides p j x := (stage U (index j)).decides p.val () (some x)
  dense := by
    intro p j
    obtain ⟨q, hqp, v, hv⟩ := (stage U (index j)).dense p.val ()
    cases v with
    | none => exact (hno j q (hqp.trans p.property) hv).elim
    | some x => exact ⟨⟨q, hqp.trans p.property⟩, hqp, x, hv⟩
  persistent hqp h := (stage U _).persistent hqp h
  unique hv hw := Option.some.inj ((stage U _).unique hv hw)

/-- A full ordered name on the cone below p0, with actual source
membership at every decision. Incompatible conditions outside the cone
are deliberately absent from this definition. -/
def HasOrderedEmbeddingBelow (U : RegularName P V) (p0 : P) : Prop :=
  ∃ E : FunctionDecisions (Set.Iic p0) I V,
    (∀ p : Set.Iic p0, ∀ i j x y, i < j → E.decides p i x → E.decides p j y → x < y) ∧
    ∀ p : Set.Iic p0, ∀ i x, E.decides p i x → U.holds p.val x

theorem exists_stopping_refinement (U : RegularName P V) (p0 : P)
    (hno : ¬HasOrderedEmbeddingBelow (I := I) U p0) :
    ∃ i : I, ∃ q : P, q ≤ p0 ∧ (stage U i).decides q () none := by
  classical
  by_contra hstop
  have hnever : ∀ i : I, ∀ q : P, q ≤ p0 → ¬(stage U i).decides q () none :=
    fun i q hqp h => hstop ⟨i, q, hqp, h⟩
  apply hno
  refine ⟨someOnCone U p0 id hnever, ?_, ?_⟩
  · intro p i j x y hij hx hy
    exact selected_ordered hij hx hy
  · intro p i x hx
    exact selected_actual hx

/-- Stop at the least index whose empty outcome is possible. All earlier
indices remain nonempty on the resulting cone, and enumerate the whole
source there with dense equality witnesses. No closure hypothesis is used. -/
theorem exists_shorter_enumeration (U : RegularName P V) (p0 : P)
    (hno : ¬HasOrderedEmbeddingBelow (I := I) U p0) :
    ∃ q : P, q ≤ p0 ∧ ∃ i : I, ∃ E : FunctionDecisions (Set.Iic q) (Set.Iio i) V,
      (∀ p : Set.Iic q, ∀ j k x y, j < k → E.decides p j x → E.decides p k y → x < y) ∧
      (∀ p : Set.Iic q, ∀ j x, E.decides p j x → U.holds p.val x) ∧
      ∀ p : Set.Iic q, ∀ x : V, U.holds p.val x →
        ∃ r : Set.Iic q, r ≤ p ∧ ∃ j : Set.Iio i, E.decides r j x := by
  classical
  let stops : Set I := {i | ∃ q : P, q ≤ p0 ∧ (stage U i).decides q () none}
  have hs : stops.Nonempty := exists_stopping_refinement U p0 hno
  let i : I := wellFounded_lt.min stops hs
  have hi : i ∈ stops := wellFounded_lt.min_mem stops hs
  obtain ⟨q, hqp0, hstop⟩ := hi
  have hnever : ∀ j : Set.Iio i, ∀ p : P, p ≤ q → ¬(stage U j.val).decides p () none := by
    intro j p hpq hn
    have hj : j.val ∈ stops := ⟨p, hpq.trans hqp0, hn⟩
    have hij : i ≤ j.val := wellFounded_lt.min_le (s := stops) hj
    exact j.property.not_ge hij
  let E : FunctionDecisions (Set.Iic q) (Set.Iio i) V := someOnCone U q Subtype.val hnever
  refine ⟨q, hqp0, i, E, ?_, ?_, ?_⟩
  · intro p j k x y hjk hx hy
    change (stage U j.val).decides p.val () (some x) at hx
    change (stage U k.val).decides p.val () (some y) at hy
    exact selected_ordered (U := U) (i := j.val) (j := k.val) (p := p.val) hjk hx hy
  · intro p j x hx
    exact selected_actual hx
  · intro p x hx
    obtain ⟨r, hrp, j, hr⟩ := stopped_covers hstop p.val p.property x hx
    exact ⟨⟨r, hrp.trans p.property⟩, hrp, j, hr⟩

end Erdos1172Part3RegularGreedyEnumeration
