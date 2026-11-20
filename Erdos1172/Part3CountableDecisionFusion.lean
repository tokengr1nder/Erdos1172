/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3DecisionSelection

@[expose] public section

/-!
# Coherent omegaOne clique decisions from countable extension

At each coordinate the countable preceding family is decided together.
A fresh vertex is chosen with actual membership, and uniqueness of the
earlier names preserves all cross edges at subsequent strengthenings.
There is no lower bound of the completed omegaOne sequence.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CountableDecisionFusion

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3DecisionSelection (exists_function_decisions_of_dense)

variable {P V : Type} [Preorder P] [LinearOrder V]

def CountableExtension (G : SimpleGraph V) (R : P → V → Prop) : Prop :=
  ∀ p : P, ∀ s : Set V, s.Countable → (∀ x ∈ s, R p x) →
    ∃ q : P, q ≤ p ∧ ∃ y : V, R q y ∧ ∀ x ∈ s, x < y ∧ G.Adj x y

abbrev PointName (R : P → V → Prop) :=
  {F : FunctionDecisions P Unit V // ∀ p v, F.decides p () v → R p v}

theorem mk_Iio_W1_le_aleph0 (i : W1) : #(Set.Iio i) ≤ ℵ₀ := by
  apply Cardinal.lt_aleph_one_iff.mp
  simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
    Cardinal.mk_Iio_lt i (by simp [W1])

theorem exists_next_point_name (hclosed : CountablyClosed P)
    (G : SimpleGraph V) (R : P → V → Prop)
    (hpersistent : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hextend : CountableExtension G R) (i : W1)
    (previous : ∀ j : W1, j < i → PointName R) :
    ∃ N : PointName R, ∀ p v, N.val.decides p () v →
      ∀ j (hj : j < i) w, (previous j hj).val.decides p () w → w < v ∧ G.Adj w v := by
  classical
  let T (p : P) (_ : Unit) (v : V) : Prop := R p v ∧
    ∀ q : P, q ≤ p → ∀ j (hj : j < i) w,
      (previous j hj).val.decides q () w → w < v ∧ G.Adj w v
  have hT : ∀ {p q u v}, q ≤ p → T p u v → T q u v := by
    intro p q u v hqp h
    exact ⟨hpersistent hqp h.1, fun s hsq => h.2 s (hsq.trans hqp)⟩
  have hTdense : ∀ p u, ∃ q : P, q ≤ p ∧ ∃ v : V, T q u v := by
    intro p u
    let F : FunctionDecisions P (Set.Iio i) V := {
      decides := fun q j v => (previous j.val j.property).val.decides q () v
      dense := fun q j => (previous j.val j.property).val.dense q ()
      persistent := fun {p q j v} hqp hv => (previous j.val j.property).val.persistent hqp hv
      unique := fun {p j v w} hv hw => (previous j.val j.property).val.unique hv hw }
    obtain ⟨q, hqp, hq⟩ := F.exists_simultaneous hclosed p (mk_Iio_W1_le_aleph0 i)
    let value (j : Set.Iio i) : V := (hq j).choose
    have hvalue (j : Set.Iio i) :
        (previous j.val j.property).val.decides q () (value j) := (hq j).choose_spec
    have hcount : (Set.range value).Countable :=
      Cardinal.le_aleph0_iff_set_countable.mp
        (Cardinal.mk_range_le.trans (mk_Iio_W1_le_aleph0 i))
    obtain ⟨r, hrq, v, hv, hcross⟩ := hextend q (Set.range value) hcount (by
      rintro x ⟨j, rfl⟩
      exact (previous j.val j.property).property q (value j) (hvalue j))
    refine ⟨r, hrq.trans hqp, v, hv, ?_⟩
    intro s hsr j hj w hw
    have heq : value ⟨j, hj⟩ = w := (previous j hj).val.unique
      ((previous j hj).val.persistent (hsr.trans hrq) (hvalue ⟨j, hj⟩)) hw
    rw [← heq]
    exact hcross _ ⟨⟨j, hj⟩, rfl⟩
  obtain ⟨N, hN⟩ := exists_function_decisions_of_dense T
    (fun {p q u v} hqp hv => hT (u := u) hqp hv) hTdense
  refine ⟨⟨N, fun p v hv => (hN p () v hv).1⟩, ?_⟩
  intro p v hv
  exact (hN p () v hv).2 p le_rfl

noncomputable def nextPointName (hclosed : CountablyClosed P)
    (G : SimpleGraph V) (R : P → V → Prop)
    (hpersistent : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hextend : CountableExtension G R) (i : W1)
    (previous : ∀ j : W1, j < i → PointName R) : PointName R :=
  (exists_next_point_name hclosed G R hpersistent hextend i previous).choose

noncomputable def pointNames (hclosed : CountablyClosed P)
    (G : SimpleGraph V) (R : P → V → Prop)
    (hpersistent : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hextend : CountableExtension G R) : W1 → PointName R :=
  WellFoundedLT.fix (nextPointName hclosed G R hpersistent hextend)

theorem pointNames_eq (hclosed : CountablyClosed P)
    (G : SimpleGraph V) (R : P → V → Prop)
    (hpersistent : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hextend : CountableExtension G R) (i : W1) :
    pointNames hclosed G R hpersistent hextend i =
      nextPointName hclosed G R hpersistent hextend i
        (fun j _ => pointNames hclosed G R hpersistent hextend j) := by
  change WellFoundedLT.fix _ i = _
  rw [WellFoundedLT.fix_eq]
  rfl

theorem pointNames_cross (hclosed : CountablyClosed P)
    (G : SimpleGraph V) (R : P → V → Prop)
    (hpersistent : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hextend : CountableExtension G R) (i j : W1) (hij : i < j)
    (p : P) (v w : V)
    (hv : (pointNames hclosed G R hpersistent hextend i).val.decides p () v)
    (hw : (pointNames hclosed G R hpersistent hextend j).val.decides p () w) :
    v < w ∧ G.Adj v w := by
  have h := (exists_next_point_name hclosed G R hpersistent hextend j
    (fun k _ => pointNames hclosed G R hpersistent hextend k)).choose_spec
  rw [pointNames_eq hclosed G R hpersistent hextend j] at hw
  exact h p w hw i hij v hv

/-- The extension hypothesis is used to construct all point decisions;
no clique-decision system is supplied as an input. -/
theorem exists_clique_decisions_of_countable_extension (hclosed : CountablyClosed P)
    (G : SimpleGraph V) (R : P → V → Prop)
    (hpersistent : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hextend : CountableExtension G R) :
    ∃ core : CliqueDecisions P W1 V G, ∀ p i v, core.decides p i v → R p v := by
  let names := pointNames hclosed G R hpersistent hextend
  let core : CliqueDecisions P W1 V G := {
    decides := fun p i v => (names i).val.decides p () v
    dense := fun p i => (names i).val.dense p ()
    persistent := fun {p q i v} hqp hv => (names i).val.persistent hqp hv
    unique := fun {p i v w} hv hw => (names i).val.unique hv hw
    ordered := fun {p i j v w} hij hv hw =>
      (pointNames_cross hclosed G R hpersistent hextend i j hij p v w hv hw).1
    adjacent := by
      intro p i j v w hij hv hw
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact (pointNames_cross hclosed G R hpersistent hextend i j hlt p v w hv hw).2
      · exact (pointNames_cross hclosed G R hpersistent hextend j i hgt p w v hw hv).2.symm }
  exact ⟨core, fun p i v hv => (names i).property p v hv⟩

end Erdos1172Part3CountableDecisionFusion
