/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableDecisionFusion

@[expose] public section

/-!
# Coherent clique decisions with coordinate-specific requirements

The extra requirement at a coordinate is persistent. Countable extension
meets it together with every earlier point, and antichain selection retains
it at the actual deciding condition.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3ConstrainedDecisionFusion

open ErdosRadoCHAsym (W1)
open Erdos1172Part3CountableDecisionFusion (PointName mk_Iio_W1_le_aleph0)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed CliqueDecisions)
open Erdos1172Part3DecisionSelection (exists_function_decisions_of_dense)

variable {P V : Type} [Preorder P] [LinearOrder V]

def ControlledExtension (G : SimpleGraph V) (R : P → V → Prop)
    (K : W1 → P → V → Prop) : Prop :=
  ∀ i : W1, ∀ p : P, ∀ s : Set V, s.Countable → (∀ x ∈ s, R p x) →
    ∃ q : P, q ≤ p ∧ ∃ y : V, R q y ∧ K i q y ∧ ∀ x ∈ s, x < y ∧ G.Adj x y

theorem exists_next (hclosed : CountablyClosed P) (G : SimpleGraph V)
    (R : P → V → Prop) (K : W1 → P → V → Prop)
    (hR : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hK : ∀ {i p q v}, q ≤ p → K i p v → K i q v)
    (hextend : ControlledExtension G R K) (i : W1)
    (previous : ∀ j : W1, j < i → PointName R) :
    ∃ N : PointName R, ∀ p v, N.val.decides p () v → K i p v ∧
      ∀ j (hj : j < i) w, (previous j hj).val.decides p () w → w < v ∧ G.Adj w v := by
  classical
  let T (p : P) (_ : Unit) (v : V) : Prop := R p v ∧ K i p v ∧
    ∀ q : P, q ≤ p → ∀ j (hj : j < i) w,
      (previous j hj).val.decides q () w → w < v ∧ G.Adj w v
  have hT : ∀ {p q u v}, q ≤ p → T p u v → T q u v := by
    intro p q u v hqp h
    exact ⟨hR hqp h.1, hK hqp h.2.1, fun s hsq => h.2.2 s (hsq.trans hqp)⟩
  have hdense : ∀ p u, ∃ q : P, q ≤ p ∧ ∃ v : V, T q u v := by
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
    obtain ⟨r, hrq, v, hv, hKv, hcross⟩ := hextend i q (Set.range value) hcount (by
      rintro x ⟨j, rfl⟩
      exact (previous j.val j.property).property q (value j) (hvalue j))
    refine ⟨r, hrq.trans hqp, v, hv, hKv, ?_⟩
    intro s hsr j hj w hw
    have heq : value ⟨j, hj⟩ = w := (previous j hj).val.unique
      ((previous j hj).val.persistent (hsr.trans hrq) (hvalue ⟨j, hj⟩)) hw
    rw [← heq]
    exact hcross _ ⟨⟨j, hj⟩, rfl⟩
  obtain ⟨N, hN⟩ := exists_function_decisions_of_dense T
    (fun {p q u v} hqp hv => hT (u := u) hqp hv) hdense
  refine ⟨⟨N, fun p v hv => (hN p () v hv).1⟩, ?_⟩
  intro p v hv
  exact ⟨(hN p () v hv).2.1, (hN p () v hv).2.2 p le_rfl⟩

noncomputable def next (hclosed : CountablyClosed P) (G : SimpleGraph V)
    (R : P → V → Prop) (K : W1 → P → V → Prop)
    (hR : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hK : ∀ {i p q v}, q ≤ p → K i p v → K i q v)
    (hextend : ControlledExtension G R K) (i : W1)
    (previous : ∀ j : W1, j < i → PointName R) : PointName R :=
  (exists_next hclosed G R K hR hK hextend i previous).choose

theorem exists_controlled_clique (hclosed : CountablyClosed P) (G : SimpleGraph V)
    (R : P → V → Prop) (K : W1 → P → V → Prop)
    (hR : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hK : ∀ {i p q v}, q ≤ p → K i p v → K i q v)
    (hextend : ControlledExtension G R K) :
    ∃ core : CliqueDecisions P W1 V G, ∀ p i v, core.decides p i v → R p v ∧ K i p v := by
  let names : W1 → PointName R := WellFoundedLT.fix (next hclosed G R K hR hK hextend)
  have hnames (i : W1) : names i = next hclosed G R K hR hK hextend i (fun j _ => names j) := by
    dsimp only [names]
    rw [WellFoundedLT.fix_eq]
  have hspec (i : W1) (p : P) (v : V) (hv : (names i).val.decides p () v) :
      K i p v ∧ ∀ j (hj : j < i) w, (names j).val.decides p () w → w < v ∧ G.Adj w v := by
    rw [hnames i] at hv
    exact (exists_next hclosed G R K hR hK hextend i (fun j _ => names j)).choose_spec p v hv
  let core : CliqueDecisions P W1 V G := {
    decides := fun p i v => (names i).val.decides p () v
    dense := fun p i => (names i).val.dense p ()
    persistent := fun {p q i v} hqp hv => (names i).val.persistent hqp hv
    unique := fun {p i v w} hv hw => (names i).val.unique hv hw
    ordered := fun {p i j v w} hij hv hw => ((hspec j p w hw).2 i hij v hv).1
    adjacent := by
      intro p i j v w hij hv hw
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact ((hspec j p w hw).2 i hlt v hv).2
      · exact ((hspec i p v hv).2 j hgt w hw).2.symm }
  exact ⟨core, fun p i v hv => ⟨(names i).property p v hv, (hspec i p v hv).1⟩⟩

end Erdos1172Part3ConstrainedDecisionFusion
