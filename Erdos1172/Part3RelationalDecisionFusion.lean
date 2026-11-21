/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3DecisionSelection

@[expose] public section

/-!
# Coherent decisions for persistent relations between named labels

Labels need not have a linear order, and the relation between two labels
may depend on the current condition. Countable extension and persistence
supply an omegaOne family of coherent decisions. No final omegaOne lower
bound is used. The clique versions in `Part3ConstrainedDecisionFusion` and
`Part3CountableDecisionFusion` are special cases.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RelationalDecisionFusion

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3DecisionSelection (exists_function_decisions_of_dense)

theorem mk_Iio_W1_le_aleph0 (i : W1) : #(Set.Iio i) ≤ ℵ₀ := by
  apply Cardinal.lt_aleph_one_iff.mp
  simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
    Cardinal.mk_Iio_lt i (by simp [W1])

variable {P L : Type} [Preorder P]

abbrev LabelName (R : P → L → Prop) :=
  {F : FunctionDecisions P Unit L // ∀ p v, F.decides p () v → R p v}

def RelationalExtension (R : P → L → Prop) (K : W1 → P → L → Prop)
    (J : P → L → L → Prop) : Prop :=
  ∀ i : W1, ∀ p : P, ∀ s : Set L, s.Countable → (∀ v ∈ s, R p v) →
    ∃ q : P, q ≤ p ∧ ∃ v : L, R q v ∧ K i q v ∧ ∀ w ∈ s, J q w v

theorem exists_next_label (hclosed : CountablyClosed P) (R : P → L → Prop)
    (K : W1 → P → L → Prop) (J : P → L → L → Prop)
    (hR : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hK : ∀ {i p q v}, q ≤ p → K i p v → K i q v)
    (hJ : ∀ {p q v w}, q ≤ p → J p v w → J q v w)
    (hextend : RelationalExtension R K J) (i : W1)
    (previous : ∀ j : W1, j < i → LabelName R) :
    ∃ N : LabelName R, ∀ p v, N.val.decides p () v → K i p v ∧
      ∀ j (hj : j < i) w, (previous j hj).val.decides p () w → J p w v := by
  classical
  let T (p : P) (_ : Unit) (v : L) : Prop := R p v ∧ K i p v ∧
    ∀ q : P, q ≤ p → ∀ j (hj : j < i) w,
      (previous j hj).val.decides q () w → J q w v
  have hT : ∀ {p q u v}, q ≤ p → T p u v → T q u v := by
    intro p q u v hqp h
    exact ⟨hR hqp h.1, hK hqp h.2.1, fun s hsq => h.2.2 s (hsq.trans hqp)⟩
  have hdense : ∀ p u, ∃ q : P, q ≤ p ∧ ∃ v : L, T q u v := by
    intro p u
    let F : FunctionDecisions P (Set.Iio i) L := {
      decides := fun q j v => (previous j.val j.property).val.decides q () v
      dense := fun q j => (previous j.val j.property).val.dense q ()
      persistent := fun {p q j v} hqp hv => (previous j.val j.property).val.persistent hqp hv
      unique := fun {p j v w} hv hw => (previous j.val j.property).val.unique hv hw }
    obtain ⟨q, hqp, hq⟩ := F.exists_simultaneous hclosed p (mk_Iio_W1_le_aleph0 i)
    let value (j : Set.Iio i) : L := (hq j).choose
    have hvalue (j : Set.Iio i) :
        (previous j.val j.property).val.decides q () (value j) := (hq j).choose_spec
    have hcount : (Set.range value).Countable :=
      Cardinal.le_aleph0_iff_set_countable.mp
        (Cardinal.mk_range_le.trans (mk_Iio_W1_le_aleph0 i))
    obtain ⟨r, hrq, v, hv, hKv, hcross⟩ := hextend i q (Set.range value) hcount (by
      rintro w ⟨j, rfl⟩
      exact (previous j.val j.property).property q (value j) (hvalue j))
    refine ⟨r, hrq.trans hqp, v, hv, hKv, ?_⟩
    intro s hsr j hj w hw
    have heq : value ⟨j, hj⟩ = w := (previous j hj).val.unique
      ((previous j hj).val.persistent (hsr.trans hrq) (hvalue ⟨j, hj⟩)) hw
    rw [← heq]
    exact hJ hsr (hcross _ ⟨⟨j, hj⟩, rfl⟩)
  obtain ⟨N, hN⟩ := exists_function_decisions_of_dense T
    (fun {p q u v} hqp hv => hT (u := u) hqp hv) hdense
  exact ⟨⟨N, fun p v hv => (hN p () v hv).1⟩,
    fun p v hv => ⟨(hN p () v hv).2.1, (hN p () v hv).2.2 p le_rfl⟩⟩

noncomputable def nextLabel (hclosed : CountablyClosed P) (R : P → L → Prop)
    (K : W1 → P → L → Prop) (J : P → L → L → Prop)
    (hR : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hK : ∀ {i p q v}, q ≤ p → K i p v → K i q v)
    (hJ : ∀ {p q v w}, q ≤ p → J p v w → J q v w)
    (hextend : RelationalExtension R K J) (i : W1)
    (previous : ∀ j : W1, j < i → LabelName R) : LabelName R :=
  (exists_next_label hclosed R K J hR hK hJ hextend i previous).choose

theorem exists_relational_decisions (hclosed : CountablyClosed P) (R : P → L → Prop)
    (K : W1 → P → L → Prop) (J : P → L → L → Prop)
    (hR : ∀ {p q v}, q ≤ p → R p v → R q v)
    (hK : ∀ {i p q v}, q ≤ p → K i p v → K i q v)
    (hJ : ∀ {p q v w}, q ≤ p → J p v w → J q v w)
    (hextend : RelationalExtension R K J) :
    ∃ F : FunctionDecisions P W1 L,
      (∀ p i v, F.decides p i v → R p v ∧ K i p v) ∧
      ∀ p i j v w, i < j → F.decides p i v → F.decides p j w → J p v w := by
  let names : W1 → LabelName R := WellFoundedLT.fix (nextLabel hclosed R K J hR hK hJ hextend)
  have hnames (i : W1) : names i = nextLabel hclosed R K J hR hK hJ hextend i (fun j _ => names j) := by
    dsimp only [names]
    rw [WellFoundedLT.fix_eq]
  have hspec (i : W1) (p : P) (v : L) (hv : (names i).val.decides p () v) :
      K i p v ∧ ∀ j (hj : j < i) w, (names j).val.decides p () w → J p w v := by
    rw [hnames i] at hv
    exact (exists_next_label hclosed R K J hR hK hJ hextend i (fun j _ => names j)).choose_spec p v hv
  let F : FunctionDecisions P W1 L := {
    decides := fun p i v => (names i).val.decides p () v
    dense := fun p i => (names i).val.dense p ()
    persistent := fun {p q i v} hqp hv => (names i).val.persistent hqp hv
    unique := fun {p i v w} hv hw => (names i).val.unique hv hw }
  exact ⟨F, fun p i v hv => ⟨(names i).property p v hv, (hspec i p v hv).1⟩,
    fun p i j v w hij hv hw => (hspec j p w hw).2 i hij v hv⟩

end Erdos1172Part3RelationalDecisionFusion
