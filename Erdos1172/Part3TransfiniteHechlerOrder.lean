/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3SparseIterationCarriers
public import Erdos1172.Part3NiceFunctionDictionaries

@[expose] public section

/-!
# A recursively defined order at every cutoff through omegaTwo

The carriers are fixed sparse functions. At coordinate `i`, side codes
are interpreted as nice function names for the actual earlier order at
`i`. Well-founded recursion constructs those earlier orders and their
exact name dictionaries. The recursion is totalized on incoherent input;
well-founded induction proves that the totalization branch is never used
by the constructed stages. Closure and successor identification are
separate obligations, not assumptions of this construction.
-/

open Cardinal Ordinal Set

namespace Erdos1172Part3TransfiniteHechlerOrder

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3SparseIterationCarriers
open Erdos1172Part3NiceFunctionNames
open Erdos1172Part3NiceFunctionDictionaries (dictionary)
open Erdos1172Part3FunctionDecisions

structure NamedOrder (a : Cut) where
  order : Preorder (Carrier a)
  top_le : ∀ p : Carrier a, @LE.le _ order.toLE p (empty a)
  decode : W2 ≃ @NiceFunctionName (Carrier a) W1 W1 order

def NamedOrder.Le {a : Cut} (R : NamedOrder a) (q p : Carrier a) : Prop :=
  @LE.le _ R.order.toLE q p

def NamedOrder.Bound {a : Cut} (R : NamedOrder a) (c : W2)
    (p : Carrier a) (j v : W1) : Prop :=
  letI := R.order
  BoundedAt (R.decode c).toDecisions p j v

theorem NamedOrder.bound_mono {a : Cut} (R : NamedOrder a) {c : W2}
    {q p : Carrier a} {j v : W1} (h : R.Bound c p j v) (hqp : R.Le q p) :
    R.Bound c q j v := by
  let := R.order
  exact boundedAt_mono h hqp

def DatumExtends {a : Cut} (R : NamedOrder a) (base : Carrier a)
    (new old : Datum) : Prop :=
  (∀ j v, old.val.1.val j = some v → new.val.1.val j = some v) ∧
    old.val.2.val ⊆ new.val.2.val ∧
    ∀ j, old.val.1.val j = none → ∀ v, new.val.1.val j = some v →
      ∀ c ∈ old.val.2.val, R.Bound c base j v

theorem datumExtends_refl {a : Cut} (R : NamedOrder a) (base : Carrier a) (d : Datum) :
    DatumExtends R base d d := by
  refine ⟨fun _ _ h => h, Set.Subset.rfl, ?_⟩
  intro j hj v hv _ _
  rw [hj] at hv
  cases hv

theorem datumExtends_trans {a : Cut} (R : NamedOrder a) {q p : Carrier a}
    (hqp : R.Le q p) {d e f : Datum}
    (hde : DatumExtends R q d e) (hef : DatumExtends R p e f) :
    DatumExtends R q d f := by
  refine ⟨fun j v hv => hde.1 j v (hef.1 j v hv), hef.2.1.trans hde.2.1, ?_⟩
  intro j hfj v hdj c hcf
  cases hej : e.val.1.val j with
  | none => exact hde.2.2 j hej v hdj c (hef.2.1 hcf)
  | some w =>
    have hdw := hde.1 j w hej
    have hwv : w = v := Option.some.inj (hdw.symm.trans hdj)
    rw [← hwv]
    exact R.bound_mono (hef.2.2 j hfj w hej c hcf) hqp

def StrongerWith {a : Cut} (prev : ∀ b : Cut, b < a → NamedOrder b)
    (q p : Carrier a) : Prop :=
  ∀ (i : W2) (hi : (i : Cut) < a) (d : Datum), value p i = some d →
    ∃ e : Datum, value q i = some e ∧
      DatumExtends (prev (i : Cut) hi) (truncate q.val (i : Cut)) e d

def Coherent {a : Cut} (prev : ∀ b : Cut, b < a → NamedOrder b) : Prop :=
  ∀ (b : Cut) (hb : b < a) (q p : Carrier b),
    (prev b hb).Le q p ↔ StrongerWith (fun c hc => prev c (hc.trans hb)) q p

theorem strongerWith_refl {a : Cut} (prev : ∀ b : Cut, b < a → NamedOrder b)
    (p : Carrier a) : StrongerWith prev p p := by
  intro i hi d hd
  exact ⟨d, hd, datumExtends_refl _ _ d⟩

theorem strongerWith_restrict {a : Cut} (prev : ∀ b : Cut, b < a → NamedOrder b)
    (hc : Coherent prev) {q p : Carrier a} (hqp : StrongerWith prev q p)
    (b : Cut) (hb : b < a) :
    (prev b hb).Le (truncate q.val b) (truncate p.val b) := by
  classical
  apply (hc b hb _ _).mpr
  intro i hi d hd
  rw [value_truncate, if_pos hi] at hd
  obtain ⟨e, he, hde⟩ := hqp i (hi.trans hb) d hd
  refine ⟨e, ?_, ?_⟩
  · rw [value_truncate, if_pos hi]
    exact he
  · simpa only [truncate_truncate q.val hi.le] using hde

theorem strongerWith_trans {a : Cut} (prev : ∀ b : Cut, b < a → NamedOrder b)
    (hc : Coherent prev) {p q r : Carrier a}
    (hpq : StrongerWith prev p q) (hqr : StrongerWith prev q r) :
    StrongerWith prev p r := by
  intro i hi d hd
  obtain ⟨e, he, hed⟩ := hqr i hi d hd
  obtain ⟨f, hf, hfe⟩ := hpq i hi e he
  exact ⟨f, hf, datumExtends_trans _ (strongerWith_restrict prev hc hpq _ hi) hfe hed⟩

theorem strongerWith_empty {a : Cut} (prev : ∀ b : Cut, b < a → NamedOrder b)
    (p : Carrier a) : StrongerWith prev p (empty a) := by
  intro i hi d hd
  cases hd

@[instance_reducible] def generatedPreorder {a : Cut}
    (prev : ∀ b : Cut, b < a → NamedOrder b)
    (hc : Coherent prev) : Preorder (Carrier a) where
  le := StrongerWith prev
  le_refl := strongerWith_refl prev
  le_trans := fun _ _ _ => strongerWith_trans prev hc

noncomputable def generatedOrder (hGCH : GCH) {a : Cut}
    (prev : ∀ b : Cut, b < a → NamedOrder b) (hc : Coherent prev) : NamedOrder a := by
  letI := generatedPreorder prev hc
  exact ⟨generatedPreorder prev hc, strongerWith_empty prev,
    dictionary hGCH (mk_carrier_le hGCH a) (empty a) (strongerWith_empty prev)⟩

@[instance_reducible] def flatPreorder (a : Cut) : Preorder (Carrier a) where
  le _ _ := True
  le_refl _ := True.intro
  le_trans _ _ _ _ _ := True.intro

noncomputable def flatOrder (hGCH : GCH) (a : Cut) : NamedOrder a := by
  letI := flatPreorder a
  exact ⟨flatPreorder a, fun _ => True.intro,
    dictionary hGCH (mk_carrier_le hGCH a) (empty a) (fun _ => True.intro)⟩

noncomputable def step (hGCH : GCH) (a : Cut)
    (prev : ∀ b : Cut, b < a → NamedOrder b) : NamedOrder a := by
  classical
  exact if hc : Coherent prev then generatedOrder hGCH prev hc else flatOrder hGCH a

theorem step_le_iff (hGCH : GCH) {a : Cut}
    (prev : ∀ b : Cut, b < a → NamedOrder b) (hc : Coherent prev) (q p : Carrier a) :
    (step hGCH a prev).Le q p ↔ StrongerWith prev q p := by
  classical
  rw [step, dif_pos hc]
  rfl

noncomputable def stage (hGCH : GCH) : ∀ a : Cut, NamedOrder a :=
  wellFounded_lt.fix (step hGCH)

theorem stage_eq (hGCH : GCH) (a : Cut) :
    stage hGCH a = step hGCH a (fun b _ => stage hGCH b) :=
  WellFounded.fix_eq wellFounded_lt (step hGCH) a

/-- Every constructed stage uses the intended coordinatewise relation.
The incoherent-input totalization does not occur on this recursion. -/
theorem stage_le_iff (hGCH : GCH) (a : Cut) (q p : Carrier a) :
    (stage hGCH a).Le q p ↔ StrongerWith (fun b _ => stage hGCH b) q p := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    have hc : Coherent (fun b (_ : b < a) => stage hGCH b) := by
      intro b hb q p
      exact ih b hb q p
    rw [stage_eq hGCH a]
    exact step_le_iff hGCH _ hc q p

theorem stage_coherent (hGCH : GCH) (a : Cut) :
    Coherent (fun b (_ : b < a) => stage hGCH b) :=
  fun b _ q p => stage_le_iff hGCH b q p

theorem stage_restrict_le (hGCH : GCH) {a : Cut} {q p : Carrier a}
    (hqp : (stage hGCH a).Le q p) (b : Cut) (hb : b < a) :
    (stage hGCH b).Le (truncate q.val b) (truncate p.val b) :=
  strongerWith_restrict _ (stage_coherent hGCH a) ((stage_le_iff hGCH a q p).mp hqp) b hb

/-- A type synonym carrying the constructed, rather than an arbitrary,
preorder. The underlying sparse condition is unchanged. -/
def Stage (_hGCH : GCH) (a : Cut) : Type := Carrier a

noncomputable instance (hGCH : GCH) (a : Cut) : Preorder (Stage hGCH a) :=
  (stage hGCH a).order

instance (hGCH : GCH) (a : Cut) : Inhabited (Stage hGCH a) := ⟨empty a⟩

theorem le_iff (hGCH : GCH) {a : Cut} (q p : Stage hGCH a) :
    q ≤ p ↔ StrongerWith (fun b _ => stage hGCH b) q p := stage_le_iff hGCH a q p

theorem mk_stage_le (hGCH : GCH) (a : Cut) : #(Stage hGCH a) ≤ ℵ_ 2 :=
  mk_carrier_le hGCH a

end Erdos1172Part3TransfiniteHechlerOrder
