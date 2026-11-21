/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NamedFinalTail
public import Erdos1172.Part3RegularLeastMember
public import Erdos1172.Part3CofinalLineCover

@[expose] public section

/-!
# Exact ground index intervals for named rows

First decide the least possible enumeration index crossing a fixed upper
cut. Every earlier index is then uniformly below that cut. A least-or-empty
decision for the actual regular row either makes the row permanently empty,
or fixes its first enumeration index. The entire row is then densely and
exactly enumerated by the resulting ground half-open interval.

Only individual decisions, well-founded least choices, and persistence are
used. Cofinality is explicit. No closure, generic model, or separate
no-maximum assumption is needed. This is a row decomposition ingredient,
not a higher-rank named covering theorem.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedRowInterval

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FunctionDecisions (FunctionDecisions)
open Erdos1172Part3RegularMembership (RegularName meet ground)
open Erdos1172Part3RegularLeastMember
open Erdos1172Part3NamedCofinality (OrderedDecisions CofinalDecisions)
open Erdos1172Part3NamedFinalTail (DenseCoverage)
open Erdos1172Part3RegularConeRestriction (onCone)
open Erdos1172Part3CofinalLineCover (LineCoverData)

variable {P I V : Type} [Preorder P] [LinearOrder I] [LinearOrder V]

/-- The actual source intersected with a fixed ground row. -/
noncomputable def rowName (data : LineCoverData V) (U : RegularName P V) (i : W1) :
    RegularName P V :=
  meet U (ground {x : V | data.row x = i})

/-- Restrict both the condition cone and the enumeration domain. -/
def intervalE (E : FunctionDecisions P I V) (q : P) (a b : I) :
    FunctionDecisions (Set.Iic q) (Set.Ico a b) V where
  decides p j x := E.decides p.val j.val x
  dense p j := by
    obtain ⟨r, hrp, x, hx⟩ := E.dense p.val j.val
    exact ⟨⟨r, hrp.trans p.property⟩, hrp, x, hx⟩
  persistent hqp h := E.persistent hqp h
  unique hx hy := E.unique hx hy

theorem intervalE_ordered (E : FunctionDecisions P I V)
    (hordered : OrderedDecisions E) (q : P) (a b : I) :
    OrderedDecisions (intervalE E q a b) := by
  intro p j k x y hjk hx hy
  exact hordered hjk hx hy

/-- Values in strict order at a common condition have indices in the same
strict order. This uses uniqueness in the equal-index case. -/
theorem index_lt_of_value_lt (E : FunctionDecisions P I V)
    (hordered : OrderedDecisions E) {p : P} {a b : I} {x y : V}
    (ha : E.decides p a x) (hb : E.decides p b y) (hxy : x < y) : a < b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact hab
  · have heq : x = y := E.unique (hab ▸ ha) hb
    exact (hxy.ne heq).elim
  · exact (lt_asymm hxy (hordered hba hb ha)).elim

variable [WellFoundedLT I]

/-- The least index which can cross the cut is attained on a refinement.
Smaller indices remain below the cut everywhere below the original cone. -/
theorem exists_least_crossing (E : FunctionDecisions P I V)
    (hcofinal : CofinalDecisions E) (p0 : P) (cut : V) :
    ∃ q : P, q ≤ p0 ∧ ∃ b : I, ∃ y : V,
      E.decides q b y ∧ cut ≤ y ∧
      ∀ r : P, r ≤ p0 → ∀ j : I, j < b → ∀ x : V, E.decides r j x → x < cut := by
  classical
  let crossing : Set I := {j | ∃ q : P, q ≤ p0 ∧ ∃ y : V,
    E.decides q j y ∧ cut ≤ y}
  have hcrossing : crossing.Nonempty := by
    obtain ⟨q, hqp0, j, y, hj, hcut⟩ := hcofinal p0 cut
    exact ⟨j, q, hqp0, y, hj, hcut⟩
  let b : I := wellFounded_lt.min crossing hcrossing
  have hb : b ∈ crossing := wellFounded_lt.min_mem crossing hcrossing
  obtain ⟨q, hqp0, y, hby, hcut⟩ := hb
  refine ⟨q, hqp0, b, y, hby, hcut, ?_⟩
  intro r hrp0 j hj x hx
  apply lt_of_not_ge
  intro hcx
  have hjcrossing : j ∈ crossing := ⟨r, hrp0, x, hx, hcx⟩
  have hbj : b ≤ j := wellFounded_lt.min_le (s := crossing) hjcrossing
  exact hj.not_ge hbj

/-- Every bounded index interval is strictly shorter than the full
well-order, through its inclusion in the proper initial segment at b. -/
theorem typeLT_Ico_lt (a b : I) : typeLT (Set.Ico a b) < typeLT I := by
  have hle : typeLT (Set.Ico a b) ≤ typeLT (Set.Iio b) :=
    Ordinal.type_mono (show Set.Ico a b ⊆ Set.Iio b from fun _ hx => hx.2)
  apply hle.trans_lt
  rw [Ordinal.type_Iio_lt]
  exact Ordinal.typein_lt_type _ b

variable [WellFoundedLT V]

/-- Densely, a row is permanently empty or has an actual complete ordered
enumeration on one fixed shorter ground interval. The nonempty case gives
the stronger strict endpoint inequality a < b. -/
theorem exists_exact_row_interval (data : LineCoverData V) (U : RegularName P V)
    (E : FunctionDecisions P I V) (hordered : OrderedDecisions E)
    (hcofinal : CofinalDecisions E)
    (hmem : ∀ p : P, ∀ j : I, ∀ x : V, E.decides p j x → U.holds p x)
    (hcover : DenseCoverage E U) (p0 : P) (i : W1) :
    ∃ q : P, q ≤ p0 ∧
      ((∀ r : P, r ≤ q → ∀ x : V, ¬(rowName data U i).holds r x) ∨
        ∃ a b : I, a < b ∧ typeLT (Set.Ico a b) < typeLT I ∧
          OrderedDecisions (intervalE E q a b) ∧
          (∀ p : Set.Iic q, ∀ j : Set.Ico a b, ∀ x : V,
            (intervalE E q a b).decides p j x → (rowName data U i).holds p.val x) ∧
          DenseCoverage (intervalE E q a b) (onCone q (rowName data U i))) := by
  obtain ⟨q, hqp0, b, y, hby, hcuty, hbefore⟩ := exists_least_crossing E hcofinal p0 (data.cut i)
  obtain ⟨r, hrq, outcome, hleast⟩ := exists_least_deciding_refinement (rowName data U i) q
  cases outcome with
  | none => exact ⟨r, hrq.trans hqp0, Or.inl hleast⟩
  | some x =>
      have hxrow : (rowName data U i).holds r x := hleast.1
      obtain ⟨s, hsr, a, hax⟩ := hcover r x hxrow.1
      have hsq : s ≤ q := hsr.trans hrq
      have hsp0 : s ≤ p0 := hsq.trans hqp0
      have hbys : E.decides s b y := E.persistent hsq hby
      have hxcut : x < data.cut i := hxrow.2 ▸ data.lt_cut_row x
      have hab : a < b := index_lt_of_value_lt E hordered hax hbys (hxcut.trans_le hcuty)
      refine ⟨s, hsp0, Or.inr ⟨a, b, hab, typeLT_Ico_lt a b,
        intervalE_ordered E hordered s a b, ?_, ?_⟩⟩
      · intro p j z hz
        have hzE : E.decides p.val j.val z := hz
        have haxp : E.decides p.val a x := E.persistent p.property hax
        have hxz : x ≤ z := by
          rcases eq_or_lt_of_le j.property.1 with haj | haj
          · exact (E.unique (haj ▸ haxp) hzE).le
          · exact (hordered haj haxp hzE).le
        have hzcut : z < data.cut i :=
          hbefore p.val (p.property.trans hsp0) j.val j.property.2 z hzE
        refine ⟨hmem p.val j.val z hzE, le_antisymm (data.row_le z i hzcut) ?_⟩
        have hrows : data.row x ≤ data.row z := data.row_mono hxz
        exact hxrow.2 ▸ hrows
      · intro p z hz
        have hzrow : (rowName data U i).holds p.val z := hz
        obtain ⟨t, htp, k, hkz⟩ := hcover p.val z hzrow.1
        have hts : t ≤ s := htp.trans p.property
        have hakt : E.decides t a x := E.persistent hts hax
        have hbty : E.decides t b y := E.persistent hts hbys
        have hak : a ≤ k := by
          apply le_of_not_gt
          intro hka
          have hzx : z < x := hordered hka hkz hakt
          exact hleast.2 t (hts.trans hsr) z hzx ((rowName data U i).persistent htp hzrow)
        have hzcut : z < data.cut i := hzrow.2 ▸ data.lt_cut_row z
        have hkb : k < b := index_lt_of_value_lt E hordered hkz hbty (hzcut.trans_le hcuty)
        exact ⟨⟨t, hts⟩, htp, ⟨k, hak, hkb⟩, hkz⟩

end Erdos1172Part3NamedRowInterval
