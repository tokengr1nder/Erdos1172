/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3GuardedTraceFamily
public import Erdos1172.Part3NamedCenteredLoss

@[expose] public section

/-!
# Blue-derived smallness for regular trace families

An earlier cut belongs to the support only when its blue section is
positive under every strengthening of the current condition. Base
smallness is included, and countable completeness and blue-core
extraction are proved from the displayed laws of the regular family.
The family need not be proper outside the named domain.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3NamedBlueDerivedIdeal

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularNeighborhoodCode
open Erdos1172Part3RegularNamedIdeal
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3ClosedDecisionSystem (CountablyClosed)
open Erdos1172Part3NamedCenteredLoss (MonotoneSmallness)

variable {P I : Type} [Preorder P] [LinearOrder I] {G H : SimpleGraph W2}
variable {r : Code P I G ↪ W2} {σ : NiceCliqueName P I W2 G ↪ W2}
variable {source : RegularName P W2} {a : W2}

def along {X Y : Type} (F : X → RegularName P Y) (f : X → Y) : RegularName P X where
  holds p x := (F x).holds p (f x)
  persistent hqp h := (F _).persistent hqp h
  of_dense p x := (F x).of_dense p (f x)

noncomputable def fiber (H : SimpleGraph W2) (a : W2) (U : RegularName P W2) :
    RegularName P W2 := meet U (ground {x | H.Adj x a})

noncomputable def blueSection (H : SimpleGraph W2) (a b : W2) (U : RegularName P W2) :
    RegularName P W2 := meet U (ground {x | H.Adj x a ∧ x < b})

noncomputable def support (H : SimpleGraph W2) (D : RegularName P W2)
    (J : W2 → RegularName P (RegularName P W2)) (a : W2) (U : RegularName P W2) :
    RegularName P W2 :=
  meet (ground {b | b < a}) (meet D (along (fun b => neg (J b)) (fun b => blueSection H a b U)))

noncomputable def blueSmallName (r : Code P I G ↪ W2) (H : SimpleGraph W2)
    (D : RegularName P W2) (J : W2 → RegularName P (RegularName P W2)) (a : W2) :
    RegularName P (RegularName P W2) := reindex (smallName r H a) (support H D J a)

theorem blueSection_fiber_same (H : SimpleGraph W2) (a b : W2) (U : RegularName P W2) :
    blueSection H a b (fiber H a U) = blueSection H a b U := by
  apply RegularName.ext
  intro p x
  change ((U.holds p x ∧ H.Adj x a) ∧ H.Adj x a ∧ x < b) ↔
    (U.holds p x ∧ H.Adj x a ∧ x < b)
  tauto

theorem blueSection_fiber_comm (H : SimpleGraph W2) (a b c : W2) (U : RegularName P W2) :
    blueSection H a b (fiber H c U) = fiber H c (blueSection H a b U) := by
  apply RegularName.ext
  intro p x
  change ((U.holds p x ∧ H.Adj x c) ∧ H.Adj x a ∧ x < b) ↔
    ((U.holds p x ∧ H.Adj x a ∧ x < b) ∧ H.Adj x c)
  tauto

theorem blueSmall_fiber (r : Code P I G ↪ W2) (H : SimpleGraph W2)
    (D : RegularName P W2) (J : W2 → RegularName P (RegularName P W2))
    (a : W2) (U : RegularName P W2) (p : P) :
    (blueSmallName r H D J a).holds p (fiber H a U) ↔
      (blueSmallName r H D J a).holds p U := by
  have heq : support H D J a (fiber H a U) = support H D J a U := by
    apply RegularName.ext
    intro q b
    change (b < a ∧ D.holds q b ∧ (neg (J b)).holds q (blueSection H a b (fiber H a U))) ↔
      (b < a ∧ D.holds q b ∧ (neg (J b)).holds q (blueSection H a b U))
    rw [blueSection_fiber_same]
  change (smallName r H a).holds p (support H D J a (fiber H a U)) ↔ _
  rw [heq]
  rfl

theorem blueSmall_mono (D : RegularName P W2)
    (J : W2 → RegularName P (RegularName P W2)) (hmono : ∀ b, MonotoneSmallness (J b))
    (p : P) (U V : RegularName P W2) (hsub : ∀ x, (implication U V).holds p x)
    (hV : (blueSmallName r H D J a).holds p V) :
    (blueSmallName r H D J a).holds p U := by
  apply smallName_mono_set (V := support H D J a V) ?_ hV
  intro b hba q hqp hq
  refine ⟨hq.1, hq.2.1, ?_⟩
  intro s hsq hs
  apply hq.2.2 s hsq
  apply hmono b s (blueSection H a b U) (blueSection H a b V) ?_ hs
  intro x t hts ht
  exact ⟨hsub x t ((hts.trans hsq).trans hqp) ht.1, ht.2⟩

/-- A local cover at the later cut covers the support except for a
bounded initial interval. Negation of the cover at an earlier cut would
make its positive section small at the same strengthening. -/
theorem base_le_blue (hclosed : CountablyClosed P) (ha : GoodCut r σ H source a)
    (D : RegularName P W2) (J : W2 → RegularName P (RegularName P W2))
    (hbase : ∀ b p, D.holds p b → ∀ U : RegularName P W2,
      (smallName r H b).holds p U → (J b).holds p U)
    (p : P) (U : RegularName P W2) (hU : (smallName r H a).holds p U) :
    (blueSmallName r H D J a).holds p U := by
  classical
  apply (smallName r H a).of_dense p (support H D J a U)
  intro q hqp
  obtain ⟨s, hsq, c, hc, hn, hcover⟩ := hU q hqp
  have hcode : (smallName r H a).holds s (eval G H c) :=
    smallName_of_witness ⟨c, hc, hn, fun x hx t hts ht => ht⟩
  have hbound := Erdos1172Part3NamedPositiveExtension.small_ground_bounded_interval ha s hc
  let covers (n : ℕ) : RegularName P W2 := if n = 0 then eval G H c else ground (Set.Iic (r c))
  have hcovers : (smallName r H a).holds s (join covers) :=
    smallName_countable_join hclosed ha s covers (by
      intro n
      dsimp only [covers]
      split_ifs <;> assumption)
  refine ⟨s, hsq, smallName_mono_set (V := join covers) ?_ hcovers⟩
  intro b hba t hts ht
  by_cases hle : b ≤ r c
  · exact join_of_holds covers 1 hle
  have hct : (eval G H c).holds t b := by
    by_contra hnot
    obtain ⟨v, hvt, hv⟩ := (not_holds_iff_exists_neg (eval G H c) t b).mp hnot
    apply ht.2.2 v hvt
    apply hbase b v (D.persistent hvt ht.2.1) (blueSection H a b U)
    apply smallName_of_witness
    refine ⟨c, lt_of_not_ge hle, hv, ?_⟩
    intro x hxb w hwv hw
    exact hcover x (hxb.trans hba) w ((hwv.trans hvt).trans hts) hw.1
  exact join_of_holds covers 0 hct

/-- The extracted clique is genuinely blue and has exact type omegaOne.
Its named membership has one deciding condition per point. -/
theorem blue_core_of_positive (hclosed : CountablyClosed P) (ha : GoodCut r σ H source a)
    (D : RegularName P W2) (J : W2 → RegularName P (RegularName P W2))
    (hbase : ∀ b p, D.holds p b → ∀ U : RegularName P W2,
      (smallName r H b).holds p U → (J b).holds p U)
    (p : P) (U : RegularName P W2) (hU : ¬(blueSmallName r H D J a).holds p U) :
    ∃ C : Set W2, H.IsClique C ∧ typeLT C = ω_ 1 ∧
      ∀ x ∈ C, x < a ∧ H.Adj x a ∧ ∃ q : P, q ≤ p ∧ U.holds q x := by
  have hpos : ¬(smallName r H a).holds p (fiber H a U) := by
    intro h
    exact hU ((blueSmall_fiber r H D J a U p).mp
      (base_le_blue hclosed ha D J hbase p (fiber H a U) h))
  obtain ⟨q, hqp, hq⟩ := (not_holds_iff_exists_neg (smallName r H a) p (fiber H a U)).mp hpos
  obtain ⟨core, hcore⟩ := Erdos1172Part3NamedColorCore.exists_cone_color_core
    hclosed ha false (fiber H a U) q hq (fun t ht x hx => hx.2)
  obtain ⟨f, hf, hclique, horigin⟩ :=
    Erdos1172Part3CliqueConeExtension.exists_clique_map_with_origins core
      (Erdos1172Part3ClosedDenseRequirements.countablyClosed_Iic hclosed q)
      ⟨q, (show q ≤ q from le_rfl)⟩
      (by simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl])
  refine ⟨Set.range f, hclique, ?_, ?_⟩
  · simpa only [W1, Ordinal.type_toType] using Ordinal.typeLT_range_of_strictMono f hf
  · rintro x ⟨i, rfl⟩
    obtain ⟨t, _, ht⟩ := horigin i
    have h := hcore t i (f i) ht
    exact ⟨h.2.1, h.2.2, t.val, t.property.trans hqp, h.1.1⟩

theorem blueExtraction_derived (hclosed : CountablyClosed P) (ha : GoodCut r σ H source a)
    (D : RegularName P W2) (J : W2 → RegularName P (RegularName P W2))
    (hbase : ∀ b p, D.holds p b → ∀ U : RegularName P W2,
      (smallName r H b).holds p U → (J b).holds p U)
    (rows : RegularName P W2) (p0 : P) :
    Erdos1172Part3NamedCenteredFamily.BlueExtraction (blueSmallName r H D J a) H rows p0 := by
  intro p hpp0 U hsub hU
  obtain ⟨C, hC, hCt, hmem⟩ := blue_core_of_positive hclosed ha D J hbase p U hU
  exact ⟨C, hC, hCt, fun x hx => (hmem x hx).2.2⟩

end Erdos1172Part3NamedBlueDerivedIdeal
