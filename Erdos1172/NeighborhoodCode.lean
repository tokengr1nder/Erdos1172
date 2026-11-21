/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Cardinal.SmallUnionCode
public import Erdos1172.ForMathlib.SetTheory.Ordinal.ClubClosure
public import Erdos1172.ForMathlib.SetTheory.Ordinal.ErdosRadoGCHAsymmetric

@[expose] public section

/-!
# Global neighborhood codes for Part 2
-/

open Cardinal Ordinal Set Function Order

namespace Erdos1172NeighborhoodCode

abbrev W1 : Type := (ω_ 1 : Ordinal.{0}).ToType
abbrev W3 : Type := (ω_ 3 : Ordinal.{0}).ToType
abbrev Atom : Type := Fin 3 × W3
abbrev Code : Type := SmallUnionCode.Code W1 Atom

theorem cof_W3 : Order.cof W3 = ℵ_ 3 := by
  rw [Ordinal.cof_toType]
  have hreg : (ℵ_ 3 : Cardinal.{0}).IsRegular := by
    convert Cardinal.isRegular_aleph_add_one 2 using 1 <;> norm_num
  simpa only [Cardinal.ord_aleph] using hreg.cof_ord

instance : IsRegularCardinalOrder W3 where
  type_lt_le_ord_cof := by rw [cof_W3, Cardinal.ord_aleph, Ordinal.type_toType]

theorem alephZero_lt_cof_W3 : ℵ₀ < Order.cof W3 := by
  rw [cof_W3, ← Cardinal.aleph_zero]
  exact Cardinal.aleph_lt_aleph.mpr (by norm_num)

theorem mk_taggedCode_le {K : Type} [Countable K] (hGCH : GCH) :
    #(SmallUnionCode.Code W1 (K × W3)) ≤ ℵ_ 3 := by
  apply SmallUnionCode.mk_code_le (μ := ℵ_ 1)
    (Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_aleph 1))
    (Cardinal.aleph0_le_aleph 3)
  · simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl]
  · simp only [Cardinal.mk_prod, Cardinal.lift_id, W3, Cardinal.mk_toType, Ordinal.card_omega]
    calc #K * ℵ_ 3 ≤ ℵ_ 3 * ℵ_ 3 := mul_le_mul'
          (Cardinal.mk_le_aleph0.trans (Cardinal.aleph0_le_aleph 3)) le_rfl
      _ = ℵ_ 3 := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 3)
  · exact hGCH.aleph_three_power_aleph_one.le

theorem mk_Code_le (hGCH : GCH) : #Code ≤ ℵ_ 3 := mk_taggedCode_le hGCH

noncomputable def rank (hGCH : GCH) : Code ↪ W3 :=
  Classical.choice ((Cardinal.le_def Code W3).mp (by
    simpa only [W3, Cardinal.mk_toType, Ordinal.card_omega] using mk_Code_le hGCH))

def atoms (G H : SimpleGraph W3) : Atom → Set W3
  | (0, x) => {y | G.Adj x y}
  | (1, x) => {y | H.Adj x y}
  | (2, x) => Set.Iic x

def eval (G H : SimpleGraph W3) : Code → Set W3 :=
  SmallUnionCode.eval (atoms G H)

theorem mk_le_alephOne_of_lt_alephTwo {J : Type} (hJ : #J < ℵ_ 2) :
    #J ≤ ℵ_ 1 := by
  apply Order.lt_succ_iff.mp
  convert hJ using 1
  rw [Cardinal.succ_aleph]; norm_num

theorem mk_localCode_le_gen {C : Type} (r : C ↪ W3) (a : W3) :
    #{c : C // r c < a} ≤ ℵ_ 2 := by
  refine (Cardinal.mk_le_of_injective (f := fun c : {c : C // r c < a} =>
    (⟨r c.val, c.property⟩ : Set.Iio a)) fun c d h =>
      Subtype.ext (r.injective (congrArg Subtype.val h))).trans ?_
  apply Order.lt_succ_iff.mp
  simpa only [W3, Cardinal.mk_toType, Ordinal.card_omega,
    Cardinal.succ_aleph, show (2 : Ordinal) + 1 = 3 by norm_num] using
    Cardinal.mk_Iio_lt a (Cardinal.ord_cardinalMk (α := W3))

abbrev LocalCode (r : Code ↪ W3) (a : W3) := {c : Code // r c < a}

theorem mk_LocalCode_le (r : Code ↪ W3) (a : W3) :
    #(LocalCode r a) ≤ ℵ_ 2 := mk_localCode_le_gen r a

theorem mk_unionRanks_le_gen {B : Type} (hGCH : GCH)
    (r : SmallUnionCode.Code W1 B ↪ W3) (a : W3) :
    #(Set.range (fun c : W1 → {c // r c < a} =>
      r (SmallUnionCode.union (fun i => (c i).val)))) ≤ ℵ_ 2 := by
  refine Cardinal.mk_range_le.trans ?_
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
  exact (Cardinal.power_le_power_right (mk_localCode_le_gen r a)).trans_eq
    hGCH.aleph_two_power_aleph_one

theorem exists_unionBound_gen {B : Type} (hGCH : GCH)
    (r : SmallUnionCode.Code W1 B ↪ W3) (a : W3) :
    ∃ b : W3, ∀ c : W1 → {c // r c < a},
      r (SmallUnionCode.union (fun i => (c i).val)) < b := by
  have hsmall := (mk_unionRanks_le_gen hGCH r a).trans_lt
    (Cardinal.aleph_lt_aleph.mpr (by norm_num : (2 : Ordinal) < 3))
  rw [← cof_W3] at hsmall
  obtain ⟨b, hb⟩ := not_isCofinal_iff.mp (fun hc => hsmall.not_ge (Order.cof_le hc))
  exact ⟨b, fun c => hb _ ⟨c, rfl⟩⟩

theorem exists_unionBound (hGCH : GCH) (r : Code ↪ W3) (a : W3) :
    ∃ b : W3, ∀ c : W1 → LocalCode r a,
      r (SmallUnionCode.union (fun i => (c i).val)) < b :=
  exists_unionBound_gen hGCH r a

noncomputable def unionBound (hGCH : GCH) (r : Code ↪ W3) (a : W3) : W3 :=
  (exists_unionBound hGCH r a).choose

theorem unionBound_spec (hGCH : GCH) (r : Code ↪ W3) (a : W3)
    (c : W1 → LocalCode r a) :
    r (SmallUnionCode.union (fun i => (c i).val)) < unionBound hGCH r a :=
  (exists_unionBound hGCH r a).choose_spec c

theorem union_rank_lt_gen {B : Type} (hGCH : GCH)
    (r : SmallUnionCode.Code W1 B ↪ W3) {a : W3}
    (ha : ErdosRadoGCHAsym.IsOmegaTwoSup a)
    (hclosed : ClubClosure.ClosedUnder (fun x => (exists_unionBound_gen hGCH r x).choose) a)
    (c : W1 → SmallUnionCode.Code W1 B) (hc : ∀ i, r (c i) < a) :
    r (SmallUnionCode.union c) < a := by
  obtain ⟨b, hba, hb⟩ :=
    ErdosRadoGCHAsym.exists_strict_bound_of_small_of_IsOmegaTwoSup ha
      (seed := Set.range (fun i => r (c i)))
      (by simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
        Cardinal.mk_range_le (f := fun i => r (c i)))
      (by rintro _ ⟨i, rfl⟩; exact hc i)
  exact ((exists_unionBound_gen hGCH r b).choose_spec
    (fun i => ⟨c i, hb _ ⟨i, rfl⟩⟩)).trans (hclosed b hba)

theorem union_rank_lt_of_closedUnder (hGCH : GCH) (r : Code ↪ W3)
    {a : W3} (ha : ErdosRadoGCHAsym.IsOmegaTwoSup a)
    (hclosed : ClubClosure.ClosedUnder (unionBound hGCH r) a)
    (c : W1 → Code) (hc : ∀ i, r (c i) < a) :
    r (SmallUnionCode.union c) < a :=
  union_rank_lt_gen hGCH r ha hclosed c hc

theorem exists_club_taggedCut {K : Type} [Countable K] (hGCH : GCH)
    (r : SmallUnionCode.Code W1 (K × W3) ↪ W3) (atms : K × W3 → Set W3) :
    ∃ club : Set W3, IsClub club ∧ ∀ a ∈ club,
      ErdosRadoGCHAsym.IsOmegaTwoSup a →
      r SmallUnionCode.empty < a ∧
      (∀ c, r c < a → r (SmallUnionCode.compl c) < a) ∧
      (∀ c : W1 → SmallUnionCode.Code W1 (K × W3), (∀ i, r (c i) < a) →
        r (SmallUnionCode.union c) < a) ∧
      (∀ k : K, ∀ x < a, r (SmallUnionCode.atom (k, x)) < a) ∧
      (∀ c, r c < a → Set.Iio a ⊆ SmallUnionCode.eval atms c →
        Set.univ ⊆ SmallUnionCode.eval atms c) := by
  have hcof := alephZero_lt_cof_W3
  have hca : IsClub (⋂ k : K, {a | ClubClosure.ClosedUnder (fun x => r (SmallUnionCode.atom (k, x))) a}) :=
    IsClub.iInter_of_countable hcof.ne' fun k =>
      ClubClosure.isClub_closedUnder (fun x => r (SmallUnionCode.atom (k, x))) hcof
  have hcc := ClubClosure.isClub_rankClosed r (fun c => r (SmallUnionCode.compl c)) hcof
  have hcu := ClubClosure.isClub_closedUnder (fun x => (exists_unionBound_gen hGCH r x).choose) hcof
  have hce := ClubClosure.isClub_closedUnder (fun _ => r SmallUnionCode.empty) hcof
  obtain ⟨cr, hcr, hr⟩ := ClubClosure.exists_club_reflects r (SmallUnionCode.eval atms) Set.univ hcof
  refine ⟨_, (((hca.inter hcof.ne' hcc).inter hcof.ne' hcu).inter hcof.ne' hce).inter hcof.ne' hcr, ?_⟩
  rintro a ⟨⟨⟨⟨ha, hc⟩, hu⟩, he⟩, hr'⟩ hsup
  obtain ⟨b, hba, _⟩ := ErdosRadoGCHAsym.exists_strict_bound_of_small_of_IsOmegaTwoSup hsup
    (seed := ∅) (by simp) (by simp)
  exact ⟨he b hba, hc, union_rank_lt_gen hGCH r hsup hu,
    fun k x hx => (Set.mem_iInter.mp ha k) x hx,
    fun c hc' hsub => hr a hr' c hc' (by simpa only [Set.univ_inter] using hsub)⟩

structure GoodCut (r : Code ↪ W3) (G H : SimpleGraph W3) (a : W3) : Prop where
  isOmegaTwoSup : ErdosRadoGCHAsym.IsOmegaTwoSup a
  empty_lt : r SmallUnionCode.empty < a
  compl_lt : ∀ c, r c < a → r (SmallUnionCode.compl c) < a
  union_lt : ∀ c : W1 → Code, (∀ i, r (c i) < a) →
    r (SmallUnionCode.union c) < a
  atom_lt : ∀ k : Fin 3, ∀ x < a, r (SmallUnionCode.atom (k, x)) < a
  reflects_univ : ∀ c, r c < a → Set.Iio a ⊆ eval G H c →
    Set.univ ⊆ eval G H c

theorem exists_club_goodCut (hGCH : GCH) (r : Code ↪ W3)
    (G H : SimpleGraph W3) :
    ∃ club : Set W3, IsClub club ∧ ∀ a ∈ club,
      ErdosRadoGCHAsym.IsOmegaTwoSup a → GoodCut r G H a := by
  obtain ⟨club, hclub, hg⟩ := exists_club_taggedCut hGCH r (atoms G H)
  exact ⟨club, hclub, fun a ha hsup =>
    let ⟨he, hc, hu, hat, hrefl⟩ := hg a ha hsup
    ⟨hsup, he, hc, hu, hat, hrefl⟩⟩

theorem isStationary_goodCut (hGCH : GCH) (r : Code ↪ W3)
    (G H : SimpleGraph W3) : IsStationary {a | GoodCut r G H a} := by
  obtain ⟨club, hclub, hgood⟩ := exists_club_goodCut hGCH r G H
  intro test htest
  obtain ⟨a, hsup, ha, hatest⟩ :=
    ErdosRadoGCHAsym.isStationary_isOmegaTwoSup_omegaThree
      (hclub.inter alephZero_lt_cof_W3.ne' htest)
  exact ⟨a, hgood a ha hsup, hatest⟩

end Erdos1172NeighborhoodCode
