/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.ForMathlib.SetTheory.Cardinal.SmallUnionCode
public import Erdos1172.ForMathlib.SetTheory.Cardinal.GCHConsequences1172
public import Erdos1172.ForMathlib.SetTheory.Ordinal.ClubClosure
public import Erdos1172.ForMathlib.SetTheory.Ordinal.ErdosRadoCHAsymmetric

@[expose] public section

open Cardinal Ordinal Set Function Order

namespace Erdos1172Part3NeighborhoodCode

abbrev W2 : Type := (ω_ 2 : Ordinal.{0}).ToType
abbrev Atom : Type := Fin 3 × W2
abbrev Code : Type := SmallUnionCode.Code ℕ Atom

theorem cof_W2 : Order.cof W2 = ℵ_ 2 := by
  rw [Ordinal.cof_toType]
  have hreg : (ℵ_ 2 : Cardinal.{0}).IsRegular := by
    convert Cardinal.isRegular_aleph_add_one 1 using 1 <;> norm_num
  simpa only [Cardinal.ord_aleph] using hreg.cof_ord

instance : IsRegularCardinalOrder W2 where
  type_lt_le_ord_cof := by rw [cof_W2, Cardinal.ord_aleph, Ordinal.type_toType]

theorem alephZero_lt_cof_W2 : ℵ₀ < Order.cof W2 := by
  rw [cof_W2]
  exact Cardinal.aleph0_lt_aleph.mpr (by norm_num)

theorem mk_Code_le (hGCH : GCH) : #Code ≤ ℵ_ 2 := by
  refine SmallUnionCode.mk_code_le (μ := ℵ₀) Cardinal.one_le_aleph0
    (Cardinal.aleph0_le_aleph 2) Cardinal.mk_nat.le ?_ hGCH.aleph_two_power_aleph_zero.le
  simp only [Atom, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_fin,
    W2, Cardinal.mk_toType, Ordinal.card_omega]
  exact (mul_le_mul' (Cardinal.natCast_le_aleph0.trans (Cardinal.aleph0_le_aleph 2)) le_rfl).trans_eq
    (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 2))

noncomputable def rank (hGCH : GCH) : Code ↪ W2 :=
  Classical.choice ((Cardinal.le_def Code W2).mp (by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using mk_Code_le hGCH))

def atoms (G H : SimpleGraph W2) : Atom → Set W2
  | (0, x) => {y | G.Adj x y}
  | (1, x) => {y | H.Adj x y}
  | (2, x) => Set.Iic x

def eval (G H : SimpleGraph W2) : Code → Set W2 := SmallUnionCode.eval (atoms G H)

abbrev LocalCode (r : Code ↪ W2) (a : W2) := {c : Code // r c < a}

theorem mk_LocalCode_le (r : Code ↪ W2) (a : W2) : #(LocalCode r a) ≤ ℵ_ 1 := by
  refine (Cardinal.mk_le_of_injective (f := fun c : LocalCode r a =>
    (⟨r c.val, c.property⟩ : Set.Iio a)) fun c d h =>
      Subtype.ext (r.injective (congrArg Subtype.val h))).trans ?_
  apply Order.lt_succ_iff.mp
  simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega,
    Cardinal.succ_aleph, show (1 : Ordinal) + 1 = 2 by norm_num] using
    Cardinal.mk_Iio_lt a (Cardinal.ord_cardinalMk (α := W2))

theorem exists_unionBound (hCH : CH) (r : Code ↪ W2) (a : W2) :
    ∃ b : W2, ∀ c : ℕ → LocalCode r a,
      r (SmallUnionCode.union (fun i => (c i).val)) < b := by
  have hcard : #(Set.range (fun c : ℕ → LocalCode r a =>
      r (SmallUnionCode.union (fun i => (c i).val)))) ≤ ℵ_ 1 := by
    refine Cardinal.mk_range_le.trans ?_
    rw [Cardinal.mk_arrow]; simp only [Cardinal.lift_id, Cardinal.mk_nat]
    exact (Cardinal.power_le_power_right (mk_LocalCode_le r a)).trans_eq
      hCH.aleph_one_power_aleph_zero
  have hsmall := cof_W2 ▸ hcard.trans_lt (Cardinal.aleph_lt_aleph.mpr (by norm_num : (1 : Ordinal) < 2))
  obtain ⟨b, hb⟩ := not_isCofinal_iff.mp (fun hc => hsmall.not_ge (Order.cof_le hc))
  exact ⟨b, fun c => hb _ ⟨c, rfl⟩⟩

noncomputable def unionBound (hCH : CH) (r : Code ↪ W2) (a : W2) : W2 :=
  (exists_unionBound hCH r a).choose

theorem unionBound_spec (hCH : CH) (r : Code ↪ W2) (a : W2)
    (c : ℕ → LocalCode r a) :
    r (SmallUnionCode.union (fun i => (c i).val)) < unionBound hCH r a :=
  (exists_unionBound hCH r a).choose_spec c

theorem union_rank_lt_of_closedUnder (hCH : CH) (r : Code ↪ W2)
    {a : W2} (ha : ErdosRadoCHAsym.IsOmegaOneSup a)
    (hclosed : ClubClosure.ClosedUnder (unionBound hCH r) a)
    (c : ℕ → Code) (hc : ∀ i, r (c i) < a) :
    r (SmallUnionCode.union c) < a := by
  obtain ⟨b, hba, hb⟩ :=
    ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup ha
      (seed := Set.range (fun i => r (c i)))
      (by simpa only [Cardinal.mk_nat] using Cardinal.mk_range_le (f := fun i => r (c i)))
      (by rintro _ ⟨i, rfl⟩; exact hc i)
  exact (unionBound_spec hCH r b (fun i => ⟨c i, hb _ ⟨i, rfl⟩⟩)).trans (hclosed b hba)

structure GoodCut (r : Code ↪ W2) (G H : SimpleGraph W2) (a : W2) : Prop where
  isOmegaOneSup : ErdosRadoCHAsym.IsOmegaOneSup a
  empty_lt : r SmallUnionCode.empty < a
  compl_lt : ∀ c, r c < a → r (SmallUnionCode.compl c) < a
  union_lt : ∀ c : ℕ → Code, (∀ i, r (c i) < a) → r (SmallUnionCode.union c) < a
  atom_lt : ∀ k : Fin 3, ∀ x < a, r (SmallUnionCode.atom (k, x)) < a
  reflects_univ : ∀ c, r c < a → Set.Iio a ⊆ eval G H c → Set.univ ⊆ eval G H c

theorem exists_club_goodCut (hCH : CH) (r : Code ↪ W2) (G H : SimpleGraph W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club,
      ErdosRadoCHAsym.IsOmegaOneSup a → GoodCut r G H a := by
  have hcof := alephZero_lt_cof_W2
  have hca : IsClub (⋂ k : Fin 3, {a | ClubClosure.ClosedUnder (fun x => r (SmallUnionCode.atom (k, x))) a}) :=
    IsClub.iInter_of_countable hcof.ne' fun k =>
      ClubClosure.isClub_closedUnder (fun x => r (SmallUnionCode.atom (k, x))) hcof
  have hcc := ClubClosure.isClub_rankClosed r (fun c => r (SmallUnionCode.compl c)) hcof
  have hcu := ClubClosure.isClub_closedUnder (unionBound hCH r) hcof
  have hce := ClubClosure.isClub_closedUnder (fun _ => r SmallUnionCode.empty) hcof
  obtain ⟨cr, hcr, hr⟩ := ClubClosure.exists_club_reflects r (eval G H) Set.univ hcof
  refine ⟨_, (((hca.inter hcof.ne' hcc).inter hcof.ne' hcu).inter hcof.ne' hce).inter hcof.ne' hcr, ?_⟩
  rintro a ⟨⟨⟨⟨ha, hc⟩, hu⟩, he⟩, hr'⟩ hsup
  obtain ⟨b, hba, _⟩ := ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup hsup
    (seed := ∅) (by simp) (by simp)
  exact ⟨hsup, he b hba, hc, union_rank_lt_of_closedUnder hCH r hsup hu,
    fun k x hx => (Set.mem_iInter.mp ha k) x hx,
    fun c hc' hsub => hr a hr' c hc' (by simpa only [Set.univ_inter] using hsub)⟩

theorem isStationary_goodCut (hCH : CH) (r : Code ↪ W2) (G H : SimpleGraph W2) :
    IsStationary {a | GoodCut r G H a} := by
  obtain ⟨club, hclub, hgood⟩ := exists_club_goodCut hCH r G H
  intro test htest
  obtain ⟨a, hsup, ha, hatest⟩ := ErdosRadoCHAsym.isStationary_isOmegaOneSup_omegaTwo
    (hclub.inter alephZero_lt_cof_W2.ne' htest)
  exact ⟨a, hgood a ha hsup, hatest⟩

end Erdos1172Part3NeighborhoodCode
