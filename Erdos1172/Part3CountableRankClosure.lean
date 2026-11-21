/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3NeighborhoodCode

@[expose] public section

open Cardinal Ordinal Set Function Order

namespace Erdos1172Part3CountableRankClosure

open Erdos1172Part3NeighborhoodCode

abbrev Local {C : Type} (r : C ↪ W2) (a : W2) := {c : C // r c < a}

theorem mk_local_le {C : Type} (r : C ↪ W2) (a : W2) : #(Local r a) ≤ ℵ_ 1 := by
  have he : #(Local r a) ≤ #(Set.Iio a) := Cardinal.mk_le_of_injective (f := fun c : Local r a =>
      (⟨r c.val, c.property⟩ : Set.Iio a)) (by
        intro c d h
        exact Subtype.ext (r.injective (congrArg Subtype.val h)))
  apply he.trans
  apply Order.lt_succ_iff.mp
  have hlt := Cardinal.mk_Iio_lt a (Cardinal.ord_cardinalMk (α := W2))
  simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega,
    Cardinal.succ_aleph, show (1 : Ordinal) + 1 = 2 by norm_num] using hlt

theorem exists_operationBound {C : Type} (hCH : CH) (r : C ↪ W2)
    (op : (ℕ → C) → C) (a : W2) :
    ∃ b : W2, ∀ c : ℕ → Local r a, r (op (fun i => (c i).val)) < b := by
  have hcard : #(Set.range (fun c : ℕ → Local r a =>
      r (op (fun i => (c i).val)))) ≤ ℵ_ 1 := by
    refine Cardinal.mk_range_le.trans ?_
    rw [Cardinal.mk_arrow]
    simp only [Cardinal.lift_id, Cardinal.mk_nat]
    exact (Cardinal.power_le_power_right (mk_local_le r a)).trans_eq hCH.aleph_one_power_aleph_zero
  have hsmall := hcard.trans_lt (Cardinal.aleph_lt_aleph.mpr (by norm_num : (1 : Ordinal) < 2))
  rw [← cof_W2] at hsmall
  obtain ⟨b, hb⟩ := not_isCofinal_iff.mp (fun hc => hsmall.not_ge (Order.cof_le hc))
  exact ⟨b, fun c => hb _ ⟨c, rfl⟩⟩

noncomputable def operationBound {C : Type} (hCH : CH) (r : C ↪ W2)
    (op : (ℕ → C) → C) (a : W2) : W2 :=
  (exists_operationBound hCH r op a).choose

theorem operationBound_spec {C : Type} (hCH : CH) (r : C ↪ W2)
    (op : (ℕ → C) → C) (a : W2) (c : ℕ → Local r a) :
    r (op (fun i => (c i).val)) < operationBound hCH r op a :=
  (exists_operationBound hCH r op a).choose_spec c

theorem operation_rank_lt_of_closedUnder {C : Type} (hCH : CH) (r : C ↪ W2)
    (op : (ℕ → C) → C) {a : W2} (ha : ErdosRadoCHAsym.IsOmegaOneSup a)
    (hclosed : ClubClosure.ClosedUnder (operationBound hCH r op) a)
    (c : ℕ → C) (hc : ∀ i, r (c i) < a) : r (op c) < a := by
  obtain ⟨b, hba, hb⟩ :=
    ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup ha
      (seed := Set.range (fun i => r (c i))) (by
        simpa only [Cardinal.mk_nat] using (Cardinal.mk_range_le (f := fun i => r (c i)))) (by
        rintro _ ⟨i, rfl⟩
        exact hc i)
  exact (operationBound_spec hCH r op b (fun i => ⟨c i, hb _ ⟨i, rfl⟩⟩)).trans (hclosed b hba)

/-- Any countable-arity operation on a ranked type is closed locally on
a club of cuts of cofinality `omegaOne`. -/
theorem exists_club_countableClosed {C : Type} (hCH : CH) (r : C ↪ W2)
    (op : (ℕ → C) → C) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club,
      ErdosRadoCHAsym.IsOmegaOneSup a →
      ∀ c : ℕ → C, (∀ i, r (c i) < a) → r (op c) < a :=
  ⟨{a | ClubClosure.ClosedUnder (operationBound hCH r op) a},
    ClubClosure.isClub_closedUnder (operationBound hCH r op) alephZero_lt_cof_W2,
    fun _ hc ha => operation_rank_lt_of_closedUnder hCH r op ha hc⟩

end Erdos1172Part3CountableRankClosure
