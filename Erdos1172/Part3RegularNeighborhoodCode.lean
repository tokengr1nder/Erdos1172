/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3RegularCliqueNeighborhoods
public import Erdos1172.Part3RegularNeighborhoodReflection

@[expose] public section

/-!
# A small algebra of named block neighborhoods

Well-founded countable expressions are interpreted as regular membership
predicates. Block atoms use actual decisions below the current condition.
GCH bounds the syntax by alephTwo; CH and the chain condition construct
club many locally closed cuts reflecting inclusion of any regular source.
This is an algebra and reflection theorem, not a block-existence theorem.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3RegularNeighborhoodCode

open ErdosRadoCHAsym (W2)
open Erdos1172Part3RegularMembership
open Erdos1172Part3RegularCliqueNeighborhoods
open Erdos1172Part3RegularNeighborhoodReflection
open Erdos1172Part3NiceCliqueNames (NiceCliqueName)
open Erdos1172Part3StationaryDecisions (OmegaTwoCC)
open Erdos1172Part3CountableRankClosure (exists_club_countableClosed)
open Erdos1172Part3NeighborhoodCode (alephZero_lt_cof_W2)

variable {P I : Type} [Preorder P] [LinearOrder I]

abbrev Atom (P I : Type) [Preorder P] [LinearOrder I] (G : SimpleGraph W2) :=
  (Fin 3 × W2) ⊕ NiceCliqueName P I W2 G

abbrev Code (P I : Type) [Preorder P] [LinearOrder I] (G : SimpleGraph W2) :=
  SmallUnionCode.Code ℕ (Atom P I G)

def pointName (G : SimpleGraph W2) (k : Fin 3) (x : W2) : Code P I G :=
  SmallUnionCode.atom (.inl (k, x))

def blockName {G : SimpleGraph W2} (N : NiceCliqueName P I W2 G) : Code P I G :=
  SmallUnionCode.atom (.inr N)

noncomputable def atoms (G H : SimpleGraph W2) : Atom P I G → RegularName P W2
  | .inl (0, x) => ground {y | G.Adj x y}
  | .inl (1, x) => ground {y | H.Adj x y}
  | .inl (2, x) => ground (Set.Iic x)
  | .inr N => afterClique N.toClique

noncomputable def operate (G H : SimpleGraph W2) :
    (Σ n, SmallUnionCode.Arity ℕ (Atom P I G) n → RegularName P W2) → RegularName P W2
  | ⟨.inl 0, _⟩ => ground ∅
  | ⟨.inl 1, f⟩ => neg (f ())
  | ⟨.inl 2, f⟩ => join f
  | ⟨.inr b, _⟩ => atoms G H b

noncomputable def eval (G H : SimpleGraph W2) : Code P I G → RegularName P W2 :=
  WType.elim _ (operate G H)

@[simp] theorem eval_empty (G H : SimpleGraph W2) :
    eval (P := P) (I := I) G H SmallUnionCode.empty = ground ∅ := rfl

@[simp] theorem eval_compl (G H : SimpleGraph W2) (c : Code P I G) :
    eval G H (SmallUnionCode.compl c) = neg (eval G H c) := rfl

@[simp] theorem eval_union (G H : SimpleGraph W2) (c : ℕ → Code P I G) :
    eval G H (SmallUnionCode.union c) = join (fun n => eval G H (c n)) := rfl

@[simp] theorem eval_blockName (G H : SimpleGraph W2) (N : NiceCliqueName P I W2 G) :
    eval G H (blockName N) = afterClique N.toClique := rfl

theorem mk_Code_le (hGCH : GCH) (hP : #P ≤ ℵ_ 2) (hI : #I ≤ ℵ_ 1)
    (G : SimpleGraph W2) : #(Code P I G) ≤ ℵ_ 2 := by
  apply SmallUnionCode.mk_code_le (μ := ℵ₀) Cardinal.one_le_aleph0
    (Cardinal.aleph0_le_aleph 2) Cardinal.mk_nat.le
  · have hpoint : #(Fin 3 × W2) ≤ ℵ_ 2 := by
      simp only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_fin,
        W2, Cardinal.mk_toType, Ordinal.card_omega]
      exact (mul_le_mul' (Cardinal.natCast_le_aleph0.trans
        (Cardinal.aleph0_le_aleph 2)) le_rfl).trans_eq
          (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 2))
    have hblock := Erdos1172Part3CliqueNameCoding.mk_nice_clique_name_le hGCH hP hI
      (show #W2 ≤ ℵ_ 2 by simp only [W2, Cardinal.mk_toType, Ordinal.card_omega, le_refl]) G
    change #((Fin 3 × W2) ⊕ NiceCliqueName P I W2 G) ≤ ℵ_ 2
    rw [Cardinal.mk_sum]
    simp only [Cardinal.lift_id]
    exact (add_le_add hpoint hblock).trans_eq
      (Cardinal.add_eq_self (Cardinal.aleph0_le_aleph 2))
  · exact hGCH.aleph_two_power_aleph_zero.le

noncomputable def rank (hGCH : GCH) (hP : #P ≤ ℵ_ 2) (hI : #I ≤ ℵ_ 1)
    (G : SimpleGraph W2) : Code P I G ↪ W2 :=
  Classical.choice ((Cardinal.le_def _ _).mp (by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using mk_Code_le hGCH hP hI G))

noncomputable def blockRank (hGCH : GCH) (hP : #P ≤ ℵ_ 2) (hI : #I ≤ ℵ_ 1)
    (G : SimpleGraph W2) : NiceCliqueName P I W2 G ↪ W2 :=
  Classical.choice ((Cardinal.le_def _ _).mp (by
    simpa only [W2, Cardinal.mk_toType, Ordinal.card_omega] using
      Erdos1172Part3CliqueNameCoding.mk_nice_clique_name_le hGCH hP hI
        (show #W2 ≤ ℵ_ 2 by simp only [W2, Cardinal.mk_toType, Ordinal.card_omega, le_refl]) G))

structure GoodCut {G : SimpleGraph W2} (r : Code P I G ↪ W2)
    (σ : NiceCliqueName P I W2 G ↪ W2) (H : SimpleGraph W2)
    (source : RegularName P W2) (a : W2) : Prop where
  isOmegaOneSup : ErdosRadoCHAsym.IsOmegaOneSup a
  empty_lt : r SmallUnionCode.empty < a
  compl_lt : ∀ c, r c < a → r (SmallUnionCode.compl c) < a
  union_lt : ∀ c : ℕ → Code P I G, (∀ n, r (c n) < a) → r (SmallUnionCode.union c) < a
  point_lt : ∀ k : Fin 3, ∀ x < a, r (pointName G k x) < a
  block_lt : ∀ N, σ N < a → r (blockName N) < a
  values_below : ∀ N, σ N < a → ∀ x ∈ N.values, x < a
  reflects_source : ∀ c, r c < a → ∀ p : P,
    (∀ x < a, ∀ q : P, q ≤ p → source.holds q x → (eval G H c).holds q x) →
    ∀ x : W2, ∀ q : P, q ≤ p → source.holds q x → (eval G H c).holds q x

theorem exists_club_goodCut (hCH : CH) (hcc : OmegaTwoCC P) (hI : #I ≤ ℵ_ 1)
    (G H : SimpleGraph W2) (r : Code P I G ↪ W2)
    (σ : NiceCliqueName P I W2 G ↪ W2) (source : RegularName P W2) :
    ∃ club : Set W2, IsClub club ∧ ∀ a ∈ club,
      ErdosRadoCHAsym.IsOmegaOneSup a → GoodCut r σ H source a := by
  let c0 := {a | ClubClosure.ClosedUnder (fun _ => r SmallUnionCode.empty) a}
  have hc0 : IsClub c0 := ClubClosure.isClub_closedUnder _ alephZero_lt_cof_W2
  let c1 := {a | ∀ c, r c < a → r (SmallUnionCode.compl c) < a}
  have hc1 : IsClub c1 := ClubClosure.isClub_rankClosed r _ alephZero_lt_cof_W2
  obtain ⟨c2, hc2, h2⟩ := exists_club_countableClosed hCH r SmallUnionCode.union
  let c3 := ⋂ k : Fin 3, {a | ClubClosure.ClosedUnder (fun x => r (pointName G k x)) a}
  have hc3 : IsClub c3 := IsClub.iInter_of_countable alephZero_lt_cof_W2.ne'
    (fun k => ClubClosure.isClub_closedUnder _ alephZero_lt_cof_W2)
  let c4 := {a | ∀ N, σ N < a → r (blockName N) < a}
  have hc4 : IsClub c4 := ClubClosure.isClub_rankClosed σ _ alephZero_lt_cof_W2
  let bound (N : NiceCliqueName P I W2 G) : W2 :=
    Erdos1172Part3CoreObjectCode.objectBound ⟨N.values, N.mk_values_le hI⟩
  let c5 := {a | ∀ N, σ N < a → bound N < a}
  have hc5 : IsClub c5 := ClubClosure.isClub_rankClosed σ bound alephZero_lt_cof_W2
  obtain ⟨c6, hc6, h6⟩ := exists_club_reflects_named_inclusion hcc r (eval G H) source
  let clubs : Fin 7 → Set W2
    | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | 5 => c5 | 6 => c6
  have hclubs : ∀ i, IsClub (clubs i) := by
    intro i
    fin_cases i <;> assumption
  refine ⟨⋂ i, clubs i, IsClub.iInter_of_countable alephZero_lt_cof_W2.ne' hclubs, ?_⟩
  intro a ha hsup
  have hmem (i : Fin 7) : a ∈ clubs i := Set.mem_iInter.mp ha i
  obtain ⟨b, hba, _⟩ := ErdosRadoCHAsym.exists_strict_bound_of_countable_of_IsOmegaOneSup
    hsup (seed := ∅) (by simp) (by simp)
  refine ⟨hsup, hmem 0 b hba, hmem 1, h2 a (hmem 2) hsup, ?_, hmem 4, ?_, ?_⟩
  · intro k x hx
    exact Set.mem_iInter.mp (hmem 3) k x hx
  · intro N hN x hx
    exact (Erdos1172Part3CoreObjectCode.objectBound_spec
      ⟨N.values, N.mk_values_le hI⟩ x hx).trans (hmem 5 N hN)
  · exact h6 a (hmem 6)

end Erdos1172Part3RegularNeighborhoodCode
