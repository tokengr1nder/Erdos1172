/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.NeighborhoodIdealCore

@[expose] public section

/-!
# Countable-Color Neighborhood Ideal and the Unselected `ω₃ → (ω₂ + 1)²_ω` Remark

In Baumgartner, Hajnal, and Todorčević (`[BHT93, p. 2]`, `arXiv:math/9311207`) and `[Va99, 7.87]`,
the original Part (i) problem asks whether `GCH` implies `ω₃ → (ω₂ + 2)²_ω`, which remains **open**.
As an unselected background remark (`omegaThree_to_omegaTwo_add_one_countable_of_gch`), this module
notes that our `< ℵ₂`-complete neighborhood-ideal machinery on `ω₃` extends to countably many
colors and recovers the known `ω₂ + 1` relation `GCH → ω₃ → (ω₂ + 1)²_ω` due to Erdős and Rado
(`[ErRa56]`; `[BHT93, Theorem 2.1]`).
-/

open Cardinal Ordinal Set Function Order

namespace Erdos1172CountableNeighborhoodStep

open Erdos1172NeighborhoodCode (mk_taggedCode_le mk_localCode_le_gen exists_unionBound_gen
  union_rank_lt_gen exists_club_taggedCut alephZero_lt_cof_W3)
open Erdos1172NeighborhoodIdeal (codedSmall_iUnion codedSmall_union)
open Erdos1172NeighborhoodIdealCore (exists_core_of_small)

abbrev W1 : Type := Erdos1172NeighborhoodCode.W1
abbrev W3 : Type := Erdos1172NeighborhoodCode.W3
abbrev OmegaAtom : Type := (ℕ ⊕ Unit) × W3
abbrev OmegaCode : Type := SmallUnionCode.Code W1 OmegaAtom

theorem mk_OmegaCode_le (hGCH : GCH) : #OmegaCode ≤ ℵ_ 3 := mk_taggedCode_le hGCH

noncomputable def rank (hGCH : GCH) : OmegaCode ↪ W3 :=
  Classical.choice ((Cardinal.le_def OmegaCode W3).mp (by
    simpa only [W3, Cardinal.mk_toType, Ordinal.card_omega] using mk_OmegaCode_le hGCH))

def colorGraph (col : Sym2 W3 → ℕ) (n : ℕ) : SimpleGraph W3 where
  Adj x y := x ≠ y ∧ col s(x, y) = n
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def atoms (col : Sym2 W3 → ℕ) : OmegaAtom → Set W3
  | (.inl n, x) => {y | (colorGraph col n).Adj x y}
  | (.inr (), x) => Set.Iic x

def eval (col : Sym2 W3 → ℕ) : OmegaCode → Set W3 :=
  SmallUnionCode.eval (atoms col)

structure OmegaGoodCut (r : OmegaCode ↪ W3) (col : Sym2 W3 → ℕ) (a : W3) : Prop where
  isOmegaTwoSup : ErdosRadoGCHAsym.IsOmegaTwoSup a
  empty_lt : r SmallUnionCode.empty < a
  compl_lt : ∀ c, r c < a → r (SmallUnionCode.compl c) < a
  union_lt : ∀ c : W1 → OmegaCode, (∀ i, r (c i) < a) →
    r (SmallUnionCode.union c) < a
  atom_lt : ∀ k : ℕ ⊕ Unit, ∀ x < a, r (SmallUnionCode.atom (k, x)) < a
  reflects_univ : ∀ c, r c < a → Set.Iio a ⊆ eval col c →
    Set.univ ⊆ eval col c

theorem exists_club_omegaGoodCut (hGCH : GCH) (r : OmegaCode ↪ W3)
    (col : Sym2 W3 → ℕ) :
    ∃ club : Set W3, IsClub club ∧ ∀ a ∈ club,
      ErdosRadoGCHAsym.IsOmegaTwoSup a → OmegaGoodCut r col a := by
  obtain ⟨club, hclub, hg⟩ := exists_club_taggedCut hGCH r (atoms col)
  exact ⟨club, hclub, fun a ha hsup =>
    let ⟨he, hc, hu, hat, hrefl⟩ := hg a ha hsup
    ⟨hsup, he, hc, hu, hat, hrefl⟩⟩

theorem isStationary_omegaGoodCut (hGCH : GCH) (r : OmegaCode ↪ W3)
    (col : Sym2 W3 → ℕ) : IsStationary {a | OmegaGoodCut r col a} := by
  obtain ⟨club, hclub, hgood⟩ := exists_club_omegaGoodCut hGCH r col
  intro test htest
  obtain ⟨a, hsup, ha, hatest⟩ :=
    ErdosRadoGCHAsym.isStationary_isOmegaTwoSup_omegaThree
      (hclub.inter alephZero_lt_cof_W3.ne' htest)
  exact ⟨a, hgood a ha hsup, hatest⟩

def OmegaSmall (r : OmegaCode ↪ W3) (col : Sym2 W3 → ℕ) (a : W3) (s : Set W3) : Prop :=
  ∃ c : OmegaCode, r c < a ∧ a ∉ eval col c ∧ s ⊆ eval col c

theorem omegaSmall_mono {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    {s t : Set W3} (hst : s ⊆ t) (ht : OmegaSmall r col a t) :
    OmegaSmall r col a s := by
  rcases ht with ⟨c, hc, hca, ht⟩
  exact ⟨c, hc, hca, hst.trans ht⟩

theorem omegaIUnion_small {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) {J : Type} (s : J → Set W3)
    (hJ : #J < ℵ_ 2) (hs : ∀ j, OmegaSmall r col a (s j)) :
    OmegaSmall r col a (⋃ j, s j) :=
  codedSmall_iUnion ha.empty_lt ha.union_lt s hJ hs

theorem omegaUnion_small {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) {s t : Set W3}
    (hs : OmegaSmall r col a s) (ht : OmegaSmall r col a t) :
    OmegaSmall r col a (s ∪ t) :=
  codedSmall_union ha.empty_lt ha.union_lt hs ht

theorem omegaBounded_small {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) {x : W3} (hx : x < a) :
    OmegaSmall r col a (Set.Iic x) :=
  ⟨SmallUnionCode.atom (.inr (), x), ha.atom_lt (.inr ()) x hx, hx.not_ge, Set.Subset.rfl⟩

theorem omegaPrior_not_small {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) : ¬OmegaSmall r col a (Set.Iio a) :=
  fun ⟨c, hc, hca, hsub⟩ => hca (ha.reflects_univ c hc hsub (Set.mem_univ a))

theorem omegaNonneighbors_small {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) (n : ℕ) {x : W3}
    (hx : x < a) (hxa : (colorGraph col n).Adj x a) :
    OmegaSmall r col a {y | ¬(colorGraph col n).Adj x y} :=
  ⟨SmallUnionCode.compl (SmallUnionCode.atom (.inl n, x)),
    ha.compl_lt _ (ha.atom_lt (.inl n) x hx), not_not.mpr hxa, Set.Subset.rfl⟩

theorem omegaExists_core {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) (n : ℕ)
    (s : Set W3) (hs : ¬OmegaSmall r col a s) (hsBelow : s ⊆ Set.Iio a)
    (hsColor : ∀ x ∈ s, (colorGraph col n).Adj x a) :
    ∃ core : Set W3, core ⊆ s ∧ (colorGraph col n).IsClique core ∧ typeLT core = ω_ 2 :=
  exists_core_of_small ha.isOmegaTwoSup omegaSmall_mono (omegaUnion_small ha)
    (omegaIUnion_small ha) (omegaBounded_small ha) (colorGraph col n)
    (omegaNonneighbors_small ha n) s hs hsBelow hsColor

/-- **Unselected remark (Erdős–Rado `[ErRa56]`; `[BHT93, Theorem 2.1]`)**: under `GCH`, the
countable-color `< ℵ₂`-complete neighborhood ideal on `ω₃` recovers `ω₃ → (ω₂ + 1)²_ω`, while
the original `[BHT93, p. 2]` Part (i) question `ω₃ → (ω₂ + 2)²_ω` under `GCH` remains open. -/
theorem omegaThree_to_omegaTwo_add_one_countable_of_gch (hGCH : GCH) :
    OrdinalCountableRamsey (ω_ 3 : Ordinal.{0}) (ω_ 2 + 1) := by
  intro col
  obtain ⟨a, ha, _⟩ := isStationary_omegaGoodCut hGCH (rank hGCH) col IsClub.univ
  let fiber (n : ℕ) : Set W3 := {x | x < a ∧ (colorGraph col n).Adj x a}
  have hpos : ∃ n : ℕ, ¬OmegaSmall (rank hGCH) col a (fiber n) := by
    by_contra! hall
    have hnat : #ℕ < ℵ_ 2 := by
      rw [Cardinal.mk_nat, ← Cardinal.aleph_zero]
      exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
    have hcov : Set.Iio a ⊆ ⋃ n, fiber n := fun x hx => Set.mem_iUnion.mpr ⟨col s(x, a), hx, hx.ne, rfl⟩
    exact omegaPrior_not_small ha (omegaSmall_mono hcov (omegaIUnion_small ha fiber hnat hall))
  obtain ⟨n, hn⟩ := hpos
  obtain ⟨core, hsub, hclique, htype⟩ := omegaExists_core ha n (fiber n) hn
    (fun _ hx => hx.1) (fun _ hx => hx.2)
  have hsClique : (colorGraph col n).IsClique (Set.insert a core) :=
    hclique.insert (fun x hx _ => ((hsub hx).2).symm)
  exact ⟨n, Set.insert a core, fun x hx y hy hne => (hsClique hx hy hne).2,
    (Ordinal.typeLT_insert_of_forall_lt (fun x hx => (hsub hx).1)).trans (by rw [htype])⟩

end Erdos1172CountableNeighborhoodStep
