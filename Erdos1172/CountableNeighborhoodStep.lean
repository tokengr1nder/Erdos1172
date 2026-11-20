/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Zorn
public import Erdos1172.Statement
public import Erdos1172.NeighborhoodCode
public import Erdos1172.NeighborhoodIdealCore

@[expose] public section

/-!
# Countable-Color Neighborhood Ideal and the `ω₃ → (ω₂ + 1)²_ω` Partial Step

In Baumgartner, Hajnal, and Todorčević (`[BHT93, p. 2]`, `arXiv:math/9311207`) and the 1999
Budapest conference booklet (`[Va99, 7.87]`, p. 13, whose circulating photocopy was cropped at the
right margin immediately after `\omega_3 \to (\omega_2`), the original Part (i) problem asks
whether `GCH` implies the countable-color partition relation `ω₃ → (ω₂ + 2)²_ω`. That original
`ω₃ → (ω₂ + 2)²_ω` question under `GCH` remains **open** (and the cropped-scan binary
reconstruction on `erdosproblems.com/1172` is omitted from this formalization).

This module establishes the weaker countable-color relation `GCH → ω₃ → (ω₂ + 1)²_ω`
(`omegaThree_to_omegaTwo_add_one_countable_of_gch`) as a **partial step** toward the original
Part (i) using our `< ℵ₂`-complete neighborhood-code and neighborhood-ideal machinery on `ω₃`
(`OmegaAtom := (ℕ ⊕ Unit) × W3`, `OmegaCode`, `OmegaGoodCut`, `OmegaSmall`, `omegaExists_core`).
Mathematically, `GCH → ω₃ → (ω₂ + 1)²_ω` also follows from the classical Erdős–Rado theorem
(`ErRa56`; `BHT93`, Theorem 2.1: `(2^{<κ})⁺ → (κ + 1)²_μ` for `μ < κ` at `κ = ω₂`, `μ = ω`).
-/

open Cardinal Ordinal Set Function Order

namespace Erdos1172CountableNeighborhoodStep

abbrev W1 : Type := Erdos1172NeighborhoodCode.W1
abbrev W3 : Type := Erdos1172NeighborhoodCode.W3
abbrev OmegaAtom : Type := (ℕ ⊕ Unit) × W3
abbrev OmegaCode : Type := SmallUnionCode.Code W1 OmegaAtom

theorem mk_OmegaAtom_le : #OmegaAtom ≤ ℵ_ 3 := by
  simp only [OmegaAtom, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_sum,
    Cardinal.mk_nat, Cardinal.mk_eq_one, W3, Cardinal.mk_toType, Ordinal.card_omega]
  have h1 : (ℵ₀ + 1 : Cardinal.{0}) ≤ ℵ_ 3 := by
    rw [Cardinal.add_eq_left le_rfl Cardinal.one_le_aleph0]
    exact Cardinal.aleph0_le_aleph 3
  calc
    (ℵ₀ + 1 : Cardinal.{0}) * ℵ_ 3 ≤ ℵ_ 3 * ℵ_ 3 := mul_le_mul' h1 le_rfl
    _ = ℵ_ 3 := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 3)

theorem mk_OmegaCode_le (hGCH : GCH) : #OmegaCode ≤ ℵ_ 3 := by
  apply SmallUnionCode.mk_code_le (μ := ℵ_ 1)
    (Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_aleph 1))
    (Cardinal.aleph0_le_aleph 3)
  · simp only [W1, Cardinal.mk_toType, Ordinal.card_omega, le_refl]
  · exact mk_OmegaAtom_le
  · exact hGCH.aleph_three_power_aleph_one.le

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

abbrev LocalCode (r : OmegaCode ↪ W3) (a : W3) := {c : OmegaCode // r c < a}

theorem mk_LocalCode_le (r : OmegaCode ↪ W3) (a : W3) :
    #(LocalCode r a) ≤ ℵ_ 2 := by
  have he : #(LocalCode r a) ≤ #(Set.Iio a) :=
    Cardinal.mk_le_of_injective (f := fun c : LocalCode r a =>
      (⟨r c.val, c.property⟩ : Set.Iio a)) (by
        intro c d h
        exact Subtype.ext (r.injective (congrArg Subtype.val h)))
  apply he.trans
  apply Order.lt_succ_iff.mp
  have hlt := Cardinal.mk_Iio_lt a (Cardinal.ord_cardinalMk (α := W3))
  simpa only [W3, Cardinal.mk_toType, Ordinal.card_omega,
    Cardinal.succ_aleph, show (2 : Ordinal) + 1 = 3 by norm_num] using hlt

theorem exists_unionBound (hGCH : GCH) (r : OmegaCode ↪ W3) (a : W3) :
    ∃ b : W3, ∀ c : W1 → LocalCode r a,
      r (SmallUnionCode.union (fun i => (c i).val)) < b := by
  have hle : #(Set.range (fun c : W1 → LocalCode r a =>
      r (SmallUnionCode.union (fun i => (c i).val)))) ≤ ℵ_ 2 := by
    refine Cardinal.mk_range_le.trans ?_
    rw [Cardinal.mk_arrow]
    simp only [Cardinal.lift_id, W1, Cardinal.mk_toType, Ordinal.card_omega]
    exact (Cardinal.power_le_power_right (mk_LocalCode_le r a)).trans_eq
      hGCH.aleph_two_power_aleph_one
  have hsmall := hle.trans_lt
    (Cardinal.aleph_lt_aleph.mpr (by norm_num : (2 : Ordinal) < 3))
  rw [← Erdos1172NeighborhoodCode.cof_W3] at hsmall
  obtain ⟨b, hb⟩ := not_isCofinal_iff.mp
    (fun hc => hsmall.not_ge (Order.cof_le hc))
  exact ⟨b, fun c => hb _ ⟨c, rfl⟩⟩

noncomputable def unionBound (hGCH : GCH) (r : OmegaCode ↪ W3) (a : W3) : W3 :=
  (exists_unionBound hGCH r a).choose

theorem union_rank_lt_of_closedUnder (hGCH : GCH) (r : OmegaCode ↪ W3)
    {a : W3} (ha : ErdosRadoGCHAsym.IsOmegaTwoSup a)
    (hclosed : ClubClosure.ClosedUnder (unionBound hGCH r) a)
    (c : W1 → OmegaCode) (hc : ∀ i, r (c i) < a) :
    r (SmallUnionCode.union c) < a := by
  obtain ⟨b, hba, hb⟩ :=
    ErdosRadoGCHAsym.exists_strict_bound_of_small_of_IsOmegaTwoSup ha
      (seed := Set.range (fun i => r (c i))) (by
        simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
          (Cardinal.mk_range_le (f := fun i => r (c i)))) (by
        rintro _ ⟨i, rfl⟩
        exact hc i)
  exact ((exists_unionBound hGCH r b).choose_spec
    (fun i => ⟨c i, hb _ ⟨i, rfl⟩⟩)).trans (hclosed b hba)

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
  have hcof := Erdos1172NeighborhoodCode.alephZero_lt_cof_W3
  let caNat : Set W3 := ⋂ n : ℕ,
    {a | ClubClosure.ClosedUnder (fun x => r (SmallUnionCode.atom (.inl n, x))) a}
  have hcaNat : IsClub caNat := IsClub.iInter_of_countable hcof.ne'
    (fun n => ClubClosure.isClub_closedUnder
      (fun x => r (SmallUnionCode.atom (.inl n, x))) hcof)
  let caUnit : Set W3 :=
    {a | ClubClosure.ClosedUnder (fun x => r (SmallUnionCode.atom (.inr (), x))) a}
  have hcaUnit : IsClub caUnit := ClubClosure.isClub_closedUnder
    (fun x => r (SmallUnionCode.atom (.inr (), x))) hcof
  let cc : Set W3 := {a | ∀ c, r c < a → r (SmallUnionCode.compl c) < a}
  have hcc : IsClub cc := ClubClosure.isClub_rankClosed r
    (fun c => r (SmallUnionCode.compl c)) hcof
  let cu : Set W3 := {a | ClubClosure.ClosedUnder (unionBound hGCH r) a}
  have hcu : IsClub cu := ClubClosure.isClub_closedUnder (unionBound hGCH r) hcof
  let ce : Set W3 := {a | ClubClosure.ClosedUnder (fun _ => r SmallUnionCode.empty) a}
  have hce : IsClub ce := ClubClosure.isClub_closedUnder
    (fun _ => r SmallUnionCode.empty) hcof
  obtain ⟨cr, hcr, hr⟩ := ClubClosure.exists_club_reflects r (eval col) Set.univ hcof
  refine ⟨((((caNat ∩ caUnit) ∩ cc) ∩ cu) ∩ ce) ∩ cr,
    ((((hcaNat.inter hcof.ne' hcaUnit).inter hcof.ne' hcc).inter
      hcof.ne' hcu).inter hcof.ne' hce).inter hcof.ne' hcr, ?_⟩
  rintro a ⟨⟨⟨⟨⟨haN, haU⟩, hc⟩, hu⟩, he⟩, hr'⟩ hsup
  refine ⟨hsup, ?_, hc, union_rank_lt_of_closedUnder hGCH r hsup hu, ?_, ?_⟩
  · obtain ⟨b, hba, _⟩ :=
      ErdosRadoGCHAsym.exists_strict_bound_of_small_of_IsOmegaTwoSup hsup
        (seed := ∅) (by simp) (by simp)
    exact he b hba
  · rintro (n | ⟨⟩) x hx
    · exact (Set.mem_iInter.mp haN n) x hx
    · exact haU x hx
  · intro c hc' hsub
    exact hr a hr' c hc' (by simpa only [Set.univ_inter] using hsub)

theorem isStationary_omegaGoodCut (hGCH : GCH) (r : OmegaCode ↪ W3)
    (col : Sym2 W3 → ℕ) : IsStationary {a | OmegaGoodCut r col a} := by
  obtain ⟨club, hclub, hgood⟩ := exists_club_omegaGoodCut hGCH r col
  intro test htest
  obtain ⟨a, hsup, ha, hatest⟩ :=
    ErdosRadoGCHAsym.isStationary_isOmegaTwoSup_omegaThree
      (hclub.inter Erdos1172NeighborhoodCode.alephZero_lt_cof_W3.ne' htest)
  exact ⟨a, hgood a ha hsup, hatest⟩

def OmegaSmall (r : OmegaCode ↪ W3) (col : Sym2 W3 → ℕ) (a : W3) (s : Set W3) : Prop :=
  ∃ c : OmegaCode, r c < a ∧ a ∉ eval col c ∧ s ⊆ eval col c

theorem omegaSmall_mono {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    {s t : Set W3} (hst : s ⊆ t) (ht : OmegaSmall r col a t) :
    OmegaSmall r col a s := by
  rcases ht with ⟨c, hc, hca, ht⟩
  exact ⟨c, hc, hca, hst.trans ht⟩

theorem omegaEmpty_small {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) : OmegaSmall r col a ∅ :=
  ⟨SmallUnionCode.empty, ha.empty_lt, by simp [eval], Set.empty_subset _⟩

theorem omegaIUnion_small {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) {J : Type} (s : J → Set W3)
    (hJ : #J < ℵ_ 2) (hs : ∀ j, OmegaSmall r col a (s j)) :
    OmegaSmall r col a (⋃ j, s j) := by
  classical
  choose c hc hca hcs using hs
  have hcard : #J ≤ #W1 := by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using
      Erdos1172NeighborhoodCode.mk_le_alephOne_of_lt_alephTwo hJ
  obtain ⟨e⟩ := (Cardinal.le_def J W1).mp hcard
  let t : W1 → OmegaCode := fun i =>
    if h : ∃ j, e j = i then c h.choose else SmallUnionCode.empty
  have ht : ∀ i, r (t i) < a ∧ a ∉ eval col (t i) := by
    intro i
    dsimp only [t]
    split_ifs with h
    · exact ⟨hc h.choose, hca h.choose⟩
    · exact ⟨ha.empty_lt, by simp [eval]⟩
  refine ⟨SmallUnionCode.union t, ha.union_lt t (fun i => (ht i).1), ?_, ?_⟩
  · change a ∉ ⋃ i, eval col (t i)
    simp only [Set.mem_iUnion, not_exists]
    exact fun i => (ht i).2
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    change x ∈ ⋃ i, eval col (t i)
    refine Set.mem_iUnion.mpr ⟨e j, ?_⟩
    have h : ∃ j', e j' = e j := ⟨j, rfl⟩
    have he : h.choose = j := e.injective h.choose_spec
    have hteq : t (e j) = c j := by simp only [t, h, ↓reduceDIte, he]
    rw [hteq]
    exact hcs j hj

theorem omegaUnion_small {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) {s t : Set W3}
    (hs : OmegaSmall r col a s) (ht : OmegaSmall r col a t) :
    OmegaSmall r col a (s ∪ t) := by
  have h := omegaIUnion_small ha (fun b : Bool => if b then s else t)
    (show #Bool < ℵ_ 2 by
      simp only [Cardinal.mk_fintype, Fintype.card_bool, Nat.cast_ofNat]
      exact (Cardinal.natCast_lt_aleph0 : (2 : Cardinal) < ℵ₀).trans_le
        (Cardinal.aleph0_le_aleph 2))
    (by intro b; cases b <;> assumption)
  have heq : (⋃ b : Bool, if b then s else t) = s ∪ t := by
    ext x; simp [Bool.exists_bool, or_comm]
  rwa [heq] at h

theorem omegaBounded_small {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) {x : W3} (hx : x < a) :
    OmegaSmall r col a (Set.Iic x) :=
  ⟨SmallUnionCode.atom (.inr (), x), ha.atom_lt (.inr ()) x hx, hx.not_ge, Set.Subset.rfl⟩

theorem omegaPrior_not_small {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) : ¬OmegaSmall r col a (Set.Iio a) := by
  rintro ⟨c, hc, hca, hsub⟩
  exact hca (ha.reflects_univ c hc hsub (Set.mem_univ a))

theorem omegaNonneighbors_small {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) (n : ℕ) {x : W3}
    (hx : x < a) (hxa : (colorGraph col n).Adj x a) :
    OmegaSmall r col a {y | ¬(colorGraph col n).Adj x y} := by
  refine ⟨SmallUnionCode.compl (SmallUnionCode.atom (.inl n, x)),
    ha.compl_lt _ (ha.atom_lt (.inl n) x hx), ?_, Set.Subset.rfl⟩
  change ¬a ∈ ({y | (colorGraph col n).Adj x y})ᶜ
  exact not_not.mpr hxa

theorem omegaExists_core {r : OmegaCode ↪ W3} {col : Sym2 W3 → ℕ} {a : W3}
    (ha : OmegaGoodCut r col a) (n : ℕ)
    (s : Set W3) (hs : ¬OmegaSmall r col a s) (hsBelow : s ⊆ Set.Iio a)
    (hsColor : ∀ x ∈ s, (colorGraph col n).Adj x a) :
    ∃ core : Set W3, core ⊆ s ∧ (colorGraph col n).IsClique core ∧
      typeLT core = ω_ 2 := by
  obtain ⟨c, hc⟩ := Erdos1172NeighborhoodIdealCore.exists_maximal_clique_subset
    (colorGraph col n) s
  have hcard : ℵ_ 2 ≤ #c := by
    by_contra h
    have hlt : #c < ℵ_ 2 := lt_of_not_ge h
    obtain ⟨cutoff, hcutoff, hbound⟩ :=
      ErdosRadoGCHAsym.exists_strict_bound_of_small_of_IsOmegaTwoSup ha.isOmegaTwoSup
        (Erdos1172NeighborhoodCode.mk_le_alephOne_of_lt_alephTwo hlt)
        (fun x hx => hsBelow (hc.1.1 hx))
    let bad : Set W3 := ⋃ x : c, {y | ¬(colorGraph col n).Adj x.val y}
    have hbad : OmegaSmall r col a bad := omegaIUnion_small ha _ hlt (fun x =>
      omegaNonneighbors_small ha n (hsBelow (hc.1.1 x.property))
        (hsColor x.val (hc.1.1 x.property)))
    have hsmall : OmegaSmall r col a (bad ∪ Set.Iic cutoff) :=
      omegaUnion_small ha hbad (omegaBounded_small ha hcutoff)
    obtain ⟨y, hys, hy⟩ := Set.not_subset.mp (fun hsub => hs (omegaSmall_mono hsub hsmall))
    have hlater : ∀ x ∈ c, x < y := fun x hx =>
      (hbound x hx).trans (lt_of_not_ge (fun hle => hy (Or.inr hle)))
    have hadj : ∀ x ∈ c, (colorGraph col n).Adj x y := by
      intro x hx
      by_contra hxy
      exact hy (Or.inl (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxy⟩))
    have hinsert : insert y c ⊆ s ∧ (colorGraph col n).IsClique (insert y c) :=
      ⟨Set.insert_subset hys hc.1.1,
        hc.1.2.insert (fun x hx _ => (hadj x hx).symm)⟩
    exact (hlater y (hc.2 hinsert (Set.subset_insert y c) (Set.mem_insert y c))).false
  have htype : (ω_ 2 : Ordinal.{0}) ≤ typeLT c := by
    rw [← Cardinal.ord_aleph]
    exact (Cardinal.ord_le_ord.mpr hcard).trans (Cardinal.ord_le_type (· < ·))
  obtain ⟨core, hsub, htype⟩ := Ordinal.exists_subset_typeLT_eq c htype
  exact ⟨core, hsub.trans hc.1.1, hc.1.2.subset hsub, htype⟩

/-- **Partial step toward original `[BHT93, p. 2]` Part (i)**: under `GCH`, the countable-color
`< ℵ₂`-complete neighborhood ideal on `ω₃` proves `ω₃ → (ω₂ + 1)²_ω`
(`OrdinalCountableRamsey (ω_ 3) (ω_ 2 + 1)`). This weaker relation also follows from Erdős–Rado
(`ErRa56`; `BHT93`, Theorem 2.1), while the original `ω₃ → (ω₂ + 2)²_ω` under `GCH` remains open. -/
theorem omegaThree_to_omegaTwo_add_one_countable_of_gch (hGCH : GCH) :
    OrdinalCountableRamsey (ω_ 3 : Ordinal.{0}) (ω_ 2 + 1) := by
  intro col
  let r := rank hGCH
  obtain ⟨a, ha, _⟩ := isStationary_omegaGoodCut hGCH r col IsClub.univ
  let fiber (n : ℕ) : Set W3 := {x | x < a ∧ (colorGraph col n).Adj x a}
  have hpos : ∃ n : ℕ, ¬OmegaSmall r col a (fiber n) := by
    by_contra h
    have hall : ∀ n : ℕ, OmegaSmall r col a (fiber n) := fun n =>
      Classical.not_not.mp (fun hn => h ⟨n, hn⟩)
    have hnat : #ℕ < ℵ_ 2 := by
      rw [Cardinal.mk_nat, ← Cardinal.aleph_zero]
      exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
    have hunion : OmegaSmall r col a (⋃ n : ℕ, fiber n) :=
      omegaIUnion_small ha fiber hnat hall
    apply omegaPrior_not_small ha
    refine omegaSmall_mono ?_ hunion
    intro x hx
    exact Set.mem_iUnion.mpr ⟨col s(x, a), hx, hx.ne, rfl⟩
  obtain ⟨n, hn⟩ := hpos
  obtain ⟨core, hsub, hclique, htype⟩ := omegaExists_core ha n (fiber n) hn
    (fun _ hx => hx.1) (fun _ hx => hx.2)
  have hsClique : (colorGraph col n).IsClique (Set.insert a core) :=
    hclique.insert (fun x hx _ => ((hsub hx).2).symm)
  have hsType : typeLT (Set.insert a core : Set W3) = ω_ 2 + 1 :=
    (Ordinal.typeLT_insert_of_forall_lt (fun x hx => (hsub hx).1)).trans (by rw [htype])
  exact ⟨n, Set.insert a core, fun x hx y hy hne => (hsClique hx hy hne).2, hsType⟩

end Erdos1172CountableNeighborhoodStep
