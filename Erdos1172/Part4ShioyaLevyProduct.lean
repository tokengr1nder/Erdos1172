/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCollapseConditions
public import Erdos1172.Part4ShioyaProductRefinement

@[expose] public section

/-! # The small-support Lévy product and its bounded stages -/

set_option autoImplicit false
noncomputable section
universe u

namespace Erdos1172Shioya.LevyProduct

variable {κ θ : Cardinal.{u}} {I : Type u} {A : I → Type u} {S T : Set I}

def support (v : ∀ i, Collapse.Condition κ (A i)) : Set I := {i | (v i).graph.Nonempty}

structure Family (κ : Cardinal.{u}) {I : Type u} (A : I → Type u) (S : Set I) where
  value : ∀ i, Collapse.Condition κ (A i)
  small : Cardinal.mk (support value) < κ
  inside : support value ⊆ S

theorem value_injective : Function.Injective (Family.value : Family κ A S → _) := by
  rintro ⟨v,_,_⟩ ⟨_,_,_⟩ rfl
  rfl

instance : PartialOrder (Family κ A S) := PartialOrder.lift Family.value value_injective

theorem le_iff {p q : Family κ A S} : p ≤ q ↔ ∀ i, p.value i ≤ q.value i := Iff.rfl

def empty (hκ : 0 < κ) : Family κ A S where
  value _ := Collapse.empty hκ
  small := by simpa [support, Collapse.empty] using hκ
  inside := by simp [support, Collapse.empty]

theorem le_empty (p : Family κ A S) (hκ : 0 < κ) : p ≤ empty hκ := fun i => Collapse.le_empty (p.value i) hκ

theorem eq_empty_of_not_supported {v : ∀ i, Collapse.Condition κ (A i)} {i : I} (h : i ∉ support v)
    (hκ : 0 < κ) : v i = Collapse.empty hκ :=
  Collapse.graph_injective (Set.not_nonempty_iff_eq_empty.mp h)

theorem value_outside (p : Family κ A S) {i : I} (hi : i ∉ S) (hκ : 0 < κ) :
    p.value i = Collapse.empty hκ := eq_empty_of_not_supported (fun h => hi (p.inside h)) hκ

def widen (h : S ⊆ T) (p : Family κ A S) : Family κ A T :=
  ⟨p.value,p.small,p.inside.trans h⟩

def cut (hκ : 0 < κ) (T : Set I) (p : Family κ A S) : Family κ A T := by
  classical
  let v (i : I) := if i ∈ T then p.value i else Collapse.empty hκ
  have hs {i : I} (hi : i ∈ support v) : i ∈ T ∧ i ∈ support p.value := by
    by_cases h : i ∈ T
    · exact ⟨h, by simpa [support,v,h] using hi⟩
    · simp [support,v,h,Collapse.empty] at hi
  exact ⟨v,(Cardinal.mk_le_mk_of_subset (fun _ hi => (hs hi).2)).trans_lt p.small,fun _ hi => (hs hi).1⟩

theorem cut_at (hκ : 0 < κ) (p : Family κ A S) {i : I} (hi : i ∈ T) :
    (cut hκ T p).value i = p.value i := by classical simp [cut,hi]

theorem cut_not_at (hκ : 0 < κ) (p : Family κ A S) {i : I} (hi : i ∉ T) :
    (cut hκ T p).value i = Collapse.empty hκ := value_outside (cut hκ T p) hi hκ

theorem cut_mono (hκ : 0 < κ) (T : Set I) : Monotone (cut (A := A) (S := S) hκ T) := by
  intro p q h i
  by_cases hi : i ∈ T
  · simpa only [cut_at hκ _ hi] using h i
  · rw [cut_not_at hκ _ hi,cut_not_at hκ _ hi]

theorem cut_cut (hκ : 0 < κ) {U : Set I} (h : U ⊆ T) (p : Family κ A S) :
    cut hκ U (cut hκ T p) = cut hκ U p := by
  apply value_injective
  funext i
  by_cases hi : i ∈ U
  · rw [cut_at hκ _ hi,cut_at hκ _ hi,cut_at hκ _ (h hi)]
  · rw [cut_not_at hκ _ hi,cut_not_at hκ _ hi]

def paste (hκ : Cardinal.aleph0 ≤ κ) (hT : T ⊆ S) (p : Family κ A T) (q : Family κ A (S \ T)) :
    Family κ A S := by
  classical
  let v (i : I) := if i ∈ T then p.value i else q.value i
  have hs : support v ⊆ support p.value ∪ support q.value := by
    intro i hi
    by_cases h : i ∈ T
    · exact Or.inl (by simpa [support,v,h] using hi)
    · exact Or.inr (by simpa [support,v,h] using hi)
  exact ⟨v,(Cardinal.mk_le_mk_of_subset hs).trans_lt ((Cardinal.mk_union_le _ _).trans_lt
    (Cardinal.add_lt_of_lt hκ p.small q.small)),fun _ hi => (hs hi).elim
      (fun h => hT (p.inside h)) (fun h => (q.inside h).1)⟩

theorem paste_at (hκ : Cardinal.aleph0 ≤ κ) (hT : T ⊆ S) (p : Family κ A T) (q : Family κ A (S \ T))
    {i : I} (hi : i ∈ T) : (paste hκ hT p q).value i = p.value i := by classical simp [paste,hi]

theorem paste_not_at (hκ : Cardinal.aleph0 ≤ κ) (hT : T ⊆ S) (p : Family κ A T) (q : Family κ A (S \ T))
    {i : I} (hi : i ∉ T) : (paste hκ hT p q).value i = q.value i := by classical simp [paste,hi]

def split (hκ : Cardinal.aleph0 ≤ κ) (hT : T ⊆ S) :
    Family κ A S ≃o Family κ A T × Family κ A (S \ T) where
  toFun p := (cut (Cardinal.aleph0_pos.trans_le hκ) T p,cut (Cardinal.aleph0_pos.trans_le hκ) (S \ T) p)
  invFun z := paste hκ hT z.1 z.2
  left_inv p := by
    apply value_injective
    funext i
    let hpos := Cardinal.aleph0_pos.trans_le hκ
    by_cases hi : i ∈ T
    · rw [paste_at hκ hT _ _ hi,cut_at hpos _ hi]
    · rw [paste_not_at hκ hT _ _ hi]
      by_cases hs : i ∈ S
      · exact cut_at hpos _ ⟨hs,hi⟩
      · rw [cut_not_at hpos _ (fun h => hs h.1),value_outside p hs hpos]
  right_inv z := by
    let hpos := Cardinal.aleph0_pos.trans_le hκ
    apply Prod.ext <;> apply value_injective <;> funext i
    · by_cases hi : i ∈ T
      · exact (cut_at hpos _ hi).trans (paste_at hκ hT _ _ hi)
      · exact (cut_not_at hpos _ hi).trans (value_outside z.1 hi hpos).symm
    · by_cases hi : i ∈ S \ T
      · exact (cut_at hpos _ hi).trans (paste_not_at hκ hT _ _ hi.2)
      · exact (cut_not_at hpos _ hi).trans (value_outside z.2 hi hpos).symm
  map_rel_iff' := by
    intro p q
    let hpos := Cardinal.aleph0_pos.trans_le hκ
    constructor
    · intro h i
      change cut hpos T p ≤ cut hpos T q ∧ cut hpos (S \ T) p ≤ cut hpos (S \ T) q at h
      by_cases ht : i ∈ T
      · simpa only [cut_at hpos _ ht] using h.1 i
      · by_cases hs : i ∈ S
        · simpa only [cut_at hpos _ (show i ∈ S \ T from ⟨hs,ht⟩)] using h.2 i
        · rw [value_outside p hs hpos,value_outside q hs hpos]
    · intro h
      exact ⟨cut_mono hpos T h, cut_mono hpos (S \ T) h⟩

theorem compatible_of_agree_on_support (hκ : Cardinal.aleph0 ≤ κ) (p q : Family κ A S)
    (h : ∀ i ∈ support p.value, i ∈ support q.value → p.value i = q.value i) :
    ∃ r : Family κ A S, r ≤ p ∧ r ≤ q := by
  let T := support p.value
  let pos := Cardinal.aleph0_pos.trans_le hκ
  let r := paste hκ p.inside (cut pos T p) (cut pos (S \ T) q)
  refine ⟨r, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ T
    · exact ((paste_at hκ _ _ _ hi).trans (cut_at pos p hi)).le
    · rw [eq_empty_of_not_supported hi pos]
      exact Collapse.le_empty _ _
  · intro i
    by_cases hi : i ∈ T
    · by_cases hq : i ∈ support q.value
      · exact (((paste_at hκ _ _ _ hi).trans (cut_at pos p hi)).trans (h i hi hq)).le
      · rw [eq_empty_of_not_supported hq pos]
        exact Collapse.le_empty _ _
    · by_cases hs : i ∈ S
      · exact ((paste_not_at hκ _ _ _ hi).trans (cut_at pos q ⟨hs,hi⟩)).le
      · rw [value_outside q hs pos]
        exact Collapse.le_empty _ _

def atOne (hκ : Cardinal.aleph0 ≤ κ) (i : I) (c : Collapse.Condition κ (A i)) :
    Family κ A {i} := by
  classical
  let v := Function.update (fun j => Collapse.empty (α := A j) (Cardinal.aleph0_pos.trans_le hκ)) i c
  have hs : support v ⊆ {i} := by
    intro j hj
    by_contra h
    have hn : j ≠ i := h
    simp [support,v,Function.update_of_ne hn,Collapse.empty] at hj
  exact ⟨v,(Cardinal.mk_le_mk_of_subset hs).trans_lt (by simpa using Cardinal.one_lt_aleph0.trans_le hκ),hs⟩

theorem atOne_value (hκ : Cardinal.aleph0 ≤ κ) (i : I) (c : Collapse.Condition κ (A i)) :
    (atOne hκ i c).value i = c := by classical simp [atOne]

def singletonIso (hκ : Cardinal.aleph0 ≤ κ) (i : I) :
    Family κ A {i} ≃o Collapse.Condition κ (A i) where
  toFun p := p.value i
  invFun := atOne hκ i
  left_inv p := by
    apply value_injective
    funext j
    by_cases h : j = i
    · subst j
      exact atOne_value _ _ _
    · exact (value_outside (atOne hκ i (p.value i)) (i := j) h (Cardinal.aleph0_pos.trans_le hκ)).trans
        (value_outside p (i := j) h (Cardinal.aleph0_pos.trans_le hκ)).symm
  right_inv := atOne_value hκ i
  map_rel_iff' := by
    intro p q
    refine ⟨fun h j => ?_, fun h => h i⟩
    by_cases hj : j = i
    · exact hj ▸ h
    · rw [value_outside p (i := j) hj (Cardinal.aleph0_pos.trans_le hκ),
        value_outside q (i := j) hj (Cardinal.aleph0_pos.trans_le hκ)]

theorem shortInfima (hκ : κ.IsRegular) : ShortInfima κ (Family κ A S) := by
  intro L _ _ hL f hf
  choose a ha using fun i => Collapse.shortInfima (α := A i) hκ L hL (fun l => (f l).value i)
    (fun _ _ h => hf h i)
  let D := ⋃ l : L, support (f l).value
  have hs : support a ⊆ D := by
    intro i hi
    by_contra hout
    have he (l : L) : (f l).value i = Collapse.empty hκ.pos :=
      eq_empty_of_not_supported (fun h => hout (Set.mem_iUnion.mpr ⟨l,h⟩)) hκ.pos
    have hb : Collapse.empty hκ.pos ≤ a i := (ha i).2 (Set.forall_mem_range.mpr (fun l => (he l).ge))
    have hh := Collapse.le_iff.mp hb
    exact Set.not_nonempty_empty (hi.mono hh)
  have hD : Cardinal.mk D < κ := (Cardinal.mk_iUnion_le _).trans_lt (Cardinal.mul_lt_of_lt hκ.aleph0_le hL
    (Cardinal.iSup_lt_of_lt_cof_ord (a := κ) (by rwa [hκ.cof_ord]) (fun l => (f l).small)))
  let p : Family κ A S := ⟨a,(Cardinal.mk_le_mk_of_subset hs).trans_lt hD,
    fun i hi => by obtain ⟨l,hl⟩ := Set.mem_iUnion.mp (hs hi); exact (f l).inside hl⟩
  refine ⟨p,Set.forall_mem_range.mpr (fun l i => (ha i).1 (Set.mem_range_self l)),?_⟩
  intro q hq i
  exact (ha i).2 (Set.forall_mem_range.mpr (fun l => hq (Set.mem_range_self l) i))

theorem separative [∀ i, Nontrivial (A i)] (hκ : Cardinal.aleph0 ≤ κ) : Separative (Family κ A S) := by
  classical
  intro p q h
  obtain ⟨i,hi⟩ : ∃ i, ¬p.value i ≤ q.value i := by by_contra! hall; exact h hall
  have hS : i ∈ S := by
    by_contra hn
    apply hi
    rw [value_outside q hn (Cardinal.aleph0_pos.trans_le hκ)]
    exact Collapse.le_empty _ _
  obtain ⟨c,hc,hno⟩ := Collapse.separative hκ (p.value i) (q.value i) hi
  let v := Function.update p.value i c
  have hs : support v ⊆ insert i (support p.value) := by
    intro j hj
    by_cases he : j = i
    · exact Or.inl he
    · exact Or.inr (by simpa [v,support,Function.update_of_ne he] using hj)
  let r : Family κ A S := ⟨v,(Cardinal.mk_le_mk_of_subset hs).trans_lt
    (Cardinal.mk_insert_le.trans_lt (Cardinal.add_lt_of_lt hκ p.small (Cardinal.one_lt_aleph0.trans_le hκ))),
    fun j hj => (hs hj).elim (fun he => he ▸ hS) (fun hh => p.inside hh)⟩
  refine ⟨r,fun j => ?_,fun ⟨t,htr,htq⟩ => hno ⟨t.value i,?_,htq i⟩⟩
  · by_cases hj : j = i
    · subst j
      simpa [r,v] using hc
    · change Function.update p.value i c j ≤ p.value j
      rw [Function.update_of_ne hj]
  · simpa [r,v] using htr i

theorem cardinal_lt (hθ : θ.IsInaccessible) (hκ : κ < θ) (hpos : 0 < κ)
    (hS : Cardinal.mk S < θ) (hA : ∀ i ∈ S, Cardinal.mk (A i) < θ) : Cardinal.mk (Family κ A S) < θ := by
  let code (p : Family κ A S) : Set (Σ j : S, Collapse.Condition κ (A j.val)) :=
    Set.range (fun j : S => Sigma.mk j (p.value j.val))
  have hinj : Function.Injective code := by
    intro p q he
    apply value_injective
    funext i
    by_cases hi : i ∈ S
    · let j : S := ⟨i,hi⟩
      obtain ⟨k,hk⟩ := (Set.ext_iff.mp he (Sigma.mk j (p.value j.val))).mp (Set.mem_range_self j)
      obtain rfl : k = j := congrArg Sigma.fst hk
      exact (eq_of_heq (Sigma.mk.inj hk).2).symm
    · exact (value_outside p hi hpos).trans (value_outside q hi hpos).symm
  apply (Cardinal.mk_le_of_injective hinj).trans_lt
  rw [Cardinal.mk_set]
  apply hθ.isStrongPrelimit
  rw [Cardinal.mk_sigma]
  exact Cardinal.sum_lt_of_isRegular hθ.isRegular hS (fun i => Collapse.cardinal_lt hθ hκ (hA i.val i.property))

abbrev Index (θ : Cardinal.{u}) := θ.ord.ToType
abbrev Alphabet (i : Index θ) := ULift.{u} Bool ⊕ i.toOrd.val.ToType
abbrev Stage (κ : Cardinal.{u}) (i : Index θ) := Family κ Alphabet (Set.Iio i)
abbrev Full (κ θ : Cardinal.{u}) := Family κ (Alphabet (θ := θ)) Set.univ

theorem alphabet_cardinal_lt (hθ : θ.IsInaccessible) (i : Index θ) : Cardinal.mk (Alphabet i) < θ := by
  rw [show Cardinal.mk (Alphabet i) = _ from Cardinal.mk_sum _ _]
  simp only [Cardinal.lift_id,Cardinal.mk_uLift,Cardinal.mk_bool,Cardinal.lift_ofNat,Cardinal.mk_toType]
  exact Cardinal.add_lt_of_lt hθ.aleph0_lt.le ((Cardinal.natCast_le_aleph0 (n := 2)).trans_lt hθ.aleph0_lt)
    (Cardinal.lt_ord.mp i.toOrd.property)

theorem stage_cardinal_lt (hθ : θ.IsInaccessible) (hκ : κ < θ) (hpos : 0 < κ) (i : Index θ) :
    Cardinal.mk (Stage κ i) < θ :=
  cardinal_lt hθ hκ hpos (by simpa [Index] using (Cardinal.mk_Iio_lt i (by simp [Index])))
    (fun j _ => alphabet_cardinal_lt hθ j)

def pairIso {B C D E : Type u} [PartialOrder B] [PartialOrder C] [PartialOrder D] [PartialOrder E]
    (b : B ≃o C) (d : D ≃o E) : B × D ≃o C × E where
  toEquiv := b.toEquiv.prodCongr d.toEquiv
  map_rel_iff' := and_congr b.le_iff_le d.le_iff_le

def stageProjection (hκ : Cardinal.aleph0 ≤ κ) {i j : Index θ} (hij : i ≤ j) :
    PartialProjection κ (Stage κ j) (Stage κ i) :=
  productProjection (split hκ (Set.Iio_subset_Iio hij)) (empty (Cardinal.aleph0_pos.trans_le hκ))

theorem stageProjection_apply (hκ : Cardinal.aleph0 ≤ κ) {i j : Index θ} (hij : i ≤ j) (p : Stage κ j) :
    (stageProjection hκ hij).proj ⟨p,Set.mem_univ _⟩ = cut (Cardinal.aleph0_pos.trans_le hκ) (Set.Iio i) p := rfl

abbrev Remainder (κ : Cardinal.{u}) (i t j : Index θ) :=
  Family κ Alphabet ((Set.Iio j \ Set.Iio i) \ {t})

def stageSplit (hκ : Cardinal.aleph0 ≤ κ) {i t j : Index θ} (hit : i ≤ t) (htj : t < j) :
    Stage κ j ≃o (Stage κ i × Collapse.Condition κ (Alphabet t)) × Remainder κ i t j := by
  let e₀ := split (A := Alphabet) hκ (Set.Iio_subset_Iio (hit.trans htj.le))
  have ht : {t} ⊆ Set.Iio j \ Set.Iio i := Set.singleton_subset_iff.mpr ⟨htj,not_lt_of_ge hit⟩
  let e₁ := (split (A := Alphabet) hκ ht).trans (pairIso (singletonIso hκ t) (OrderIso.refl _))
  exact (e₀.trans (pairIso (OrderIso.refl _) e₁)).trans (OrderIso.prodAssoc _ _ _).symm

theorem stageSplit_base (hκ : Cardinal.aleph0 ≤ κ) {i t j : Index θ} (hit : i ≤ t) (htj : t < j) (p : Stage κ j) :
    (stageSplit hκ hit htj p).1.1 = (stageProjection hκ (hit.trans htj.le)).proj ⟨p, Set.mem_univ _⟩ := rfl

theorem stageSplit_coordinate (hκ : Cardinal.aleph0 ≤ κ) {i t j : Index θ}
    (hit : i ≤ t) (htj : t < j) (p : Stage κ j) : (stageSplit hκ hit htj p).1.2 = p.value t := by
  let pos := Cardinal.aleph0_pos.trans_le hκ
  change (cut pos {t} (cut pos (Set.Iio j \ Set.Iio i) p)).value t = _
  exact (cut_at pos _ (Set.mem_singleton t)).trans (cut_at pos p ⟨htj,not_lt_of_ge hit⟩)

end Erdos1172Shioya.LevyProduct
