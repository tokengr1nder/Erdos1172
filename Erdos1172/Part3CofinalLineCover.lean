/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3WeakFiniteTraceLaws

@[expose] public section

/-!
# Monotone covers of cofinal omegaOne subsets

On a well-order of cardinality at most alephOne which has a cofinal
omegaOne subset, construct a monotone family of exact omegaOne covers
indexed by functions W1 -> W1. Every cofinal omegaOne subset belongs to
one cover. This is the first-dimensional covering step of BHT Lemma 4.2;
it does not assume the domination principle or a higher-dimensional cover.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CofinalLineCover

open ErdosRadoCHAsym (W1)
open Erdos1172Part3ConvergentCore (mk_Iio_W1_lt mk_Iic_W1_lt)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

theorem cofinal_omegaOne_prefix_countable (A : Set V) (hA : IsCofinal A)
    (htype : typeLT A = ω_ 1) (x : V) : (A ∩ Set.Iio x).Countable := by
  obtain ⟨a, ha, hxa⟩ := hA x
  have hcardA : #A = ℵ_ 1 := by
    rw [← Ordinal.card_type ((· < ·) : A → A → Prop)]
    change (typeLT A).card = ℵ_ 1
    rw [htype, Ordinal.card_omega]
  have hcard : #(Set.Iio (⟨a, ha⟩ : A)) < ℵ_ 1 := by
    have h := Cardinal.mk_Iio_lt (⟨a, ha⟩ : A)
      (show Cardinal.ord #A = typeLT A by rw [hcardA, htype, Cardinal.ord_aleph])
    simpa only [hcardA] using h
  let e : (A ∩ Set.Iio x : Set V) ↪ Set.Iio (⟨a, ha⟩ : A) := {
    toFun y := ⟨⟨y.val, y.property.1⟩, y.property.2.trans_le hxa⟩
    inj' := fun _ _ h => Subtype.ext (congrArg (fun z : Set.Iio (⟨a, ha⟩ : A) => z.val.val) h) }
  exact Cardinal.le_aleph0_iff_set_countable.mp
    ((Cardinal.mk_le_of_injective e.injective).trans (Cardinal.lt_aleph_one_iff.mp hcard))

theorem typeLT_le_omegaOne_of_countable_prefixes (A : Set V)
    (hprefix : ∀ x : V, (A ∩ Set.Iio x).Countable) : typeLT A ≤ ω_ 1 := by
  have hlt (x : A) : Ordinal.typein ((· < ·) : A → A → Prop) x < ω_ 1 := by
    rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_typein]
    let e : Set.Iio x ↪ (A ∩ Set.Iio x.val : Set V) := {
      toFun y := ⟨y.val.val, y.val.property, y.property⟩
      inj' := fun _ _ h => Subtype.ext (Subtype.ext
        (congrArg (fun z : (A ∩ Set.Iio x.val : Set V) => z.val) h)) }
    exact Cardinal.lt_aleph_one_iff.mpr ((Cardinal.mk_le_of_injective e.injective).trans
      (Cardinal.le_aleph0_iff_set_countable.mpr (hprefix x.val)))
  by_contra h
  obtain ⟨x, hx⟩ := Ordinal.typein_surj ((· < ·) : A → A → Prop) (lt_of_not_ge h)
  exact (hlt x).ne hx

structure LineCoverData (V : Type) [LinearOrder V] where
  cut : W1 → V
  strict : StrictMono cut
  cofinal : ∀ x : V, ∃ i : W1, x < cut i
  code : V ↪ W1

noncomputable def LineCoverData.row (data : LineCoverData V) (x : V) : W1 :=
  wellFounded_lt.min {i : W1 | x < data.cut i} (data.cofinal x)

omit [WellFoundedLT V] in
theorem LineCoverData.lt_cut_row (data : LineCoverData V) (x : V) : x < data.cut (data.row x) :=
  wellFounded_lt.min_mem {i : W1 | x < data.cut i} (data.cofinal x)

omit [WellFoundedLT V] in
theorem LineCoverData.row_le (data : LineCoverData V) (x : V) (i : W1) (hi : x < data.cut i) :
    data.row x ≤ i := wellFounded_lt.min_le (s := {j : W1 | x < data.cut j}) hi

omit [WellFoundedLT V] in
theorem LineCoverData.row_mono (data : LineCoverData V) : Monotone data.row := by
  intro x y hxy
  exact data.row_le x (data.row y) (hxy.trans_lt (data.lt_cut_row y))

def LineCoverData.seed (data : LineCoverData V) : Set V := Set.range data.cut

omit [WellFoundedLT V] in
theorem LineCoverData.seed_cofinal (data : LineCoverData V) : IsCofinal data.seed := by
  intro x
  obtain ⟨i, hi⟩ := data.cofinal x
  exact ⟨data.cut i, ⟨i, rfl⟩, hi.le⟩

theorem LineCoverData.seed_type (data : LineCoverData V) : typeLT data.seed = ω_ 1 := by
  rw [LineCoverData.seed, Ordinal.typeLT_range_of_strictMono data.cut data.strict]
  exact Ordinal.type_toType _

noncomputable def LineCoverData.cover (data : LineCoverData V) (f : W1 → W1) : Set V :=
  data.seed ∪ {x | data.code x < f (data.row x)}

omit [WellFoundedLT V] in
theorem LineCoverData.cover_mono (data : LineCoverData V) : Monotone data.cover := by
  intro f g hfg x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (hx.trans_le (hfg (data.row x)))

omit [WellFoundedLT V] in
theorem LineCoverData.cover_cofinal (data : LineCoverData V) (f : W1 → W1) :
    IsCofinal (data.cover f) := data.seed_cofinal.mono Set.subset_union_left

omit [WellFoundedLT V] in
theorem LineCoverData.row_selection_countable (data : LineCoverData V) (f : W1 → W1) (i : W1) :
    {x : V | data.row x = i ∧ data.code x < f i}.Countable := by
  let e : {x : V | data.row x = i ∧ data.code x < f i} ↪ Set.Iio (f i) := {
    toFun x := ⟨data.code x.val, x.property.2⟩
    inj' := fun _ _ h => Subtype.ext (data.code.injective (congrArg Subtype.val h)) }
  exact Cardinal.le_aleph0_iff_set_countable.mp
    ((Cardinal.mk_le_of_injective e.injective).trans (Cardinal.lt_aleph_one_iff.mp (mk_Iio_W1_lt (f i))))

theorem LineCoverData.cover_prefix_countable (data : LineCoverData V) (f : W1 → W1) (x : V) :
    (data.cover f ∩ Set.Iio x).Countable := by
  have hrows : (Set.Iic (data.row x)).Countable :=
    Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp (mk_Iic_W1_lt (data.row x)))
  have hraw : ({y : V | data.code y < f (data.row y)} ∩ Set.Iio x).Countable := by
    apply (hrows.biUnion (fun i _ => data.row_selection_countable f i)).mono
    intro y hy
    exact Set.mem_iUnion.mpr ⟨data.row y, Set.mem_iUnion.mpr
      ⟨data.row_mono hy.2.le, rfl, hy.1⟩⟩
  have hseed := cofinal_omegaOne_prefix_countable data.seed data.seed_cofinal data.seed_type x
  apply (hseed.union hraw).mono
  intro y hy
  rcases hy.1 with hyseed | hyraw
  · exact Or.inl ⟨hyseed, hy.2⟩
  · exact Or.inr ⟨hyraw, hy.2⟩

theorem LineCoverData.cover_type (data : LineCoverData V) (f : W1 → W1) :
    typeLT (data.cover f) = ω_ 1 := by
  apply le_antisymm (typeLT_le_omegaOne_of_countable_prefixes _ (data.cover_prefix_countable f))
  rw [← data.seed_type]
  exact Ordinal.type_mono (show data.seed ⊆ data.cover f from Set.subset_union_left)

theorem LineCoverData.covers (data : LineCoverData V) (A : Set V) (hA : IsCofinal A)
    (htype : typeLT A = ω_ 1) : ∃ f : W1 → W1, A ⊆ data.cover f := by
  classical
  have hrow (i : W1) : {x : V | x ∈ A ∧ data.row x = i}.Countable := by
    apply (cofinal_omegaOne_prefix_countable A hA htype (data.cut i)).mono
    intro x hx
    exact ⟨hx.1, hx.2 ▸ data.lt_cut_row x⟩
  have hbound (i : W1) : ∃ b : W1, ∀ x : V, x ∈ A → data.row x = i → data.code x < b := by
    obtain ⟨b, hb⟩ := exists_bound_of_countable
      (data.code '' {x : V | x ∈ A ∧ data.row x = i}) ((hrow i).image data.code)
    exact ⟨b, fun x hx hi => hb (data.code x) ⟨x, ⟨hx, hi⟩, rfl⟩⟩
  choose bounds hb using hbound
  exact ⟨bounds, fun x hx => Or.inr (hb (data.row x) x hx rfl)⟩

theorem exists_lineCoverData (hV : #V ≤ ℵ_ 1) (A : Set V) (hA : IsCofinal A)
    (htype : typeLT A = ω_ 1) : Nonempty (LineCoverData V) := by
  classical
  have heq : typeLT W1 = typeLT A := by rw [htype]; exact Ordinal.type_toType _
  obtain ⟨e⟩ := Ordinal.type_eq.mp heq
  let cut : W1 → V := fun i => (e i).val
  have hstrict : StrictMono cut := fun _ _ h => e.map_rel_iff.mpr h
  have hcofinal : ∀ x : V, ∃ i : W1, x < cut i := by
    intro x
    obtain ⟨a, ha, hxa⟩ := hA x
    obtain ⟨i, hi⟩ := e.surjective (⟨a, ha⟩ : A)
    obtain ⟨j, hj⟩ := exists_bound_of_countable ({i} : Set W1) (by simp)
    have hc : cut i = a := congrArg Subtype.val hi
    exact ⟨j, (hxa.trans_eq hc.symm).trans_lt (hstrict (hj i (by simp)))⟩
  obtain ⟨code⟩ : Nonempty (V ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using hV)
  exact ⟨⟨cut, hstrict, hcofinal, code⟩⟩

theorem exists_monotone_cofinal_line_covers (hV : #V ≤ ℵ_ 1)
    (hseed : ∃ A : Set V, IsCofinal A ∧ typeLT A = ω_ 1) :
    ∃ cover : (W1 → W1) → Set V, Monotone cover ∧
      (∀ f, IsCofinal (cover f) ∧ typeLT (cover f) = ω_ 1) ∧
      ∀ A : Set V, IsCofinal A → typeLT A = ω_ 1 → ∃ f : W1 → W1, A ⊆ cover f := by
  obtain ⟨A, hA, htype⟩ := hseed
  obtain ⟨data⟩ := exists_lineCoverData hV A hA htype
  exact ⟨data.cover, data.cover_mono, fun f => ⟨data.cover_cofinal f, data.cover_type f⟩, data.covers⟩

end Erdos1172Part3CofinalLineCover
