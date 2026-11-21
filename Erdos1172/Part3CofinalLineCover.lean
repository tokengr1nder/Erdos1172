/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3OmegaSuccessorCore

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
    exact Set.mem_iUnion.mpr ⟨data.row y, Set.mem_iUnion.mpr ⟨data.row_mono hy.2.le, rfl, hy.1⟩⟩
  have hseed := cofinal_omegaOne_prefix_countable data.seed data.seed_cofinal data.seed_type x
  apply (hseed.union hraw).mono
  intro y hy
  rcases hy.1 with hyseed | hyraw
  · exact Or.inl ⟨hyseed, hy.2⟩
  · exact Or.inr ⟨hyraw, hy.2⟩

end Erdos1172Part3CofinalLineCover
