/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CofinalPowerEndpoints

@[expose] public section

/-!
# Cofinal finite-power cuts and exact row bounds

Any cofinal finite-power subset of a small well-order supplies an actual
omegaOne cut sequence. Its proper row sections have smaller order type.
Conversely, countably complete finite-power smallness on every row gives
the correct whole-order upper bound. The cut and bound constructions
are independent of an assumed higher-dimensional covering family.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CofinalFiniteCuts

open ErdosRadoCHAsym (W1)
open Erdos1172Part3FiniteTraceSchemes (Index typeLT_index)
open Erdos1172Part3CofinalLineCover (LineCoverData)
open Erdos1172Part3HechlerOrder (exists_bound_of_countable)

variable {V : Type} [LinearOrder V] [WellFoundedLT V]

theorem cofinal_prefix_type_lt (A : Set V) (hA : IsCofinal A) (x : V) :
    typeLT (A ∩ Set.Iio x : Set V) < typeLT A := by
  obtain ⟨a, ha, hxa⟩ := hA x
  let f : (A ∩ Set.Iio x : Set V) → Set.Iio (⟨a, ha⟩ : A) :=
    fun y => ⟨⟨y.val, y.property.1⟩, y.property.2.trans_le hxa⟩
  have hf : StrictMono f := fun _ _ h => h
  have hle := (RelEmbedding.ofMonotone f hf).ordinal_type_le
  exact hle.trans_lt (Ordinal.typein_lt_type _ (⟨a, ha⟩ : A))

theorem typeLT_le_of_prefix_type_lt (A : Set V) (δ : Ordinal.{0})
    (hprefix : ∀ x : V, typeLT (A ∩ Set.Iio x : Set V) < δ) : typeLT A ≤ δ := by
  have hlt (x : A) : Ordinal.typein ((· < ·) : A → A → Prop) x < δ := by
    let f : Set.Iio x → (A ∩ Set.Iio x.val : Set V) :=
      fun y => ⟨y.val.val, y.val.property, y.property⟩
    have hf : StrictMono f := fun _ _ h => h
    exact (RelEmbedding.ofMonotone f hf).ordinal_type_le.trans_lt (hprefix x.val)
  by_contra h
  obtain ⟨x, hx⟩ := Ordinal.typein_surj ((· < ·) : A → A → Prop) (lt_of_not_ge h)
  exact (hlt x).ne hx

noncomputable def basePoint : (n : ℕ) → Index n
  | 0 => Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩
  | n + 1 => toLex (Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩, basePoint n)

noncomputable def lineIndex : (n : ℕ) → W1 → Index n
  | 0 => id
  | n + 1 => fun i => toLex (i, basePoint n)

theorem lineIndex_strict (n : ℕ) : StrictMono (lineIndex n) := by
  cases n with
  | zero => exact strictMono_id
  | succ n =>
    intro x y hxy
    rw [Prod.Lex.lt_iff]
    exact Or.inl hxy

theorem lineIndex_cofinal (n : ℕ) (x : Index n) : ∃ i : W1, x < lineIndex n i := by
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := exists_bound_of_countable ({x} : Set W1) (by simp)
    exact ⟨i, hi x (by simp)⟩
  | succ n =>
    obtain ⟨i, hi⟩ := exists_bound_of_countable ({(ofLex x).1} : Set W1) (by simp)
    refine ⟨i, ?_⟩
    rw [Prod.Lex.lt_iff]
    exact Or.inl (hi (ofLex x).1 (by simp))

theorem exists_finite_power_lineCutData (hV : #V ≤ ℵ_ 1) (n : ℕ) (A : Set V)
    (hA : IsCofinal A) (htype : typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    Nonempty (LineCoverData V) := by
  have heq : typeLT (Index n) = typeLT A := (typeLT_index n).trans htype.symm
  obtain ⟨e⟩ := Ordinal.type_eq.mp heq
  let cut : W1 → V := fun i => (e (lineIndex n i)).val
  have hstrict : StrictMono cut := fun _ _ h => e.map_rel_iff.mpr (lineIndex_strict n h)
  have hcofinal : ∀ x : V, ∃ i : W1, x < cut i := by
    intro x
    obtain ⟨a, ha, hxa⟩ := hA x
    obtain ⟨j, hj⟩ := e.surjective (⟨a, ha⟩ : A)
    obtain ⟨i, hji⟩ := lineIndex_cofinal n j
    have hlt : (e j).val < cut i := e.map_rel_iff.mpr hji
    rw [hj] at hlt
    exact ⟨i, hxa.trans_lt hlt⟩
  obtain ⟨code⟩ : Nonempty (V ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using hV)
  exact ⟨⟨cut, hstrict, hcofinal, code⟩⟩

def rowSection (data : LineCoverData V) (A : Set V) (i : W1) : Set V :=
  {x | x ∈ A ∧ data.row x = i}

theorem cofinal_row_type_lt (data : LineCoverData V) (A : Set V) (hA : IsCofinal A) (i : W1) :
    typeLT (rowSection data A i) < typeLT A := by
  apply (Ordinal.type_mono (show rowSection data A i ⊆ (A ∩ Set.Iio (data.cut i) : Set V) from ?_)).trans_lt
    (cofinal_prefix_type_lt A hA (data.cut i))
  intro x hx
  exact ⟨hx.1, hx.2 ▸ data.lt_cut_row x⟩

theorem typeLT_le_finite_power_of_rows_small (data : LineCoverData V) (n : ℕ) (A : Set V)
    (hrows : ∀ i : W1, typeLT (rowSection data A i) <
      (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)) :
    typeLT A ≤ (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) := by
  apply typeLT_le_of_prefix_type_lt
  intro x
  have hc : (Set.Iic (data.row x)).Countable := Cardinal.le_aleph0_iff_set_countable.mp
    (Cardinal.lt_aleph_one_iff.mp (Erdos1172Part3ConvergentCore.mk_Iic_W1_lt (data.row x)))
  have hsmall := Erdos1172Part3FiniteOrderTypeIdeal.countable_biUnion_type_lt_finite_power n
    (Set.Iic (data.row x)) hc (rowSection data A) (fun i _ => hrows i)
  apply (Ordinal.type_mono (show (A ∩ Set.Iio x : Set V) ⊆
    ⋃ i ∈ Set.Iic (data.row x), rowSection data A i from ?_)).trans_lt hsmall
  intro y hy
  exact Set.mem_iUnion.mpr ⟨data.row y, Set.mem_iUnion.mpr ⟨data.row_mono hy.2.le, hy.1, rfl⟩⟩

theorem covers_of_countable_prefixes (data : LineCoverData V) (A : Set V)
    (hprefix : ∀ x : V, (A ∩ Set.Iio x).Countable) : ∃ f : W1 → W1, A ⊆ data.cover f := by
  classical
  have hrow (i : W1) : (rowSection data A i).Countable := by
    apply (hprefix (data.cut i)).mono
    intro x hx
    exact ⟨hx.1, hx.2 ▸ data.lt_cut_row x⟩
  have hbound (i : W1) : ∃ b : W1, ∀ x : V, x ∈ A → data.row x = i → data.code x < b := by
    obtain ⟨b, hb⟩ := exists_bound_of_countable (data.code '' rowSection data A i)
      ((hrow i).image data.code)
    exact ⟨b, fun x hx hi => hb (data.code x) ⟨x, ⟨hx, hi⟩, rfl⟩⟩
  choose bounds hb using hbound
  exact ⟨bounds, fun x hx => Or.inr (hb (data.row x) x hx rfl)⟩

end Erdos1172Part3CofinalFiniteCuts
