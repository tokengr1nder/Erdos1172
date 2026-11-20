/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CountableSupportProfiles

@[expose] public section

/-!
# Countably universal labels on a larger coordinate set

Under CH, at most `2 ^ alephOne` coordinates with at most `alephOne`
labels admit an `omegaOne`-indexed family extending every countable
partial labelling. This is a covering family, not an injective code for
the partial labellings. In particular it applies to omegaTwo coordinates
under GCH, beyond the coordinate bound of injective profile coding.
-/

open Cardinal Ordinal Set Function

namespace Erdos1172Part3CountablyUniversalLabels

open ErdosRadoCHAsym (W1 W2)
open Erdos1172Part3CountableSupportProfiles (Profile support mk_Profile_le)

abbrev Coordinates := {d : Set W1 // d.Countable}

abbrev Signature (d : Coordinates) := d.val → Bool

abbrev Table (V : Type) := Σ d : Coordinates, Profile (Signature d) V

theorem mk_coordinates_le (hCH : CH) : #Coordinates ≤ ℵ_ 1 := by
  let encode (d : Coordinates) : {s : Set W1 // #s ≤ ℵ₀} :=
    ⟨d.val, Cardinal.le_aleph0_iff_set_countable.mpr d.property⟩
  have hinj : Injective encode :=
    fun _ _ h => Subtype.ext (congrArg (fun c : {s : Set W1 // #s ≤ ℵ₀} => c.val) h)
  apply (Cardinal.mk_le_of_injective hinj).trans
  simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega,
    max_eq_left (Cardinal.aleph0_le_aleph 1), hCH.aleph_one_power_aleph_zero]
    using Cardinal.mk_bounded_set_le W1 ℵ₀

theorem mk_signature_le (hCH : CH) (d : Coordinates) : #(Signature d) ≤ ℵ_ 1 := by
  change #(d.val → Bool) ≤ ℵ_ 1
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.lift_id, Cardinal.mk_bool]
  exact (Cardinal.power_le_power_left (by norm_num : (2 : Cardinal) ≠ 0)
    (Cardinal.le_aleph0_iff_set_countable.mpr d.property)).trans_eq (Cardinal.CH_iff.mp hCH)

theorem mk_table_le {V : Type} (hCH : CH) (hV : #V ≤ ℵ_ 1) : #(Table V) ≤ ℵ_ 1 := by
  change #(Σ d : Coordinates, Profile (Signature d) V) ≤ ℵ_ 1
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun d : Coordinates => #(Profile (Signature d) V))
        ≤ Cardinal.sum (fun _ : Coordinates => ℵ_ 1) :=
      Cardinal.sum_le_sum _ _ (fun d => mk_Profile_le hCH (mk_signature_le hCH d) hV)
    _ = #Coordinates * ℵ_ 1 := Cardinal.sum_const' _ _
    _ ≤ ℵ_ 1 * ℵ_ 1 := mul_le_mul' (mk_coordinates_le hCH) le_rfl
    _ = ℵ_ 1 := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)

variable {I V : Type}

def signature (e : I ↪ (W1 → Bool)) (d : Coordinates) (i : I) : Signature d :=
  fun x => e i x.val

/-- Countably many coordinates distinguish every pair in any countable
set of labels of the full Boolean cube. -/
theorem exists_separating_coordinates (e : I ↪ (W1 → Bool))
    (s : Set I) (hs : s.Countable) :
    ∃ d : Coordinates, Set.InjOn (signature e d) s := by
  classical
  have hw (i j : I) (hij : i ≠ j) : ∃ x : W1, e i x ≠ e j x := by
    by_contra hn
    push Not at hn
    exact hij (e.injective (funext hn))
  let chooseCoord (z : I × I) : W1 :=
    if h : z.1 ≠ z.2 then (hw z.1 z.2 h).choose else
      Classical.choice (Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos 1).ne')
  let d : Coordinates := ⟨chooseCoord '' (s ×ˢ s), (hs.prod hs).image chooseCoord⟩
  refine ⟨d, ?_⟩
  intro i hi j hj heq
  by_contra hne
  have hx : chooseCoord (i, j) ∈ d.val := ⟨(i, j), ⟨hi, hj⟩, rfl⟩
  have hvalues : e i (chooseCoord (i, j)) = e j (chooseCoord (i, j)) :=
    congrFun heq ⟨chooseCoord (i, j), hx⟩
  have hnevalues : e i (chooseCoord (i, j)) ≠ e j (chooseCoord (i, j)) := by
    simpa only [chooseCoord, dif_pos hne] using (hw i j hne).choose_spec
  exact hnevalues hvalues

def evaluate (e : I ↪ (W1 → Bool)) (t : Table V) (i : I) : Option V :=
  t.2.val (signature e t.1 i)

/-- Every countable partial labelling has one table extending all its
specified values. The table itself uses only countably many signatures. -/
theorem exists_table_extension (e : I ↪ (W1 → Bool)) (p : Profile I V) :
    ∃ t : Table V, ∀ i v, p.val i = some v → evaluate e t i = some v := by
  classical
  obtain ⟨d, hd⟩ := exists_separating_coordinates e (support p) p.property
  let key := signature e d
  let entry (k : Signature d) : Option V :=
    if h : ∃ i ∈ support p, key i = k then p.val h.choose else none
  have hsupport : {k | entry k ≠ none} ⊆ key '' support p := by
    intro k hk
    by_cases h : ∃ i ∈ support p, key i = k
    · exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩
    · change entry k ≠ none at hk
      simp only [entry, dif_neg h, ne_eq, not_true_eq_false] at hk
  let t : Table V := ⟨d, entry, ((p.property.image key).mono hsupport)⟩
  refine ⟨t, ?_⟩
  intro i v hiv
  have hi : i ∈ support p := by
    change p.val i ≠ none
    rw [hiv]
    exact Option.some_ne_none v
  have hex : ∃ j ∈ support p, key j = key i := ⟨i, hi, rfl⟩
  have hj : hex.choose = i := hd hex.choose_spec.1 hi hex.choose_spec.2
  change entry (key i) = some v
  simp only [entry, dif_pos hex, hj, hiv]

structure CountableCover (I V : Type) where
  label : W1 → I → Option V
  covers : ∀ p : Profile I V, ∃ c : W1, ∀ i v, p.val i = some v → label c i = some v

/-- The coordinate cardinality may be as large as the full Boolean cube.
No injectivity of the resulting cover code is claimed. -/
theorem exists_countableCover (hCH : CH) (hI : #I ≤ 2 ^ (ℵ_ 1)) (hV : #V ≤ ℵ_ 1) :
    Nonempty (CountableCover I V) := by
  classical
  obtain ⟨e⟩ : Nonempty (I ↪ (W1 → Bool)) := (Cardinal.le_def _ _).mp (by
    simpa only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_bool, W1,
      Cardinal.mk_toType, Ordinal.card_omega] using hI)
  obtain ⟨rank⟩ : Nonempty (Table V ↪ W1) := (Cardinal.le_def _ _).mp (by
    simpa only [W1, Cardinal.mk_toType, Ordinal.card_omega] using mk_table_le hCH hV)
  let F (c : W1) : I → Option V :=
    if h : ∃ t, rank t = c then evaluate e h.choose else fun _ => none
  refine ⟨⟨F, ?_⟩⟩
  intro p
  obtain ⟨t, ht⟩ := exists_table_extension e p
  have hex : ∃ u, rank u = rank t := ⟨t, rfl⟩
  have hu : hex.choose = t := rank.injective hex.choose_spec
  refine ⟨rank t, ?_⟩
  intro i v hiv
  simpa only [F, dif_pos hex, hu] using ht i v hiv

theorem exists_countableCover_of_gch (hGCH : GCH) (hI : #I ≤ ℵ_ 2) (hV : #V ≤ ℵ_ 1) :
    Nonempty (CountableCover I V) := by
  apply exists_countableCover hGCH.toCH _ hV
  have hp : (2 : Cardinal) ^ (ℵ_ 1) = ℵ_ 2 := by
    simpa only [Order.succ_eq_add_one, show (1 : Ordinal) + 1 = 2 by norm_num] using hGCH 1
  rwa [hp]

noncomputable def CountableCover.code (cover : CountableCover I V) (p : Profile I V) : W1 :=
  (cover.covers p).choose

theorem CountableCover.code_spec (cover : CountableCover I V) (p : Profile I V)
    (i : I) (v : V) (hiv : p.val i = some v) :
    cover.label (cover.code p) i = some v := (cover.covers p).choose_spec i v hiv

theorem CountableCover.agree_on_overlap (cover : CountableCover I V)
    {p q : Profile I V} (hcode : cover.code p = cover.code q)
    {i : I} {v w : V} (hp : p.val i = some v) (hq : q.val i = some w) : v = w := by
  have hv := cover.code_spec p i v hp
  have hw := cover.code_spec q i w hq
  rw [hcode] at hv
  exact Option.some.inj (hv.symm.trans hw)

end Erdos1172Part3CountablyUniversalLabels
