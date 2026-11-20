/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4GroundFineSeedOrderType
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-!
# Canonical huge-cardinal measure characterization and automatic inaccessibility

Under `(U, a)` with `FineOn U a`, `NormalOn U a`, `FiberOrderType U κ θ a` (`ot(a i) = κ`),
`CardinalInterFilter (U : Filter I) κ`, and `κ < θ`:

1. If `[CountableInterFilter (U : Filter I)]` holds, then `ℵ₀ < κ`, `κ.IsInaccessible`, and
   `θ.IsInaccessible` are all derived theorems (`aleph0_lt_of_fine_order_type`,
   `inaccessible_source_of_fine_order_type`, `inaccessible_target_of_fine_order_type`,
   `inaccessible_pair_of_fine_order_type`).
2. Conversely, if `ℵ₀ < κ` holds, then `CountableInterFilter (U : Filter I)`, `κ.IsInaccessible`,
   and `θ.IsInaccessible` are all derived without assuming `CountableInterFilter` separately
   (`inaccessible_source_of_aleph0_lt`, `inaccessible_pair_of_aleph0_lt`).
3. Packaging Kanamori's canonical measure presentation (*The Higher Infinite*, Theorem 24.8) on
   `HugeFiberSpace κ θ := {s : Set θ.ord.ToType // Nonempty (κ.ord.ToType ≃o s)}` defines
   `IsHugeWithTarget κ θ` and `IsHugeCardinal κ`, proved equivalent (`isHugeWithTarget_iff_exists_fine_measure`)
   to the general `(I, U, a)` presentation via `Ultrafilter.map`.
-/

set_option autoImplicit false
noncomputable section

open Filter Cardinal Order Ordinal Set

universe u

namespace Erdos1172GroundUltrapower

section DerivedInaccessibility

private theorem toType_lt_iff_val_lt {o : Ordinal.{u}} {x y : o.ToType} :
    x < y ↔ x.toOrd.val < y.toOrd.val :=
  (Ordinal.ToType.mk.symm.lt_iff_lt).symm.trans Subtype.mk_lt_mk

private theorem toType_Iio_card_lt {c : Cardinal.{u}} (b : c.ord.ToType) :
    #(Set.Iio b) < c := by
  let emb : Set.Iio b ↪ b.toOrd.val.ToType :=
    { toFun := fun u =>
        Ordinal.ToType.mk ⟨u.val.toOrd.val, toType_lt_iff_val_lt.mp u.property⟩
      inj' := fun u₁ u₂ h => by
        have hv := congrArg (fun z : b.toOrd.val.ToType => z.toOrd.val) h
        simp only [Ordinal.ToType.mk.symm_apply_apply] at hv
        exact Subtype.ext (Ordinal.ToType.mk.symm.injective (Subtype.ext hv)) }
  refine (Cardinal.mk_le_of_injective emb.injective).trans_lt ?_
  rw [Cardinal.mk_toType]
  exact Cardinal.lt_ord.mp b.toOrd.property

private theorem exists_cut_with_card {θ μ : Cardinal.{u}} (hμ : μ < θ) :
    ∃ β : θ.ord.ToType, #(Set.Iio β) = μ := by
  have hord : μ.ord < θ.ord := Cardinal.ord_lt_ord.mpr hμ
  let β : θ.ord.ToType := Ordinal.ToType.mk ⟨μ.ord, hord⟩
  have hβ_eq : β.toOrd.val = μ.ord :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply ⟨μ.ord, hord⟩)
  let e : Set.Iio β ≃ μ.ord.ToType :=
    { toFun := fun u =>
        Ordinal.ToType.mk ⟨u.val.toOrd.val,
          show u.val.toOrd.val < μ.ord from (toType_lt_iff_val_lt.mp u.property).trans_eq hβ_eq⟩
      invFun := fun v =>
        let hv_lt : v.toOrd.val < θ.ord := lt_trans (show v.toOrd.val < μ.ord from v.toOrd.property) hord
        ⟨Ordinal.ToType.mk ⟨v.toOrd.val, hv_lt⟩,
          show Ordinal.ToType.mk ⟨v.toOrd.val, hv_lt⟩ < β from
            toType_lt_iff_val_lt.mpr
              ((congrArg Subtype.val
                (Ordinal.ToType.mk.symm_apply_apply ⟨v.toOrd.val, hv_lt⟩)).trans_lt
                ((show v.toOrd.val < μ.ord from v.toOrd.property).trans_eq hβ_eq.symm))⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Ordinal.ToType.mk.symm.injective
        apply Subtype.ext
        simp only [Ordinal.ToType.mk.symm_apply_apply]
      right_inv := fun v => by
        apply Ordinal.ToType.mk.symm.injective
        apply Subtype.ext
        simp only [Ordinal.ToType.mk.symm_apply_apply] }
  exact ⟨β, (Cardinal.mk_congr e).trans (Cardinal.mk_ord_toType μ)⟩

theorem pos_source_of_fine_order_type {I : Type u} {κ θ : Cardinal.{u}}
    (U : Ultrafilter I) {a : I → Set θ.ord.ToType}
    (hk : κ < θ) (hf : FineOn U a) (ht : FiberOrderType U κ θ a) :
    0 < κ := by
  rcases eq_or_ne κ 0 with rfl | hne
  · have hθ0 : (0 : Ordinal.{u}) < θ.ord := by
      rw [← Cardinal.ord_zero]
      exact Cardinal.ord_lt_ord.mpr hk
    let ξ₀ : θ.ord.ToType := Ordinal.ToType.mk ⟨0, hθ0⟩
    obtain ⟨i, hi_ot, hi_ξ⟩ := (ht.and (hf ξ₀)).exists
    let k : (0 : Cardinal.{u}).ord.ToType := (Classical.choice hi_ot).symm ⟨ξ₀, hi_ξ⟩
    have hk_lt : k.toOrd.val < (0 : Ordinal.{u}) :=
      (show k.toOrd.val < (0 : Cardinal.{u}).ord from k.toOrd.property).trans_eq Cardinal.ord_zero
    exact (not_lt_of_ge zero_le hk_lt).elim
  · exact pos_iff_ne_zero.mpr hne

private theorem exists_seed_rank_exceeding {I : Type u} {κ θ : Cardinal.{u}}
    (U : Ultrafilter I) [CountableInterFilter (U : Filter I)]
    [CardinalInterFilter (U : Filter I) κ] {a : I → Set θ.ord.ToType}
    (hk : κ < θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    ∃ r : I → κ.ord.ToType, ∀ x : κ.ord.ToType, ∀ᶠ i in U, x < r i := by
  classical
  have hpos : 0 < κ := pos_source_of_fine_order_type U hk hf ht
  have hne : Nonempty κ.ord.ToType :=
    Cardinal.mk_ne_zero_iff.mp ((Cardinal.mk_ord_toType κ).trans_ne hpos.ne')
  let dflt : κ.ord.ToType := Classical.choice hne
  have hk_ord : κ.ord < θ.ord := Cardinal.ord_lt_ord.mpr hk
  let ξ₀ : θ.ord.ToType := Ordinal.ToType.mk ⟨κ.ord, hk_ord⟩
  have hξ₀_val : ξ₀.toOrd.val = κ.ord :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply ⟨κ.ord, hk_ord⟩)
  let r (i : I) : κ.ord.ToType :=
    if h : Nonempty (κ.ord.ToType ≃o a i) ∧ ξ₀ ∈ a i then
      (Classical.choice h.1).symm ⟨ξ₀, h.2⟩
    else dflt
  refine ⟨r, fun x => ?_⟩
  have hfix : collapse U (Germ.const x.toOrd.val.toZFSet) = x.toOrd.val.toZFSet :=
    diagonal_fix_of_cardinalInterFilter U κ x.toOrd.val x.toOrd.property
  have hcol : collapse U (fineRankGerm U κ θ a ξ₀) = κ.ord.toZFSet :=
    (collapse_fineRankGerm U κ θ a hf hn ht ξ₀).trans (congrArg Ordinal.toZFSet hξ₀_val)
  have hmem : collapse U (Germ.const x.toOrd.val.toZFSet) ∈ collapse U (fineRankGerm U κ θ a ξ₀) := by
    rw [hfix, hcol]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr x.toOrd.property
  have hev : memRel U (Germ.const x.toOrd.val.toZFSet) (fineRankGerm U κ θ a ξ₀) :=
    (collapse_mem_collapse_iff U _ _).mp hmem
  filter_upwards [hev, ht, hf ξ₀] with i hi hi_ot hi_ξ
  have hcond : Nonempty (κ.ord.ToType ≃o a i) ∧ ξ₀ ∈ a i := ⟨hi_ot, hi_ξ⟩
  have hr_eq : (r i).toOrd.val.toZFSet =
      ((Classical.choice hi_ot).symm ⟨ξ₀, hi_ξ⟩).toOrd.val.toZFSet := by
    simp only [r, dif_pos hcond]
  have hi_zf : x.toOrd.val.toZFSet ∈ (r i).toOrd.val.toZFSet := by
    change x.toOrd.val.toZFSet ∈
      (if h : Nonempty (κ.ord.ToType ≃o a i) ∧ ξ₀ ∈ a i then
        ((Classical.choice h.1).symm ⟨ξ₀, h.2⟩).toOrd.val.toZFSet else ∅) at hi
    rwa [dif_pos hcond, ← hr_eq] at hi
  exact toType_lt_iff_val_lt.mpr (Ordinal.toZFSet_mem_toZFSet_iff.mp hi_zf)

/-- Under `CountableInterFilter` and `CardinalInterFilter _ κ`, a `(κ, θ)`-fine normal measure
with `κ < θ` forces `ℵ₀ < κ`. -/
theorem aleph0_lt_of_fine_order_type {I : Type u} {κ θ : Cardinal.{u}}
    (U : Ultrafilter I) [CountableInterFilter (U : Filter I)]
    [CardinalInterFilter (U : Filter I) κ] {a : I → Set θ.ord.ToType}
    (hk : κ < θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    ℵ₀ < κ := by
  obtain ⟨r, hr⟩ := exists_seed_rank_exceeding U hk hf hn ht
  by_contra hnot
  have hle : #κ.ord.ToType ≤ ℵ₀ := (Cardinal.mk_ord_toType κ).trans_le (not_lt.mp hnot)
  have : Countable κ.ord.ToType := Cardinal.mk_le_aleph0_iff.mp hle
  have hall : ∀ᶠ i in U, ∀ x : κ.ord.ToType, x < r i := eventually_countable_forall.mpr hr
  obtain ⟨i, hi⟩ := hall.exists
  exact lt_irrefl (r i) (hi (r i))

/-- Under `CountableInterFilter` and `CardinalInterFilter _ κ`, a `(κ, θ)`-fine normal measure
with `κ < θ` forces `κ` to be strongly inaccessible. -/
theorem inaccessible_source_of_fine_order_type {I : Type u} {κ θ : Cardinal.{u}}
    (U : Ultrafilter I) [CountableInterFilter (U : Filter I)]
    [CardinalInterFilter (U : Filter I) κ] {a : I → Set θ.ord.ToType}
    (hk : κ < θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    κ.IsInaccessible := by
  obtain ⟨r, hr⟩ := exists_seed_rank_exceeding U hk hf hn ht
  have hω : ℵ₀ < κ := aleph0_lt_of_fine_order_type U hk hf hn ht
  refine ⟨hω, ?_, ?_⟩
  · rw [← Ordinal.cof_toType, Order.le_cof_iff]
    intro s hs
    by_contra hnot
    have hlt : #s < κ := not_le.mp hnot
    have hall : ∀ᶠ i in U, ∀ x : s, x.val < r i :=
      (Filter.eventually_cardinal_forall hlt).mpr fun x => hr x.val
    obtain ⟨i, hi⟩ := hall.exists
    obtain ⟨y, hy_mem, hy_ge⟩ := hs (r i)
    exact lt_irrefl (r i) (hy_ge.trans_lt (hi ⟨y, hy_mem⟩))
  · intro μ hμ
    by_contra hnot
    have hge : #κ.ord.ToType ≤ #(Set μ.ord.ToType) := by
      rw [Cardinal.mk_ord_toType, Cardinal.mk_set, Cardinal.mk_ord_toType]
      exact not_lt.mp hnot
    obtain ⟨F⟩ := (Cardinal.le_def _ _).mp hge
    let S : Set μ.ord.ToType := {t | ∀ᶠ i in U, t ∈ F (r i)}
    have hpt (t : μ.ord.ToType) : ∀ᶠ i in U, (t ∈ F (r i) ↔ t ∈ S) := by
      by_cases htS : t ∈ S
      · exact htS.mono fun _ h => iff_of_true h htS
      · exact (U.eventually_not.mpr htS).mono fun _ h => iff_of_false h htS
    have hcard_μ : #μ.ord.ToType < κ := (Cardinal.mk_ord_toType μ).trans_lt hμ
    have hall : ∀ᶠ i in U, F (r i) = S :=
      ((Filter.eventually_cardinal_forall hcard_μ).mpr hpt).mono fun _ hi => Set.ext hi
    obtain ⟨i₀, hi₀⟩ := hall.exists
    let x₀ : κ.ord.ToType := r i₀
    have hconst : ∀ᶠ i in U, r i = x₀ :=
      hall.mono fun i hi => F.injective (hi.trans hi₀.symm)
    obtain ⟨i, hlt, heq⟩ := ((hr x₀).and hconst).exists
    exact lt_irrefl x₀ (hlt.trans_eq heq)

private theorem fiber_closed_under_func {I : Type u} {θ : Cardinal.{u}}
    (U : Ultrafilter I) {a : I → Set θ.ord.ToType}
    (hf : FineOn U a) (hn : NormalOn U a) (g : θ.ord.ToType → θ.ord.ToType) :
    ∀ᶠ i in U, ∀ η ∈ a i, g η ∈ a i := by
  classical
  by_contra hnot
  have hex : ∀ᶠ i in U, ∃ η, η ∈ a i ∧ g η ∉ a i := by
    filter_upwards [U.eventually_not.mpr hnot] with i hi
    by_contra hall_i
    exact hi fun η hη => Classical.not_not.mp fun hgn => hall_i ⟨η, hη, hgn⟩
  obtain ⟨_, η₀, _⟩ := hex.exists
  let sel (i : I) : θ.ord.ToType :=
    if h : ∃ η, η ∈ a i ∧ g η ∉ a i then h.choose else η₀
  have hsel : ∀ᶠ i in U, sel i ∈ a i ∧ g (sel i) ∉ a i :=
    hex.mono fun i hi => by simpa only [sel, dif_pos hi] using hi.choose_spec
  obtain ⟨η, hη⟩ := hn sel (hsel.mono fun _ h => h.1)
  have hbad : ∀ᶠ i in U, g η ∉ a i :=
    (hsel.and hη).mono fun _ h => h.2 ▸ h.1.2
  obtain ⟨_, hin, hout⟩ := ((hf (g η)).and hbad).exists
  exact hout hin

/-- If `κ` is strongly inaccessible and `(U, a)` is a `(κ, θ)`-fine normal measure with `κ < θ`,
then `θ` is also strongly inaccessible. -/
theorem inaccessible_target_of_fine_order_type {I : Type u} {κ θ : Cardinal.{u}}
    (U : Ultrafilter I) {a : I → Set θ.ord.ToType}
    (hκ : κ.IsInaccessible) (hk : κ < θ)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    θ.IsInaccessible := by
  classical
  refine ⟨hκ.aleph0_lt.trans hk, ?_, ?_⟩
  · rw [← Ordinal.cof_toType, Order.le_cof_iff]
    intro s hs
    by_contra hnot
    have hlt : #s < θ := not_le.mp hnot
    obtain ⟨β, hβ_card⟩ := exists_cut_with_card hlt
    obtain ⟨emb⟩ := (Cardinal.le_def _ _).mp hβ_card.symm.le
    let g (η : θ.ord.ToType) : θ.ord.ToType :=
      if h : ∃ x : s, (emb x).val = η then h.choose.val else β
    have hg_at (x : s) : g (emb x).val = x.val := by
      have hex : ∃ y : s, (emb y).val = (emb x).val := ⟨x, rfl⟩
      simp only [g, dif_pos hex]
      have heq_sub : emb hex.choose = emb x := Subtype.ext hex.choose_spec
      exact congrArg Subtype.val (emb.injective heq_sub)
    let good (i : I) : Prop :=
      Nonempty (κ.ord.ToType ≃o a i) ∧ β ∈ a i ∧ ∀ η ∈ a i, g η ∈ a i
    have hgood : ∀ᶠ i in U, good i :=
      ht.and ((hf β).and (fiber_closed_under_func U hf hn g))
    let kTop (i : I) (hi : good i) : κ.ord.ToType :=
      let e := Classical.choice hi.1
      let b₀ : κ.ord.ToType := e.symm ⟨β, hi.2.1⟩
      let φ : Set.Iio b₀ → Ordinal.{u} := fun u =>
        (e.symm ⟨g (e u.val).val, hi.2.2 (e u.val).val (e u.val).property⟩).toOrd.val
      have hcard_u : #(Set.Iio b₀) < κ := toType_Iio_card_lt b₀
      Ordinal.ToType.mk ⟨⨆ u : Set.Iio b₀, (φ u + 1),
        Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hκ.isRegular.cof_ord])
          (fun _ => (e.symm _).toOrd.property)⟩
    let δ_fn (i : I) : θ.ord.ToType :=
      if hi : good i then ((Classical.choice hi.1) (kTop i hi)).val else β
    have hδ_mem : ∀ᶠ i in U, δ_fn i ∈ a i :=
      hgood.mono fun i hi => by simp only [δ_fn, dif_pos hi]; exact ((Classical.choice hi.1) _).property
    obtain ⟨δ, hδ_eq⟩ := hn δ_fn hδ_mem
    have hlt_δ (x : s) : x.val < δ := by
      let η := (emb x).val
      obtain ⟨i, ⟨hi, hη_in⟩, hδ_i⟩ := ((hgood.and (hf η)).and hδ_eq).exists
      let e := Classical.choice hi.1
      let b₀ : κ.ord.ToType := e.symm ⟨β, hi.2.1⟩
      let u₀ : κ.ord.ToType := e.symm ⟨η, hη_in⟩
      have hu₀_lt : u₀ < b₀ := e.symm.lt_iff_lt.mpr (emb x).property
      let φ : Set.Iio b₀ → Ordinal.{u} := fun u =>
        (e.symm ⟨g (e u.val).val, hi.2.2 (e u.val).val (e u.val).property⟩).toOrd.val
      let k_gx : κ.ord.ToType := e.symm ⟨g η, hi.2.2 η hη_in⟩
      have hφ_eq : φ ⟨u₀, hu₀_lt⟩ = k_gx.toOrd.val := by
        dsimp only [φ, k_gx, u₀]
        rw [e.apply_symm_apply ⟨η, hη_in⟩]
      have hlt_ord : k_gx.toOrd.val < (kTop i hi).toOrd.val := by
        rw [congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _), ← hφ_eq]
        exact Ordinal.lt_iSup_add_one φ ⟨u₀, hu₀_lt⟩
      have he_lt : (e k_gx).val < (e (kTop i hi)).val :=
        Subtype.mk_lt_mk.mp (e.lt_iff_lt.mpr (toType_lt_iff_val_lt.mpr hlt_ord))
      have he_gx : (e k_gx).val = x.val :=
        (congrArg Subtype.val (e.apply_symm_apply ⟨g η, hi.2.2 η hη_in⟩)).trans (hg_at x)
      have hdef_top : δ_fn i = (e (kTop i hi)).val := dif_pos hi
      have he_top : (e (kTop i hi)).val = δ := hdef_top.symm.trans hδ_i
      rwa [he_gx, he_top] at he_lt
    obtain ⟨y, hy_mem, hy_ge⟩ := hs δ
    exact lt_irrefl δ (hy_ge.trans_lt (hlt_δ ⟨y, hy_mem⟩))
  · intro μ hμ
    by_contra hnot
    obtain ⟨β, hβ_card⟩ := exists_cut_with_card hμ
    have hge : #θ.ord.ToType ≤ #(Set (Set.Iio β)) := by
      rw [Cardinal.mk_ord_toType, Cardinal.mk_set, hβ_card]
      exact not_lt.mp hnot
    obtain ⟨F⟩ := (Cardinal.le_def _ _).mp hge
    let good (i : I) : Prop := Nonempty (κ.ord.ToType ≃o a i) ∧ β ∈ a i
    have hgood : ∀ᶠ i in U, good i := ht.and (hf β)
    have hex_pair (i : I) (hi : good i) :
        ∃ p : θ.ord.ToType × θ.ord.ToType, p.1 ∈ a i ∧ p.2 ∈ a i ∧ p.1 ≠ p.2 ∧
          ∀ η ∈ a i, ∀ hη : η < β, (⟨η, hη⟩ ∈ F p.1 ↔ ⟨η, hη⟩ ∈ F p.2) := by
      let e := Classical.choice hi.1
      let b₀ : κ.ord.ToType := e.symm ⟨β, hi.2⟩
      have hub (u : Set.Iio b₀) : (e u.val).val < β := by
        have hlt : e u.val < e b₀ := e.lt_iff_lt.mpr u.property
        have hb₀ : (e b₀).val = β := congrArg Subtype.val (e.apply_symm_apply ⟨β, hi.2⟩)
        exact (Subtype.mk_lt_mk.mp hlt).trans_eq hb₀
      let rest' (k : κ.ord.ToType) : Set (Set.Iio b₀) :=
        {u | ⟨(e u.val).val, hub u⟩ ∈ F (e k).val}
      have hcard_set : #(Set (Set.Iio b₀)) < #κ.ord.ToType := by
        rw [Cardinal.mk_set, Cardinal.mk_ord_toType]
        exact hκ.isStrongLimit.isStrongPrelimit (toType_Iio_card_lt b₀)
      have hnot_inj : ¬ Function.Injective rest' := fun hinj =>
        not_le_of_gt hcard_set (Cardinal.mk_le_of_injective hinj)
      have hex_k : ∃ k₁ k₂ : κ.ord.ToType, rest' k₁ = rest' k₂ ∧ k₁ ≠ k₂ := by
        by_contra hall_k
        apply hnot_inj
        intro k₁ k₂ heq_r
        by_contra hne_k
        exact hall_k ⟨k₁, k₂, heq_r, hne_k⟩
      obtain ⟨k₁, k₂, heq_r, hne_k⟩ := hex_k
      refine ⟨((e k₁).val, (e k₂).val), (e k₁).property, (e k₂).property,
        fun hv => hne_k (e.injective (Subtype.ext hv)), ?_⟩
      intro η hη_in hη_lt
      let u₀ : κ.ord.ToType := e.symm ⟨η, hη_in⟩
      have hu₀ : u₀ < b₀ := e.symm.lt_iff_lt.mpr hη_lt
      have hmem_iff : (⟨u₀, hu₀⟩ : Set.Iio b₀) ∈ rest' k₁ ↔ ⟨u₀, hu₀⟩ ∈ rest' k₂ := by
        rw [heq_r]
      have hu₀_raw : (e u₀).val = η :=
        congrArg Subtype.val (e.apply_symm_apply ⟨η, hη_in⟩)
      have hu₀_val : (⟨(e u₀).val, hub ⟨u₀, hu₀⟩⟩ : Set.Iio β) = ⟨η, hη_lt⟩ :=
        Subtype.ext hu₀_raw
      change (⟨(e u₀).val, hub ⟨u₀, hu₀⟩⟩ : Set.Iio β) ∈ F (e k₁).val ↔
        (⟨(e u₀).val, hub ⟨u₀, hu₀⟩⟩ : Set.Iio β) ∈ F (e k₂).val at hmem_iff
      rwa [hu₀_val] at hmem_iff
    let pairFn (i : I) : θ.ord.ToType × θ.ord.ToType :=
      if hi : good i then (hex_pair i hi).choose else (β, β)
    have h1_mem : ∀ᶠ i in U, (pairFn i).1 ∈ a i :=
      hgood.mono fun i hi => by simp only [pairFn, dif_pos hi]; exact (hex_pair i hi).choose_spec.1
    have h2_mem : ∀ᶠ i in U, (pairFn i).2 ∈ a i :=
      hgood.mono fun i hi => by simp only [pairFn, dif_pos hi]; exact (hex_pair i hi).choose_spec.2.1
    obtain ⟨x, hx⟩ := hn (fun i => (pairFn i).1) h1_mem
    obtain ⟨y, hy⟩ := hn (fun i => (pairFn i).2) h2_mem
    obtain ⟨i₀, ⟨hi₀, hx₀⟩, hy₀⟩ := ((hgood.and hx).and hy).exists
    have hxy_ne : x ≠ y := by
      have hne_i₀ : (pairFn i₀).1 ≠ (pairFn i₀).2 := by
        simp only [pairFn, dif_pos hi₀]
        exact (hex_pair i₀ hi₀).choose_spec.2.2.1
      rwa [hx₀, hy₀] at hne_i₀
    have hF_ne : F x ≠ F y := fun h => hxy_ne (F.injective h)
    have hex_z : ∃ z : Set.Iio β, ¬ (z ∈ F x ↔ z ∈ F y) := by
      by_contra hall_z
      apply hF_ne
      ext z
      exact Classical.not_not.mp fun hnz => hall_z ⟨z, hnz⟩
    obtain ⟨z, hz_diff⟩ := hex_z
    obtain ⟨i, ⟨⟨hi, hz_in⟩, hxi⟩, hyi⟩ := (((hgood.and (hf z.val)).and hx).and hy).exists
    have hag : (⟨z.val, z.property⟩ : Set.Iio β) ∈ F (pairFn i).1 ↔
        ⟨z.val, z.property⟩ ∈ F (pairFn i).2 := by
      simp only [pairFn, dif_pos hi]
      exact (hex_pair i hi).choose_spec.2.2.2 z.val hz_in z.property
    rw [hxi, hyi] at hag
    exact hz_diff hag

/-- Full pair-inaccessibility theorem under `CountableInterFilter` and `CardinalInterFilter _ κ`. -/
theorem inaccessible_pair_of_fine_order_type {I : Type u} {κ θ : Cardinal.{u}}
    (U : Ultrafilter I) [CountableInterFilter (U : Filter I)]
    [CardinalInterFilter (U : Filter I) κ] {a : I → Set θ.ord.ToType}
    (hk : κ < θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    κ.IsInaccessible ∧ θ.IsInaccessible := by
  have hκ := inaccessible_source_of_fine_order_type U hk hf hn ht
  exact ⟨hκ, inaccessible_target_of_fine_order_type U hκ hk hf hn ht⟩

/-- Full pair-inaccessibility + countable completeness theorem from `ℵ₀ < κ` alone. -/
theorem inaccessible_pair_of_aleph0_lt {I : Type u} {κ θ : Cardinal.{u}}
    (U : Ultrafilter I) [CardinalInterFilter (U : Filter I) κ]
    {a : I → Set θ.ord.ToType} (hω : ℵ₀ < κ) (hk : κ < θ)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    CountableInterFilter (U : Filter I) ∧ κ.IsInaccessible ∧ θ.IsInaccessible := by
  have hcnt : CountableInterFilter (U : Filter I) :=
    CardinalInterFilter.toCountableInterFilter (U : Filter I) hω
  exact ⟨hcnt, inaccessible_pair_of_fine_order_type U hk hf hn ht⟩

end DerivedInaccessibility

section CanonicalHugeCardinal

theorem hugeFiberVal_orderType {κ θ : Cardinal.{u}}
    (U : Ultrafilter (HugeFiberSpace κ θ)) :
    FiberOrderType U κ θ Subtype.val :=
  Eventually.of_forall fun s => s.property

theorem IsHugeWithTarget.inaccessible_pair {κ θ : Cardinal.{u}}
    (h : IsHugeWithTarget κ θ) : κ.IsInaccessible ∧ θ.IsInaccessible := by
  obtain ⟨hω, hk, U, hcard, hf, hn⟩ := h
  have : CardinalInterFilter (U : Filter (HugeFiberSpace κ θ)) κ := hcard
  exact (inaccessible_pair_of_aleph0_lt U hω hk hf hn (hugeFiberVal_orderType U)).2

theorem IsHugeWithTarget.inaccessible_right {κ θ : Cardinal.{u}}
    (h : IsHugeWithTarget κ θ) : θ.IsInaccessible :=
  h.inaccessible_pair.2

/-- Pushforward of any `(I, U, a)` fine normal measure with `FiberOrderType U κ θ a` onto
Kanamori's canonical carrier `HugeFiberSpace κ θ`. -/
theorem isHugeWithTarget_of_fine_measure {I : Type u} {κ θ : Cardinal.{u}}
    (U : Ultrafilter I) [CountableInterFilter (U : Filter I)]
    [CardinalInterFilter (U : Filter I) κ] {a : I → Set θ.ord.ToType}
    (hk : κ < θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a) :
    IsHugeWithTarget κ θ := by
  classical
  have hω : ℵ₀ < κ := aleph0_lt_of_fine_order_type U hk hf hn ht
  obtain ⟨i₀, hi₀⟩ := ht.exists
  let dflt : HugeFiberSpace κ θ := ⟨a i₀, hi₀⟩
  let π (i : I) : HugeFiberSpace κ θ :=
    if h : Nonempty (κ.ord.ToType ≃o a i) then ⟨a i, h⟩ else dflt
  have hπ_val : ∀ᶠ i in U, (π i).val = a i :=
    ht.mono fun i hi => by simp only [π, dif_pos hi]
  let W : Ultrafilter (HugeFiberSpace κ θ) := Ultrafilter.map π U
  have hW_card : CardinalInterFilter (W : Filter (HugeFiberSpace κ θ)) κ :=
    { cardinal_sInter_mem := fun S hS hmem => by
        change π ⁻¹' (⋂₀ S) ∈ (U : Filter I)
        rw [Set.preimage_sInter]
        have hcard_idx : #S < κ := hS
        rw [Filter.cardinal_bInter_mem (l := (U : Filter I)) (c := κ) hcard_idx]
        intro s hs
        exact hmem s hs }
  have hW_fine : FineOn W Subtype.val := fun ξ => by
    change ∀ᶠ i in U, ξ ∈ (π i).val
    exact (hπ_val.and (hf ξ)).mono fun i hi => hi.1.symm ▸ hi.2
  have hW_normal : NormalOn W Subtype.val := fun f h => by
    have h' : ∀ᶠ i in U, f (π i) ∈ a i := by
      have hm : ∀ᶠ i in U, f (π i) ∈ (π i).val := h
      exact (hπ_val.and hm).mono fun i hi => hi.1 ▸ hi.2
    obtain ⟨ξ, hξ⟩ := hn (fun i => f (π i)) h'
    exact ⟨ξ, hξ⟩
  exact ⟨hω, hk, W, hW_card, hW_fine, hW_normal⟩

/-- Exact equivalence between Kanamori's canonical `IsHugeWithTarget κ θ` and the general
`(I, U, a)` presentation. -/
theorem isHugeWithTarget_iff_exists_fine_measure {κ θ : Cardinal.{u}} :
    IsHugeWithTarget κ θ ↔
      ∃ (I : Type u) (U : Ultrafilter I) (a : I → Set θ.ord.ToType),
        CountableInterFilter (U : Filter I) ∧
        CardinalInterFilter (U : Filter I) κ ∧
        κ < θ ∧ FineOn U a ∧ NormalOn U a ∧ FiberOrderType U κ θ a := by
  constructor
  · rintro ⟨hω, hk, U, hcard, hf, hn⟩
    have : CardinalInterFilter (U : Filter (HugeFiberSpace κ θ)) κ := hcard
    have hcnt : CountableInterFilter (U : Filter (HugeFiberSpace κ θ)) :=
      CardinalInterFilter.toCountableInterFilter (U : Filter (HugeFiberSpace κ θ)) hω
    exact ⟨HugeFiberSpace κ θ, U, Subtype.val, hcnt, hcard, hk, hf, hn,
      hugeFiberVal_orderType U⟩
  · rintro ⟨I, U, a, hcnt, hcard, hk, hf, hn, ht⟩
    have : CountableInterFilter (U : Filter I) := hcnt
    have : CardinalInterFilter (U : Filter I) κ := hcard
    exact isHugeWithTarget_of_fine_measure U hk hf hn ht

/-- `IsHugeWithTarget κ θ` yields the full ground elementary embedding package (`crit = κ`,
`j(κ) = θ`, and `θ`-sequence closure of the transitive target class). -/
theorem IsHugeWithTarget.exists_groundEmbedding_closure {κ θ : Cardinal.{u}}
    (h : IsHugeWithTarget κ θ) :
    ∃ U : Ultrafilter (HugeFiberSpace κ θ),
      ∃ _ : CountableInterFilter (U : Filter (HugeFiberSpace κ θ)),
        (∀ α < κ.ord, (groundEmbedding U α.toZFSet).val = α.toZFSet) ∧
        κ.ord.toZFSet ∈ (groundEmbedding U κ.ord.toZFSet).val ∧
        (groundEmbedding U κ.ord.toZFSet).val = θ.ord.toZFSet ∧
        ∀ S F : ZFSet.{u}, ZFSet.IsFunc θ.ord.toZFSet S F →
          (∀ (ξ : θ.ord.ToType) y, ZFSet.pair ξ.toOrd.val.toZFSet y ∈ F → y ∈ targetClass U) →
          F ∈ targetClass U := by
  obtain ⟨hω, hk, U, hcard, hf, hn⟩ := h
  have : CardinalInterFilter (U : Filter (HugeFiberSpace κ θ)) κ := hcard
  have hcnt : CountableInterFilter (U : Filter (HugeFiberSpace κ θ)) :=
    CardinalInterFilter.toCountableInterFilter (U : Filter (HugeFiberSpace κ θ)) hω
  exact ⟨U, hcnt,
    groundEmbedding_fine_critical_image_closure U κ θ Subtype.val hf hn
      (hugeFiberVal_orderType U) hk⟩

end CanonicalHugeCardinal

end Erdos1172GroundUltrapower
