/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCodedStageTransport
public import Erdos1172.Part4ShioyaDenseCoding

@[expose] public section

/-! # Synchronized coding stages of the Lévy presentation -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya.LevyProduct

variable {κ θ ν : Cardinal.{u}}

private theorem small_subsets_at_power {Y : Type u} (hν : Cardinal.aleph0 ≤ ν)
    (hκ : κ ≤ ν) (hY : Cardinal.mk Y ≤ 2 ^ ν) :
    Cardinal.mk {s : Set Y // Cardinal.mk s < κ} ≤ 2 ^ ν := by
  classical
  let M := {s : Set Y // Cardinal.mk s < κ}
  have emb (s : M) : Nonempty (s.val ↪ ν.ord.ToType) := by
    apply (Cardinal.le_def _ _).mp
    simpa only [Cardinal.mk_ord_toType] using s.property.le.trans hκ
  let code (s : M) (i : ν.ord.ToType) : Option Y :=
    if h : ∃ x, (emb s).some x = i then some h.choose.val else none
  have hc (s : M) (x : Y) : x ∈ s.val ↔ ∃ i, code s i = some x := by
    constructor
    · intro hx
      let y : s.val := ⟨x,hx⟩
      refine ⟨(emb s).some y,?_⟩
      have h : ∃ z, (emb s).some z = (emb s).some y := ⟨y,rfl⟩
      simp only [code,dif_pos h,Option.some.injEq]
      exact congrArg Subtype.val ((emb s).some.injective h.choose_spec)
    · rintro ⟨i,hi⟩
      by_cases h : ∃ z, (emb s).some z = i
      · have he : h.choose.val = x := by simpa only [code,dif_pos h,Option.some.injEq] using hi
        exact he ▸ h.choose.property
      · rw [show code s i = none from dif_neg h] at hi
        cases hi
  have hinj : Function.Injective code := by
    intro s t he
    apply Subtype.ext
    exact Set.ext fun x => (hc s x).trans (he ▸ (hc t x).symm)
  have hμ := hν.trans (Cardinal.cantor ν).le
  have hopt : Cardinal.mk (Option Y) ≤ 2 ^ ν := by
    rw [Cardinal.mk_option]
    exact (add_le_add hY (le_refl (1 : Cardinal))).trans_eq (Cardinal.add_one_eq hμ)
  apply (Cardinal.mk_le_of_injective hinj).trans
  rw [← Cardinal.power_def,Cardinal.mk_ord_toType]
  exact (Cardinal.power_le_power_right hopt).trans_eq (by rw [← Cardinal.power_mul,Cardinal.mul_eq_self hν])

private theorem stage_cardinal_le_power (hν : Cardinal.aleph0 ≤ ν) (hκ : κ ≤ ν) (hpos : 0 < κ)
    (j : Index θ) (hj : j.toOrd.val.card ≤ 2 ^ ν) : Cardinal.mk (Stage κ j) ≤ 2 ^ ν := by
  let μ : Cardinal.{u} := 2 ^ ν
  have hinf : Cardinal.aleph0 ≤ μ := hν.trans (Cardinal.cantor ν).le
  have hkμ : κ ≤ μ := hκ.trans (Cardinal.cantor ν).le
  let S := Set.Iio j
  let Z := Σ i : S, Collapse.Condition κ (Alphabet i.val)
  have hI : Cardinal.mk S ≤ μ := by
    let g (i : S) : j.toOrd.val.ToType := Ordinal.ToType.mk
      ⟨i.val.toOrd.val,Ordinal.ToType.mk.symm.strictMono i.property⟩
    have hg (i : S) : (g i).toOrd.val = i.val.toOrd.val := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
    apply (Cardinal.mk_le_of_injective (f := g) ?_).trans
    · simpa only [Cardinal.mk_toType] using hj
    · intro a b h
      exact Subtype.ext (Ordinal.ToType.mk.symm.injective (Subtype.ext
        ((hg a).symm.trans ((congrArg (fun x : j.toOrd.val.ToType => x.toOrd.val) h).trans (hg b)))))
  have hfactor (i : S) : Cardinal.mk (Collapse.Condition κ (Alphabet i.val)) ≤ μ := by
    have ha : Cardinal.mk (Alphabet i.val) ≤ μ := by
      rw [show Cardinal.mk (Alphabet i.val) = _ from Cardinal.mk_sum _ _]
      simp only [Cardinal.lift_id,Cardinal.mk_uLift,Cardinal.mk_bool,Cardinal.lift_ofNat,Cardinal.mk_toType]
      exact (add_le_add ((Cardinal.natCast_le_aleph0 (n := 2)).trans hinf)
        ((Ordinal.card_le_card (Ordinal.ToType.mk.symm.monotone i.property.le)).trans hj)).trans_eq
        (Cardinal.add_eq_self hinf)
    let Y := κ.ord.ToType × Alphabet i.val
    have hY : Cardinal.mk Y ≤ μ := by
      rw [show Cardinal.mk Y = _ from Cardinal.mk_prod _ _]
      simpa only [Cardinal.lift_id,Cardinal.mk_ord_toType] using
        (mul_le_mul' hkμ ha).trans_eq (Cardinal.mul_eq_self hinf)
    let g (c : Collapse.Condition κ (Alphabet i.val)) : {s : Set Y // Cardinal.mk s < κ} := ⟨c.graph,c.small⟩
    exact (Cardinal.mk_le_of_injective (f := g) (fun _ _ h => Collapse.graph_injective (congrArg Subtype.val h))).trans
      (small_subsets_at_power hν hκ hY)
  have hZ : Cardinal.mk Z ≤ μ := by
    rw [show Cardinal.mk Z = _ from Cardinal.mk_sigma (fun i : S => Collapse.Condition κ (Alphabet i.val))]
    apply (Cardinal.sum_le_mk_mul_iSup _).trans
    exact (mul_le_mul' hI (ciSup_le' hfactor)).trans_eq (Cardinal.mul_eq_self hinf)
  let dir (p : Stage κ j) (i : support p.value) : Z := ⟨⟨i.val,p.inside i.property⟩,p.value i.val⟩
  let code (p : Stage κ j) : {s : Set Z // Cardinal.mk s < κ} :=
    ⟨Set.range (dir p),Cardinal.mk_range_le.trans_lt p.small⟩
  have agree (p q : Stage κ j) (he : code p = code q) (i : support p.value) : p.value i.val = q.value i.val := by
    obtain ⟨k,hk⟩ := (Set.ext_iff.mp (congrArg Subtype.val he) (dir p i)).mp (Set.mem_range_self i)
    have hk' : k.val = i.val := congrArg (fun z : Z => z.1.val) hk
    obtain ⟨k,hks⟩ := k
    obtain ⟨i,his⟩ := i
    obtain rfl : k = i := hk'
    exact (eq_of_heq (Sigma.mk.inj hk).2).symm
  have hinj : Function.Injective code := by
    intro p q he
    apply value_injective
    funext i
    by_cases hp : i ∈ support p.value
    · exact agree p q he ⟨i,hp⟩
    by_cases hq : i ∈ support q.value
    · exact (agree q p he.symm ⟨i,hq⟩).symm
    exact (eq_empty_of_not_supported hp hpos).trans (eq_empty_of_not_supported hq hpos).symm
  exact (Cardinal.mk_le_of_injective hinj).trans (small_subsets_at_power hν hκ hZ)

variable (hκ : κ.IsRegular) (hκθ : κ < θ) (hθ : θ.IsInaccessible)

private theorem exists_coding_slots (old late : Index θ) :
    ∃ (j : Index θ) (slots : TailSlots old (stageBase hκ hκθ hθ j).Poset),
      late ≤ j ∧ slots.length = j := by
  let start := max old late
  let ν := max κ start.toOrd.val.card
  have hν : Cardinal.aleph0 ≤ ν := hκ.aleph0_le.trans (le_max_left _ _)
  have hνθ : ν < θ := max_lt hκθ (Cardinal.lt_ord.mp start.toOrd.property)
  let μ : Cardinal.{u} := 2 ^ ν
  have hμθ : μ < θ := hθ.isStrongPrelimit hνθ
  have hμ : Cardinal.aleph0 ≤ μ := hν.trans (Cardinal.cantor ν).le
  let j : Index θ := Ordinal.ToType.mk ⟨start.toOrd.val + μ.ord,
    Ordinal.isPrincipal_add_ord hθ.aleph0_lt.le start.toOrd.property (Cardinal.ord_lt_ord.mpr hμθ)⟩
  have hj : j.toOrd.val = start.toOrd.val + μ.ord := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  have hstart : start ≤ j := by
    apply Ordinal.ToType.mk.symm.le_iff_le.mp
    change start.toOrd.val ≤ j.toOrd.val
    rw [hj]
    exact le_self_add
  have hcard : j.toOrd.val.card ≤ μ := by
    rw [hj,Ordinal.card_add,Cardinal.card_ord]
    exact (Cardinal.add_eq_right hμ ((le_max_right κ _).trans (Cardinal.cantor ν).le)).le
  have hsize : Cardinal.mk (stageBase hκ hκθ hθ j).Poset ≤ μ :=
    (Cardinal.mk_congr (stageIso hκ hκθ hθ j).toEquiv).le.trans
      (stage_cardinal_le_power hν (le_max_left κ _) hκ.pos j hcard)
  obtain ⟨e⟩ : Nonempty ((stageBase hκ hκθ hθ j).Poset ↪ μ.ord.ToType) :=
    (Cardinal.le_def _ _).mp (by simpa only [Cardinal.mk_ord_toType] using hsize)
  let slot (q : (stageBase hκ hκθ hθ j).Poset) : j.toOrd.val.ToType := Ordinal.ToType.mk
    ⟨start.toOrd.val + (e q).toOrd.val, by
      change start.toOrd.val + (e q).toOrd.val < j.toOrd.val
      rw [hj]
      exact add_lt_add_right (show (e q).toOrd.val < μ.ord from (e q).toOrd.property) start.toOrd.val⟩
  have hs (q) : (slot q).toOrd.val = start.toOrd.val + (e q).toOrd.val :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  refine ⟨j,⟨j,Ordinal.ToType.mk.symm.monotone ((le_max_left old late).trans hstart),⟨slot,?_⟩,?_⟩,
    (le_max_right old late).trans hstart,rfl⟩
  · intro p q h
    have he := congrArg (fun k : j.toOrd.val.ToType => k.toOrd.val) h
    rw [hs,hs] at he
    exact e.injective (Ordinal.ToType.mk.symm.injective (Subtype.ext (add_left_cancel he)))
  · intro q
    change old.toOrd.val ≤ (slot q).toOrd.val
    rw [hs]
    exact (show old.toOrd.val ≤ start.toOrd.val from Ordinal.ToType.mk.symm.monotone (le_max_left old late)).trans
      le_self_add

private theorem cut_widen (hpos : 0 < κ) {i j : Index θ} (hij : i ≤ j) (p : Stage κ i) :
    cut hpos (Set.Iio i) (widen (Set.Iio_subset_Iio hij) p) = p := by
  apply value_injective
  funext s
  by_cases hs : s ∈ Set.Iio i
  · exact cut_at hpos _ hs
  · exact (cut_not_at hpos _ hs).trans (value_outside p hs hpos).symm

private theorem append_oldBit {X : Type u} (p : Condition κ θ) (slots : TailSlots p.length X)
    (payload : X → p.Algebra) (k : p.length.toOrd.val.ToType) :
    p.appendBits slots payload (StringName.includeIndex slots.extendsLength k) = p.bits k := by
  classical
  have hn : ¬∃ q, slots.slot q = StringName.includeIndex slots.extendsLength k := by
    rintro ⟨q,hq⟩
    have hh := slots.fresh q
    rw [hq,StringName.includeIndex_toOrd] at hh
    exact k.toOrd.property.not_ge hh
  unfold Condition.appendBits
  rw [dif_neg hn,StringName.padBits_includeIndex]

theorem exists_synchronized_coding_exact (a : (stageSystem hκ hκθ hθ).Entry) (late : Index θ) :
    ∃ b ≤ a, late ≤ b.stage ∧ b.length = b.stage ∧ (b.forget (stageSystem hκ hκθ hθ)).Codes ∧
      ∃ h : a.stage ≤ b.stage, (codedRestriction hκ hκθ hθ h).proj ⟨b.point,Set.mem_univ _⟩ = a.point ∧
        (⊤ : (stageBase hκ hκθ hθ b.stage).Algebra) ≤ extensionValue (codedRestriction hκ hκθ hθ h).booleanHom
          (a.forget (stageSystem hκ hκθ hθ)).name (b.forget (stageSystem hκ hκθ hθ)).name := by
  classical
  let T := stageSystem hκ hκθ hθ
  obtain ⟨j,slots,hlj,hsj⟩ := exists_coding_slots hκ hκθ hθ a.length (max a.stage late)
  have haj : a.stage ≤ j := (le_max_left _ _).trans hlj
  let π := T.restrict haj
  let e := stageIso hκ hκθ hθ
  let q₀ := (e j).symm (widen (Set.Iio_subset_Iio haj) (e a.stage a.point))
  let d : π.dom := ⟨q₀,Set.mem_univ _⟩
  have hd : π.proj d = a.point := by
    change (e a.stage).symm (cut hκ.pos (Set.Iio a.stage) (e j ((e j).symm _))) = _
    rw [OrderIso.apply_symm_apply,cut_widen hκ.pos haj]
    exact (e a.stage).symm_apply_apply _
  let v : Condition κ θ := {T.base j with point := d.val, length := a.length, bits := fun k => π.booleanHom (a.bits k)}
  let bits : slots.length.toOrd.val.ToType → (T.base j).Algebra := v.appendBits slots (fun q : v.Poset => condition q)
  let b : T.Entry := ⟨j,d.val,slots.length,bits⟩
  have he : (⊤ : (T.base j).Algebra) ≤ extensionValue π.booleanHom (a.forget T).name (b.forget T).name := by
    change (⊤ : (T.base j).Algebra) ≤ extensionValue π.booleanHom (StringName.ofBits a.length.toOrd.val a.bits)
      (StringName.ofBits slots.length.toOrd.val bits)
    apply extensionValue_of_bits π.booleanHom (StringName.ofBits a.length.toOrd.val a.bits)
      (StringName.ofBits slots.length.toOrd.val bits) slots.extendsLength
    intro k
    rw [StringName.bits_ofBits a.bits,StringName.bits_ofBits bits]
    exact congrArg (fun z => ⊤ ⊓ z) (append_oldBit v slots (fun q => condition q) k).symm
  refine ⟨b,⟨haj, (π.dom_condition d _).mpr (condition_mono hd.le),le_top.trans he⟩,
    (le_max_right _ _).trans hlj,hsj,?_,haj,hd,he⟩
  intro q
  exact ⟨slots.slot q,v.append_at slots (fun r => condition r) q⟩

theorem exists_synchronized_coding (a : (stageSystem hκ hκθ hθ).Entry) (late : Index θ) :
    ∃ b ≤ a, late ≤ b.stage ∧ b.length = b.stage ∧ (b.forget (stageSystem hκ hκθ hθ)).Codes := by
  obtain ⟨b,hb,hl,hs,hc,_⟩ := exists_synchronized_coding_exact hκ hκθ hθ a late
  exact ⟨b,hb,hl,hs,hc⟩

end Erdos1172Shioya.LevyProduct
