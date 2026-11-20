/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaLevyProduct

@[expose] public section

/-! # Coherent restrictions and bounded support in the Lévy product -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u

namespace Erdos1172Shioya.LevyProduct

variable {κ θ : Cardinal.{u}} {I : Type u} {A : I → Type u} {S T U : Set I}

def restrictionProjection (hκ : Cardinal.aleph0 ≤ κ) (h : T ⊆ S) :
    PartialProjection κ (Family κ A S) (Family κ A T) :=
  productProjection (split hκ h) (empty (Cardinal.aleph0_pos.trans_le hκ))

theorem restrictionProjection_apply (hκ : Cardinal.aleph0 ≤ κ) (h : T ⊆ S) (p : Family κ A S) :
    (restrictionProjection hκ h).proj ⟨p, Set.mem_univ _⟩ =
      cut (Cardinal.aleph0_pos.trans_le hκ) T p := rfl

theorem restrict_exact (hκ : Cardinal.aleph0 ≤ κ) (h : T ⊆ S) (p : Family κ A S)
    (q : Family κ A T) (hq : q ≤ cut (Cardinal.aleph0_pos.trans_le hκ) T p) :
    ∃ r ≤ p, cut (Cardinal.aleph0_pos.trans_le hκ) T r = q := by
  let e := split (A := A) hκ h
  refine ⟨e.symm (q,(e p).2), e.symm_apply_le.mpr ⟨hq,le_rfl⟩,?_⟩
  exact congrArg Prod.fst (e.apply_symm_apply (q,(e p).2))

theorem restrictionProjection_booleanHom_comp (hκ : Cardinal.aleph0 ≤ κ) (hTS : T ⊆ S) (hUT : U ⊆ T) :
    (restrictionProjection (A := A) hκ hTS).booleanHom.comp (restrictionProjection hκ hUT).booleanHom =
      (restrictionProjection hκ (hUT.trans hTS)).booleanHom := by
  ext b
  let π := restrictionProjection (A := A) hκ hTS
  let σ := restrictionProjection (A := A) hκ hUT
  let τ := restrictionProjection (A := A) hκ (hUT.trans hTS)
  let pos := Cardinal.aleph0_pos.trans_le hκ
  have hm (p : Family κ A S) : condition p ≤ π.booleanHom (σ.booleanHom b) ↔
      condition p ≤ τ.booleanHom b := by
    have h₁ := π.dom_condition ⟨p,Set.mem_univ _⟩ (σ.booleanHom b)
    have h₂ := σ.dom_condition ⟨cut pos T p,Set.mem_univ _⟩ b
    have h₃ := τ.dom_condition ⟨p,Set.mem_univ _⟩ b
    change condition (cut pos T p) ≤ σ.booleanHom b ↔ condition (cut pos U (cut pos T p)) ≤ b at h₂
    rw [cut_cut pos hUT] at h₂
    exact (h₁.trans h₂).trans h₃.symm
  have hd (p : Family κ A S) : ∃ q ∈ (Set.univ : Set (Family κ A S)), q ≤ p :=
    ⟨p, Set.mem_univ _,le_rfl⟩
  exact le_antisymm (le_of_dense_conditions_le Set.univ hd (fun p => (hm p.val).mp))
    (le_of_dense_conditions_le Set.univ hd (fun p => (hm p.val).mpr))

theorem stageProjection_booleanHom_comp (hκ : Cardinal.aleph0 ≤ κ) {i j k : Index θ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (stageProjection hκ hjk).booleanHom.comp (stageProjection hκ hij).booleanHom =
      (stageProjection hκ (hij.trans hjk)).booleanHom :=
  restrictionProjection_booleanHom_comp hκ (Set.Iio_subset_Iio hjk) (Set.Iio_subset_Iio hij)

def fullProjection (hκ : Cardinal.aleph0 ≤ κ) (i : Index θ) :
    PartialProjection κ (Full κ θ) (Stage κ i) := restrictionProjection hκ (Set.subset_univ _)

theorem fullProjection_apply (hκ : Cardinal.aleph0 ≤ κ) (i : Index θ) (p : Full κ θ) :
    (fullProjection hκ i).proj ⟨p,Set.mem_univ _⟩ = cut (Cardinal.aleph0_pos.trans_le hκ) (Set.Iio i) p := rfl

theorem fullProjection_booleanHom_comp (hκ : Cardinal.aleph0 ≤ κ) {i j : Index θ} (hij : i ≤ j) :
    (fullProjection hκ j).booleanHom.comp (stageProjection hκ hij).booleanHom =
      (fullProjection hκ i).booleanHom :=
  restrictionProjection_booleanHom_comp hκ (Set.subset_univ _) (Set.Iio_subset_Iio hij)

theorem full_support_bounded (hθ : θ.IsRegular) (hκθ : κ ≤ θ) (p : Full κ θ) :
    ∃ i : Index θ, support p.value ⊆ Set.Iio i := by
  classical
  have hn : ¬IsCofinal (support p.value) := by
    intro hc
    have h := Order.cof_le hc
    rw [show Order.cof (Index θ) = θ from (Ordinal.cof_toType θ.ord).trans hθ.cof_ord] at h
    exact (p.small.trans_le hκθ).not_ge h
  by_contra! h
  apply hn
  intro i
  obtain ⟨j,hj,hle⟩ := Set.not_subset.mp (h i)
  exact ⟨j,hj,le_of_not_gt hle⟩

def extendStage {i : Index θ} (p : Stage κ i) : Full κ θ := widen (Set.subset_univ _) p

theorem exists_stage (hθ : θ.IsRegular) (hκθ : κ ≤ θ) (p : Full κ θ) :
    ∃ (i : Index θ) (q : Stage κ i), extendStage q = p := by
  obtain ⟨i,hi⟩ := full_support_bounded hθ hκθ p
  exact ⟨i,⟨p.value,p.small,hi⟩,value_injective rfl⟩

theorem full_cardinal_le (hθ : θ.IsInaccessible) (hκθ : κ < θ) (hpos : 0 < κ) :
    Cardinal.mk (Full κ θ) ≤ θ := by
  let f : (Σ i : Index θ, Stage κ i) → Full κ θ := fun z => extendStage z.2
  have hs : Function.Surjective f := by
    intro p
    obtain ⟨i,q,h⟩ := exists_stage hθ.isRegular hκθ.le p
    exact ⟨⟨i,q⟩,h⟩
  have he (i : Index θ) : Nonempty (Stage κ i ↪ Index θ) := by
    apply (Cardinal.le_def _ _).mp
    simpa only [Index,Cardinal.mk_ord_toType] using (stage_cardinal_lt hθ hκθ hpos i).le
  let g : (Σ i : Index θ, Stage κ i) → Index θ × Index θ := fun z => (z.1,(he z.1).some z.2)
  have hg : Function.Injective g := by
    rintro ⟨i,p⟩ ⟨j,q⟩ h
    obtain rfl : i = j := congrArg Prod.fst h
    exact congrArg (Sigma.mk i) ((he i).some.injective (congrArg Prod.snd h))
  exact (Cardinal.mk_le_of_surjective hs).trans ((Cardinal.mk_le_of_injective hg).trans
    (by simp [Index,Cardinal.mk_prod,Cardinal.mul_eq_self hθ.aleph0_lt.le]))

instance alphabetNontrivial (i : Index θ) : Nontrivial (Alphabet i) :=
  ⟨⟨Sum.inl ⟨false⟩, Sum.inl ⟨true⟩, by intro h; cases h⟩⟩

theorem exists_coordinate_surjection (hθ : θ.IsInaccessible) (i : Index θ) (Y : Type u) [Nonempty Y]
    (hY : Cardinal.mk Y < θ) : ∃ t j : Index θ, i ≤ t ∧ t < j ∧ ∃ f : Alphabet t → Y, Function.Surjective f := by
  let a : Index θ := Ordinal.ToType.mk ⟨(Cardinal.mk Y).ord, Cardinal.ord_lt_ord.mpr hY⟩
  have ha : a.toOrd.val = (Cardinal.mk Y).ord := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  let t := max i a
  have hat : a.toOrd.val ≤ t.toOrd.val := Ordinal.ToType.mk.symm.monotone (le_max_right i a)
  have hcard : Cardinal.mk Y ≤ Cardinal.mk t.toOrd.val.ToType := by
    have hh := Ordinal.card_le_card hat
    simpa only [ha, Cardinal.card_ord, Cardinal.mk_toType] using hh
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hcard
  let emb : Y → Alphabet t := fun y => Sum.inr (e y)
  have hinj : Function.Injective emb := fun _ _ h => e.injective (Sum.inr.inj h)
  have hnext : Order.succ t.toOrd.val < θ.ord := (Cardinal.isSuccLimit_ord hθ.aleph0_lt.le).succ_lt
    (show t.toOrd.val < θ.ord from t.toOrd.property)
  let j : Index θ := Ordinal.ToType.mk ⟨Order.succ t.toOrd.val,hnext⟩
  have hj : j.toOrd.val = Order.succ t.toOrd.val := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  refine ⟨t,j,le_max_left _ _,?_,Function.invFun emb,(Function.leftInverse_invFun hinj).surjective⟩
  apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
  change t.toOrd.val < j.toOrd.val
  rw [hj]
  exact Order.lt_succ _

theorem stage_separative (hκ : Cardinal.aleph0 ≤ κ) (i : Index θ) : Separative (Stage κ i) := separative hκ

theorem full_separative (hκ : Cardinal.aleph0 ≤ κ) : Separative (Full κ θ) := separative hκ

end Erdos1172Shioya.LevyProduct
