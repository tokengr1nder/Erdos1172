/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCohenCover
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-! # Reading in the bounded-string forcing over a Boolean algebra -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.CohenCover

variable {θ : Cardinal.{u}} {B : Type u} [NontrivialCompleteBooleanAlgebra B]

private theorem strengthen {P : Type u} [Preorder P] (p : P) (b : Completion P)
    (hp : condition p ⊓ b ≠ ⊥) : ∃ r ≤ p, condition r ≤ b := by
  obtain ⟨t,ht⟩ := exists_condition_le hp
  obtain ⟨r,hrt,hrp⟩ := (mem_condition_iff p t).mp (condition_le_iff.mp (ht.trans inf_le_left)) t le_rfl
  exact ⟨r,hrp,(condition_mono hrt).trans (ht.trans inf_le_right)⟩

theorem condition_withValue (q : Condition θ B) {b : B} (hb : b ≠ ⊥) (h : b ≤ q.value) :
    condition (q.withValue b hb) = condition q ⊓ firstStageHom θ B b := by
  refine le_antisymm (le_inf (condition_mono (q.withValue_le b hb h))
    ((condition_le_firstStageHom_iff _ b).mpr le_rfl)) ?_
  apply le_of_dense_conditions_le (Set.univ : Set (Condition θ B)) (fun p => ⟨p,Set.mem_univ p,le_rfl⟩)
  intro p hp
  have hv : p.val.value ≤ b := (condition_le_firstStageHom_iff _ _).mp (hp.trans inf_le_right)
  apply condition_le_iff.mpr
  apply (mem_condition_iff _ _).mpr
  intro s hs
  obtain ⟨r,hrs,hrq⟩ := (mem_condition_iff q p.val).mp (condition_le_iff.mp (hp.trans inf_le_left)) s hs
  exact ⟨r,hrs,(Condition.value_mono (hrs.trans hs)).trans hv,hrq.2⟩

namespace Condition

def read (q : Condition θ B) (c : Completion (Condition θ B)) : B :=
  sSup {b : B | ∃ hb : b ≠ ⊥, b ≤ q.value ∧ condition (q.withValue b hb) ≤ c}

theorem le_read (q : Condition θ B) (c : Completion (Condition θ B)) {b : B}
    (hb : b ≠ ⊥) (hbq : b ≤ q.value) (hc : condition (q.withValue b hb) ≤ c) : b ≤ q.read c :=
  le_sSup ⟨hb,hbq,hc⟩

theorem read_le_value (q : Condition θ B) (c : Completion (Condition θ B)) : q.read c ≤ q.value :=
  sSup_le (fun _ ⟨_,h,_⟩ => h)

theorem inf_firstStageHom_read (q : Condition θ B) (c : Completion (Condition θ B)) :
    condition q ⊓ firstStageHom θ B (q.read c) ≤ c := by
  rw [read, map_sSup, sSup_image']
  erw [inf_iSup_eq]
  apply iSup_le
  rintro ⟨b,hb,hbq,hc⟩
  exact (condition_withValue q hb hbq).ge.trans hc

theorem read_mono_same_value {p q : Condition θ B} (hqp : q ≤ p) (hv : q.value = p.value)
    (c : Completion (Condition θ B)) : p.read c ≤ q.read c := by
  apply sSup_le
  rintro b ⟨hb,hbp,hbc⟩
  have hbq := hbp.trans_eq hv.symm
  apply q.le_read c hb hbq
  rw [condition_withValue _ hb hbq]
  rw [condition_withValue _ hb hbp] at hbc
  exact (inf_le_inf_right _ (condition_mono hqp)).trans hbc

end Condition

theorem disjoint_cover {I : Type u} (a : I → B) :
    ∃ w : I → B, (∀ i, w i ≤ a i) ∧ (∀ i j, i ≠ j → w i ⊓ w j = ⊥) ∧ (⨆ i, w i) = ⨆ i, a i := by
  classical
  obtain ⟨_lo, wf⟩ := exists_wellFoundedLT I
  letI := _lo
  haveI : WellFoundedLT (I) := wf
  let past (i : I) := ⨆ j : Set.Iio i, a j.val
  let w (i : I) := a i ⊓ (past i)ᶜ
  have hd {i j : I} (h : i < j) : w i ⊓ w j = ⊥ :=
    bot_unique ((inf_le_inf (inf_le_left.trans (le_iSup (fun k : Set.Iio j => a k.val) ⟨i,h⟩))
      (show w j ≤ (past j)ᶜ from inf_le_right)).trans inf_compl_eq_bot.le)
  refine ⟨w, fun _ => inf_le_left, ?_, le_antisymm (iSup_mono (fun _ => inf_le_left)) (iSup_le ?_)⟩
  · intro i j hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact hd h
    · exact (inf_comm _ _).trans (hd h)
  · intro i
    apply wf.induction i
    intro j ih
    calc a j = (a j ⊓ past j) ⊔ w j := by
           change a j = (a j ⊓ past j) ⊔ (a j ⊓ (past j)ᶜ)
           rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
         _ ≤ ⨆ k, w k := sup_le
           (inf_le_right.trans (iSup_le (fun k : Set.Iio j => ih k.val k.property))) (le_iSup w j)

private theorem partition_mix {I : Type u} (w v : I → B)
    (hd : ∀ i j, i ≠ j → w i ⊓ w j = ⊥) (j : I) :
    w j ⊓ (⨆ i, w i ⊓ v i) = w j ⊓ v j := by
  rw [inf_iSup_eq]
  refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le j ?_)
  · by_cases h : j = i
    · subst i
      exact inf_le_right
    · exact ((inf_le_inf_left _ inf_le_left).trans_eq (hd j i h)).trans bot_le
  · exact le_inf inf_le_left le_rfl

private theorem read_one_cover {J : Type u} (p : Condition θ B) (c : J → Completion (Condition θ B))
    (hc : condition p ≤ ⨆ j, c j) :
    p.value ≤ ⨆ t : {t : Condition θ B // t ≤ p ∧ ∃ j, condition t ≤ c j}, t.val.value := by
  classical
  let I := {t : Condition θ B // t ≤ p ∧ ∃ j, condition t ≤ c j}
  let a : B := ⨆ t : I, t.val.value
  by_contra h
  have hn : p.value ⊓ aᶜ ≠ ⊥ := fun he => h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  let t := p.withValue _ hn
  have ht : t ≤ p := p.withValue_le _ hn inf_le_left
  have hall := (condition_mono ht).trans hc
  have hh : ⊥ < ⨆ j, condition t ⊓ c j := by
    erw [← inf_iSup_eq]
    rw [inf_eq_left.mpr hall]
    exact bot_lt_iff_ne_bot.mpr (condition_ne_bot t)
  obtain ⟨j,hj⟩ := nonzero_wit hh
  obtain ⟨r,hrt,hrj⟩ := strengthen t _ hj.ne'
  let i : I := ⟨r,hrt.trans ht,j,hrj⟩
  have h₁ : r.value ≤ a := le_iSup (fun k : I => k.val.value) i
  have h₂ : r.value ≤ aᶜ := (Condition.value_mono hrt).trans inf_le_right
  exact r.positive (bot_unique ((le_inf h₁ h₂).trans inf_compl_eq_bot.le))

/-- A single extension mixes different readings over the original base condition. -/
theorem exists_pure_row_reading (hθ : θ.IsRegular)
    (hcc : ∀ {I : Type u} (a : I → B), (∀ i, a i ≠ ⊥) → (∀ i j, i ≠ j → a i ⊓ a j = ⊥) → Cardinal.mk I < θ)
    {J : Type u} (p : Condition θ B) (c : J → Completion (Condition θ B)) (hc : condition p ≤ ⨆ j, c j) :
    ∃ q ≤ p, q.value = p.value ∧ p.value ≤ ⨆ j, q.read (c j) := by
  classical
  let I := {t : Condition θ B // t ≤ p ∧ ∃ j, condition t ≤ c j}
  obtain ⟨v, hv, hd, he⟩ := disjoint_cover (fun i : I => i.val.value)
  let S := {i : I // v i ≠ ⊥}
  let w (s : S) := v s.val
  let r (s : S) := s.val.val
  have hdisj (s t : S) (hst : s ≠ t) : w s ⊓ w t = ⊥ :=
    hd _ _ (fun h => hst (Subtype.ext h))
  have hcov : p.value ≤ ⨆ s : S, w s := by
    apply ((read_one_cover p c hc).trans_eq he.symm).trans
    apply iSup_le
    intro i
    by_cases hi : v i = ⊥
    · exact hi.le.trans bot_le
    · exact le_iSup w (⟨i,hi⟩ : S)
  let len (s : S) := (r s).length.toOrd.val
  let δ := ⨆ s, len s
  have hδ : δ < θ.ord := Ordinal.iSup_lt_of_lt_cof
    (by rw [hθ.cof_ord]; exact hcc w (fun s => s.property) hdisj) (fun s => (r s).length.toOrd.property)
  let ix : θ.ord.ToType := Ordinal.ToType.mk ⟨δ,hδ⟩
  have hix : ix.toOrd.val = δ := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  have hl (s : S) : (r s).length.toOrd.val ≤ ix.toOrd.val := (Ordinal.le_iSup len s).trans_eq hix.symm
  let bits (x : ix.toOrd.val.ToType) := ⨆ s : S, w s ⊓ StringName.padBits (hl s) (r s).bits x
  let q : Condition θ B := ⟨p.value,p.positive,ix,bits⟩
  have hqr (s : S) : q.withValue (w s) s.property ≤ r s := by
    apply (Condition.le_iff _ _).mpr
    refine ⟨hv s.val, hl s, fun i => ?_⟩
    change w s ⊓ (r s).bits i = w s ⊓ ⨆ j : S, w j ⊓ StringName.padBits (hl j) (r j).bits (StringName.includeIndex (hl s) i)
    rw [partition_mix w _ hdisj s, StringName.padBits_includeIndex]
  have hqp : q ≤ p := ⟨le_rfl,hcov.trans (iSup_le fun s => ((hqr s).trans s.val.property.1).2)⟩
  refine ⟨q,hqp,rfl,hcov.trans (iSup_le fun s => ?_)⟩
  obtain ⟨j,hj⟩ := s.val.property.2
  have hval : w s ≤ p.value := (hv s.val).trans (Condition.value_mono s.val.property.1)
  exact le_iSup_of_le j (q.le_read _ s.property hval ((condition_mono (hqr s)).trans hj))

private theorem pure_lower_bound (hθ : θ.IsRegular) {L : Type u} [LinearOrder L]
    (hL : Cardinal.mk L < θ) (p : Condition θ B) (f : L → Condition θ B) (hf : Antitone f)
    (hfp : ∀ i, f i ≤ p) (hv : ∀ i, (f i).value = p.value) :
    ∃ q ≤ p, q.value = p.value ∧ ∀ i, q ≤ f i := by
  classical
  by_cases hne : Nonempty L
  case neg => exact ⟨p, le_rfl, rfl, fun i => (hne ⟨i⟩).elim⟩
  let len (i : L) := (f i).length.toOrd.val
  let δ := ⨆ i, len i
  have hδ : δ < θ.ord := Ordinal.iSup_lt_of_lt_cof (by rwa [hθ.cof_ord]) (fun i => (f i).length.toOrd.property)
  let ix : θ.ord.ToType := Ordinal.ToType.mk ⟨δ,hδ⟩
  have hix : ix.toOrd.val = δ := congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  have hl (i : L) : (f i).length.toOrd.val ≤ ix.toOrd.val := (Ordinal.le_iSup len i).trans_eq hix.symm
  have forward {i j : L} (hij : i ≤ j) (x : (len i).ToType) (y : (len j).ToType)
      (he : x.toOrd.val = y.toOrd.val) : p.value ⊓ (f i).bits x = p.value ⊓ (f j).bits y := by
    obtain ⟨_,hle,hb⟩ := (Condition.le_iff _ _).mp (hf hij)
    have hy : StringName.includeIndex hle x = y :=
      Ordinal.ToType.mk.symm.injective (Subtype.ext ((StringName.includeIndex_toOrd hle x).trans he))
    rw [← hv j, ← hy]
    exact hb x
  have agree {i j : L} (x : (len i).ToType) (y : (len j).ToType) (he : x.toOrd.val = y.toOrd.val) :
      p.value ⊓ (f i).bits x = p.value ⊓ (f j).bits y := by
    rcases le_total i j with h | h
    · exact forward h x y he
    · exact (forward h y x he.symm).symm
  have stage (x : ix.toOrd.val.ToType) : ∃ j, x.toOrd.val < len j :=
    Ordinal.lt_iSup_iff.mp (x.toOrd.property.trans_eq hix)
  let pos (x : ix.toOrd.val.ToType) : (len (stage x).choose).ToType :=
    Ordinal.ToType.mk ⟨x.toOrd.val,(stage x).choose_spec⟩
  have hpos (x : ix.toOrd.val.ToType) : (pos x).toOrd.val = x.toOrd.val :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  let q : Condition θ B := ⟨p.value,p.positive,ix,fun x => (f (stage x).choose).bits (pos x)⟩
  have hq (i : L) : q ≤ f i := by
    apply (Condition.le_iff _ _).mpr
    exact ⟨(hv i).ge,hl i,fun x => agree x _
      ((StringName.includeIndex_toOrd (hl i) x).symm.trans (hpos _).symm)⟩
  exact ⟨q, (hq hne.some).trans (hfp _), rfl, hq⟩

/-- All rows of a short well-ordered family are read over the same first-stage value. -/
theorem exists_short_row_reading (hθ : θ.IsRegular)
    (hcc : ∀ {I : Type u} (a : I → B), (∀ i, a i ≠ ⊥) → (∀ i j, i ≠ j → a i ⊓ a j = ⊥) → Cardinal.mk I < θ)
    {L : Type u} [LinearOrder L] [WellFoundedLT L] (hL : Cardinal.mk L < θ)
    {J : L → Type u} (p : Condition θ B) (c : ∀ i, J i → Completion (Condition θ B))
    (hc : ∀ i, condition p ≤ ⨆ j, c i j) :
    ∃ q ≤ p, q.value = p.value ∧ ∀ i, p.value ≤ ⨆ j, q.read (c i j) := by
  classical
  let S := {q : Condition θ B // q ≤ p ∧ q.value = p.value}
  let good (i : L) (s : S) := p.value ≤ ⨆ j, s.val.read (c i j)
  let stage (i : L) (prior : ∀ j, j < i → S) (s : S) := (∀ j hj, s ≤ prior j hj) ∧ good i s
  let _ : Nonempty S := ⟨⟨p,le_rfl,rfl⟩⟩
  let step (i : L) (prior : ∀ j, j < i → S) := Classical.epsilon (stage i prior)
  let s := wellFounded_lt.fix step
  have eqn (i : L) : s i = step i (fun j _ => s j) := WellFounded.fix_eq _ _ _
  have result (i : L) : stage i (fun j _ => s j) (s i) := by
    induction i using (wellFounded_lt : WellFounded ((· < ·) : L → L → Prop)).induction with
    | h i ih =>
      let f (j : Set.Iio i) := (s j.val).val
      have hf : Antitone f := by
        intro a b hab
        rcases lt_or_eq_of_le hab with hab | rfl
        · exact (ih b.val b.property).1 a.val hab
        · exact le_rfl
      obtain ⟨q,hqp,hv,hprior⟩ := pure_lower_bound hθ ((Cardinal.mk_set_le (Set.Iio i)).trans_lt hL)
        p f hf (fun j => (s j.val).property.1) (fun j => (s j.val).property.2)
      obtain ⟨r,hrq,hrv,hr⟩ := exists_pure_row_reading hθ hcc q (c i) ((condition_mono hqp).trans (hc i))
      have hex : ∃ z, stage i (fun j _ => s j) z :=
        ⟨⟨r,hrq.trans hqp,hrv.trans hv⟩,fun j hj => hrq.trans (hprior ⟨j,hj⟩),hv.ge.trans hr⟩
      exact (eqn i).symm ▸ Classical.epsilon_spec hex
  have hs : Antitone (fun i => (s i).val) := by
    intro i j hij
    rcases lt_or_eq_of_le hij with h | rfl
    · exact (result j).1 i h
    · exact le_rfl
  obtain ⟨q,hqp,hv,hqs⟩ := pure_lower_bound hθ hL p _ hs (fun i => (s i).property.1) (fun i => (s i).property.2)
  exact ⟨q,hqp,hv, fun i => (result i).2.trans (iSup_mono fun j =>
    Condition.read_mono_same_value (hqs i) (hv.trans (s i).property.2.symm) (c i j))⟩

end Erdos1172Shioya.CohenCover
