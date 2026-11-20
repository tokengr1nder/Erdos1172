/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4AnonymousInternalLevyCollapse
public import Erdos1172.Part4ShioyaInternalOrderTransport
public import Erdos1172.Part4ShioyaBoundedDensePowerset
public import Erdos1172.Part4ShioyaIterationTailGCH

@[expose] public section

/-! # Countable-fusion real preservation, interval collapse, and full GCH in `InternalLevyAlgebra`

Over `InternalLevyStage κ α` and `InternalLevyAlgebra κ θ`:
1. Stage-local truth reading (`levyReads`) and countable fusion (`internalLevyStage_binary_reading`),
2. Preservation of `𝒫(ω)`, `check κ =ᴮ omegaOne`, and `CH` at all stages `α`,
3. Collapse of every ordinal `γ < α` to `κ` (`internalLevyStage_collapses_below`), and
4. Unconditional full internal GCH (`internalLevy_fullGCH_eq_top`) under ground tail GCH at `≥ θ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Flypitch Ordinal
open Cardinal bSet Lattice ErdosOmegaTwo ErdosFullGCH ErdosHartogs ErdosNameTransport
open ErdosPartialInjection ErdosRelationGraph ErdosInjectionExtension
open Erdos1172LevyCohen Erdos1172CompleteSubalgebra Erdos1172BooleanNameIteration
open Erdos1172PosetCompletion Erdos1172PositiveBoolean Erdos1172Shioya.ForcingCover
open bSet.ErdosShioyaInternal

universe u

namespace Erdos1172AnonymousInternalLevy

variable {κ : Cardinal.{u}}

private theorem ordinalLabel_mem {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {α : Ordinal.{u}} (i : α.ToType) {Γ : B} :
    Γ ≤ ordinalLabel i ∈ᴮ ordinalCarrier α :=
  check_mem (PSet.mk_mem_mk_of_lt (toOrd_lt i))

private theorem checked_eq_omegaOne_of_real_bound' {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (e : CompleteLatticeHom (anonymousAlgebra κ) B) (hκ : κ.IsInaccessible)
    (bound : (⊤ : B) ≤ injects_into (bv_powerset omega) (check (PSet.ordinalMk κ.ord))) :
    (⊤ : B) ≤ check (PSet.ordinalMk κ.ord) =ᴮ omegaOne := by
  apply omegaOne_property_unique
  refine le_inf (check_Ord (PSet.Ord_mk _)) (le_inf ?_ ?_)
  · rw [← imp_bot, ← deduction]
    exact bv_absurd _ (injects_into_trans (le_top.trans bound) inf_le_right) ErdosCantor.powerset_not_injects
  · refine le_iInf fun x => projection_imp.mpr fun _ _ hx => ?_
    apply ordinalCarrier_cases hx
    intro i _ _ hi
    have small := projection_imp.mp ((anonymous_checked_members_countable κ hκ).trans
      (iInf_le _ (ordinalLabel i))) (⊤ : anonymousAlgebra κ) le_rfl (ordinalLabel_mem i)
    have ho : e ⊤ ≤ Ord (mapNames e omega) := by
      simpa only [omega, map_check] using (Ord_omega : e ⊤ ≤ Ord (omega : bSet B))
    have mapped := map_injects_into_of_ordinal e small ho
    simp only [ordinalLabel, omega, TopHomClass.map_top, map_check] at mapped
    exact bv_rw'' (bv_symm hi) (le_top.trans mapped) B_ext_injects_into_left

private theorem exists_fresh_omegaOne' {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {Γ : B} {D : bSet B} (count : Γ ≤ injects_into D omega) :
    ∃ z : bSet B, Γ ≤ z ∈ᴮ omegaOne ∧ Γ ≤ (z ∈ᴮ D)ᶜ := by
  have join : Γ ≤ ⨆ z : bSet B, (z ∈ᴮ omegaOne) ⊓ (z ∈ᴮ D)ᶜ := by
    let P := ⨆ z : bSet B, (z ∈ᴮ omegaOne) ⊓ (z ∈ᴮ D)ᶜ
    have err : Γ ⊓ Pᶜ ≤ ⊥ := by
      let e := Γ ⊓ Pᶜ
      have sub : e ≤ omegaOne ⊆ᴮ D := by
        rw [subset_unfold']
        refine le_iInf fun z => projection_imp.mpr fun a ha hz => ?_
        by_contra hn
        have nz : a ⊓ (z ∈ᴮ D)ᶜ ≠ ⊥ := fun eq => hn (disjoint_compl_right_iff.mp (disjoint_iff.mpr eq))
        have inP : a ⊓ (z ∈ᴮ D)ᶜ ≤ P := le_iSup_of_le z (le_inf (inf_le_left.trans hz) inf_le_right)
        have inPc : a ⊓ (z ∈ᴮ D)ᶜ ≤ Pᶜ := (inf_le_left.trans ha).trans inf_le_right
        exact nz (le_bot_iff.mp ((le_inf inP inPc).trans inf_compl_eq_bot.le))
      have inj : e ≤ injects_into omegaOne omega :=
        injects_into_trans (injects_into_of_subset sub) (inf_le_left.trans count)
      have ninj : e ≤ (injects_into omegaOne omega)ᶜ :=
        le_top.trans (omegaOne_property.trans (inf_le_right.trans inf_le_left))
      exact (le_inf inj ninj).trans inf_compl_eq_bot.le
    calc
      Γ = Γ ⊓ (P ⊔ Pᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
      _ = (Γ ⊓ P) ⊔ (Γ ⊓ Pᶜ) := inf_sup_left _ _ _
      _ ≤ P ⊔ ⊥ := sup_le_sup inf_le_right err
      _ = P := sup_bot_eq _
  obtain ⟨z, hz⟩ := exists_convert join (B_ext_inf B_ext_mem_left (B_ext_neg (h := B_ext_mem_left)))
  exact ⟨z, hz.trans inf_le_left, hz.trans inf_le_right⟩

private theorem checked_family_bounds_cardinal' {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {θ : Cardinal.{u}} {Γ : B} (x : κ.ord.ToType → bSet B)
    (hCH : Γ ≤ bSet.CH) (hone : Γ ≤ check (PSet.ordinalMk κ.ord) =ᴮ omegaOne)
    (hupper : Γ ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaTwo)
    (hx : ∀ i, Γ ≤ x i ∈ᴮ check (PSet.ordinalMk θ.ord)) :
    Γ ≤ ⨆ β : θ.ord.ToType, ⨅ i : κ.ord.ToType, x i ∈ᴮ check (PSet.ordinalMk β.toOrd.val) := by
  let A_fam : bSet B := .mk κ.ord.ToType x (fun _ => ⊤)
  have ha : Γ ≤ A_fam ⊆ᴮ omegaTwo := by
    rw [subset_unfold]
    exact le_iInf fun i => (bv_rw'' hupper (hx i) B_ext_mem_right).trans_eq top_imp.symm
  have hs := ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le κ A_fam
    (Cardinal.mk_ord_toType κ).le
  obtain ⟨y, hy⟩ := ErdosOmegaTwoBounded.exists_strict_upper_bound hCH ha
    (bv_rw'' hone (le_top.trans hs) B_ext_injects_into_right)
  have hi (i : κ.ord.ToType) : Γ ≤ x i ∈ᴮ y :=
    mem_of_mem_subset (hy.trans inf_le_right) (le_top.trans (mem_mk' A_fam i))
  have h := bv_rw'' (bv_symm hupper) (hy.trans inf_le_left) B_ext_mem_right
  rw [PSet.ordinalMk_eq_def θ.ord, check_unfold, mem_unfold] at h
  change Γ ≤ ⨆ i : θ.ord.ToType, ⊤ ⊓ (y =ᴮ check (PSet.ordinalMk i.toOrd.val)) at h
  apply (le_inf (le_refl Γ) h).trans
  rw [inf_iSup_eq]
  exact iSup_le fun β => le_iSup_of_le β (le_iInf fun i =>
    bv_rw'' (inf_le_right.trans inf_le_right) (inf_le_left.trans (hi i)) B_ext_mem_right)

/-- Anonymous-algebra predicate asserting that `g` forces `c` in `InternalLevyStage κ α`. -/
def levyReads (α : Ordinal.{u}) (c : InternalLevyStage κ α) (g : bSet (anonymousAlgebra κ)) :
    anonymousAlgebra κ :=
  ⨆ p : {p : InternalLevyCondition κ α // condition p ≤ c},
    p.val.value ⊓ (g =ᴮ name p.val)

theorem levyReads_ext (α : Ordinal.{u}) (c : InternalLevyStage κ α) :
    B_ext (levyReads α c) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_bv_eq_left)

theorem levyReads_inf_compl_eq_bot (α : Ordinal.{u}) (c : InternalLevyStage κ α)
    (g : bSet (anonymousAlgebra κ)) :
    levyReads α c g ⊓ levyReads α cᶜ g = ⊥ := by
  unfold levyReads
  rw [iSup_inf_eq]
  apply le_antisymm ?_ bot_le
  refine iSup_le fun p => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun r => ?_
  let b := (p.val.value ⊓ (g =ᴮ name p.val)) ⊓ (r.val.value ⊓ (g =ᴮ name r.val))
  by_cases hb : b = ⊥
  · exact hb.le
  · let s := shrink p.val b hb (inf_le_left.trans inf_le_left)
    have hs_p : s ≤ p.val := shrink_le p.val b hb (inf_le_left.trans inf_le_left)
    have hs_r : s ≤ r.val :=
      ⟨inf_le_right.trans inf_le_left,
       subset_of_eq (bv_trans (bv_symm (inf_le_right.trans inf_le_right)) (inf_le_left.trans inf_le_right))⟩
    have hs_bot : condition s ≤ c ⊓ cᶜ :=
      le_inf ((condition_mono hs_p).trans p.property) ((condition_mono hs_r).trans r.property)
    exact False.elim (condition_ne_bot s (le_bot_iff.mp (hs_bot.trans inf_compl_eq_bot.le)))

theorem condition_inf_sourceHom_levyReads_le (α : Ordinal.{u})
    (p : InternalLevyCondition κ α) (c : InternalLevyStage κ α) :
    condition p ⊓ sourceHom (internalLevyPoset κ α) (levyReads α c (name p)) ≤ c := by
  unfold levyReads
  rw [_root_.map_iSup]
  erw [inf_iSup_eq]
  refine iSup_le fun s => ?_
  have hle_s : condition p ⊓ sourceHom (internalLevyPoset κ α) (s.val.value ⊓ (name p =ᴮ name s.val)) ≤
      condition s.val := by
    intro r hr
    change r ∈ (condition p).val ∧ r ∈ (sourceHom _ _).val at hr
    have hrb := (condition_le_source _ r _).mp (condition_le_iff.mpr hr.2)
    apply (mem_condition_iff s.val r).mpr
    intro t htr
    obtain ⟨v, hvt, hvp⟩ := (mem_condition_iff p r).mp hr.1 t htr
    have hvb := hvt.1.trans (htr.1.trans hrb)
    exact ⟨v, hvt, hvb.trans inf_le_left,
      subset_trans' (subset_of_eq (bv_symm (hvb.trans inf_le_right))) hvp.2⟩
  exact hle_s.trans s.property

theorem levyReads_mono_of_subset {α : Ordinal.{u}} {g r : bSet (anonymousAlgebra κ)}
    {Γ : anonymousAlgebra κ} {c : InternalLevyStage κ α}
    (hsub : Γ ≤ g ⊆ᴮ r) (hr : Γ ≤ r ∈ᴮ internalLevyPoset κ α) :
    Γ ⊓ levyReads α c g ≤ levyReads α c r := by
  unfold levyReads
  rw [inf_iSup_eq]
  refine iSup_le fun p => ?_
  let Δ := Γ ⊓ (p.val.value ⊓ (g =ᴮ name p.val))
  by_contra hnot
  have hpos : Δ ⊓ (levyReads α c r)ᶜ ≠ ⊥ := fun h0 =>
    hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
  have hctx : Δ ⊓ (levyReads α c r)ᶜ ≤ Γ := inf_le_left.trans inf_le_left
  have hval : Δ ⊓ (levyReads α c r)ᶜ ≤ p.val.value :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have heq : Δ ⊓ (levyReads α c r)ᶜ ≤ g =ᴮ name p.val :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  obtain ⟨t, htp, htb, hteq⟩ := exists_extension_refinement p.val hpos hval (hctx.trans hr)
    (subset_trans' (subset_of_eq (bv_symm heq)) (hctx.trans hsub))
  have ht_read : t.value ≤ levyReads α c r :=
    le_iSup_of_le ⟨t, (condition_mono htp).trans p.property⟩ (le_inf le_rfl hteq)
  exact t.nonzero (le_bot_iff.mp ((le_inf ht_read (htb.trans inf_le_right)).trans inf_compl_eq_bot.le))

theorem exists_levy_deciding_extension {α : Ordinal.{u}} {g : bSet (anonymousAlgebra κ)}
    {Γ : anonymousAlgebra κ} (hg : Γ ≤ g ∈ᴮ internalLevyPoset κ α) (c : InternalLevyStage κ α) :
    ∃ r : bSet (anonymousAlgebra κ), Γ ≤ r ∈ᴮ internalLevyPoset κ α ∧
      Γ ≤ g ⊆ᴮ r ∧ Γ ≤ levyReads α c r ⊔ levyReads α cᶜ r := by
  let V := ⨆ r : bSet (anonymousAlgebra κ), (r ∈ᴮ internalLevyPoset κ α) ⊓
    (g ⊆ᴮ r ⊓ (levyReads α c r ⊔ levyReads α cᶜ r))
  have hcov : Γ ≤ V := by
    by_contra hnot
    have hpos : Γ ⊓ Vᶜ ≠ ⊥ := fun h0 => hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    obtain ⟨p, hpb, hpeq⟩ := exists_canonical_refinement hpos (inf_le_left.trans hg)
    have hdec : ∃ r : InternalLevyCondition κ α, r ≤ p ∧ (condition r ≤ c ∨ condition r ≤ cᶜ) := by
      by_cases h0 : condition p ⊓ c = ⊥
      · exact ⟨p, le_rfl, Or.inr (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h0))⟩
      · obtain ⟨q, hq⟩ := exists_condition_le h0
        obtain ⟨r, hr_q, hr_p⟩ := (mem_condition_iff p q).mp
          (condition_le_iff.mp (hq.trans inf_le_left)) q le_rfl
        exact ⟨r, hr_p, Or.inl ((condition_mono hr_q).trans (hq.trans inf_le_right))⟩
    obtain ⟨r, hrp, hbranch⟩ := hdec
    have hsub : r.value ≤ g ⊆ᴮ name r := subset_trans' (subset_of_eq (hrp.1.trans hpeq)) hrp.2
    have hread : r.value ≤ levyReads α c (name r) ⊔ levyReads α cᶜ (name r) := by
      rcases hbranch with hl | hr
      · exact (le_iSup_of_le ⟨r, hl⟩ (le_inf le_rfl bv_refl)).trans le_sup_left
      · exact (le_iSup_of_le ⟨r, hr⟩ (le_inf le_rfl bv_refl)).trans le_sup_right
    have hrV : r.value ≤ V := le_iSup_of_le (name r) (le_inf (name_mem r) (le_inf hsub hread))
    exact r.nonzero (le_bot_iff.mp ((le_inf hrV (hrp.1.trans (hpb.trans inf_le_right))).trans inf_compl_eq_bot.le))
  obtain ⟨r, hr⟩ := exists_convert hcov (B_ext_inf B_ext_mem_left
    (B_ext_inf B_ext_subset_right (B_ext_sup (h₁ := levyReads_ext α c) (h₂ := levyReads_ext α cᶜ))))
  exact ⟨r, hr.trans inf_le_left, hr.trans (inf_le_right.trans inf_le_left),
    hr.trans (inf_le_right.trans inf_le_right)⟩

/-- Countable fusion in `InternalLevyStage κ α`: every condition refines to decide any `ℕ`-sequence
into `anonymousAlgebra κ`. -/
theorem internalLevyStage_binary_reading (α : Ordinal.{u})
    (p : InternalLevyCondition κ α) (c : ℕ → InternalLevyStage κ α) :
    ∃ t : InternalLevyCondition κ α, t ≤ p ∧ ∃ b : ℕ → anonymousAlgebra κ, ∀ n : ℕ,
      condition t ≤ (c n ⊓ sourceHom (internalLevyPoset κ α) (b n)) ⊔
        ((c n)ᶜ ⊓ (sourceHom (internalLevyPoset κ α) (b n))ᶜ) := by
  classical
  let Γ := p.value
  let State := {r : bSet (anonymousAlgebra κ) // Γ ≤ r ∈ᴮ internalLevyPoset κ α}
  have hext (n : ℕ) (s : State) :
      ∃ u : State, Γ ≤ s.val ⊆ᴮ u.val ∧ Γ ≤ levyReads α (c n) u.val ⊔ levyReads α (c n)ᶜ u.val := by
    obtain ⟨r, hr, hsub, hread⟩ := exists_levy_deciding_extension s.property (c n)
    exact ⟨⟨r, hr⟩, hsub, hread⟩
  choose next hnext using hext
  let states : ℕ → State := Nat.rec ⟨name p, name_mem p⟩ next
  let s (n : ℕ) := (states n).val
  have hmono : ∀ n m : ℕ, m ≤ n → Γ ≤ s m ⊆ᴮ s n := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst hm0
      exact subset_self
    | succ n ih =>
      intro m hm
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact subset_self
      · exact subset_trans' (ih m (Nat.lt_succ_iff.mp hlt)) (hnext n (states n)).1
  let r_u := bv_union (ErdosNameSequence.family s)
  have hr_u : Γ ≤ r_u ∈ᴮ internalLevyPoset κ α :=
    internalLevyCollapse_union
      (ErdosNameSequence.family_subset fun n => (states n).property)
      (ErdosNameSequence.family_countable s)
      (ErdosNameSequence.family_inclusionChain fun m n hmn => hmono n m hmn)
  obtain ⟨t, htp, htv, hteq⟩ := exists_extension_refinement p p.nonzero le_rfl hr_u
    (ErdosNameSequence.term_subset_union s 0)
  refine ⟨t, htp, fun n => levyReads α (c n) (name t), fun n => ?_⟩
  have hdec_u : Γ ≤ levyReads α (c n) r_u ⊔ levyReads α (c n)ᶜ r_u := by
    have hstep := (hnext n (states n)).2
    have hsub_u := ErdosNameSequence.term_subset_union s (n + 1) (Γ := Γ)
    calc
      Γ ≤ Γ ⊓ (levyReads α (c n) (s (n + 1)) ⊔ levyReads α (c n)ᶜ (s (n + 1))) := le_inf le_rfl hstep
      _ = (Γ ⊓ levyReads α (c n) (s (n + 1))) ⊔ (Γ ⊓ levyReads α (c n)ᶜ (s (n + 1))) := inf_sup_left _ _ _
      _ ≤ levyReads α (c n) r_u ⊔ levyReads α (c n)ᶜ r_u :=
        sup_le ((levyReads_mono_of_subset hsub_u hr_u).trans le_sup_left)
          ((levyReads_mono_of_subset hsub_u hr_u).trans le_sup_right)
  have hdec_t : t.value ≤ levyReads α (c n) (name t) ⊔ levyReads α (c n)ᶜ (name t) :=
    bv_rw'' hteq (htv.trans hdec_u)
      (B_ext_sup (h₁ := levyReads_ext α (c n)) (h₂ := levyReads_ext α (c n)ᶜ))
  let j := sourceHom (internalLevyPoset κ α)
  have hother : j (levyReads α (c n)ᶜ (name t)) ≤ (j (levyReads α (c n) (name t)))ᶜ := by
    apply le_compl_iff_disjoint_right.mpr
    rw [disjoint_iff, ← InfHomClass.map_inf, inf_comm, levyReads_inf_compl_eq_bot, BotHomClass.map_bot]
  have hcov_t : condition t ≤ j (levyReads α (c n) (name t)) ⊔ j (levyReads α (c n)ᶜ (name t)) := by
    rw [← SupHomClass.map_sup]
    exact (condition_le_source _ t _).mpr hdec_t
  calc
    condition t ≤ condition t ⊓ (j (levyReads α (c n) (name t)) ⊔ j (levyReads α (c n)ᶜ (name t))) :=
      le_inf le_rfl hcov_t
    _ = (condition t ⊓ j (levyReads α (c n) (name t))) ⊔
        (condition t ⊓ j (levyReads α (c n)ᶜ (name t))) := inf_sup_left _ _ _
    _ ≤ (c n ⊓ j (levyReads α (c n) (name t))) ⊔
        ((c n)ᶜ ⊓ (j (levyReads α (c n) (name t)))ᶜ) :=
      sup_le_sup (le_inf (condition_inf_sourceHom_levyReads_le α t (c n)) inf_le_right)
        (le_inf (condition_inf_sourceHom_levyReads_le α t (c n)ᶜ) (inf_le_right.trans hother))

theorem internalLevyStage_reals_preserved (α : Ordinal.{u}) :
    (⊤ : InternalLevyStage κ α) ≤
      mapNames (sourceHom (internalLevyPoset κ α)) (bv_powerset omega) =ᴮ bv_powerset omega := by
  let j := sourceHom (internalLevyPoset κ α)
  apply subset_ext
  · simpa only [omega, map_check] using map_powerset_subset j (omega : bSet (anonymousAlgebra κ))
  · rw [subset_unfold']
    refine le_iInf fun x => projection_imp.mpr fun γ _ hx => ?_
    by_contra hn
    have nz : γ ⊓ (x ∈ᴮ mapNames j (bv_powerset omega))ᶜ ≠ ⊥ :=
      fun eq => hn (disjoint_compl_right_iff.mp (disjoint_iff.mpr eq))
    obtain ⟨p, hp⟩ := exists_condition_le nz
    obtain ⟨t, htp, b, hb⟩ := internalLevyStage_binary_reading α p (fun n => of_nat n ∈ᴮ x)
    have hx_sub : condition t ≤ x ⊆ᴮ omega :=
      (condition_mono htp).trans (mem_powerset_iff.mp ((hp.trans inf_le_left).trans hx))
    have heq : condition t ≤ x =ᴮ mapNames j (Erdos1172CohenIteration.realName b) :=
      Erdos1172CohenIteration.eq_map_realName_of_binary_agreement j hx_sub hb
    have hym : (⊤ : InternalLevyStage κ α) ≤
        mapNames j (Erdos1172CohenIteration.realName b) ∈ᴮ mapNames j (bv_powerset omega) := by
      rw [← map_mem, ← TopHomClass.map_top j]
      exact OrderHomClass.mono j (mem_powerset_iff.mpr (Erdos1172CohenIteration.realName_subset b))
    exact condition_ne_bot t (le_bot_iff.mp
      ((le_inf (mem_congr (bv_symm heq) bv_refl (le_top.trans hym))
        ((condition_mono htp).trans (hp.trans inf_le_right))).trans inf_compl_eq_bot.le))

theorem internalLevyStage_reals_inject_checked (hκ : κ.IsInaccessible) (α : Ordinal.{u}) :
    (⊤ : InternalLevyStage κ α) ≤ injects_into (bv_powerset omega) (check (PSet.ordinalMk κ.ord)) := by
  let j := sourceHom (internalLevyPoset κ α)
  have ho : j ⊤ ≤ Ord (mapNames j (check (PSet.ordinalMk κ.ord))) := by
    rw [map_check]
    exact check_Ord (PSet.Ord_mk _)
  have inj := map_injects_into_of_ordinal j (anonymous_powerset_omega_injects_checked_upper κ hκ) ho
  rw [TopHomClass.map_top, map_check] at inj
  exact bv_rw'' (internalLevyStage_reals_preserved α) inj B_ext_injects_into_left

theorem internalLevyStage_checked_eq_omegaOne (hκ : κ.IsInaccessible) (α : Ordinal.{u}) :
    (⊤ : InternalLevyStage κ α) ≤ check (PSet.ordinalMk κ.ord) =ᴮ omegaOne :=
  checked_eq_omegaOne_of_real_bound' (sourceHom (internalLevyPoset κ α)) hκ
    (internalLevyStage_reals_inject_checked hκ α)

theorem internalLevyStage_forces_CH (hκ : κ.IsInaccessible) (α : Ordinal.{u}) :
    (⊤ : InternalLevyStage κ α) ≤ bSet.CH := by
  apply ErdosCHHartogs.CH_iff_powerset_omega_injects_omegaOne.mpr
  exact bv_rw'' (internalLevyStage_checked_eq_omegaOne hκ α)
    (internalLevyStage_reals_inject_checked hκ α) B_ext_injects_into_right

/-- Generic surjection name at coordinate `γ < α` in `InternalLevyStage κ α`. -/
def stageCollapseGraph (α γ : Ordinal.{u}) : bSet (InternalLevyStage κ α) :=
  .mk (κ.ord.ToType × γ.ToType)
    (fun k => pair (ordinalLabel k.1) (ordinalLabel k.2))
    (fun k => ⨆ q : {q : InternalLevyCondition κ α //
        q.value ≤ pair (pair (ordinalCarrier γ) (ordinalLabel k.1)) (ordinalLabel k.2) ∈ᴮ name q},
      condition q.val)

/-- Every ordinal `γ < α` injects into `κ` in `InternalLevyStage κ α`. -/
theorem internalLevyStage_collapses_below (hκ : κ.IsInaccessible) {α γ : Ordinal.{u}} (hγα : γ < α) :
    (⊤ : InternalLevyStage κ α) ≤ injects_into (ordinalCarrier γ) (ordinalCarrier κ.ord) := by
  by_cases hγ0 : γ = 0
  · subst hγ0
    have hemp : (⊤ : InternalLevyStage κ α) ≤ ordinalCarrier 0 =ᴮ (∅ : bSet (InternalLevyStage κ α)) := by
      apply subset_ext ?_ empty_subset
      rw [ordinalCarrier, PSet.ordinalMk_eq_def 0, subset_unfold]
      exact le_iInf fun x => False.elim (not_lt_bot (toOrd_lt x))
    exact bv_rw'' (ϕ := fun z => injects_into z (ordinalCarrier κ.ord))
      (bv_symm hemp) (injects_into_of_subset empty_subset) B_ext_injects_into_left
  · have hγ_pos : 0 < γ := bot_lt_iff_ne_bot.mpr hγ0
    let F := stageCollapseGraph (κ := κ) α γ
    let Q := internalLevyPoset κ α
    have hpair_mem (i : κ.ord.ToType) (y : γ.ToType) :
        (pair (ordinalLabel i) (ordinalLabel y) ∈ᴮ F) =
        ⨆ q : {q : InternalLevyCondition κ α //
            q.value ≤ pair (pair (ordinalCarrier γ) (ordinalLabel i)) (ordinalLabel y) ∈ᴮ name q},
          condition q.val := by
      apply le_antisymm
      · dsimp only [F, stageCollapseGraph]
        rw [mem_unfold]
        refine iSup_le fun l => ?_
        by_cases hkl : (i, y) = l
        · subst hkl
          exact inf_le_left
        · have hne : (pair (ordinalLabel i) (ordinalLabel y) =ᴮ
              (pair (ordinalLabel l.1) (ordinalLabel l.2) : bSet (InternalLevyStage κ α))) = ⊥ := by
            apply le_bot_iff.mp
            have h := pair_eq_pair_iff (x := (ordinalLabel i : bSet (InternalLevyStage κ α)))
              (y := ordinalLabel y) (x' := ordinalLabel l.1) (y' := ordinalLabel l.2) |>.mp le_rfl
            by_cases h1 : i = l.1
            · have h2 : y ≠ l.2 := fun e2 => hkl (Prod.ext h1 e2)
              have hr := h.2
              rw [ordinalLabel_eq, if_neg h2] at hr
              exact hr
            · have hl := h.1
              rw [ordinalLabel_eq, if_neg h1] at hl
              exact hl
          erw [hne, inf_bot_eq]
          exact bot_le
      · refine iSup_le fun ⟨q, hq⟩ => ?_
        dsimp only [F, stageCollapseGraph]
        rw [mem_unfold]
        exact le_iSup_of_le (i, y) (le_inf (le_iSup (fun r : {r : InternalLevyCondition κ α //
          r.value ≤ pair (pair (ordinalCarrier γ) (ordinalLabel i)) (ordinalLabel y) ∈ᴮ name r} =>
            condition r.val) ⟨q, hq⟩) bv_refl)
    have hdisj_val (i : κ.ord.ToType) {y₁ y₂ : γ.ToType} (hne : y₁ ≠ y₂) :
        (pair (ordinalLabel i) (ordinalLabel y₁) ∈ᴮ F) ⊓
        (pair (ordinalLabel i) (ordinalLabel y₂) ∈ᴮ F) = ⊥ := by
      rw [hpair_mem i y₁, hpair_mem i y₂]
      erw [iSup_inf_eq]
      apply le_antisymm ?_ bot_le
      refine iSup_le fun ⟨q₁, hq₁⟩ => ?_
      erw [inf_iSup_eq]
      refine iSup_le fun ⟨q₂, hq₂⟩ => ?_
      by_contra hpos
      obtain ⟨r, hr₁, hr₂⟩ := (condition_inf_ne_bot_iff q₁ q₂).mp (fun h0 => hpos h0.le)
      have hm₁ : r.value ≤ pair (pair (ordinalCarrier γ) (ordinalLabel i)) (ordinalLabel y₁) ∈ᴮ name r :=
        mem_of_mem_subset hr₁.2 (hr₁.1.trans hq₁)
      have hm₂ : r.value ≤ pair (pair (ordinalCarrier γ) (ordinalLabel i)) (ordinalLabel y₂) ∈ᴮ name r :=
        mem_of_mem_subset hr₂.2 (hr₂.1.trans hq₂)
      have hr_fn : r.value ≤ is_func (name r) :=
        (countableCollapse_mem.mp (mem_internalLevyCollapse.mp (name_mem r)).1).2.1
      have heq_y : r.value ≤ ordinalLabel y₁ =ᴮ ordinalLabel y₂ :=
        eq_of_is_func_of_eq hr_fn bv_refl hm₁ hm₂
      rw [ordinalLabel_eq, if_neg hne] at heq_y
      exact r.nonzero (le_bot_iff.mp heq_y)
    have hF_sub : (⊤ : InternalLevyStage κ α) ≤ F ⊆ᴮ prod (ordinalCarrier κ.ord) (ordinalCarrier γ) := by
      dsimp only [F, stageCollapseGraph]
      rw [subset_unfold]
      refine le_iInf fun k => ?_
      rw [← deduction]
      exact inf_le_left.trans (mem_prod (ordinalLabel_mem k.1) (ordinalLabel_mem k.2))
    have hF_fn : (⊤ : InternalLevyStage κ α) ≤ is_func F := by
      refine le_iInf fun a₁ => le_iInf fun a₂ => le_iInf fun v₁ => le_iInf fun v₂ => ?_
      rw [← deduction, ← deduction]
      let Δ := ((⊤ : InternalLevyStage κ α) ⊓ (pair a₁ v₁ ∈ᴮ F ⊓ pair a₂ v₂ ∈ᴮ F)) ⊓ (a₁ =ᴮ a₂)
      have hm₁ : Δ ≤ pair a₁ v₁ ∈ᴮ F := inf_le_left.trans (inf_le_right.trans inf_le_left)
      have hm₂ : Δ ≤ pair a₂ v₂ ∈ᴮ F := inf_le_left.trans (inf_le_right.trans inf_le_right)
      dsimp only [F, stageCollapseGraph] at hm₁ hm₂
      rw [mem_unfold] at hm₁ hm₂
      apply (le_inf (le_inf inf_le_right hm₁) hm₂).trans
      erw [inf_iSup_eq]
      refine iSup_le fun k₂ => ?_
      erw [inf_iSup_eq, iSup_inf_eq]
      refine iSup_le fun k₁ => ?_
      have hk₁₂ : ((a₁ =ᴮ a₂) ⊓ (F.bval k₁ ⊓ (pair a₁ v₁ =ᴮ F.func k₁))) ⊓
          (F.bval k₂ ⊓ (pair a₂ v₂ =ᴮ F.func k₂)) ≤ ordinalLabel k₁.1 =ᴮ ordinalLabel k₂.1 :=
        bv_trans (bv_symm (pair_eq_pair_iff.mp ((inf_le_left.trans inf_le_right).trans inf_le_right)).1)
          (bv_trans (inf_le_left.trans inf_le_left) (pair_eq_pair_iff.mp (inf_le_right.trans inf_le_right)).1)
      by_cases hi_eq : k₁.1 = k₂.1
      · by_cases hy_eq : k₁.2 = k₂.2
        · have hk_eq : k₁ = k₂ := Prod.ext hi_eq hy_eq
          subst hk_eq
          exact bv_trans (pair_eq_pair_iff.mp ((inf_le_left.trans inf_le_right).trans inf_le_right)).2
            (bv_symm (pair_eq_pair_iff.mp (inf_le_right.trans inf_le_right)).2)
        · have hbot : ((a₁ =ᴮ a₂) ⊓ (F.bval k₁ ⊓ (pair a₁ v₁ =ᴮ F.func k₁))) ⊓
              (F.bval k₂ ⊓ (pair a₂ v₂ =ᴮ F.func k₂)) ≤
              (pair (ordinalLabel k₁.1) (ordinalLabel k₁.2) ∈ᴮ F) ⊓
              (pair (ordinalLabel k₁.1) (ordinalLabel k₂.2) ∈ᴮ F) := by
            refine le_inf ?_ ?_
            · rw [hpair_mem]
              exact (inf_le_left.trans inf_le_right).trans inf_le_left
            · rw [hi_eq, hpair_mem]
              exact inf_le_right.trans inf_le_left
          exact (hbot.trans_eq (hdisj_val k₁.1 hy_eq)).trans bot_le
      · rw [ordinalLabel_eq, if_neg hi_eq] at hk₁₂
        exact hk₁₂.trans bot_le
    have hF_tot : (⊤ : InternalLevyStage κ α) ≤
        ⨅ x : bSet (InternalLevyStage κ α), (x ∈ᴮ ordinalCarrier κ.ord) ⟹
          ⨆ y : bSet (InternalLevyStage κ α), (y ∈ᴮ ordinalCarrier γ) ⊓ (pair x y ∈ᴮ F) := by
      refine le_iInf fun x => projection_imp.mpr fun _ _ hx => ?_
      apply ordinalCarrier_cases hx
      intro i _ _ hi
      apply le_of_dense_conditions_le Set.univ (fun p => ⟨p, Set.mem_univ _, le_rfl⟩)
      rintro ⟨p, _⟩ hp
      by_contra hnot
      let goal := ⨆ y : bSet (InternalLevyStage κ α), (y ∈ᴮ ordinalCarrier γ) ⊓ (pair x y ∈ᴮ F)
      have hpos : condition p ⊓ goalᶜ ≠ ⊥ := fun h0 =>
        hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
      obtain ⟨p₁, hp₁⟩ := exists_condition_le hpos
      obtain ⟨p₂, hp₂_p₁, hp₂_p⟩ := (mem_condition_iff p p₁).mp
        (condition_le_iff.mp (hp₁.trans inf_le_left)) p₁ le_rfl
      let dom := graphDomain (prod (ordinalCarrier α) (ordinalCarrier κ.ord)) (ordinalCarrier α) (name p₂)
      let pt : bSet (anonymousAlgebra κ) := pair (ordinalCarrier γ) (ordinalLabel i)
      have contra_p₃ (y₀ : γ.ToType) (p₃ : InternalLevyCondition κ α)
          (hp₃_p₂ : p₃ ≤ p₂) (hp₃_mem : p₃.value ≤ pair pt (ordinalLabel y₀) ∈ᴮ name p₃) : False := by
        have hp₃_F : condition p₃ ≤ pair (ordinalLabel i) (ordinalLabel y₀) ∈ᴮ F := by
          rw [hpair_mem]
          exact le_iSup (fun r : {r : InternalLevyCondition κ α //
            r.value ≤ pair pt (ordinalLabel y₀) ∈ᴮ name r} => condition r.val) ⟨p₃, hp₃_mem⟩
        have hp₃_x : condition p₃ ≤ x =ᴮ ordinalLabel i :=
          (((condition_mono hp₃_p₂).trans (condition_mono hp₂_p)).trans hp).trans hi
        have hp₃_goal : condition p₃ ≤ goal :=
          le_iSup_of_le (ordinalLabel y₀) (le_inf (ordinalLabel_mem y₀)
            (mem_congr (pair_congr (bv_symm hp₃_x) bv_refl) bv_refl hp₃_F))
        have hp₃_not : condition p₃ ≤ goalᶜ :=
          ((condition_mono hp₃_p₂).trans (condition_mono hp₂_p₁)).trans (hp₁.trans inf_le_right)
        exact condition_ne_bot p₃ (le_bot_iff.mp ((le_inf hp₃_goal hp₃_not).trans inf_compl_eq_bot.le))
      by_cases hdom_pos : p₂.value ⊓ (pt ∈ᴮ dom) ≠ ⊥
      · have hex : p₂.value ⊓ (pt ∈ᴮ dom) ≤ ⨆ y : γ.ToType, pair pt (ordinalLabel y) ∈ᴮ name p₂ := by
          have hm : p₂.value ⊓ (pt ∈ᴮ dom) ≤ ⨆ v : bSet (anonymousAlgebra κ),
              (v ∈ᴮ ordinalCarrier α) ⊓ (pair pt v ∈ᴮ name p₂) :=
            (inf_le_right.trans (mem_graphDomain _ _ (name p₂) pt).le).trans inf_le_right
          apply (le_inf inf_le_left hm).trans
          rw [inf_iSup_eq]
          refine iSup_le fun v => ?_
          have hbd : p₂.value ⊓ ((v ∈ᴮ ordinalCarrier α) ⊓ (pair pt v ∈ᴮ name p₂)) ≤
              levyBoundPred (ordinalCarrier κ.ord) (ordinalCarrier α) (pair pt v) :=
            allIn_elim (inf_le_left.trans (mem_internalLevyCollapse.mp (name_mem p₂)).2)
              (inf_le_right.trans inf_le_right)
          apply (le_inf (inf_le_right.trans inf_le_right) hbd).trans
          change _ ⊓ (⨆ ξ : bSet (anonymousAlgebra κ), (ξ ∈ᴮ ordinalCarrier α) ⊓ _) ≤ _
          rw [inf_iSup_eq]
          refine iSup_le fun ξ => ?_
          change _ ⊓ ((ξ ∈ᴮ ordinalCarrier α) ⊓ (⨆ η : bSet (anonymousAlgebra κ), (η ∈ᴮ ordinalCarrier κ.ord) ⊓ _)) ≤ _
          rw [← inf_assoc _ (ξ ∈ᴮ _), inf_iSup_eq]
          refine iSup_le fun η => ?_
          change _ ⊓ ((η ∈ᴮ ordinalCarrier κ.ord) ⊓ (⨆ y : bSet (anonymousAlgebra κ), (y ∈ᴮ ξ) ⊓ _)) ≤ _
          rw [← inf_assoc _ (η ∈ᴮ _), inf_iSup_eq]
          refine iSup_le fun y => ?_
          let e := (((pair pt v ∈ᴮ name p₂) ⊓ (ξ ∈ᴮ ordinalCarrier α)) ⊓ (η ∈ᴮ ordinalCarrier κ.ord)) ⊓
            ((y ∈ᴮ ξ) ⊓ (pair pt v =ᴮ pair (pair ξ η) y))
          have hpt_eq : e ≤ pt =ᴮ pair ξ η := (pair_eq_pair_iff.mp (inf_le_right.trans inf_le_right)).1
          have hγ_ξ : e ≤ ordinalCarrier γ =ᴮ ξ := (pair_eq_pair_iff.mp hpt_eq).1
          have hv_y : e ≤ v =ᴮ y := (pair_eq_pair_iff.mp (inf_le_right.trans inf_le_right)).2
          apply ordinalCarrier_cases (mem_congr (bv_symm hv_y) (bv_symm hγ_ξ) (inf_le_right.trans inf_le_left))
          intro y₀ f hf hy₀
          exact le_iSup_of_le y₀ (mem_congr (pair_congr bv_refl hy₀) bv_refl
            (hf.trans (((inf_le_left.trans inf_le_left).trans inf_le_left))))
        obtain ⟨y₀, hy₀_ne⟩ := exists_mem_iSup_inf_ne_bot (c := p₂.value ⊓ (pt ∈ᴮ dom))
          (by erw [inf_of_le hex]; exact hdom_pos)
        exact contra_p₃ y₀ (shrink p₂ _ hy₀_ne (inf_le_left.trans inf_le_left))
          (shrink_le _ _ _ _) inf_le_right
      · have hfresh : p₂.value ≤ (pt ∈ᴮ dom)ᶜ :=
          le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr (not_ne_iff.mp hdom_pos))
        let y₀ : γ.ToType := Ordinal.ToType.mk ⟨0, hγ_pos⟩
        have hins : p₂.value ≤ bSet.insert1 (pair pt (ordinalLabel y₀)) (name p₂) ∈ᴮ Q :=
          internalLevyCollapse_insert (check_Ord (PSet.Ord_mk α)) (name_mem p₂)
            (check_mem (PSet.mk_mem_mk_of_lt hγα)) (ordinalLabel_mem i) (ordinalLabel_mem y₀) hfresh
        obtain ⟨p₃, hp₃_p₂, _, hp₃eq⟩ := exists_extension_refinement p₂ p₂.nonzero le_rfl hins subset_insertPair
        exact contra_p₃ y₀ p₃ hp₃_p₂ (mem_congr bv_refl hp₃eq pair_mem_insertPair)
    have hF_func' : (⊤ : InternalLevyStage κ α) ≤
        is_func' (ordinalCarrier κ.ord) (ordinalCarrier γ) F :=
      le_inf hF_fn hF_tot
    have hF_surj : (⊤ : InternalLevyStage κ α) ≤ is_surj (ordinalCarrier κ.ord) (ordinalCarrier γ) F := by
      refine le_iInf fun y => projection_imp.mpr fun _ _ hy => ?_
      apply ordinalCarrier_cases hy
      intro y₀ _ _ hy₀
      apply le_of_dense_conditions_le Set.univ (fun p => ⟨p, Set.mem_univ _, le_rfl⟩)
      rintro ⟨p, _⟩ hp
      by_contra hnot
      let goal := ⨆ x : bSet (InternalLevyStage κ α), (x ∈ᴮ ordinalCarrier κ.ord) ⊓ (pair x y ∈ᴮ F)
      have hpos : condition p ⊓ goalᶜ ≠ ⊥ := fun h0 =>
        hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
      obtain ⟨p₁, hp₁⟩ := exists_condition_le hpos
      obtain ⟨p₂, hp₂_p₁, hp₂_p⟩ := (mem_condition_iff p p₁).mp
        (condition_le_iff.mp (hp₁.trans inf_le_left)) p₁ le_rfl
      obtain ⟨hp₂_cc, _⟩ := mem_internalLevyCollapse.mp (name_mem p₂)
      obtain ⟨hp₂_sub, _, hp₂_cnt⟩ := countableCollapse_mem.mp hp₂_cc
      let dom := graphDomain (prod (ordinalCarrier α) (ordinalCarrier κ.ord)) (ordinalCarrier α) (name p₂)
      let slice := comprehend (fun u => pair (ordinalCarrier γ) u ∈ᴮ dom) (ordinalCarrier κ.ord)
      have hslice_cnt : p₂.value ≤ injects_into slice omega := by
        have hdom_cnt : p₂.value ≤ injects_into dom omega :=
          CollapsePath.domain_countable hp₂_sub hp₂_cnt
        have hrel_left (w : bSet (anonymousAlgebra κ)) :
            B_ext (fun u => w =ᴮ pair (ordinalCarrier γ) u) := fun _ _ =>
          bv_trans inf_le_right (pair_congr bv_refl inf_le_left)
        let emb_s := relationGraph slice dom (fun u w => w =ᴮ pair (ordinalCarrier γ) u)
        have hemb_inj : p₂.value ≤ is_injective_function slice dom emb_s := by
          refine le_inf (relationGraph_is_function
            hrel_left
            (fun _ => B_ext_bv_eq_left) ?_ ?_) ?_
          · refine le_iInf fun u => projection_imp.mpr fun _ _ hu => ?_
            have hu_s := (mem_comprehend_and B_ext_pair_mem_right).mp hu
            exact le_iSup_of_le (pair (ordinalCarrier γ) u) (le_inf hu_s.2 bv_refl)
          · intro _ _ w₁ w₂ _ _ _ _ _ _ hw₁ hw₂ hx
            exact bv_trans hw₁ (bv_trans (pair_congr bv_refl hx) (bv_symm hw₂))
          · refine le_iInf fun u₁ => le_iInf fun u₂ => le_iInf fun w₁ => le_iInf fun w₂ => ?_
            rw [← deduction]
            let Δ_inj := p₂.value ⊓ ((pair u₁ w₁ ∈ᴮ emb_s ⊓ pair u₂ w₂ ∈ᴮ emb_s) ⊓ (w₁ =ᴮ w₂))
            have hm₁_in : Δ_inj ≤ pair u₁ w₁ ∈ᴮ emb_s :=
              inf_le_right.trans (inf_le_left.trans inf_le_left)
            have hm₂_in : Δ_inj ≤ pair u₂ w₂ ∈ᴮ emb_s :=
              inf_le_right.trans (inf_le_left.trans inf_le_right)
            have hw₁₂ : Δ_inj ≤ w₁ =ᴮ w₂ := inf_le_right.trans inf_le_right
            have hm₁ := (mem_relationGraph_iff hrel_left (fun _ => B_ext_bv_eq_left)).mp hm₁_in
            have hm₂ := (mem_relationGraph_iff hrel_left (fun _ => B_ext_bv_eq_left)).mp hm₂_in
            exact (pair_eq_pair_iff.mp (bv_trans (bv_symm hm₁.2.2) (bv_trans hw₁₂ hm₂.2.2))).2
        exact injects_into_trans (injects_into_of_injection_into (le_iSup_of_le emb_s hemb_inj)) hdom_cnt
      obtain ⟨z, hz_ω₁, hz_not_slice⟩ := exists_fresh_omegaOne' hslice_cnt
      have hz_κ : p₂.value ≤ z ∈ᴮ ordinalCarrier κ.ord :=
        mem_congr bv_refl (bv_symm (le_top.trans (anonymous_checked_upper_eq_omegaOne κ hκ))) hz_ω₁
      have hz_fresh : p₂.value ≤ (pair (ordinalCarrier γ) z ∈ᴮ dom)ᶜ := by
        rw [← imp_bot, ← deduction]
        have hin_s : p₂.value ⊓ (pair (ordinalCarrier γ) z ∈ᴮ dom) ≤ z ∈ᴮ slice :=
          (mem_comprehend_and B_ext_pair_mem_right).mpr ⟨inf_le_left.trans hz_κ, inf_le_right⟩
        exact (le_inf hin_s (inf_le_left.trans hz_not_slice)).trans inf_compl_eq_bot.le
      have hex_i : p₂.value ≤ ⨆ i : κ.ord.ToType, z =ᴮ ordinalLabel i := by
        rw [ordinalCarrier, PSet.ordinalMk_eq_def, check_unfold, mem_unfold] at hz_κ
        exact hz_κ.trans (iSup_le fun i => le_iSup_of_le i inf_le_right)
      obtain ⟨i₀, hi₀_ne⟩ := exists_mem_iSup_inf_ne_bot (c := p₂.value)
        (by erw [inf_of_le hex_i]; exact p₂.nonzero)
      let v_i := p₂.value ⊓ (z =ᴮ ordinalLabel i₀)
      have hi₀_fresh : v_i ≤ (pair (ordinalCarrier γ) (ordinalLabel i₀) ∈ᴮ dom)ᶜ :=
        bv_rw'' inf_le_right (inf_le_left.trans hz_fresh)
          (B_ext_neg (h := fun _ _ => mem_congr (pair_congr bv_refl inf_le_left) bv_refl inf_le_right))
      have hins : v_i ≤ bSet.insert1 (pair (pair (ordinalCarrier γ) (ordinalLabel i₀)) (ordinalLabel y₀))
          (name p₂) ∈ᴮ Q :=
        internalLevyCollapse_insert (check_Ord (PSet.Ord_mk α)) (inf_le_left.trans (name_mem p₂))
          (check_mem (PSet.mk_mem_mk_of_lt hγα)) (ordinalLabel_mem i₀) (ordinalLabel_mem y₀) hi₀_fresh
      obtain ⟨p₃, hp₃_p₂, _, hp₃eq⟩ := exists_extension_refinement p₂ hi₀_ne inf_le_left hins subset_insertPair
      have hp₃_mem : p₃.value ≤ pair (pair (ordinalCarrier γ) (ordinalLabel i₀)) (ordinalLabel y₀) ∈ᴮ name p₃ :=
        mem_congr bv_refl hp₃eq pair_mem_insertPair
      have hp₃_F : condition p₃ ≤ pair (ordinalLabel i₀) (ordinalLabel y₀) ∈ᴮ F := by
        rw [hpair_mem]
        exact le_iSup (fun r : {r : InternalLevyCondition κ α //
          r.value ≤ pair (pair (ordinalCarrier γ) (ordinalLabel i₀)) (ordinalLabel y₀) ∈ᴮ name r} =>
            condition r.val) ⟨p₃, hp₃_mem⟩
      have hp₃_y : condition p₃ ≤ y =ᴮ ordinalLabel y₀ :=
        (((condition_mono hp₃_p₂).trans (condition_mono hp₂_p)).trans hp).trans hy₀
      have hp₃_goal : condition p₃ ≤ goal :=
        le_iSup_of_le (ordinalLabel i₀) (le_inf (ordinalLabel_mem i₀)
          (mem_congr (pair_congr bv_refl (bv_symm hp₃_y)) bv_refl hp₃_F))
      have hp₃_not : condition p₃ ≤ goalᶜ :=
        ((condition_mono hp₃_p₂).trans (condition_mono hp₂_p₁)).trans (hp₁.trans inf_le_right)
      exact condition_ne_bot p₃ (le_bot_iff.mp ((le_inf hp₃_goal hp₃_not).trans inf_compl_eq_bot.le))
    have hsurj : (⊤ : InternalLevyStage κ α) ≤
        surjects_onto (ordinalCarrier κ.ord) (ordinalCarrier γ) :=
      le_iSup_of_le F (le_inf hF_func' hF_surj)
    exact ErdosCHHartogs.injects_into_of_larger_than_ordinal (check_Ord (PSet.Ord_mk κ.ord))
      (larger_than_of_surjects_onto hsurj)

theorem internalLevy_interval_collapse {θ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {α : Ordinal.{u}} (hα : α < θ.ord) :
    (⊤ : InternalLevyAlgebra κ θ) ≤ injects_into (ordinalCarrier α) omegaOne :=
  bv_rw'' (internalLevyStage_checked_eq_omegaOne hκ θ.ord)
    (internalLevyStage_collapses_below hκ hα) B_ext_injects_into_right

/-- Unconditional full internal GCH in `InternalLevyAlgebra κ θ` under ground tail GCH at `≥ θ`. -/
theorem internalLevy_fullGCH_eq_top {θ : Cardinal.{u}}
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (tail : ∀ μ : Cardinal.{u}, θ ≤ μ → (2 : Cardinal.{u}) ^ μ = Order.succ μ) :
    (fullGCHValue : InternalLevyAlgebra κ θ) = ⊤ := by
  let F := InternalLevyAlgebra κ θ
  obtain ⟨D, hD, hd⟩ := internalLevy_dense_size hk hκ hθ
  have hone : (⊤ : F) ≤ check (PSet.ordinalMk κ.ord) =ᴮ omegaOne :=
    internalLevyStage_checked_eq_omegaOne hκ θ.ord
  have hCH : (⊤ : F) ≤ bSet.CH := internalLevyStage_forces_CH hκ θ.ord
  have hmixed_below : (⊤ : F) ≤
      ⨅ x : bSet F, _root_.imp (x ∈ᴮ ordinalCarrier θ.ord) (injects_into x omegaOne) := by
    refine le_iInf fun x => projection_imp.mpr fun _ _ hx => ?_
    apply ordinalCarrier_cases hx
    intro i _ _ hi
    exact bv_rw'' (bv_symm hi)
      (le_top.trans (internalLevy_interval_collapse hκ (toOrd_lt i))) B_ext_injects_into_left
  have hhart : (injects_into (ordinalCarrier θ.ord) omegaOne : F)ᶜ ≤
      hartogsProperty omegaOne (ordinalCarrier θ.ord) :=
    le_inf (check_Ord (PSet.Ord_mk θ.ord)) (le_inf le_rfl (le_top.trans hmixed_below))
  have hθ_ω₂ : (injects_into (ordinalCarrier θ.ord) omegaOne : F)ᶜ ≤
      ordinalCarrier θ.ord =ᴮ omegaTwo :=
    hartogsProperty_unique one_injects_omegaOne hhart
  have hpow : (injects_into (ordinalCarrier θ.ord) omegaOne : F)ᶜ ≤
      injects_into (bv_powerset omegaOne) (ordinalCarrier θ.ord) := by
    obtain ⟨e⟩ := (Cardinal.le_def D θ.ord.ToType).mp (hD.trans_eq (Cardinal.mk_ord_toType θ).symm)
    have hsize : Cardinal.mk (PSet.ordinalMk κ.ord).Type < θ := by
      simpa only [PSet.ordinalMk_type, Cardinal.mk_ord_toType] using hk
    have hbounds : ∀ x : (PSet.ordinalMk κ.ord).Type → bSet F,
        (∀ i, (⊤ : F) ≤ x i ∈ᴮ check (PSet.ordinalMk θ.ord)) →
        (injects_into (ordinalCarrier θ.ord) omegaOne : F)ᶜ ≤
          ⨆ a : θ.ord.ToType, ⨅ i, x i ∈ᴮ check (PSet.ordinalMk a.toOrd.val) := by
      rw [PSet.ordinalMk_type]
      exact fun x hx => checked_family_bounds_cardinal' x (le_top.trans hCH) (le_top.trans hone)
        hθ_ω₂ (fun i => le_top.trans (hx i))
    have hpow_κ := Erdos1172Shioya.BoundedDensePowerset.powerset_injects_of_bounded_labels
      D e hd (PSet.ordinalMk κ.ord) hθ hsize hbounds
    exact bv_rw'' (ϕ := fun z => injects_into z (ordinalCarrier θ.ord))
      (bv_powerset_congr (le_top.trans hone)) hpow_κ B_ext_injects_into_left
  have hκθ : (⊤ : F) ≤ injects_into (ordinalCarrier κ.ord) (ordinalCarrier θ.ord) :=
    injects_into_of_subset (check_subset (ZFSet.subset_iff.mp
      (Ordinal.toZFSet_monotone (Cardinal.ord_le_ord.mpr hk.le))))
  have hω₁θ : (⊤ : F) ≤ injects_into omegaOne (ordinalCarrier θ.ord) :=
    bv_rw'' (ϕ := fun z => injects_into z (ordinalCarrier θ.ord)) hone hκθ B_ext_injects_into_left
  have hgch₁ : (⊤ : F) ≤ gchAt omegaOne := by
    let C : F := injects_into (ordinalCarrier θ.ord) omegaOne
    have hΘGCH : (⊤ : F) ≤ gchAt (ordinalCarrier θ.ord) :=
      Erdos1172Shioya.DenseCompletion.checked_gchAt D hd θ hθ.aleph0_lt.le hD (tail θ le_rfl)
    have onC : C ≤ gchAt omegaOne :=
      gchAt_of_mutual_injections le_rfl (le_top.trans hω₁θ) (le_top.trans hΘGCH)
    have onCc : Cᶜ ≤ gchAt omegaOne := gchAt_of_witness hhart hpow
    exact (sup_compl_eq_top (x := C)).ge.trans (sup_le onC onCc)
  have below (η : Ordinal.{u}) (low : η < κ.ord) : (⊤ : F) ≤ injects_into (ordinalCarrier η) omega :=
    omegaOne_member_injects (mem_congr bv_refl hone (check_mem (PSet.mk_mem_mk_of_lt low)))
  have onOrdinal (η : Ordinal.{u}) {d : F} (inf : d ≤ injects_into omega (ordinalCarrier η)) :
      d ≤ gchAt (ordinalCarrier η) := by
    by_cases low : η < κ.ord
    · exact gchAt_of_mutual_injections inf (le_top.trans (below η low))
        (le_top.trans (hCH.trans_eq gchAt_omega_eq_CH.symm))
    · apply gchAt_of_mutual_injections
        (le_top.trans (ErdosCheckedOrdinalCardinality.checked_cardinal_injects_ordinal η))
        (le_top.trans (ErdosCheckedOrdinalCardinality.checked_ordinal_injects_cardinal η))
      by_cases upper : θ ≤ η.card
      · exact le_top.trans (Erdos1172Shioya.DenseCompletion.checked_gchAt D hd η.card
          (hθ.aleph0_lt.le.trans upper) (hD.trans upper) (tail _ upper))
      · have hκη : κ ≤ η.card := le_of_not_gt fun h => low (Cardinal.lt_ord.mpr h)
        have hηθ : η.card.ord < θ.ord := Cardinal.ord_lt_ord.mpr (lt_of_not_ge upper)
        have h₁ : (⊤ : F) ≤ injects_into omegaOne (ordinalCarrier η.card.ord) :=
          bv_rw'' (ϕ := fun z => injects_into z (ordinalCarrier η.card.ord)) hone
            (injects_into_of_subset (check_subset (ZFSet.subset_iff.mp
              (Ordinal.toZFSet_monotone (Cardinal.ord_le_ord.mpr hκη))))) B_ext_injects_into_left
        exact le_top.trans (gchAt_of_mutual_injections h₁
          (internalLevy_interval_collapse hκ hηθ) hgch₁)
  apply top_unique
  refine le_iInf fun X => deduction.mp ?_
  have rep := Erdos1172Shioya.DenseCompletion.name_mutual_checked_ordinal D hd X
  apply (le_inf le_rfl (le_top.trans rep)).trans
  rw [inf_iSup_eq]
  refine iSup_le fun η => gchAt_of_mutual_injections
    (inf_le_right.trans inf_le_right) (inf_le_right.trans inf_le_left) ?_
  exact onOrdinal η (injects_into_trans (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_left))

end Erdos1172AnonymousInternalLevy
