/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4AnonymousInternalLevyConeTruth

@[expose] public section

/-! # Countable-witness compression and fresh-bit coding for the internal Lévy collapse

Over any complete Boolean algebra `R` satisfying `StrictCC R θ` and `check θ =ᴮ omegaOne`
(and specialized to `R := AmbientInternalLevy κ θ`), this module proves the two key stage-`α`
bridge theorems (`α < θ.ord`):

1. `compress_lifted_witness_to_R`: Given a first-stage Cohen condition `p : bSet R` extending `m₀`
   and a mixed witness `z : bSet (LocalizedSourceCohen R m₀ hm₀)` in the lifted stage-`α` Lévy
   poset on `coneInMaster hm₀ hp hsub`, countable-cover decision fusion in `Add(ω₁^R, 1)` plus
   `StrictCC R θ` yields an extension `p' ⊇ᴮ p` at `(⊤ : R)` and a `< θ`-supported functional
   graph `G' : SmallGroundLevyGraph U a θ α R` such that `z =ᴮ mapNames j_R G'.toBSet` on
   `coneInMaster hm₀ hp' hsub'`.
2. `code_small_ground_func_into_stage`: Conversely, given any `G : SmallGroundLevyGraph U a θ α R`
   and `p ⊇ᴮ m₀`, ground capture of `dom(p)` (`#dom < θ`) plus `exists_indexed_binary_assignment`
   on fresh ordinals `ζ : G.Idx → [μ_used, ν_ζ)` codes `G.weight` into the generic subset of `θ`;
   lifting the bounded-fiber graph through `boundedAnonName` yields `(p_mid, q_mid)` such that
   `q_mid ∈ᴮ P_lift(α)` and `q_mid =ᴮ mapNames j_R G.toBSet` on `coneInMaster hm₀ hp_mid hsub_mid`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Flypitch Ordinal
open Cardinal Filter bSet Lattice ErdosOmegaTwo ErdosNameTransport ErdosPartialInjection
open ErdosIdeal ErdosSmallPoolOperations ErdosRelationGraph
open Erdos1172LevyCohen Erdos1172CompleteSubalgebra Erdos1172BooleanNameIteration
open Erdos1172PosetCompletion Erdos1172PositiveBoolean Erdos1172RelativeValuation
open Erdos1172GroundUltrapower Erdos1172BooleanUltrapower Erdos1172LevyCollapse
open Erdos1172LevyCollapse.Matching bSet.ErdosShioyaInternal
open Erdos1172Shioya.UltrapowerStage (ordinalImage ordinalImage_code indexEquiv indexEquiv_label)

universe u

namespace Erdos1172AnonymousInternalLevy

section CountableCoverFusion
variable {R : Type u} [NontrivialCompleteBooleanAlgebra R]

private theorem exists_cover_condition {K : bSet R}
    (p : Erdos1172CohenIteration.Conditions K) {J : Type u}
    (u : J → Erdos1172CohenIteration.Algebra K) (hcov : condition p ≤ ⨆ j : J, u j) :
    ∃ (r : Erdos1172CohenIteration.Conditions K) (j : J), r ≤ p ∧ condition r ≤ u j := by
  have hmeet : condition p ⊓ (⨆ j : J, u j) ≠ ⊥ := by
    erw [inf_of_le hcov]
    exact condition_ne_bot p
  obtain ⟨j, hj⟩ := exists_mem_iSup_inf_ne_bot hmeet
  obtain ⟨q, hq⟩ := exists_condition_le hj
  obtain ⟨r, hrq, hrp⟩ :=
    (mem_condition_iff p q).mp (condition_le_iff.mp (hq.trans inf_le_left)) q le_rfl
  exact ⟨r, j, hrp, (condition_mono hrq).trans (hq.trans inf_le_right)⟩

private theorem exists_cover_condition_extension {K q : bSet R} {Γ : R}
    (Hq : Γ ≤ ErdosCohen.condition K q) {J : Type u}
    (u : J → Erdos1172CohenIteration.Algebra K)
    (hcov : (⊤ : Erdos1172CohenIteration.Algebra K) ≤ ⨆ j : J, u j) :
    ∃ r : bSet R, Γ ≤ ErdosCohen.condition K r ∧ Γ ≤ q ⊆ᴮ r ∧
      Γ ≤ ⨆ j : J, Erdos1172CohenIteration.reads (u j) r := by
  classical
  have hq_mem : Γ ≤ q ∈ᴮ ErdosCohen.conditions K := ErdosCohen.mem_conditions_iff.mpr Hq
  let V : R := ⨆ r : bSet R, (r ∈ᴮ ErdosCohen.conditions K) ⊓
    (q ⊆ᴮ r ⊓ ⨆ j : J, Erdos1172CohenIteration.reads (u j) r)
  have hle_V : Γ ≤ V := by
    by_contra hnot
    have hpos : Γ ⊓ Vᶜ ≠ ⊥ := fun h0 =>
      hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    obtain ⟨p, hpb, hpeq⟩ := exists_canonical_refinement hpos (inf_le_left.trans hq_mem)
    obtain ⟨r, j, hrp, hru⟩ := exists_cover_condition p u (le_top.trans hcov)
    have hsub : r.value ≤ q ⊆ᴮ name r := subset_trans' (bSet.subset_of_eq (hrp.1.trans hpeq)) hrp.2
    have hread : r.value ≤ ⨆ i : J, Erdos1172CohenIteration.reads (u i) (name r) :=
      (Erdos1172CohenIteration.value_le_reads hru).trans
        (le_iSup (fun i : J => Erdos1172CohenIteration.reads (u i) (name r)) j)
    have hrV : r.value ≤ V := le_iSup_of_le (name r) (le_inf (name_mem r) (le_inf hsub hread))
    exact r.nonzero (le_bot_iff.mp ((le_inf hrV (hrp.1.trans (hpb.trans inf_le_right))).trans
      inf_compl_eq_bot.le))
  obtain ⟨r, hr⟩ := exists_convert hle_V
    (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_subset_right
      (B_ext_iSup (h := fun j => Erdos1172CohenIteration.reads_ext (u j)))))
  exact ⟨r, ErdosCohen.mem_conditions_iff.mp (hr.trans inf_le_left),
    hr.trans (inf_le_right.trans inf_le_left),
    hr.trans (inf_le_right.trans inf_le_right)⟩

private theorem reads_iSup_of_extension {K q r : bSet R} {Γ : R} {J : Type u}
    {u : J → Erdos1172CohenIteration.Algebra K}
    (Hsub : Γ ≤ q ⊆ᴮ r) (Hr : Γ ≤ r ∈ᴮ ErdosCohen.conditions K)
    (Hdec : Γ ≤ ⨆ j : J, Erdos1172CohenIteration.reads (u j) q) :
    Γ ≤ ⨆ j : J, Erdos1172CohenIteration.reads (u j) r := by
  calc
    Γ ≤ Γ ⊓ ⨆ j : J, Erdos1172CohenIteration.reads (u j) q := le_inf le_rfl Hdec
    _ = ⨆ j : J, (Γ ⊓ Erdos1172CohenIteration.reads (u j) q) := inf_iSup_eq _ _
    _ ≤ ⨆ j : J, Erdos1172CohenIteration.reads (u j) r :=
      iSup_mono fun j => Erdos1172CohenIteration.reads_mono_of_subset Hsub Hr

/-- Same-condition countable fusion simultaneously deciding a countable sequence of indexed covers. -/
theorem exists_countable_cover_deciding_extension {K q : bSet R} {Γ : R}
    (HK : Γ ≤ ErdosHartogs.hartogsProperty omega K)
    (Hq : Γ ≤ ErdosCohen.condition K q)
    (J : ℕ → Type u) (u : ∀ n, J n → Erdos1172CohenIteration.Algebra K)
    (hcov : ∀ n, (⊤ : Erdos1172CohenIteration.Algebra K) ≤ ⨆ j : J n, u n j) :
    ∃ r : bSet R, Γ ≤ ErdosCohen.condition K r ∧ Γ ≤ q ⊆ᴮ r ∧
      ∀ n : ℕ, Γ ≤ ⨆ j : J n, Erdos1172CohenIteration.reads (u n j) r := by
  classical
  let State := {r : bSet R // Γ ≤ ErdosCohen.condition K r}
  have Hextend (n : ℕ) (s : State) :
      ∃ t : State, Γ ≤ s.val ⊆ᴮ t.val ∧
        Γ ≤ ⨆ j : J n, Erdos1172CohenIteration.reads (u n j) t.val := by
    obtain ⟨r, Hr, Hsub, Hread⟩ := exists_cover_condition_extension s.property (u n) (hcov n)
    exact ⟨⟨r, Hr⟩, Hsub, Hread⟩
  choose next hnext using Hextend
  let states : ℕ → State := Nat.rec ⟨q, Hq⟩ next
  let s : ℕ → bSet R := fun n => (states n).val
  have Hstep (n : ℕ) : Γ ≤ s n ⊆ᴮ s (n + 1) ∧
      Γ ≤ ⨆ j : J n, Erdos1172CohenIteration.reads (u n j) (s (n + 1)) :=
    hnext n (states n)
  have Hmono : ∀ n m : ℕ, m ≤ n → Γ ≤ s m ⊆ᴮ s n := by
    intro n
    induction n with
    | zero =>
      intro m hm
      rcases Nat.eq_zero_of_le_zero hm with rfl
      exact subset_self
    | succ n ih =>
      intro m hm
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact subset_self
      · exact subset_trans' (ih m (by omega)) (Hstep n).1
  let r : bSet R := bv_union (ErdosNameSequence.family s)
  have Hr : Γ ≤ ErdosCohen.condition K r :=
    ErdosCohen.condition_union_of_countable_chain HK
      (ErdosNameSequence.family_subset
        (fun n => ErdosCohen.mem_conditions_iff.mpr (states n).property))
      (ErdosNameSequence.family_inclusionChain (fun m n Hmn => Hmono n m Hmn))
      (ErdosNameSequence.family_countable s)
  refine ⟨r, Hr, ErdosNameSequence.term_subset_union s 0, ?_⟩
  intro n
  exact reads_iSup_of_extension (ErdosNameSequence.term_subset_union s (n + 1))
    (ErdosCohen.mem_conditions_iff.mpr Hr) (Hstep n).2

theorem nameCone_inf_firstStageHom_reads_le {K p : bSet R}
    (c : Erdos1172CohenIteration.Algebra K) :
    nameCone (ErdosCohen.conditions K) p ⊓
      Erdos1172CohenIteration.firstStageHom K (Erdos1172CohenIteration.reads c p) ≤ c := by
  let _ : CompleteBooleanAlgebra (Erdos1172CohenIteration.Algebra K) :=
    completionCompleteBooleanAlgebra
  unfold nameCone
  erw [iSup_inf_eq]
  refine iSup_le fun ⟨q, hq⟩ => ?_
  let j_K := Erdos1172CohenIteration.firstStageHom K
  have hqv : condition q ≤ j_K q.value :=
    (Erdos1172CohenIteration.condition_le_firstStageHom_iff K q q.value).mpr le_rfl
  have hr_eq : q.value ⊓ Erdos1172CohenIteration.reads c p ≤
      Erdos1172CohenIteration.reads c (name q) :=
    bv_rw' (bv_symm (inf_le_left.trans hq)) (h_congr := Erdos1172CohenIteration.reads_ext c)
      (H_new := inf_le_right)
  have hj_le : j_K q.value ⊓ j_K (Erdos1172CohenIteration.reads c p) ≤
      j_K (Erdos1172CohenIteration.reads c (name q)) :=
    (completeHom_inf j_K _ _).symm.le.trans (OrderHomClass.mono j_K hr_eq)
  exact (le_inf inf_le_left ((inf_le_inf hqv le_rfl).trans hj_le)).trans
    (Erdos1172CohenIteration.condition_inf_firstStageHom_reads_le q c)

theorem coneInMaster_inf_firstStageHom_reads_le {m₀ p : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : R) ≤ m₀ ⊆ᴮ p)
    (w : LocalizedSourceCohen R m₀ hm₀) :
    coneInMaster hm₀ hp hsub ⊓
      localizedFirstStageHom hm₀ (Erdos1172CohenIteration.reads w.val p) ≤ w := by
  change nameCone (ErdosCohen.conditions (omegaOne : bSet R)) p ⊓
    (Erdos1172CohenIteration.omegaOneFirstStageHom (Erdos1172CohenIteration.reads w.val p) ⊓
      (masterPositive m₀ hm₀).val) ≤ w.val
  exact (inf_le_inf_left (nameCone (ErdosCohen.conditions (omegaOne : bSet R)) p) inf_le_left).trans
    (nameCone_inf_firstStageHom_reads_le w.val)

theorem coneInMaster_val_inf_firstStageHom_reads_le {m₀ p : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : R) ≤ m₀ ⊆ᴮ p)
    (u : Erdos1172CohenIteration.omegaOneAlgebra R) :
    (coneInMaster hm₀ hp hsub).val ⊓
      (localizedFirstStageHom hm₀ (Erdos1172CohenIteration.reads u p)).val ≤ u := by
  change nameCone (ErdosCohen.conditions (omegaOne : bSet R)) p ⊓
    (Erdos1172CohenIteration.omegaOneFirstStageHom (Erdos1172CohenIteration.reads u p) ⊓
      (masterPositive m₀ hm₀).val) ≤ u
  exact (inf_le_inf_left (nameCone (ErdosCohen.conditions (omegaOne : bSet R)) p) inf_le_left).trans
    (nameCone_inf_firstStageHom_reads_le u)

end CountableCoverFusion

section BoundedFuncAndProductLift

/-- Δ₀ formula `∀ d ∈ D, ∀ y₁ ∈ V, ∀ y₂ ∈ V, (edge g d y₁ ∧ edge g d y₂) → y₁ = y₂`
in variables `(0 : g, 1 : D, 2 : V)`. -/
def funcBoundedFormula : InterpretedMaster.Formula (Fin 3) :=
  .allIn 1 (.allIn (some 2) (.allIn (some (some 2))
    (.imp (.both (.edge (some (some (some 0))) (some (some none)) (some none))
                 (.edge (some (some (some 0))) (some (some none)) none))
          (.eq (some none) none))))

theorem funcBoundedFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (g D V : bSet B) :
    funcBoundedFormula.eval ![g, D, V] = allIn D (fun d => allIn V (fun y₁ => allIn V (fun y₂ =>
        _root_.imp (edge g d y₁ ⊓ edge g d y₂) (y₁ =ᴮ y₂)))) :=
  rfl

theorem is_func_le_funcBoundedFormula {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {Γ : B} {g D V : bSet B} (hfn : Γ ≤ is_func g) :
    Γ ≤ funcBoundedFormula.eval ![g, D, V] := by
  rw [funcBoundedFormula_eval]
  refine allIn_intro fun {Δ₁} h₁ d _ =>
    allIn_intro fun {Δ₂} h₂ y₁ _ =>
      allIn_intro fun {Δ₃} h₃ y₂ _ => deduction.mp ?_
  exact eq_of_is_func_of_eq ((inf_le_left.trans (h₃.trans (h₂.trans h₁))).trans hfn)
    bv_refl (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)

theorem is_func_of_subset_prod_and_funcBoundedFormula {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {Γ : B} {g D V : bSet B} (hsub : Γ ≤ g ⊆ᴮ prod D V)
    (hfn : Γ ≤ funcBoundedFormula.eval ![g, D, V]) :
    Γ ≤ is_func g := by
  rw [funcBoundedFormula_eval] at hfn
  refine le_iInf fun a₁ => le_iInf fun a₂ => le_iInf fun y₁ => le_iInf fun y₂ => ?_
  rw [← deduction, ← deduction]
  let Δ : B := (Γ ⊓ (pair a₁ y₁ ∈ᴮ g ⊓ pair a₂ y₂ ∈ᴮ g)) ⊓ (a₁ =ᴮ a₂)
  have hΔ_Γ : Δ ≤ Γ := (inf_le_left.trans inf_le_left)
  have hm₁ : Δ ≤ pair a₁ y₁ ∈ᴮ g := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hm₂ : Δ ≤ pair a₂ y₂ ∈ᴮ g := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hp₁ := mem_prod_iff.mp (mem_of_mem_subset (hΔ_Γ.trans hsub) hm₁)
  have hp₂ := mem_prod_iff.mp (mem_of_mem_subset (hΔ_Γ.trans hsub) hm₂)
  have he₂ : Δ ≤ edge g a₁ y₂ := mem_congr (pair_congr (bv_symm inf_le_right) bv_refl) bv_refl hm₂
  have himp := allIn_elim (allIn_elim (allIn_elim (hΔ_Γ.trans hfn) hp₁.1) hp₁.2) hp₂.2
  exact (le_inf himp (le_inf hm₁ he₂)).trans bv_imp_elim

theorem funcBoundedFormula_congr {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    {Γ : B} {g₁ g₂ D₁ D₂ V₁ V₂ : bSet B}
    (hg : Γ ≤ g₁ =ᴮ g₂) (hD : Γ ≤ D₁ =ᴮ D₂) (hV : Γ ≤ V₁ =ᴮ V₂)
    (h : Γ ≤ funcBoundedFormula.eval ![g₁, D₁, V₁]) :
    Γ ≤ funcBoundedFormula.eval ![g₂, D₂, V₂] := by
  have h1 : Γ ≤ funcBoundedFormula.eval ![g₂, D₁, V₁] :=
    bv_rw' (bv_symm hg) (h_congr := funcBoundedFormula.eval_ext (fun z => ![z, D₁, V₁])
      (fun i => by fin_cases i <;> first | exact id_congr | exact const_congr _)) (H_new := h)
  have h2 : Γ ≤ funcBoundedFormula.eval ![g₂, D₂, V₁] :=
    bv_rw' (bv_symm hD) (h_congr := funcBoundedFormula.eval_ext (fun z => ![g₂, z, V₁])
      (fun i => by fin_cases i <;> first | exact id_congr | exact const_congr _)) (H_new := h1)
  exact bv_rw' (bv_symm hV) (h_congr := funcBoundedFormula.eval_ext (fun z => ![g₂, D₂, z])
    (fun i => by fin_cases i <;> first | exact id_congr | exact const_congr _)) (H_new := h2)

variable {I : Type u} {κ θ : Cardinal.{u}}
variable (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType]

theorem boundedAnon_indexEquiv_ordinal (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    (o : Ordinal.{u}) (pt : Erdos1172Shioya.UltrapowerStage.Point U a o.ToType) :
    let VA := Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
    (⊤ : VA) ≤ Preparation.boundedAnonName U a
        (fun i => check (PSet.ordinalMk (Erdos1172Shioya.UltrapowerStage.repr U a pt i).toOrd.val)) =ᴮ
      check (PSet.ordinalMk (indexEquiv U a o pt).toOrd.val) := by
  intro VA
  let S (i : I) := PSet.ordinalMk (Erdos1172Shioya.UltrapowerStage.repr U a pt i).toOrd.val
  have supp : Preparation.Supported U a S := ⟨pt.property.choose,
    fun t => PSet.ordinalMk ((pt.property.choose_spec.choose t).toOrd.val), EventuallyEq.rfl⟩
  let v : BoundedHull U θ a := ⟨Germ.map Erdos1172Shioya.UltrapowerStage.ordinalLabel pt.val, by
    obtain ⟨η, g, hg⟩ := pt.property
    exact ⟨η, Erdos1172Shioya.UltrapowerStage.ordinalLabel ∘ g,
      congrArg (Germ.map Erdos1172Shioya.UltrapowerStage.ordinalLabel) hg⟩⟩
  have hw : Germ.ofFun (fun i => ZFSet.mk (S i)) = v.val :=
    congrArg (Germ.map Erdos1172Shioya.UltrapowerStage.ordinalLabel)
      (Erdos1172Shioya.UltrapowerStage.repr_eq U a pt)
  have hv : boundedCollapse U θ a v = (indexEquiv U a o pt).toOrd.val.toZFSet :=
    (indexEquiv_label U a o pt).symm
  exact bv_trans (Preparation.boundedAnon_checked_family U a hk hf hn ht hκ v S supp hw)
    (check_bv_eq (PSet.equiv_iff_eq.mpr ((ZFSet.mk_out _).trans hv)))

theorem boundedAnon_supported_ordinal_lt (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    {γ : Ordinal.{u}} (o : I → Ordinal.{u}) (ho : Preparation.Supported U a o)
    (hlt : ∀ᶠ i in U, o i < γ) :
    ∃ β < ordinalImage U a γ,
      (⊤ : Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) ≤
        Preparation.boundedAnonName U a (fun i => check (PSet.ordinalMk (o i))) =ᴮ
          check (PSet.ordinalMk β) := by
  let F (i : I) := PSet.ordinalMk (o i)
  have hF : Preparation.Supported U a F := ho.map PSet.ordinalMk
  obtain ⟨η, f, hf_eq⟩ := ho
  let w : BoundedHull U θ a := ⟨Germ.ofFun (fun i => ZFSet.mk (F i)),
    ⟨η, fun S => ZFSet.mk (PSet.ordinalMk (f S)),
      Germ.coe_eq.mpr (hf_eq.mono fun _ hi => congrArg (fun x => ZFSet.mk (PSet.ordinalMk x)) hi)⟩⟩
  have hm : boundedMem U θ a w (boundedConst U θ a γ.toZFSet) := by
    change memRel U w.val (Germ.const γ.toZFSet)
    exact hlt.mono fun _ hi => Ordinal.toZFSet_mem_toZFSet_iff.mpr hi
  have hcol_mem : boundedCollapse U θ a w ∈ (ordinalImage U a γ).toZFSet := by
    rw [ordinalImage_code U a γ]
    exact (mem_boundedCollapse_iff U θ a _ _).mpr ⟨w, hm, rfl⟩
  obtain ⟨β, hβ_lt, hβ_eq⟩ := Ordinal.mem_toZFSet_iff.mp hcol_mem
  refine ⟨β, hβ_lt, ?_⟩
  exact bv_trans (Preparation.boundedAnon_checked_family U a hk hf hn ht hκ w F hF rfl)
    (check_bv_eq (PSet.equiv_iff_eq.mpr ((ZFSet.mk_out _).trans hβ_eq.symm)))

private theorem boundedAnon_prod_check_le (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible) (o₁ o₂ : Ordinal.{u}) :
    let VA := Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
    (⊤ : VA) ≤ Preparation.boundedAnonName U a
        (fun _ => check (PSet.pSet_prod (PSet.ordinalMk o₁) (PSet.ordinalMk o₂))) ⊆ᴮ
      check (PSet.pSet_prod (PSet.ordinalMk (ordinalImage U a o₁))
        (PSet.ordinalMk (ordinalImage U a o₂))) := by
  intro VA
  classical
  let A := anonymousAlgebra κ
  let P_src := PSet.pSet_prod (PSet.ordinalMk o₁) (PSet.ordinalMk o₂)
  let P_dst := PSet.pSet_prod (PSet.ordinalMk (ordinalImage U a o₁))
    (PSet.ordinalMk (ordinalImage U a o₂))
  rw [Preparation.boundedAnonName_unfold (κ := κ) U a (fun _ => check P_src), subset_unfold]
  refine le_iInf fun ch => deduction.mp ?_
  rw [top_inf_eq]
  let getIdx (x : bSet A) : Option P_src.Type :=
    if h : ∃ idx : P_src.Type, x = check (P_src.Func idx) then some h.choose else none
  let o_fst (i : I) : Ordinal.{u} :=
    match getIdx (Erdos1172BooleanUltrapower.child U (fun _ => check P_src) ch.val i) with
    | some idx => ordOfPSetIdx idx.1
    | none => 0
  let o_snd (i : I) : Ordinal.{u} :=
    match getIdx (Erdos1172BooleanUltrapower.child U (fun _ => check P_src) ch.val i) with
    | some idx => ordOfPSetIdx idx.2
    | none => 0
  by_cases ho₁ : o₁ = 0
  · subst ho₁
    have hemp : IsEmpty P_src.Type := ⟨fun idx => not_lt_of_ge zero_le (ordOfPSetIdx_lt idx.1)⟩
    have hw0 : value U (Erdos1172BooleanUltrapower.weight U (fun _ => check P_src) ch.val) = ⊥ := by
      apply le_bot_iff.mp
      rw [← value_bot U]
      apply (value_le_value_iff U).mpr
      filter_upwards [ch.val.large] with i hi
      exact (hemp.false (check_cast (ch.val.pick ⟨i, hi⟩))).elim
    exact hw0.le.trans bot_le
  · by_cases ho₂ : o₂ = 0
    · subst ho₂
      have hemp : IsEmpty P_src.Type := ⟨fun idx => not_lt_of_ge zero_le (ordOfPSetIdx_lt idx.2)⟩
      have hw0 : value U (Erdos1172BooleanUltrapower.weight U (fun _ => check P_src) ch.val) = ⊥ := by
        apply le_bot_iff.mp
        rw [← value_bot U]
        apply (value_le_value_iff U).mpr
        filter_upwards [ch.val.large] with i hi
        exact (hemp.false (check_cast (ch.val.pick ⟨i, hi⟩))).elim
      exact hw0.le.trans bot_le
    · have hget : ∀ᶠ i in U, ∃ idx : P_src.Type,
          Erdos1172BooleanUltrapower.child U (fun _ => check P_src) ch.val i = check (P_src.Func idx) ∧
          o_fst i = ordOfPSetIdx idx.1 ∧ o_snd i = ordOfPSetIdx idx.2 := by
        filter_upwards [ch.val.large] with i hi
        have hex : ∃ idx : P_src.Type,
            Erdos1172BooleanUltrapower.child U (fun _ => check P_src) ch.val i = check (P_src.Func idx) := by
          simp only [Erdos1172BooleanUltrapower.child, dif_pos hi]
          exact ⟨check_cast (ch.val.pick ⟨i, hi⟩), check_func⟩
        refine ⟨hex.choose, hex.choose_spec, ?_, ?_⟩ <;> simp only [o_fst, o_snd, getIdx, dif_pos hex]
      obtain ⟨β₁, hβ₁, heq₁⟩ := boundedAnon_supported_ordinal_lt U a hk hf hn ht hκ o_fst
        (ch.property.map fun x => match getIdx x with | some idx => ordOfPSetIdx idx.1 | none => 0)
        (hget.mono fun i ⟨idx, _, h1, _⟩ => h1 ▸ ordOfPSetIdx_lt idx.1)
      obtain ⟨β₂, hβ₂, heq₂⟩ := boundedAnon_supported_ordinal_lt U a hk hf hn ht hκ o_snd
        (ch.property.map fun x => match getIdx x with | some idx => ordOfPSetIdx idx.2 | none => 0)
        (hget.mono fun i ⟨idx, _, _, h2⟩ => h2 ▸ ordOfPSetIdx_lt idx.2)
      have hch_pair : (⊤ : VA) ≤ Preparation.boundedAnonName U a
          (Erdos1172BooleanUltrapower.child U (fun _ => check P_src) ch.val) =ᴮ
          pair (check (PSet.ordinalMk β₁)) (check (PSet.ordinalMk β₂)) := by
        let g_fst (i : I) : bSet A := check (PSet.ordinalMk (o_fst i))
        let g_snd (i : I) : bSet A := check (PSet.ordinalMk (o_snd i))
        have hs_gfst : Preparation.Supported U a g_fst :=
          (ch.property.map fun x => match getIdx x with | some idx => ordOfPSetIdx idx.1 | none => 0).map
            (fun o => (check (PSet.ordinalMk o) : bSet A))
        have hs_gsnd : Preparation.Supported U a g_snd :=
          (ch.property.map fun x => match getIdx x with | some idx => ordOfPSetIdx idx.2 | none => 0).map
            (fun o => (check (PSet.ordinalMk o) : bSet A))
        have h1 : (⊤ : VA) ≤ Preparation.boundedAnonName U a
            (Erdos1172BooleanUltrapower.child U (fun _ => check P_src) ch.val) =ᴮ
            Preparation.boundedAnonName U a (fun i => pair (g_fst i) (g_snd i)) := by
          rw [← Preparation.boundedAnonName_eq U a hk hf hn ht hκ
            (Erdos1172BooleanUltrapower.child U (fun _ => check P_src) ch.val)
            (fun i => pair (g_fst i) (g_snd i)) ch.property
            (hs_gfst.combine hs_gsnd pair)]
          rw [value_eq_of_eventuallyEq U (g := fun _ => ⊤) _, value_top]
          exact hget.mono fun i ⟨idx, hci, h1, h2⟩ => top_unique (by
            dsimp only [g_fst, g_snd]
            rw [hci, h1, h2]
            exact bv_trans (check_pset_pair (𝔹 := A))
              (pair_congr (check_bv_eq (ordOfPSetIdx_equiv idx.1))
                (check_bv_eq (ordOfPSetIdx_equiv idx.2))))
        exact bv_trans h1 (bv_trans
          (Preparation.boundedAnonName_pair U a hk hf hn ht hκ g_fst g_snd hs_gfst hs_gsnd)
          (pair_congr heq₁ heq₂))
      have hmem_dst : (⊤ : VA) ≤ pair (check (PSet.ordinalMk β₁)) (check (PSet.ordinalMk β₂)) ∈ᴮ check P_dst :=
        mem_congr bv_refl (bv_symm (check_pset_prod (𝔹 := VA)))
          (mem_prod (check_mem (PSet.mk_mem_mk_of_lt hβ₁)) (check_mem (PSet.mk_mem_mk_of_lt hβ₂)))
      exact le_top.trans (mem_congr (bv_symm hch_pair) bv_refl hmem_dst)

private theorem check_le_boundedAnon_prod (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible) (o₁ o₂ : Ordinal.{u}) :
    let VA := Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
    (⊤ : VA) ≤ check (PSet.pSet_prod (PSet.ordinalMk (ordinalImage U a o₁))
        (PSet.ordinalMk (ordinalImage U a o₂))) ⊆ᴮ
      Preparation.boundedAnonName U a
        (fun _ => check (PSet.pSet_prod (PSet.ordinalMk o₁) (PSet.ordinalMk o₂))) := by
  intro VA
  let A := anonymousAlgebra κ
  let P_src := PSet.pSet_prod (PSet.ordinalMk o₁) (PSet.ordinalMk o₂)
  let P_dst := PSet.pSet_prod (PSet.ordinalMk (ordinalImage U a o₁))
    (PSet.ordinalMk (ordinalImage U a o₂))
  rw [subset_unfold]
  refine le_iInf fun k => deduction.mp ?_
  rw [top_inf_eq, check_func]
  let idx := check_cast (𝔹 := VA) k
  let t₁ : (ordinalImage U a o₁).ToType := Ordinal.ToType.mk ⟨ordOfPSetIdx idx.1, ordOfPSetIdx_lt idx.1⟩
  let t₂ : (ordinalImage U a o₂).ToType := Ordinal.ToType.mk ⟨ordOfPSetIdx idx.2, ordOfPSetIdx_lt idx.2⟩
  let pt₁ := (indexEquiv U a o₁).symm t₁
  let pt₂ := (indexEquiv U a o₂).symm t₂
  let f₁ (i : I) := (Erdos1172Shioya.UltrapowerStage.repr U a pt₁ i).toOrd.val
  let f₂ (i : I) := (Erdos1172Shioya.UltrapowerStage.repr U a pt₂ i).toOrd.val
  let c₁ (i : I) : bSet A := check (PSet.ordinalMk (f₁ i))
  let c₂ (i : I) : bSet A := check (PSet.ordinalMk (f₂ i))
  have hs₁ : Preparation.Supported U a c₁ :=
    ⟨pt₁.property.choose, fun S => check (PSet.ordinalMk ((pt₁.property.choose_spec.choose S).toOrd.val)),
      EventuallyEq.rfl⟩
  have hs₂ : Preparation.Supported U a c₂ :=
    ⟨pt₂.property.choose, fun S => check (PSet.ordinalMk ((pt₂.property.choose_spec.choose S).toOrd.val)),
      EventuallyEq.rfl⟩
  have hmem_A : (⊤ : VA) ≤ Preparation.boundedAnonName U a
      (fun i => pair (c₁ i) (c₂ i)) ∈ᴮ
      Preparation.boundedAnonName U a (fun _ => check P_src) := by
    rw [← Preparation.boundedAnonName_mem U a hk hf hn ht hκ
      (fun i => pair (c₁ i) (c₂ i)) (fun _ => check P_src)
      (hs₁.combine hs₂ pair) (Preparation.Supported.const (check P_src)),
      value_eq_of_eventuallyEq U (g := fun _ => ⊤) _, value_top]
    exact Eventually.of_forall fun i => top_unique
      (mem_congr bv_refl (bv_symm (check_pset_prod (𝔹 := A)))
        (mem_prod (check_mem (PSet.mk_mem_mk_of_lt (toOrd_lt _)))
          (check_mem (PSet.mk_mem_mk_of_lt (toOrd_lt _)))))
  have ht₁_ord : (indexEquiv U a o₁ pt₁).toOrd.val = ordOfPSetIdx idx.1 := by
    rw [Equiv.apply_symm_apply]
    exact congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  have ht₂_ord : (indexEquiv U a o₂ pt₂).toOrd.val = ordOfPSetIdx idx.2 := by
    rw [Equiv.apply_symm_apply]
    exact congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  have hpair_eq : (⊤ : VA) ≤ Preparation.boundedAnonName U a
      (fun i => pair (c₁ i) (c₂ i)) =ᴮ
      check (P_dst.Func idx) := by
    refine bv_trans (Preparation.boundedAnonName_pair U a hk hf hn ht hκ c₁ c₂ hs₁ hs₂) ?_
    refine bv_trans (pair_congr (boundedAnon_indexEquiv_ordinal U a hk hf hn ht hκ o₁ pt₁)
      (boundedAnon_indexEquiv_ordinal U a hk hf hn ht hκ o₂ pt₂)) ?_
    rw [ht₁_ord, ht₂_ord]
    exact bv_trans (pair_congr (check_bv_eq (PSet.Equiv.symm (ordOfPSetIdx_equiv idx.1)))
      (check_bv_eq (PSet.Equiv.symm (ordOfPSetIdx_equiv idx.2))))
      (bv_symm (check_pset_pair (𝔹 := VA)))
  exact mem_congr hpair_eq bv_refl hmem_A

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
private theorem prod_ordinalCarrier_eq_check_prod {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (o₁ o₂ : Ordinal.{u}) :
    (⊤ : B) ≤ prod (ordinalCarrier o₁) (ordinalCarrier o₂) =ᴮ
      check (PSet.pSet_prod (PSet.ordinalMk o₁) (PSet.ordinalMk o₂)) :=
  bv_symm (check_pset_prod (x := PSet.ordinalMk o₁) (y := PSet.ordinalMk o₂))

private theorem boundedAnon_const_eq_of_top_eq {X Y : bSet (anonymousAlgebra κ)}
    (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    (hXY : (⊤ : anonymousAlgebra κ) ≤ X =ᴮ Y) :
    (⊤ : Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) ≤
      Preparation.boundedAnonName U a (fun _ => X) =ᴮ
        Preparation.boundedAnonName U a (fun _ => Y) := by
  rw [← Preparation.boundedAnonName_eq U a hk hf hn ht hκ
    (fun _ => X) (fun _ => Y) (Preparation.Supported.const X) (Preparation.Supported.const Y),
    value_eq_of_eventuallyEq U (g := fun _ => ⊤) (Eventually.of_forall fun _ => top_unique hXY),
    value_top]

theorem boundedAnon_prod_ordinalCarrier (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible) (o₁ o₂ : Ordinal.{u}) :
    let VA := Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
    (⊤ : VA) ≤ Preparation.boundedAnonName (κ := κ) U a
        (fun _ => prod (ordinalCarrier o₁) (ordinalCarrier o₂)) =ᴮ
      prod (ordinalCarrier (ordinalImage U a o₁)) (ordinalCarrier (ordinalImage U a o₂)) := by
  intro VA
  have hsrc_eq : (⊤ : VA) ≤ Preparation.boundedAnonName (κ := κ) U a
      (fun _ => prod (ordinalCarrier o₁) (ordinalCarrier o₂)) =ᴮ
      Preparation.boundedAnonName (κ := κ) U a
        (fun _ => check (PSet.pSet_prod (PSet.ordinalMk o₁) (PSet.ordinalMk o₂))) :=
    boundedAnon_const_eq_of_top_eq U a hk hf hn ht hκ (prod_ordinalCarrier_eq_check_prod o₁ o₂)
  have hdst_eq : (⊤ : VA) ≤
      check (PSet.pSet_prod (PSet.ordinalMk (ordinalImage U a o₁))
        (PSet.ordinalMk (ordinalImage U a o₂))) =ᴮ
      prod (ordinalCarrier (ordinalImage U a o₁)) (ordinalCarrier (ordinalImage U a o₂)) :=
    bv_symm (prod_ordinalCarrier_eq_check_prod (ordinalImage U a o₁) (ordinalImage U a o₂))
  exact bv_trans hsrc_eq (bv_trans
    (subset_ext (boundedAnon_prod_check_le U a hk hf hn ht hκ o₁ o₂)
      (check_le_boundedAnon_prod U a hk hf hn ht hκ o₁ o₂))
    hdst_eq)

end BoundedFuncAndProductLift

section CompressLiftedWitness
variable {I : Type u} {κ θ : Cardinal.{u}}
variable (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]

/-- Ground `PSet` of valid triples `((ξ, η), y)` (`y < ξ`) at stage `α`. -/
abbrev validTriplePSet (κ : Cardinal.{u}) (α : Ordinal.{u}) : PSet.{u} :=
  PSet.mk (GroundValidTriple κ α) (fun t => (levyTriplePSet κ α).Func t.val)

/-- Ground `PSet` of valid lifted triples `((ξ, η), y)` (`y < ξ`) at stage `α`. -/
abbrev validLiftedTriplePSet (θ : Cardinal.{u}) (α : Ordinal.{u}) : PSet.{u} :=
  PSet.mk (ValidLiftedTriple U a θ α) (fun t => (liftedTriplePSet U a θ α).Func t.val)

omit [CardinalInterFilter (U : Filter I) κ] in
theorem validLiftedTriplePSet_inj (θ : Cardinal.{u}) (α : Ordinal.{u})
    {t₁ t₂ : ValidLiftedTriple U a θ α} (hne : t₁ ≠ t₂) :
    ¬PSet.Equiv ((validLiftedTriplePSet U a θ α).Func t₁) ((validLiftedTriplePSet U a θ α).Func t₂) :=
  liftedTriplePSet_inj U a θ α (fun h => hne (Subtype.ext h))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem bot_of_ground_levyBoundPred_ge' {α : Ordinal.{u}}
    (idx : (levyTriplePSet κ α).Type) (hge : ordOfPSetIdx idx.1.1 ≤ ordOfPSetIdx idx.2) :
    levyBoundPred (ordinalCarrier κ.ord) (ordinalCarrier α)
      (check ((levyTriplePSet κ α).Func idx) : bSet (anonymousAlgebra κ)) ≤ ⊥ := by
  let A := anonymousAlgebra κ
  let P₀ : bSet A := pair
    (pair (check ((PSet.ordinalMk α).Func idx.1.1)) (check ((PSet.ordinalMk κ.ord).Func idx.1.2)))
    (check ((PSet.ordinalMk α).Func idx.2))
  have hp₀ : (⊤ : A) ≤ check ((levyTriplePSet κ α).Func idx) =ᴮ P₀ :=
    check_levyTriplePSet_func α idx
  change (⨆ ξ : bSet A, (ξ ∈ᴮ ordinalCarrier α) ⊓ _) ≤ ⊥
  refine iSup_le fun ξ => ?_
  change (ξ ∈ᴮ _) ⊓ (⨆ η : bSet A, (η ∈ᴮ ordinalCarrier κ.ord) ⊓ _) ≤ ⊥
  erw [inf_iSup_eq]
  refine iSup_le fun η => ?_
  change (ξ ∈ᴮ _) ⊓ ((η ∈ᴮ _) ⊓ (⨆ y : bSet A, (y ∈ᴮ ξ) ⊓ _)) ≤ ⊥
  erw [← inf_assoc, inf_iSup_eq]
  refine iSup_le fun y => ?_
  let F : A := ((ξ ∈ᴮ ordinalCarrier α) ⊓ (η ∈ᴮ ordinalCarrier κ.ord)) ⊓
    ((y ∈ᴮ ξ) ⊓ (check ((levyTriplePSet κ α).Func idx) =ᴮ pair (pair ξ η) y))
  have hp_eq : F ≤ P₀ =ᴮ pair (pair ξ η) y :=
    bv_trans (le_top.trans (bv_symm hp₀)) (inf_le_right.trans inf_le_right)
  have hξ_eq : F ≤ check ((PSet.ordinalMk α).Func idx.1.1) =ᴮ ξ :=
    (pair_eq_pair_iff.mp (pair_eq_pair_iff.mp hp_eq).1).1
  have hy_eq : F ≤ check ((PSet.ordinalMk α).Func idx.2) =ᴮ y := (pair_eq_pair_iff.mp hp_eq).2
  have hy_in : F ≤ check (PSet.ordinalMk (ordOfPSetIdx idx.2)) ∈ᴮ
      check (PSet.ordinalMk (ordOfPSetIdx idx.1.1)) :=
    mem_congr
      (bv_trans (bv_symm hy_eq) (check_bv_eq (ordOfPSetIdx_equiv idx.2)))
      (bv_trans (bv_symm hξ_eq) (check_bv_eq (ordOfPSetIdx_equiv idx.1.1)))
      (inf_le_right.trans inf_le_left)
  rw [mem_unfold] at hy_in
  refine hy_in.trans (iSup_le fun k => ?_)
  have hneqv : ¬PSet.Equiv (PSet.ordinalMk (ordOfPSetIdx idx.2))
      ((PSet.ordinalMk (ordOfPSetIdx idx.1.1)).Func (check_cast k)) := by
    intro he
    have heq := Ordinal.toZFSet_injective (ZFSet.sound
      (PSet.Equiv.trans he (ordOfPSetIdx_equiv (check_cast k))))
    exact (hge.trans_lt (heq ▸ ordOfPSetIdx_lt (check_cast k))).false
  rw [check_func, check_bval_top, top_inf_eq, check_bv_eq_bot_of_not_equiv hneqv]

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem internalLevyPoset_subset_validTriplePSet (α : Ordinal.{u}) :
    (⊤ : anonymousAlgebra κ) ≤ allIn (internalLevyPoset κ α) (fun g =>
      allIn g (fun x => x ∈ᴮ check (validTriplePSet κ α))) := by
  let A := anonymousAlgebra κ
  let P_α := levyTriplePSet κ α
  refine allIn_intro fun {Δ₁} _ g hg => allIn_intro fun {Δ₂} hΔ x hx => ?_
  have hg_sub : Δ₁ ≤ g ⊆ᴮ (check P_α : bSet A) :=
    subset_trans' (countableCollapse_mem.mp (mem_internalLevyCollapse.mp hg).1).1
      (bSet.subset_of_eq (le_top.trans (prod_ordinalCarrier_eq_check_levyTriplePSet (B := A) α)))
  have hg_bd : Δ₁ ≤ levyAllBounded (ordinalCarrier κ.ord) (ordinalCarrier α) g :=
    (mem_internalLevyCollapse.mp hg).2
  have hx_P : Δ₂ ≤ x ∈ᴮ (check P_α : bSet A) := mem_of_mem_subset (hΔ.trans hg_sub) hx
  rw [mem_unfold] at hx_P
  refine ((le_inf (le_inf hx (hΔ.trans hg_bd)) hx_P).trans_eq (inf_iSup_eq _ _)).trans
    (iSup_le fun k => ?_)
  let idx := check_cast (𝔹 := A) k
  let cP : bSet A := check P_α
  let E : A := (x ∈ᴮ g ⊓ levyAllBounded (ordinalCarrier κ.ord) (ordinalCarrier α) g) ⊓
    (cP.bval k ⊓ (x =ᴮ cP.func k))
  have hE_eq : E ≤ x =ᴮ check (P_α.Func idx) := by
    have hr : E ≤ x =ᴮ cP.func k := inf_le_right.trans inf_le_right
    exact (@check_func A _ P_α k) ▸ hr
  have hE_bd : E ≤ levyBoundPred (ordinalCarrier κ.ord) (ordinalCarrier α) (check (P_α.Func idx)) :=
    allIn_elim (inf_le_left.trans inf_le_right)
      (mem_congr hE_eq bv_refl (inf_le_left.trans inf_le_left))
  by_cases hvalid : ordOfPSetIdx idx.2 < ordOfPSetIdx idx.1.1
  · exact mem_congr (bv_symm hE_eq) bv_refl
      (check_mem (PSet.func_mem (validTriplePSet κ α) ⟨idx, hvalid⟩))
  · exact (hE_bd.trans (bot_of_ground_levyBoundPred_ge' idx (le_of_not_gt hvalid))).trans bot_le

omit [CardinalInterFilter (U : Filter I) κ] in
private theorem boundedAnon_validTriplePSet_subset (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible) (α : Ordinal.{u}) :
    let VA := Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
    (⊤ : VA) ≤ Preparation.boundedAnonName U a (fun _ => check (validTriplePSet κ α)) ⊆ᴮ
      check (validLiftedTriplePSet U a θ α) := by
  intro VA
  classical
  let A := anonymousAlgebra κ
  let V_src := validTriplePSet κ α
  rw [Preparation.boundedAnonName_unfold (κ := κ) U a (fun _ => check V_src), subset_unfold]
  refine le_iInf fun ch => deduction.mp ?_
  rw [top_inf_eq]
  by_cases hα0 : α = 0
  · subst hα0
    have hemp : IsEmpty (GroundValidTriple κ 0) := ⟨fun t => not_lt_of_ge zero_le (ordOfPSetIdx_lt t.val.1.1)⟩
    have hw0 : value U (Erdos1172BooleanUltrapower.weight U (fun _ => check V_src) ch.val) = ⊥ := by
      apply le_bot_iff.mp
      rw [← value_bot U]
      apply (value_le_value_iff U).mpr
      filter_upwards [ch.val.large] with i hi
      exact (hemp.false (check_cast (ch.val.pick ⟨i, hi⟩))).elim
    exact hw0.le.trans bot_le
  · let getT (x : bSet A) : Option (GroundValidTriple κ α) :=
      if h : ∃ t : GroundValidTriple κ α, x = check (V_src.Func t) then some h.choose else none
    let o_ξ (i : I) : Ordinal.{u} :=
      match getT (Erdos1172BooleanUltrapower.child U (fun _ => check V_src) ch.val i) with
      | some t => ordOfPSetIdx t.val.1.1
      | none => 0
    let o_η (i : I) : Ordinal.{u} :=
      match getT (Erdos1172BooleanUltrapower.child U (fun _ => check V_src) ch.val i) with
      | some t => ordOfPSetIdx t.val.1.2
      | none => 0
    let o_y (i : I) : Ordinal.{u} :=
      match getT (Erdos1172BooleanUltrapower.child U (fun _ => check V_src) ch.val i) with
      | some t => ordOfPSetIdx t.val.2
      | none => 0
    have hget : ∀ᶠ i in U, ∃ t : GroundValidTriple κ α,
        Erdos1172BooleanUltrapower.child U (fun _ => check V_src) ch.val i = check (V_src.Func t) ∧
        o_ξ i = ordOfPSetIdx t.val.1.1 ∧ o_η i = ordOfPSetIdx t.val.1.2 ∧
        o_y i = ordOfPSetIdx t.val.2 ∧ o_y i < o_ξ i := by
      filter_upwards [ch.val.large] with i hi
      have hex : ∃ t : GroundValidTriple κ α,
          Erdos1172BooleanUltrapower.child U (fun _ => check V_src) ch.val i = check (V_src.Func t) := by
        simp only [Erdos1172BooleanUltrapower.child, dif_pos hi]
        exact ⟨check_cast (ch.val.pick ⟨i, hi⟩), check_func⟩
      refine ⟨hex.choose, hex.choose_spec, ?_, ?_, ?_, ?_⟩
      · simp only [o_ξ, getT, dif_pos hex]
      · simp only [o_η, getT, dif_pos hex]
      · simp only [o_y, getT, dif_pos hex]
      · simp only [o_y, o_ξ, getT, dif_pos hex]
        exact hex.choose.property
    have hs_ξ : Preparation.Supported U a o_ξ :=
      ch.property.map fun x => match getT x with | some t => ordOfPSetIdx t.val.1.1 | none => 0
    have hs_η : Preparation.Supported U a o_η :=
      ch.property.map fun x => match getT x with | some t => ordOfPSetIdx t.val.1.2 | none => 0
    have hs_y : Preparation.Supported U a o_y :=
      ch.property.map fun x => match getT x with | some t => ordOfPSetIdx t.val.2 | none => 0
    let c_ξ (i : I) : bSet A := check (PSet.ordinalMk (o_ξ i))
    let c_η (i : I) : bSet A := check (PSet.ordinalMk (o_η i))
    let c_y (i : I) : bSet A := check (PSet.ordinalMk (o_y i))
    have hc_ξ : Preparation.Supported U a c_ξ := hs_ξ.map fun o => (check (PSet.ordinalMk o) : bSet A)
    have hc_η : Preparation.Supported U a c_η := hs_η.map fun o => (check (PSet.ordinalMk o) : bSet A)
    have hc_y : Preparation.Supported U a c_y := hs_y.map fun o => (check (PSet.ordinalMk o) : bSet A)
    obtain ⟨β_ξ, hβ_ξ, heq_ξ⟩ := boundedAnon_supported_ordinal_lt U a hk hf hn ht hκ o_ξ hs_ξ
      (hget.mono fun _ ⟨t, _, h1, _, _, _⟩ => h1 ▸ ordOfPSetIdx_lt t.val.1.1)
    obtain ⟨β_η, hβ_η_raw, heq_η⟩ := boundedAnon_supported_ordinal_lt U a hk hf hn ht hκ o_η hs_η
      (hget.mono fun _ ⟨t, _, _, h2, _, _⟩ => h2 ▸ ordOfPSetIdx_lt t.val.1.2)
    have hord_θ : ordinalImage U a κ.ord = θ.ord :=
      Ordinal.toZFSet_injective ((ordinalImage_code U a κ.ord).trans
        (boundedDiagonal_critical_image U κ θ a hf hn ht))
    have hβ_η : β_η < θ.ord := hord_θ ▸ hβ_η_raw
    obtain ⟨β_y, hβ_y, heq_y⟩ := boundedAnon_supported_ordinal_lt U a hk hf hn ht hκ o_y hs_y
      (hget.mono fun _ ⟨t, _, _, _, h3, _⟩ => h3 ▸ ordOfPSetIdx_lt t.val.2)
    have hβ_lt : β_y < β_ξ := by
      have hmem_VA : (⊤ : VA) ≤ (check (PSet.ordinalMk β_y) : bSet VA) ∈ᴮ check (PSet.ordinalMk β_ξ) := by
        refine mem_congr heq_y heq_ξ ?_
        rw [← Preparation.boundedAnonName_mem U a hk hf hn ht hκ c_y c_ξ hc_y hc_ξ,
          value_eq_of_eventuallyEq U (g := fun _ => ⊤) _, value_top]
        exact hget.mono fun _ ⟨_, _, _, _, _, hlt⟩ =>
          top_unique (check_mem (PSet.mk_mem_mk_of_lt hlt))
      by_contra hnot
      rw [mem_unfold] at hmem_VA
      have hbot : (⊤ : VA) ≤ ⊥ := hmem_VA.trans (iSup_le fun k => by
        have hneqv : ¬PSet.Equiv (PSet.ordinalMk β_y) ((PSet.ordinalMk β_ξ).Func (check_cast k)) := by
          intro he
          have heq := Ordinal.toZFSet_injective (ZFSet.sound
            (PSet.Equiv.trans he (ordOfPSetIdx_equiv (check_cast k))))
          exact ((le_of_not_gt hnot).trans_lt (heq ▸ ordOfPSetIdx_lt (check_cast k))).false
        rw [check_func, check_bval_top, top_inf_eq, check_bv_eq_bot_of_not_equiv hneqv])
      exact top_ne_bot (le_bot_iff.mp hbot)
    let i_ξ := (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt hβ_ξ)).choose
    let i_η := (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt hβ_η)).choose
    let i_y := (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt hβ_y)).choose
    have hi_ξ : PSet.Equiv (PSet.ordinalMk β_ξ) ((PSet.ordinalMk (ordinalImage U a α)).Func i_ξ) :=
      (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt hβ_ξ)).choose_spec
    have hi_η : PSet.Equiv (PSet.ordinalMk β_η) ((PSet.ordinalMk θ.ord).Func i_η) :=
      (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt hβ_η)).choose_spec
    have hi_y : PSet.Equiv (PSet.ordinalMk β_y) ((PSet.ordinalMk (ordinalImage U a α)).Func i_y) :=
      (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt hβ_y)).choose_spec
    have ho_iξ : ordOfPSetIdx i_ξ = β_ξ :=
      Ordinal.toZFSet_injective (ZFSet.sound (PSet.Equiv.trans (PSet.Equiv.symm (ordOfPSetIdx_equiv i_ξ))
        (PSet.Equiv.symm hi_ξ)))
    have ho_iy : ordOfPSetIdx i_y = β_y :=
      Ordinal.toZFSet_injective (ZFSet.sound (PSet.Equiv.trans (PSet.Equiv.symm (ordOfPSetIdx_equiv i_y))
        (PSet.Equiv.symm hi_y)))
    let t_dst : ValidLiftedTriple U a θ α := ⟨((i_ξ, i_η), i_y), by rw [ho_iy, ho_iξ]; exact hβ_lt⟩
    have hch_eq : (⊤ : VA) ≤ Preparation.boundedAnonName U a
        (Erdos1172BooleanUltrapower.child U (fun _ => check V_src) ch.val) =ᴮ
        check ((validLiftedTriplePSet U a θ α).Func t_dst) := by
      have h1 : (⊤ : VA) ≤ Preparation.boundedAnonName U a
          (Erdos1172BooleanUltrapower.child U (fun _ => check V_src) ch.val) =ᴮ
          Preparation.boundedAnonName U a (fun i => pair (pair (c_ξ i) (c_η i)) (c_y i)) := by
        rw [← Preparation.boundedAnonName_eq U a hk hf hn ht hκ
          (Erdos1172BooleanUltrapower.child U (fun _ => check V_src) ch.val)
          (fun i => pair (pair (c_ξ i) (c_η i)) (c_y i))
          ch.property ((hc_ξ.combine hc_η pair).combine hc_y pair),
          value_eq_of_eventuallyEq U (g := fun _ => ⊤) _, value_top]
        exact hget.mono fun _ ⟨t, hci, h1, h2, h3, _⟩ => top_unique (by
          dsimp only [c_ξ, c_η, c_y]
          rw [hci, h1, h2, h3]
          exact bv_trans (check_levyTriplePSet_func α t.val)
            (pair_congr (pair_congr (check_bv_eq (ordOfPSetIdx_equiv t.val.1.1))
              (check_bv_eq (ordOfPSetIdx_equiv t.val.1.2)))
              (check_bv_eq (ordOfPSetIdx_equiv t.val.2))))
      have h2 : (⊤ : VA) ≤ Preparation.boundedAnonName U a (fun i => pair (pair (c_ξ i) (c_η i)) (c_y i)) =ᴮ
          pair (pair (check (PSet.ordinalMk β_ξ)) (check (PSet.ordinalMk β_η)))
            (check (PSet.ordinalMk β_y)) := by
        refine bv_trans (Preparation.boundedAnonName_pair U a hk hf hn ht hκ
          (fun i => pair (c_ξ i) (c_η i)) c_y (hc_ξ.combine hc_η pair) hc_y) ?_
        refine pair_congr ?_ heq_y
        exact bv_trans (Preparation.boundedAnonName_pair U a hk hf hn ht hκ c_ξ c_η hc_ξ hc_η)
          (pair_congr heq_ξ heq_η)
      exact bv_trans h1 (bv_trans h2
        (bv_trans (pair_congr (pair_congr (check_bv_eq hi_ξ) (check_bv_eq hi_η)) (check_bv_eq hi_y))
          (bv_symm (check_liftedTriplePSet_func U a θ α t_dst.val))))
    exact le_top.trans (mem_congr (bv_symm hch_eq) bv_refl
      (check_mem (PSet.func_mem (validLiftedTriplePSet U a θ α) t_dst)))

def subFormula : InterpretedMaster.Formula Bool :=
  .allIn false (.allIn none (.mem none (some (some true))))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem subFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (V P : bSet B) :
    subFormula.eval (fun bl => if bl then V else P) =
      allIn P (fun g => allIn g (fun x => x ∈ᴮ V)) :=
  rfl

def posetFuncFormula : InterpretedMaster.Formula (Fin 3) :=
  .allIn 0 (.allIn (some 1) (.allIn (some (some 2)) (.allIn (some (some (some 2)))
    (.imp (.both (.edge (some (some (some none))) (some (some none)) (some none))
                 (.edge (some (some (some none))) (some (some none)) none))
          (.eq (some none) none)))))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem posetFuncFormula_eval {B : Type u} [NontrivialCompleteBooleanAlgebra B]
    (P D L : bSet B) :
    posetFuncFormula.eval ![P, D, L] = allIn P (fun g => funcBoundedFormula.eval ![g, D, L]) :=
  rfl

omit [CardinalInterFilter (U : Filter I) κ] in
private theorem lifted_poset_mem_props {W₁ : Type u} [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (α : Ordinal.{u}) {c_p : W₁} {z : bSet W₁}
    (hz : c_p ≤ z ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α))) :
    c_p ≤ z ⊆ᴮ check (validLiftedTriplePSet U a θ α) ∧
    c_p ≤ is_func z ∧
    c_p ≤ injects_into z omega := by
  classical
  let A := anonymousAlgebra κ
  let P_A := internalLevyPoset κ α
  let P_W := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => P_A))
  let V_dst := validLiftedTriplePSet U a θ α
  have hz_sub : c_p ≤ z ⊆ᴮ check V_dst := by
    let V_A : bSet A := check (validTriplePSet κ α)
    let V_W : bSet W₁ := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => V_A))
    let env_sub : Bool → bSet A := fun bl => if bl then V_A else P_A
    have hsub_W := transfer_const_formula U a hk hf hn ht hκ j₀ subFormula env_sub
      (internalLevyPoset_subset_validTriplePSet α)
    have henv_W : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun _ => env_sub v))) =
        (fun bl => if bl then V_W else P_W) := by
      funext bl; cases bl <;> rfl
    rw [henv_W, subFormula_eval] at hsub_W
    simp_rw [← subset_iff_allIn_mem] at hsub_W
    have hz_in_lifted : c_p ≤ z ⊆ᴮ V_W :=
      allIn_elim (f := fun g => g ⊆ᴮ V_W) (le_top.trans hsub_W) hz
    have hlifted_le : (⊤ : W₁) ≤ V_W ⊆ᴮ check V_dst := by
      have hm := OrderHomClass.mono j₀ (boundedAnon_validTriplePSet_subset U a hk hf hn ht hκ α)
      rwa [TopHomClass.map_top, map_subset, map_check] at hm
    exact subset_trans' hz_in_lifted (le_top.trans hlifted_le)
  have hz_func : c_p ≤ is_func z := by
    let D_A : bSet A := prod (ordinalCarrier α) (ordinalCarrier κ.ord)
    let L_A : bSet A := ordinalCarrier α
    let D_W : bSet W₁ := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => D_A))
    let L_W : bSet W₁ := mapNames j₀ (Preparation.boundedAnonName U a (fun _ => L_A))
    have hfn_A : (⊤ : A) ≤ posetFuncFormula.eval ![P_A, D_A, L_A] := by
      rw [posetFuncFormula_eval]
      refine allIn_intro fun _ g hg => is_func_le_funcBoundedFormula ?_
      exact (countableCollapse_mem.mp (mem_internalLevyCollapse.mp hg).1).2.1
    have hfn_W := transfer_const_formula U a hk hf hn ht hκ j₀ posetFuncFormula ![P_A, D_A, L_A] hfn_A
    have henv_fn : (fun v => mapNames j₀ (Preparation.boundedAnonName U a (fun _ => (![P_A, D_A, L_A] : Fin 3 → bSet A) v))) =
        ![P_W, D_W, L_W] := by
      funext i; fin_cases i <;> rfl
    rw [henv_fn, posetFuncFormula_eval] at hfn_W
    have hz_fn_lifted : c_p ≤ funcBoundedFormula.eval ![z, D_W, L_W] :=
      allIn_elim (le_top.trans hfn_W) hz
    have hord_θ : ordinalImage U a κ.ord = θ.ord :=
      Ordinal.toZFSet_injective ((ordinalImage_code U a κ.ord).trans
        (boundedDiagonal_critical_image U κ θ a hf hn ht))
    have hD_eq : (⊤ : W₁) ≤ D_W =ᴮ prod (ordinalCarrier (ordinalImage U a α)) (ordinalCarrier θ.ord) := by
      have hm := OrderHomClass.mono j₀ (boundedAnon_prod_ordinalCarrier U a hk hf hn ht hκ α κ.ord)
      rw [hord_θ, TopHomClass.map_top, map_bv_eq, ErdosNameTransport.map_prod] at hm
      simpa only [D_W, D_A, ordinalCarrier, map_check] using hm
    have hL_eq : (⊤ : W₁) ≤ L_W =ᴮ ordinalCarrier (ordinalImage U a α) := by
      have hm := OrderHomClass.mono j₀ (Preparation.boundedAnon_ordinal U a hk hf hn ht hκ α)
      rwa [TopHomClass.map_top, map_bv_eq, map_check] at hm
    have hz_sub_prod : c_p ≤ z ⊆ᴮ prod
        (prod (ordinalCarrier (ordinalImage U a α)) (ordinalCarrier θ.ord))
        (ordinalCarrier (ordinalImage U a α)) := by
      refine subset_trans' hz_sub ?_
      rw [subset_unfold]
      refine le_iInf fun k => deduction.mp ?_
      let t := check_cast k
      rw [check_func]
      exact mem_congr (bv_symm (check_liftedTriplePSet_func U a θ α t.val)) bv_refl
        (mem_prod (mem_prod (check_mem (PSet.func_mem _ t.val.1.1))
          (check_mem (PSet.func_mem _ t.val.1.2)))
          (check_mem (PSet.func_mem _ t.val.2)))
    exact is_func_of_subset_prod_and_funcBoundedFormula hz_sub_prod
      (funcBoundedFormula_congr bv_refl (le_top.trans hD_eq) (le_top.trans hL_eq) hz_fn_lifted)
  have hz_cnt : c_p ≤ injects_into z omega := by
    have hP_unfold : P_W = .mk (Preparation.BoundedAnonChildren U a (fun _ => P_A))
        (fun ch => mapNames j₀ (Preparation.boundedAnonName U a
          (Erdos1172BooleanUltrapower.child U (fun _ => P_A) ch.val)))
        (fun ch => j₀ (value U (Erdos1172BooleanUltrapower.weight U (fun _ => P_A) ch.val))) := by
      dsimp only [P_W]
      rw [Preparation.boundedAnonName_unfold (κ := κ) U a (fun _ => P_A), mapNames_mk]
    have hz_unfold : c_p ≤ ⨆ ch : Preparation.BoundedAnonChildren U a (fun _ => P_A),
        j₀ (value U (Erdos1172BooleanUltrapower.weight U (fun _ => P_A) ch.val)) ⊓
          (z =ᴮ mapNames j₀ (Preparation.boundedAnonName U a
            (Erdos1172BooleanUltrapower.child U (fun _ => P_A) ch.val))) := by
      have hm : c_p ≤ z ∈ᴮ P_W := hz
      rw [hP_unfold, mem_unfold] at hm
      exact hm
    refine hz_unfold.trans (iSup_le fun ch => ?_)
    let g_ch := Erdos1172BooleanUltrapower.child U (fun _ => P_A) ch.val
    obtain ⟨ν_ch, G_ch, hG_ch⟩ := ch.property
    have hcov_S (S : Set θ.ord.ToType) :
        ∃ x_S : ULift.{u} ℕ → bSet A, ∀ w : bSet A,
          ((G_ch S ∈ᴮ P_A) ⊓ (w ∈ᴮ G_ch S)) ≤ ⨆ n : ULift.{u} ℕ, (x_S n ∈ᴮ G_ch S) ⊓ (w =ᴮ x_S n) :=
      exists_countable_member_cover (G_ch S) (G_ch S ∈ᴮ P_A)
        (countableCollapse_mem.mp (mem_internalLevyCollapse.mp le_rfl).1).2.2
    choose x_fn hx_fn using hcov_S
    let X_seq (n : ℕ) (i : I) : bSet A := x_fn (boundedFiber θ a ν_ch i) ⟨n⟩
    have hX_supp (n : ℕ) : Preparation.Supported U a (X_seq n) :=
      ⟨ν_ch, fun S => x_fn S ⟨n⟩, EventuallyEq.rfl⟩
    let fam_W : bSet W₁ := ErdosNameSequence.family
      (fun n => mapNames j₀ (Preparation.boundedAnonName U a (X_seq n)))
    have hVA_sub : value U (Erdos1172BooleanUltrapower.weight U (fun _ => P_A) ch.val) ≤
        Preparation.boundedAnonName U a g_ch ⊆ᴮ
          ErdosNameSequence.family (fun n => Preparation.boundedAnonName U a (X_seq n)) := by
      rw [Preparation.boundedAnonName_unfold (κ := κ) U a g_ch, subset_unfold]
      refine le_iInf fun sub_ch => deduction.mp ?_
      have hcard_nat : #(ULift.{u} ℕ) < Cardinal.aleph 1 := by simp
      have hstep1 : value U (Erdos1172BooleanUltrapower.weight U (fun _ => P_A) ch.val) ⊓
          value U (Erdos1172BooleanUltrapower.weight U g_ch sub_ch.val) ≤
          value U (fun i => ⨆ n : ULift.{u} ℕ,
            Erdos1172BooleanUltrapower.child U g_ch sub_ch.val i =ᴮ X_seq n.down i) := by
        rw [← value_inf]
        apply (value_le_value_iff U).mpr
        filter_upwards [ch.val.large, sub_ch.val.large, hG_ch] with i hi₁ hi₂ hgi
        have hw1 : Erdos1172BooleanUltrapower.weight U (fun _ => P_A) ch.val i ≤ g_ch i ∈ᴮ P_A := by
          simpa only [Erdos1172BooleanUltrapower.weight, selected, g_ch,
            Erdos1172BooleanUltrapower.child, dif_pos hi₁] using mem_mk' P_A (ch.val.pick ⟨i, hi₁⟩)
        have hw2 : Erdos1172BooleanUltrapower.weight U g_ch sub_ch.val i ≤
            Erdos1172BooleanUltrapower.child U g_ch sub_ch.val i ∈ᴮ g_ch i := by
          simpa only [Erdos1172BooleanUltrapower.weight, selected,
            Erdos1172BooleanUltrapower.child, dif_pos hi₂] using mem_mk' (g_ch i) (sub_ch.val.pick ⟨i, hi₂⟩)
        have hxi := hx_fn (boundedFiber θ a ν_ch i) (Erdos1172BooleanUltrapower.child U g_ch sub_ch.val i)
        change G_ch (boundedFiber θ a ν_ch i) = g_ch i at hgi
        rw [hgi] at hxi
        exact (inf_le_inf hw1 hw2).trans (hxi.trans (iSup_mono fun n => inf_le_right))
      rw [value_small_iSup U (Cardinal.aleph 1) hcard_nat] at hstep1
      refine hstep1.trans (iSup_le fun n => ?_)
      rw [Preparation.boundedAnonName_eq U a hk hf hn ht hκ
        (Erdos1172BooleanUltrapower.child U g_ch sub_ch.val) (X_seq n.down) sub_ch.property (hX_supp n.down)]
      exact mem_congr (bv_symm le_rfl) bv_refl
        (ErdosNameSequence.term_mem_family (fun m => Preparation.boundedAnonName U a (X_seq m)) n.down)
    have hW_sub : j₀ (value U (Erdos1172BooleanUltrapower.weight U (fun _ => P_A) ch.val)) ≤
        mapNames j₀ (Preparation.boundedAnonName U a g_ch) ⊆ᴮ fam_W := by
      have hm := OrderHomClass.mono j₀ hVA_sub
      rw [map_subset] at hm
      have hfam_eq : mapNames j₀ (ErdosNameSequence.family (fun n => Preparation.boundedAnonName U a (X_seq n))) =
          fam_W := by
        dsimp only [ErdosNameSequence.family, fam_W]
        rw [mapNames_mk]
        congr 1
        funext n
        exact TopHomClass.map_top j₀
      rwa [hfam_eq] at hm
    have hg_cnt : j₀ (value U (Erdos1172BooleanUltrapower.weight U (fun _ => P_A) ch.val)) ≤
        injects_into (mapNames j₀ (Preparation.boundedAnonName U a g_ch)) omega :=
      injects_into_trans (injects_into_of_subset hW_sub) (ErdosNameSequence.family_countable _)
    exact bv_rw' (ϕ := fun X => injects_into X omega) inf_le_right
      (h_congr := B_ext_injects_into_left) (H_new := inf_le_left.trans hg_cnt)
  exact ⟨hz_sub, hz_func, hz_cnt⟩

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem mapNames_is_func_le_hom {R W₁ : Type u}
    [NontrivialCompleteBooleanAlgebra R] [NontrivialCompleteBooleanAlgebra W₁]
    (j_R : CompleteLatticeHom R W₁) {c : W₁} {G D V : bSet R}
    (hsub : (⊤ : R) ≤ G ⊆ᴮ prod D V)
    (hfn : c ≤ is_func (mapNames j_R G)) :
    c ≤ j_R (is_func G) := by
  have h2 := is_func_le_funcBoundedFormula (D := mapNames j_R D) (V := mapNames j_R V) hfn
  have h3 : j_R (funcBoundedFormula.eval ![G, D, V]) =
      funcBoundedFormula.eval ![mapNames j_R G, mapNames j_R D, mapNames j_R V] := by
    rw [funcBoundedFormula.map_eval j_R]
    exact congrArg funcBoundedFormula.eval (funext fun i => by fin_cases i <;> rfl)
  rw [← h3] at h2
  exact h2.trans (OrderHomClass.mono j_R
    (is_func_of_subset_prod_and_funcBoundedFormula (le_top.trans hsub) le_rfl))

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem cone_read_piece_eq {R W₁ : Type u}
    [CompleteBooleanAlgebra R] [CompleteBooleanAlgebra W₁]
    {T : Type u}
    (j_R : CompleteLatticeHom R W₁)
    (c_p' : W₁) (w : T → W₁)
    (r_some : T → R) (r_none : R)
    (hdisj : ∀ {t₁ t₂ : T}, t₁ ≠ t₂ → w t₁ ⊓ w t₂ = ⊥)
    (hdec : (⊤ : R) ≤ (⨆ t : T, r_some t) ⊔ r_none)
    (hle_some : ∀ t : T, c_p' ⊓ j_R (r_some t) ≤ w t)
    (hle_none : ∀ t : T, (c_p' ⊓ w t) ⊓ j_R r_none ≤ ⊥)
    (t : T) :
    c_p' ⊓ w t = c_p' ⊓ j_R (r_some t) := by
  classical
  apply le_antisymm
  · have htop_dec : c_p' ≤ (⨆ t' : T, j_R (r_some t')) ⊔ j_R r_none := by
      have hm := OrderHomClass.mono j_R hdec
      rw [TopHomClass.map_top, completeHom_sup, _root_.map_iSup] at hm
      exact le_top.trans hm
    have h1 : c_p' ⊓ w t ≤
        ((c_p' ⊓ w t) ⊓ ⨆ t' : T, j_R (r_some t')) ⊔ ((c_p' ⊓ w t) ⊓ j_R r_none) := by
      calc
        c_p' ⊓ w t ≤ (c_p' ⊓ w t) ⊓ ((⨆ t' : T, j_R (r_some t')) ⊔ j_R r_none) :=
          le_inf le_rfl (inf_le_left.trans htop_dec)
        _ = _ := inf_sup_left _ _ _
    refine h1.trans (sup_le ?_ ((hle_none t).trans bot_le))
    rw [inf_iSup_eq]
    refine iSup_le fun t' => ?_
    by_cases htt' : t = t'
    · subst htt'
      exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · have hbot : (c_p' ⊓ w t) ⊓ j_R (r_some t') ≤ w t ⊓ w t' :=
        le_inf (inf_le_left.trans inf_le_right)
          ((inf_le_inf_right (j_R (r_some t')) inf_le_left).trans (hle_some t'))
      exact (hbot.trans_eq (hdisj htt')).trans bot_le
  · exact le_inf inf_le_left (hle_some t)

omit [CardinalInterFilter (U : Filter I) κ] in
/-- Abstract compression of a lifted stage-`α` Lévy witness `z : bSet (LocalizedSourceCohen R m₀ hm₀)`
into a `SmallGroundLevyGraph U a θ α R` on a refined first-stage Cohen condition `p' ⊇ᴮ p`. -/
theorem compress_lifted_witness_to_R_gen
    {R : Type u} [NontrivialCompleteBooleanAlgebra R]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (cc : StrictCC R θ)
    {m₀ p : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : R) ≤ m₀ ⊆ᴮ p)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))
      (LocalizedSourceCohen R m₀ hm₀))
    (α : Ordinal.{u})
    (z : bSet (LocalizedSourceCohen R m₀ hm₀))
    (hz : coneInMaster hm₀ hp hsub ≤
      z ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α))) :
    ∃ (p' : bSet R) (hp' : (⊤ : R) ≤ ErdosCohen.condition omegaOne p')
      (hsub_p' : (⊤ : R) ≤ p ⊆ᴮ p')
      (G' : SmallGroundLevyGraph U a θ α R),
      coneInMaster hm₀ hp' (subset_trans' hsub hsub_p') ≤
        z =ᴮ mapNames (localizedFirstStageHom hm₀) G'.toBSet := by
  classical
  let W₁ := LocalizedSourceCohen R m₀ hm₀
  let j_R := localizedFirstStageHom hm₀
  let c_p := coneInMaster hm₀ hp hsub
  let V_dst := validLiftedTriplePSet U a θ α
  obtain ⟨hz_sub, hz_func, hz_cnt⟩ := lifted_poset_mem_props U a hk hκ hf hn ht j₀ α hz
  -- Step 4: Countable cover of `z` in `W₁`, fused decision in `Add(ω₁^R, 1)`, and `< θ` antichain support.
  obtain ⟨x_z, hx_z⟩ := exists_countable_member_cover z c_p hz_cnt
  let w_piece (n : ℕ) (t : ValidLiftedTriple U a θ α) : W₁ :=
    c_p ⊓ ((x_z ⟨n⟩ ∈ᴮ z) ⊓ (check (V_dst.Func t) =ᴮ x_z ⟨n⟩))
  have hw_disj (n : ℕ) {t₁ t₂ : ValidLiftedTriple U a θ α} (hne : t₁ ≠ t₂) :
      w_piece n t₁ ⊓ w_piece n t₂ = ⊥ := by
    apply le_bot_iff.mp
    have heq1 : w_piece n t₁ ⊓ w_piece n t₂ ≤ check (V_dst.Func t₁) =ᴮ x_z ⟨n⟩ :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    have heq2 : w_piece n t₁ ⊓ w_piece n t₂ ≤ check (V_dst.Func t₂) =ᴮ x_z ⟨n⟩ :=
      inf_le_right.trans (inf_le_right.trans inf_le_right)
    exact (bv_trans heq1 (bv_symm heq2)).trans_eq
      (check_bv_eq_bot_of_not_equiv (validLiftedTriplePSet_inj U a θ α hne))
  have hw_join (t : ValidLiftedTriple U a θ α) :
      c_p ⊓ (check (V_dst.Func t) ∈ᴮ z) = ⨆ n : ℕ, w_piece n t := by
    apply le_antisymm
    · calc
        c_p ⊓ (check (V_dst.Func t) ∈ᴮ z)
          = c_p ⊓ (c_p ⊓ (check (V_dst.Func t) ∈ᴮ z)) := by rw [← inf_assoc, inf_idem]
        _ ≤ c_p ⊓ ⨆ n : ULift.{u} ℕ, (x_z n ∈ᴮ z) ⊓ (check (V_dst.Func t) =ᴮ x_z n) :=
          inf_le_inf_left c_p (hx_z (check (V_dst.Func t)))
        _ = ⨆ n : ULift.{u} ℕ, w_piece n.down t := inf_iSup_eq c_p _
        _ ≤ ⨆ n : ℕ, w_piece n t := iSup_le fun n => le_iSup (fun m : ℕ => w_piece m t) n.down
    · refine iSup_le fun n => le_inf inf_le_left ?_
      exact mem_congr (bv_symm (inf_le_right.trans inf_le_right)) bv_refl
        (inf_le_right.trans inf_le_left)
  let u_part (n : ℕ) : Option (ValidLiftedTriple U a θ α) → Erdos1172CohenIteration.omegaOneAlgebra R
    | some t => (w_piece n t).val
    | none => (⨆ t : ValidLiftedTriple U a θ α, (w_piece n t).val)ᶜ
  have hu_cov (n : ℕ) : (⊤ : Erdos1172CohenIteration.omegaOneAlgebra R) ≤
      ⨆ s : Option (ValidLiftedTriple U a θ α), u_part n s := by
    rw [← sup_compl_eq_top (x := ⨆ t : ValidLiftedTriple U a θ α, (w_piece n t).val)]
    exact sup_le
      (iSup_le fun t => le_iSup (u_part n) (some t))
      (le_iSup (u_part n) none)
  obtain ⟨p', hp', hsub_p', hdec⟩ := exists_countable_cover_deciding_extension
    omegaOne_property hp (fun _ => Option (ValidLiftedTriple U a θ α)) u_part hu_cov
  let hsub_m₀' : (⊤ : R) ≤ m₀ ⊆ᴮ p' := subset_trans' hsub hsub_p'
  let c_p' := coneInMaster hm₀ hp' hsub_m₀'
  have hc_le : c_p' ≤ c_p := coneInMaster_mono hm₀ hp hsub hp' hsub_m₀' hsub_p'
  -- On `c_p'`, each `w_piece n t` equals `c_p' ⊓ j_R (reads (w_piece n t).val p')`.
  have hw_read_eq (n : ℕ) (t : ValidLiftedTriple U a θ α) :
      c_p' ⊓ w_piece n t = c_p' ⊓ j_R (Erdos1172CohenIteration.reads (w_piece n t).val p') := by
    have hdec' : (⊤ : R) ≤
        (⨆ s : ValidLiftedTriple U a θ α, Erdos1172CohenIteration.reads (w_piece n s).val p') ⊔
          Erdos1172CohenIteration.reads (u_part n none) p' := by
      refine (hdec n).trans (iSup_le fun opt => ?_)
      cases opt with
      | none => exact le_sup_right
      | some s =>
        exact le_sup_of_le_left
          (le_iSup (fun s' : ValidLiftedTriple U a θ α => Erdos1172CohenIteration.reads (w_piece n s').val p') s)
    have hle_none (s : ValidLiftedTriple U a θ α) :
        (c_p' ⊓ w_piece n s) ⊓ j_R (Erdos1172CohenIteration.reads (u_part n none) p') ≤ ⊥ := by
      change (c_p'.val ⊓ (w_piece n s).val) ⊓ (j_R _).val ≤ ⊥
      have h1 : (c_p'.val ⊓ (w_piece n s).val) ⊓
          (j_R (Erdos1172CohenIteration.reads (u_part n none) p')).val ≤
          (w_piece n s).val ⊓ u_part n none :=
        le_inf (inf_le_left.trans inf_le_right)
          ((inf_le_inf_right (j_R (Erdos1172CohenIteration.reads (u_part n none) p')).val inf_le_left).trans
            (coneInMaster_val_inf_firstStageHom_reads_le hm₀ hp' hsub_m₀' (u_part n none)))
      have h2 : (w_piece n s).val ⊓ u_part n none ≤ ⊥ :=
        (inf_le_inf (le_iSup (fun s' => (w_piece n s').val) s) le_rfl).trans inf_compl_eq_bot.le
      exact h1.trans h2
    exact cone_read_piece_eq j_R c_p' (w_piece n)
      (fun s => Erdos1172CohenIteration.reads (w_piece n s).val p')
      (Erdos1172CohenIteration.reads (u_part n none) p')
      (fun hne => hw_disj n hne) hdec'
      (fun s => coneInMaster_inf_firstStageHom_reads_le hm₀ hp' hsub_m₀' (w_piece n s))
      hle_none t
  let Supp (n : ℕ) : Set (ValidLiftedTriple U a θ α) :=
    {t | Erdos1172CohenIteration.reads (w_piece n t).val p' ≠ ⊥}
  have hSupp_lt (n : ℕ) : #(Supp n) < θ := by
    refine cc (fun x : Supp n => Erdos1172CohenIteration.reads (w_piece n x.val).val p')
      (fun x => x.property) fun x₁ x₂ hne => ?_
    exact Erdos1172CohenIteration.reads_inf_eq_bot
      (congrArg Subtype.val (hw_disj n (fun he => hne (Subtype.ext he))))
  let Idx_G : Type u := Σ n : ULift.{u} ℕ, Supp n.down
  have hIdx_lt : #Idx_G < θ := by
    rw [Cardinal.mk_sigma]
    have hg (n : ULift.{u} ℕ) : (#(Supp n.down)).ord < θ.ord :=
      Cardinal.ord_lt_ord.mpr (hSupp_lt n.down)
    let supOrd := ⨆ n : ULift.{u} ℕ, (#(Supp n.down)).ord + 1
    have hcard_nat : #(ULift.{u} ℕ) < θ := by
      simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0] using hθ.aleph0_lt
    have hsup_ord : supOrd < θ.ord :=
      Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hθ.isRegular.cof_ord]) hg
    have hle_sup (n : ULift.{u} ℕ) : #(Supp n.down) ≤ supOrd.card := by
      have ho : (#(Supp n.down)).ord ≤ supOrd :=
        (Ordinal.lt_iSup_add_one (fun m : ULift.{u} ℕ => (#(Supp m.down)).ord) n).le
      simpa only [Cardinal.card_ord] using Ordinal.card_le_card ho
    exact ((Cardinal.sum_le_sum _ _ hle_sup).trans_eq (Cardinal.sum_const' _ supOrd.card)).trans_lt
      (Cardinal.mul_lt_of_lt hθ.aleph0_lt.le hcard_nat (Cardinal.lt_ord.mp hsup_ord))
  let G_raw : bSet R := .mk Idx_G
    (fun k => check ((liftedTriplePSet U a θ α).Func k.2.val.val))
    (fun k => Erdos1172CohenIteration.reads (w_piece k.1.down k.2.val).val p')
  have hz_eq_G : c_p' ≤ z =ᴮ mapNames j_R G_raw := by
    have hG_sub : (⊤ : W₁) ≤ mapNames j_R G_raw ⊆ᴮ check V_dst := by
      dsimp only [G_raw]
      rw [mapNames_mk, subset_unfold]
      dsimp only [bSet.type, bSet.bval, bSet.func]
      refine le_iInf fun k => deduction.mp ?_
      exact le_top.trans (by rw [map_check]; exact check_mem (PSet.func_mem V_dst k.2.val))
    have hrow (t : ValidLiftedTriple U a θ α) :
        c_p' ⊓ (check (V_dst.Func t) ∈ᴮ z) =
        c_p' ⊓ (check (V_dst.Func t) ∈ᴮ mapNames j_R G_raw) := by
      have hlhs : c_p' ⊓ (check (V_dst.Func t) ∈ᴮ z) =
          ⨆ n : ℕ, c_p' ⊓ j_R (Erdos1172CohenIteration.reads (w_piece n t).val p') := by
        calc
          c_p' ⊓ (check (V_dst.Func t) ∈ᴮ z) = c_p' ⊓ (c_p ⊓ (check (V_dst.Func t) ∈ᴮ z)) := by
              rw [← inf_assoc, inf_eq_left.mpr hc_le]
          _ = c_p' ⊓ ⨆ n : ℕ, w_piece n t := by rw [hw_join t]
          _ = ⨆ n : ℕ, c_p' ⊓ w_piece n t := inf_iSup_eq c_p' _
          _ = ⨆ n : ℕ, c_p' ⊓ j_R (Erdos1172CohenIteration.reads (w_piece n t).val p') :=
            iSup_congr fun n => hw_read_eq n t
      have hrhs : c_p' ⊓ (check (V_dst.Func t) ∈ᴮ mapNames j_R G_raw) =
          ⨆ n : ℕ, c_p' ⊓ j_R (Erdos1172CohenIteration.reads (w_piece n t).val p') := by
        dsimp only [G_raw]
        rw [mapNames_mk, mem_unfold, inf_iSup_eq]
        apply le_antisymm
        · refine iSup_le fun ⟨n, ⟨t', ht'⟩⟩ => ?_
          change c_p' ⊓ (j_R (Erdos1172CohenIteration.reads (w_piece n.down t').val p') ⊓
            (check (V_dst.Func t) =ᴮ mapNames j_R (check ((liftedTriplePSet U a θ α).Func t'.val)))) ≤ _
          rw [map_check]
          by_cases htt' : t = t'
          · subst htt'
            exact (inf_le_inf_left c_p' inf_le_left).trans
              (le_iSup (fun m : ℕ => c_p' ⊓ j_R (Erdos1172CohenIteration.reads (w_piece m t).val p')) n.down)
          · have hneq : (check (V_dst.Func t) : bSet W₁) =ᴮ
                check ((liftedTriplePSet U a θ α).Func t'.val) = ⊥ :=
              check_bv_eq_bot_of_not_equiv (validLiftedTriplePSet_inj U a θ α htt')
            exact (inf_le_right.trans (inf_le_right.trans hneq.le)).trans bot_le
        · refine iSup_le fun n => ?_
          by_cases hpos : Erdos1172CohenIteration.reads (w_piece n t).val p' = ⊥
          · rw [hpos, BotHomClass.map_bot, inf_bot_eq]
            exact bot_le
          · refine le_iSup_of_le ⟨⟨n⟩, ⟨t, hpos⟩⟩ ?_
            change c_p' ⊓ j_R (Erdos1172CohenIteration.reads (w_piece n t).val p') ≤
              c_p' ⊓ (j_R (Erdos1172CohenIteration.reads (w_piece n t).val p') ⊓
                (check (V_dst.Func t) =ᴮ mapNames j_R (check ((liftedTriplePSet U a θ α).Func t.val))))
            rw [map_check]
            exact inf_le_inf_left c_p' (le_inf le_rfl bv_refl)
      exact hlhs.trans hrhs.symm
    have rep (Y : bSet W₁) (sub : c_p' ≤ Y ⊆ᴮ check V_dst) :
        c_p' ≤ Y =ᴮ ErdosCheckedIndicator.checkedIndicator V_dst
          (fun t => c_p' ⊓ (check (V_dst.Func t) ∈ᴮ Y)) := by
      have h0 : c_p' ≤ Y =ᴮ ErdosCheckedIndicator.checkedIndicator V_dst
          (fun t => check (V_dst.Func t) ∈ᴮ Y) := by
        rw [ErdosCheckedIndicator.checkedIndicator_membership_eq]
        exact eq_membership_indicator_of_subset sub
      exact bv_trans h0 (subset_ext
        (ErdosCheckedIndicator.checkedIndicator_subset_of_coefficients _ fun _ => le_inf inf_le_left inf_le_right)
        (ErdosCheckedIndicator.checkedIndicator_subset_of_coefficients _ fun _ => inf_le_right.trans inf_le_right))
    have r1 := rep z (hc_le.trans hz_sub)
    rw [congrArg (ErdosCheckedIndicator.checkedIndicator V_dst) (funext hrow)] at r1
    exact bv_trans r1 (bv_symm (rep (mapNames j_R G_raw) (le_top.trans hG_sub)))
  have hG_func : (⊤ : R) ≤ is_func G_raw := by
    have hG_prod : (⊤ : R) ≤ G_raw ⊆ᴮ prod
        (prod (ordinalCarrier (ordinalImage U a α)) (ordinalCarrier θ.ord))
        (ordinalCarrier (ordinalImage U a α)) := by
      dsimp only [G_raw]
      rw [subset_unfold]
      refine le_iInf fun k => deduction.mp ?_
      exact le_top.trans (mem_congr (bv_symm (check_liftedTriplePSet_func U a θ α k.2.val.val)) bv_refl
        (mem_prod (mem_prod (check_mem (PSet.func_mem _ _)) (check_mem (PSet.func_mem _ _)))
          (check_mem (PSet.func_mem _ _))))
    have h1 : c_p' ≤ is_func (mapNames j_R G_raw) :=
      is_func_of_subset (bSet.subset_of_eq (bv_symm hz_eq_G)) (hc_le.trans hz_func)
    have hmap_fn : c_p' ≤ j_R (is_func G_raw) := mapNames_is_func_le_hom j_R hG_prod h1
    exact ((coneInMaster_le_firstStageHom_iff hm₀ hp' hsub_m₀' (is_func G_raw)).mp hmap_fn).ge
  exact ⟨p', hp', hsub_p',
    { Idx := Idx_G
      card_lt := hIdx_lt
      triple := fun k => k.2.val
      weight := fun k => Erdos1172CohenIteration.reads (w_piece k.1.down k.2.val).val p'
      func := hG_func },
    hz_eq_G⟩

omit [CardinalInterFilter (U : Filter I) κ] in
/-- Specialization of `compress_lifted_witness_to_R_gen` to `R := AmbientInternalLevy κ θ`. -/
theorem compress_lifted_witness_to_R
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {m₀ p : bSet (AmbientInternalLevy κ θ)}
    (hm₀ : (⊤ : AmbientInternalLevy κ θ) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : AmbientInternalLevy κ θ) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : AmbientInternalLevy κ θ) ≤ m₀ ⊆ᴮ p)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))
      (LocalizedSourceCohen (AmbientInternalLevy κ θ) m₀ hm₀))
    (α : Ordinal.{u})
    (z : bSet (LocalizedSourceCohen (AmbientInternalLevy κ θ) m₀ hm₀))
    (hz : coneInMaster hm₀ hp hsub ≤
      z ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α))) :
    ∃ (p' : bSet (AmbientInternalLevy κ θ))
      (hp' : (⊤ : AmbientInternalLevy κ θ) ≤ ErdosCohen.condition omegaOne p')
      (hsub_p' : (⊤ : AmbientInternalLevy κ θ) ≤ p ⊆ᴮ p')
      (G' : SmallGroundLevyGraph U a θ α (AmbientInternalLevy κ θ)),
      coneInMaster hm₀ hp' (subset_trans' hsub hsub_p') ≤
        z =ᴮ mapNames (localizedFirstStageHom hm₀) G'.toBSet :=
  compress_lifted_witness_to_R_gen (R := AmbientInternalLevy κ θ) U a hk.le hκ hθ hf hn ht
    (ambientInternalLevy_strictCC hk hκ hθ) hm₀ hp hsub j₀ α z hz

end CompressLiftedWitness

section CodeSmallGroundFunc
variable {I : Type u} {κ θ : Cardinal.{u}}
variable (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem strict_upper_bound_theta' (hθ : θ.IsRegular)
    {D : Type u} (hD : #D < θ) (f : D → θ.ord.ToType) :
    ∃ b : θ.ord.ToType, ∀ d : D, f d < b := by
  by_contra! h
  have hc : IsCofinal (Set.range f) := fun a => by
    obtain ⟨d, hd⟩ := h a
    exact ⟨f d, Set.mem_range_self d, hd⟩
  have hh := Order.cof_le hc
  rw [Ordinal.cof_toType, hθ.cof_ord] at hh
  exact hD.not_ge (hh.trans Cardinal.mk_range_le)

omit [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem boundedAnon_fineRank_ordinal (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    (ξ : θ.ord.ToType) {ν : θ.ord.ToType} (hξν : ξ ≤ ν) :
    let VA := Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
    (⊤ : VA) ≤ Preparation.boundedAnonName U a
        (fun i => check (PSet.ordinalMk (typeLT ↥(boundedFiber θ a ν i ∩ Set.Iio ξ)))) =ᴮ
      check (PSet.ordinalMk ξ.toOrd.val) := by
  intro VA
  let F_ξ (i : I) : PSet.{u} := PSet.ordinalMk (typeLT ↥(boundedFiber θ a ν i ∩ Set.Iio ξ))
  have hF_supp : Preparation.Supported U a F_ξ :=
    ⟨ν, fun S => PSet.ordinalMk (typeLT ↥(S ∩ Set.Iio ξ)), EventuallyEq.rfl⟩
  let w_ξ : BoundedHull U θ a := ⟨fineRankGerm U κ θ a ξ, fineRankGerm_boundedSupport U κ θ a ξ hf ht⟩
  have hw_val : Germ.ofFun (fun i => ZFSet.mk (F_ξ i)) = w_ξ.val := by
    have h1 : (fun i => ZFSet.mk (F_ξ i)) = fun i => (typeLT ↥(boundedFiber θ a ξ i)).toZFSet := by
      funext i
      change (typeLT ↥(boundedFiber θ a ν i ∩ Set.Iio ξ)).toZFSet = _
      rw [boundedFiber_restrict θ a hξν i]
    rw [h1]
    exact (fineRankGerm_eq_prefix U κ θ a ξ hf ht).symm
  have hw_col : boundedCollapse U θ a w_ξ = ξ.toOrd.val.toZFSet := by
    apply boundedCollapse_ordinal_agrees U θ a ξ.toOrd.val
    · intro β hβ
      let η := Ordinal.ToType.mk (⟨β, hβ.trans ξ.toOrd.property⟩ : Set.Iio θ.ord)
      refine ⟨⟨fineRankGerm U κ θ a η, fineRankGerm_boundedSupport U κ θ a η hf ht⟩, ?_⟩
      exact (collapse_fineRankGerm U κ θ a hf hn ht η).trans
        (congrArg (fun z : Set.Iio θ.ord => z.val.toZFSet) (Ordinal.ToType.mk.symm_apply_apply _))
    · exact collapse_fineRankGerm U κ θ a hf hn ht ξ
  exact bv_trans (Preparation.boundedAnon_checked_family U a hk hf hn ht hκ w_ξ F_ξ hF_supp hw_val)
    (check_bv_eq (PSet.equiv_iff_eq.mpr ((ZFSet.mk_out _).trans hw_col)))

omit [CardinalInterFilter (U : Filter I) κ] in
private theorem code_stage_step6 {R W₁ : Type u}
    [NontrivialCompleteBooleanAlgebra R] [NontrivialCompleteBooleanAlgebra W₁]
    (hk : κ ≤ θ) (hκ : κ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) W₁)
    (j_R : CompleteLatticeHom R W₁)
    (c_mid : W₁) (α : Ordinal.{u})
    (G : SmallGroundLevyGraph U a θ α R)
    (ν_all : θ.ord.ToType)
    (q_raw q_pos : Set θ.ord.ToType → bSet (anonymousAlgebra κ))
    (hq_raw_sub : ∀ S, (⊤ : anonymousAlgebra κ) ≤
      q_raw S ⊆ᴮ prod (prod (ordinalCarrier α) (ordinalCarrier κ.ord)) (ordinalCarrier α))
    (hq_pos_mem : ∀ S, (⊤ : anonymousAlgebra κ) ≤ q_pos S ∈ᴮ internalLevyPoset κ α)
    (hq_pos_eq : value U (fun i => is_func (q_raw (boundedFiber θ a ν_all i))) ≤
      Preparation.boundedAnonName U a (fun i => q_pos (boundedFiber θ a ν_all i)) =ᴮ
        Preparation.boundedAnonName U a (fun i => q_raw (boundedFiber θ a ν_all i)))
    (Q_VA : bSet (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)))
    (hq_raw_QVA : (⊤ : Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) ≤
      Preparation.boundedAnonName U a (fun i => q_raw (boundedFiber θ a ν_all i)) =ᴮ Q_VA)
    (hQVA_G : c_mid ≤ mapNames j₀ Q_VA =ᴮ mapNames j_R G.toBSet) :
    let q_mid := mapNames j₀ (Preparation.boundedAnonName U a (fun i => q_pos (boundedFiber θ a ν_all i)))
    c_mid ≤ q_mid ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α)) ∧
    c_mid ≤ q_mid =ᴮ mapNames j_R G.toBSet := by
  intro q_mid
  let A := anonymousAlgebra κ
  let VA := Erdos1172BooleanUltrapower.Algebra U A
  have hq_mid_poset : (⊤ : W₁) ≤ q_mid ∈ᴮ
      mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α)) := by
    have hVA_mem : (⊤ : VA) ≤
        Preparation.boundedAnonName U a (fun i => q_pos (boundedFiber θ a ν_all i)) ∈ᴮ
          Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α) := by
      rw [← Preparation.boundedAnonName_mem U a hk hf hn ht hκ
        (fun i => q_pos (boundedFiber θ a ν_all i)) (fun _ => internalLevyPoset κ α)
        ⟨ν_all, q_pos, EventuallyEq.rfl⟩ (Preparation.Supported.const _),
        value_eq_of_eventuallyEq U (g := fun _ => ⊤)
          (Eventually.of_forall fun i => top_unique (hq_pos_mem (boundedFiber θ a ν_all i))),
        value_top]
    simpa only [TopHomClass.map_top, map_mem] using OrderHomClass.mono j₀ hVA_mem
  have hc_forces_raw_func : c_mid ≤ j₀ (value U (fun i => is_func (q_raw (boundedFiber θ a ν_all i)))) := by
    let D_A : bSet A := prod (ordinalCarrier α) (ordinalCarrier κ.ord)
    let L_A : bSet A := ordinalCarrier α
    have hfn_eq_A (i : I) : is_func (q_raw (boundedFiber θ a ν_all i)) =
        funcBoundedFormula.eval ![q_raw (boundedFiber θ a ν_all i), D_A, L_A] :=
      le_antisymm (is_func_le_funcBoundedFormula le_rfl)
        (is_func_of_subset_prod_and_funcBoundedFormula
          (le_top.trans (hq_raw_sub (boundedFiber θ a ν_all i))) le_rfl)
    have henv_supp : Preparation.SupportedEnv U a
        (fun i => ![q_raw (boundedFiber θ a ν_all i), D_A, L_A]) :=
      ⟨ν_all, fun S => ![q_raw S, D_A, L_A], Eventually.of_forall fun _ => rfl⟩
    have hval_eval : j₀ (value U (fun i => is_func (q_raw (boundedFiber θ a ν_all i)))) =
        funcBoundedFormula.eval
          ![mapNames j₀ (Preparation.boundedAnonName U a (fun i => q_raw (boundedFiber θ a ν_all i))),
            mapNames j₀ (Preparation.boundedAnonName U a (fun _ => D_A)),
            mapNames j₀ (Preparation.boundedAnonName U a (fun _ => L_A))] := by
      simp_rw [hfn_eq_A]
      rw [Preparation.boundedAnon_formula_eval U a hk hf hn ht hκ funcBoundedFormula _ henv_supp,
        funcBoundedFormula.map_eval j₀]
      exact congrArg funcBoundedFormula.eval (funext fun idx => by fin_cases idx <;> rfl)
    rw [hval_eval]
    have hord_θ : ordinalImage U a κ.ord = θ.ord :=
      Ordinal.toZFSet_injective ((ordinalImage_code U a κ.ord).trans
        (boundedDiagonal_critical_image U κ θ a hf hn ht))
    have hD_eq : (⊤ : W₁) ≤ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => D_A)) =ᴮ
        mapNames j_R (prod (ordinalCarrier (ordinalImage U a α)) (ordinalCarrier θ.ord)) := by
      have hm := OrderHomClass.mono j₀ (boundedAnon_prod_ordinalCarrier U a hk hf hn ht hκ α κ.ord)
      rw [hord_θ, TopHomClass.map_top, map_bv_eq, ErdosNameTransport.map_prod] at hm
      rw [ErdosNameTransport.map_prod]
      simpa only [D_A, ordinalCarrier, map_check] using hm
    have hL_eq : (⊤ : W₁) ≤ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => L_A)) =ᴮ
        mapNames j_R (ordinalCarrier (ordinalImage U a α)) := by
      have hm := OrderHomClass.mono j₀ (Preparation.boundedAnon_ordinal U a hk hf hn ht hκ α)
      rw [TopHomClass.map_top, map_bv_eq] at hm
      simpa only [L_A, ordinalCarrier, map_check] using hm
    have hG_fn_W : (⊤ : W₁) ≤ funcBoundedFormula.eval
        ![mapNames j_R G.toBSet,
          mapNames j_R (prod (ordinalCarrier (ordinalImage U a α)) (ordinalCarrier θ.ord)),
          mapNames j_R (ordinalCarrier (ordinalImage U a α))] := by
      have hm := OrderHomClass.mono j_R
        (is_func_le_funcBoundedFormula
          (D := prod (ordinalCarrier (ordinalImage U a α)) (ordinalCarrier θ.ord))
          (V := ordinalCarrier (ordinalImage U a α)) G.func)
      rw [TopHomClass.map_top, funcBoundedFormula.map_eval j_R] at hm
      exact hm.trans_eq (congrArg funcBoundedFormula.eval (funext fun idx => by fin_cases idx <;> rfl))
    have hraw_eq_G : c_mid ≤ mapNames j₀
        (Preparation.boundedAnonName U a (fun i => q_raw (boundedFiber θ a ν_all i))) =ᴮ
        mapNames j_R G.toBSet := by
      have hm := OrderHomClass.mono j₀ hq_raw_QVA
      rw [TopHomClass.map_top, map_bv_eq] at hm
      exact bv_trans (le_top.trans hm) hQVA_G
    exact funcBoundedFormula_congr (bv_symm hraw_eq_G)
      (le_top.trans (bv_symm hD_eq)) (le_top.trans (bv_symm hL_eq)) (le_top.trans hG_fn_W)
  have hq_mid_eq_raw : c_mid ≤ q_mid =ᴮ
      mapNames j₀ (Preparation.boundedAnonName U a (fun i => q_raw (boundedFiber θ a ν_all i))) := by
    have hm := OrderHomClass.mono j₀ hq_pos_eq
    rw [map_bv_eq] at hm
    exact hc_forces_raw_func.trans hm
  have hraw_eq_QVA : (⊤ : W₁) ≤
      mapNames j₀ (Preparation.boundedAnonName U a (fun i => q_raw (boundedFiber θ a ν_all i))) =ᴮ
      mapNames j₀ Q_VA := by
    simpa only [TopHomClass.map_top, map_bv_eq] using OrderHomClass.mono j₀ hq_raw_QVA
  exact ⟨le_top.trans hq_mid_poset,
    bv_trans hq_mid_eq_raw (bv_trans (le_top.trans hraw_eq_QVA) hQVA_G)⟩

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem cone_bit_master_eq {L : Type u} [BooleanAlgebra L]
    {C M bit F : L} (hCM : C ≤ M)
    (hiff : C ≤ (bit ⊓ F) ⊔ (bitᶜ ⊓ Fᶜ)) :
    C ⊓ (bit ⊓ M) = C ⊓ (F ⊓ M) := by
  have hl (X : L) : C ⊓ (X ⊓ M) = C ⊓ X := by
    rw [← inf_assoc, inf_comm C X, inf_assoc, inf_eq_left.mpr hCM, inf_comm]
  rw [hl bit, hl F]
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    calc
      C ⊓ bit ≤ ((bit ⊓ F) ⊔ (bitᶜ ⊓ Fᶜ)) ⊓ bit := inf_le_inf_right bit hiff
      _ = ((bit ⊓ F) ⊓ bit) ⊔ ((bitᶜ ⊓ Fᶜ) ⊓ bit) := inf_sup_right _ _ _
      _ ≤ F ⊔ (bitᶜ ⊓ bit) :=
        sup_le_sup (inf_le_left.trans inf_le_right) (inf_le_inf_right bit inf_le_left)
      _ = F := by rw [compl_inf_eq_bot, sup_bot_eq]
  · refine le_inf inf_le_left ?_
    calc
      C ⊓ F ≤ ((bit ⊓ F) ⊔ (bitᶜ ⊓ Fᶜ)) ⊓ F := inf_le_inf_right F hiff
      _ = ((bit ⊓ F) ⊓ F) ⊔ ((bitᶜ ⊓ Fᶜ) ⊓ F) := inf_sup_right _ _ _
      _ ≤ bit ⊔ (Fᶜ ⊓ F) :=
        sup_le_sup (inf_le_left.trans inf_le_left) (inf_le_inf_right F inf_le_right)
      _ = bit := by rw [compl_inf_eq_bot, sup_bot_eq]

omit [CardinalInterFilter (U : Filter I) κ] in
private theorem exists_fresh_cohen_bit_coding
    {R : Type u} [NontrivialCompleteBooleanAlgebra R]
    (hθ : θ.IsInaccessible)
    (cc : StrictCC R θ)
    (hθ_w1 : (⊤ : R) ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaOne)
    {m₀ p : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : R) ≤ m₀ ⊆ᴮ p)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))
      (LocalizedSourceCohen R m₀ hm₀))
    (hj₀_sub : (⊤ : LocalizedSourceCohen R m₀ hm₀) ≤
      mapNames j₀ (Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) =ᴮ
        mapNames (LocalizedBelow.restrict (masterPositive m₀ hm₀))
          (Erdos1172CohenIteration.subsetName (B := R) (PSet.ordinalMk θ.ord)))
    {α : Ordinal.{u}}
    (G : SmallGroundLevyGraph U a θ α R) :
    ∃ (ν_ζ : θ.ord.ToType) (ζ : G.Idx → θ.ord.ToType)
      (p_mid : bSet R) (hp_mid : (⊤ : R) ≤ ErdosCohen.condition omegaOne p_mid)
      (hsub_mid : (⊤ : R) ≤ p ⊆ᴮ p_mid),
      (∀ k, ζ k < ν_ζ) ∧
      Function.Injective ζ ∧
      ∀ k, coneInMaster hm₀ hp_mid (subset_trans' hsub hsub_mid) ⊓
          j₀ ((check (PSet.ordinalMk (ζ k).toOrd.val) :
            bSet (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))) ∈ᴮ
            Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) =
        coneInMaster hm₀ hp_mid (subset_trans' hsub hsub_mid) ⊓
          localizedFirstStageHom hm₀ (G.weight k) := by
  classical
  let VA := Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
  let W₁ := LocalizedSourceCohen R m₀ hm₀
  let j_R := localizedFirstStageHom hm₀
  let ρ := LocalizedBelow.restrict (masterPositive m₀ hm₀)
  let dom_p := graphDomain (omegaOne : bSet R) two p
  have hdom_cnt : (⊤ : R) ≤ injects_into dom_p omega :=
    ErdosCohen.countable_of_smallDomain omegaOne_property
      (hp.trans (inf_le_right.trans inf_le_right))
  have hdom_sub_θ : (⊤ : R) ≤ dom_p ⊆ᴮ check (PSet.ordinalMk θ.ord) := by
    refine subset_trans' ?_ (bSet.subset_of_eq (bv_symm hθ_w1))
    rw [subset_unfold']
    refine le_iInf fun x => deduction.mp ?_
    exact (inf_le_right.trans (mem_graphDomain (omegaOne : bSet R) two p x).le).trans inf_le_left
  obtain ⟨A₀, hA₀_lt, hA₀_sub, hdom_A₀⟩ :=
    bSet.ErdosCountableGroundCapture.exists_ground_capture hθ.isRegular hθ.aleph0_lt cc
      (PSet.ordinalMk θ.ord) (PSet.ordinalMk_inj θ.ord) hdom_cnt hdom_sub_θ
  choose ix_of hix_of using fun x : A₀.Type => hA₀_sub x
  obtain ⟨μ_used, hμ_used⟩ := strict_upper_bound_theta' hθ.isRegular hA₀_lt
    (fun x => Ordinal.ToType.mk ⟨ordOfPSetIdx (ix_of x), ordOfPSetIdx_lt (ix_of x)⟩)
  let μ₀ := (#G.Idx).ord
  have hμ₀_lt : μ₀ < θ.ord := Cardinal.ord_lt_ord.mpr G.card_lt
  have heq_card : #G.Idx = #μ₀.ToType := by
    rw [Cardinal.mk_toType, Cardinal.card_ord]
  let e_Idx : G.Idx ≃ μ₀.ToType := Classical.choice (Cardinal.eq.mp heq_card)
  have hadd_lt {o₁ o₂ : Ordinal.{u}} (h₁ : o₁ < θ.ord) (h₂ : o₂ < θ.ord) : o₁ + o₂ < θ.ord :=
    Cardinal.lt_ord.mpr ((Ordinal.card_add o₁ o₂).trans_lt
      (Cardinal.add_lt_of_lt hθ.aleph0_lt.le (Cardinal.lt_ord.mp h₁) (Cardinal.lt_ord.mp h₂)))
  let ν_ζ : θ.ord.ToType := Ordinal.ToType.mk ⟨μ_used.toOrd.val + μ₀,
    hadd_lt (toOrd_lt μ_used) hμ₀_lt⟩
  let ζ (k : G.Idx) : θ.ord.ToType := Ordinal.ToType.mk
    ⟨μ_used.toOrd.val + (e_Idx k).toOrd.val,
     hadd_lt (toOrd_lt μ_used) ((toOrd_lt (e_Idx k)).trans hμ₀_lt)⟩
  have hζ_ord (k : G.Idx) : (ζ k).toOrd.val = μ_used.toOrd.val + (e_Idx k).toOrd.val :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  have hν_ζ_ord : ν_ζ.toOrd.val = μ_used.toOrd.val + μ₀ :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
  have hζ_ge (k : G.Idx) : μ_used.toOrd.val ≤ (ζ k).toOrd.val := by
    rw [hζ_ord]
    exact le_add_right le_rfl
  have hζ_lt_ν (k : G.Idx) : ζ k < ν_ζ := by
    apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
    change (ζ k).toOrd.val < ν_ζ.toOrd.val
    rw [hζ_ord, hν_ζ_ord]
    exact (add_lt_add_iff_left _).mpr (toOrd_lt (e_Idx k))
  have hζ_inj : Function.Injective ζ := by
    intro k₁ k₂ heq
    by_contra hne_k
    have hne_ord : (e_Idx k₁).toOrd.val ≠ (e_Idx k₂).toOrd.val :=
      fun h => hne_k (e_Idx.injective (Ordinal.ToType.mk.symm.injective (Subtype.ext h)))
    have ho : (ζ k₁).toOrd.val = (ζ k₂).toOrd.val := congrArg (fun z => z.toOrd.val) heq
    rw [hζ_ord, hζ_ord] at ho
    rcases lt_or_gt_of_ne hne_ord with hlt | hlt
    · exact (((add_lt_add_iff_left μ_used.toOrd.val).mpr hlt).trans_eq ho.symm).false
    · exact (((add_lt_add_iff_left μ_used.toOrd.val).mpr hlt).trans_eq ho).false
  let idx_θ (x : θ.ord.ToType) : (PSet.ordinalMk θ.ord).Type :=
    (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt (toOrd_lt x))).choose
  have hidx_θ_equiv (x : θ.ord.ToType) :
      PSet.Equiv ((PSet.ordinalMk θ.ord).Func (idx_θ x)) (PSet.ordinalMk x.toOrd.val) :=
    PSet.Equiv.symm (PSet.mem_iff.mp (PSet.mk_mem_mk_of_lt (toOrd_lt x))).choose_spec
  have hidx_θ_ord (x : θ.ord.ToType) : ordOfPSetIdx (idx_θ x) = x.toOrd.val :=
    Ordinal.toZFSet_injective (ZFSet.sound
      (PSet.Equiv.trans (PSet.Equiv.symm (ordOfPSetIdx_equiv (idx_θ x))) (hidx_θ_equiv x)))
  let C_fresh : PSet.{u} := PSet.mk G.Idx (fun k => (PSet.ordinalMk θ.ord).Func (idx_θ (ζ k)))
  have hC_sep : ∀ k₁ k₂ : G.Idx, k₁ ≠ k₂ → ¬PSet.Equiv (C_fresh.Func k₁) (C_fresh.Func k₂) := by
    intro k₁ k₂ hne heqv
    apply PSet.ordinalMk_inj θ.ord (idx_θ (ζ k₁)) (idx_θ (ζ k₂)) _ heqv
    intro hidx
    have ho := (hidx_θ_ord (ζ k₁)).symm.trans ((congrArg ordOfPSetIdx hidx).trans (hidx_θ_ord (ζ k₂)))
    exact hne (hζ_inj (Ordinal.ToType.mk.symm.injective (Subtype.ext ho)))
  have hC_sub_w1 : (⊤ : R) ≤ check C_fresh ⊆ᴮ omegaOne := by
    refine subset_trans' ?_ (bSet.subset_of_eq hθ_w1)
    rw [subset_unfold]
    refine le_iInf fun k => deduction.mp ?_
    rw [check_func]
    exact le_top.trans (check_mem (PSet.func_mem (PSet.ordinalMk θ.ord) (idx_θ (ζ (check_cast k)))))
  have hC_cnt : (⊤ : R) ≤ injects_into (check C_fresh) omega := by
    have hsub_ν : (⊤ : R) ≤ check C_fresh ⊆ᴮ check (PSet.ordinalMk ν_ζ.toOrd.val) := by
      rw [subset_unfold]
      refine le_iInf fun k => deduction.mp ?_
      rw [check_func]
      have hlt_ν : (ζ (check_cast k)).toOrd.val < ν_ζ.toOrd.val :=
        Ordinal.ToType.mk.symm.lt_iff_lt.mpr (hζ_lt_ν (check_cast k))
      exact le_top.trans (mem_congr (bv_symm (check_bv_eq (hidx_θ_equiv _))) bv_refl
        (check_mem (PSet.mk_mem_mk_of_lt hlt_ν)))
    have hν_w1 : (⊤ : R) ≤ check (PSet.ordinalMk ν_ζ.toOrd.val) ∈ᴮ omegaOne :=
      mem_congr bv_refl hθ_w1 (check_mem (PSet.mk_mem_mk_of_lt (toOrd_lt ν_ζ)))
    exact injects_into_trans (injects_into_of_subset hsub_ν) (omegaOne_member_injects hν_w1)
  have hC_fresh (k : G.Idx) : (⊤ : R) ≤ (check (C_fresh.Func k) ∈ᴮ dom_p)ᶜ := by
    have hbot_A₀ : (check (C_fresh.Func k) ∈ᴮ check A₀ : R) ≤ ⊥ := by
      rw [mem_unfold]
      refine iSup_le fun x => ?_
      rw [check_func, check_bval_top, top_inf_eq]
      have hneqv : ¬PSet.Equiv (C_fresh.Func k) (A₀.Func (check_cast x)) := by
        intro he
        have ho1 : (ζ k).toOrd.val = ordOfPSetIdx (ix_of (check_cast x)) :=
          Ordinal.toZFSet_injective (ZFSet.sound
            (PSet.Equiv.trans (PSet.Equiv.symm (hidx_θ_equiv (ζ k)))
              (PSet.Equiv.trans he (PSet.Equiv.trans (hix_of (check_cast x))
                (ordOfPSetIdx_equiv (ix_of (check_cast x)))))))
        have hlt_μ : ordOfPSetIdx (ix_of (check_cast x)) < μ_used.toOrd.val := by
          have hm := Ordinal.ToType.mk.symm.lt_iff_lt.mpr (hμ_used (check_cast x))
          rw [Ordinal.ToType.mk.symm_apply_apply] at hm
          exact hm
        exact ((hζ_ge k).trans_lt (ho1 ▸ hlt_μ)).false
      rw [check_bv_eq_bot_of_not_equiv hneqv]
    have hbot_dom : (check (C_fresh.Func k) ∈ᴮ dom_p : R) = ⊥ :=
      le_bot_iff.mp ((mem_of_mem_subset (le_top.trans hdom_A₀) le_rfl).trans hbot_A₀)
    rw [hbot_dom, compl_bot]
  obtain ⟨p_mid, hp_mid, hsub_mid, hbits_mid⟩ :=
    ErdosCohen.exists_indexed_binary_assignment C_fresh G.weight hC_sep
      omegaOne_property hp hC_sub_w1 hC_cnt hC_fresh
  let hsub_m₀_mid : (⊤ : R) ≤ m₀ ⊆ᴮ p_mid := subset_trans' hsub hsub_mid
  let c_mid := coneInMaster hm₀ hp_mid hsub_m₀_mid
  have hbit_agree (k : G.Idx) :
      c_mid ⊓ j₀ ((check (PSet.ordinalMk (ζ k).toOrd.val) : bSet VA) ∈ᴮ
        Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) =
      c_mid ⊓ j_R (G.weight k) := by
    let bit_k : Erdos1172CohenIteration.omegaOneAlgebra R :=
      Erdos1172CohenIteration.bitValue (omegaOne : bSet R)
        (check ((PSet.ordinalMk θ.ord).Func (idx_θ (ζ k)))) (1 : bSet R)
    have hcone_iff : nameCone (ErdosCohen.conditions (omegaOne : bSet R)) p_mid ≤
        (bit_k ⊓ Erdos1172CohenIteration.omegaOneFirstStageHom (G.weight k)) ⊔
        (bit_kᶜ ⊓ (Erdos1172CohenIteration.omegaOneFirstStageHom (G.weight k))ᶜ) := by
      let _ : CompleteBooleanAlgebra (Erdos1172CohenIteration.omegaOneAlgebra R) :=
        completionCompleteBooleanAlgebra
      unfold nameCone
      refine iSup_le fun ⟨r, hreq⟩ => ?_
      have h1 : r.value ⊓ G.weight k ≤ pair (check (C_fresh.Func k)) (1 : bSet R) ∈ᴮ name r :=
        mem_congr bv_refl (inf_le_left.trans hreq)
          ((le_inf le_top inf_le_right).trans (hbits_mid k).1)
      have h0 : r.value ⊓ (G.weight k)ᶜ ≤ pair (check (C_fresh.Func k)) (0 : bSet R) ∈ᴮ name r :=
        mem_congr bv_refl (inf_le_left.trans hreq)
          ((le_inf le_top inf_le_right).trans (hbits_mid k).2)
      exact Erdos1172CohenIteration.condition_binary_agreement h1 h0
    have hρ_bit_eq : c_mid ⊓ ρ bit_k = c_mid ⊓ j_R (G.weight k) :=
      Subtype.ext (cone_bit_master_eq (L := Erdos1172CohenIteration.omegaOneAlgebra R)
        c_mid.property hcone_iff)
    have hj₀_bit : j₀ ((check (PSet.ordinalMk (ζ k).toOrd.val) : bSet VA) ∈ᴮ
        Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) = ρ bit_k := by
      rw [map_mem j₀, map_check j₀]
      have heq1 : ((check (PSet.ordinalMk (ζ k).toOrd.val) : bSet W₁) ∈ᴮ
          mapNames j₀ (Preparation.boundedAnonName U a (fun _ => anonymousSubset κ))) =
          ((check (PSet.ordinalMk (ζ k).toOrd.val) : bSet W₁) ∈ᴮ
            mapNames ρ (Erdos1172CohenIteration.subsetName (B := R) (PSet.ordinalMk θ.ord))) :=
        le_antisymm
          (mem_congr bv_refl (le_top.trans hj₀_sub) le_rfl)
          (mem_congr bv_refl (le_top.trans (bv_symm hj₀_sub)) le_rfl)
      have heq2 : ((check (PSet.ordinalMk (ζ k).toOrd.val) : bSet W₁) ∈ᴮ
          mapNames ρ (Erdos1172CohenIteration.subsetName (B := R) (PSet.ordinalMk θ.ord))) =
          ((check ((PSet.ordinalMk θ.ord).Func (idx_θ (ζ k))) : bSet W₁) ∈ᴮ
            mapNames ρ (Erdos1172CohenIteration.subsetName (B := R) (PSet.ordinalMk θ.ord))) :=
        le_antisymm
          (mem_congr (le_top.trans (check_bv_eq (PSet.Equiv.symm (hidx_θ_equiv (ζ k))))) bv_refl le_rfl)
          (mem_congr (le_top.trans (check_bv_eq (hidx_θ_equiv (ζ k)))) bv_refl le_rfl)
      rw [heq1, heq2, ← map_check ρ, ← map_mem ρ,
        Erdos1172CohenIteration.subsetName_member_eq_bitValue (PSet.ordinalMk_inj θ.ord) (idx_θ (ζ k))]
    rw [hj₀_bit]
    exact hρ_bit_eq
  exact ⟨ν_ζ, ζ, p_mid, hp_mid, hsub_mid, hζ_lt_ν, hζ_inj, hbit_agree⟩

omit [CardinalInterFilter (U : Filter I) κ] in
private theorem boundedAnon_restricted_point_ordinal
    (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    {α : Ordinal.{u}} (pt : Erdos1172Shioya.UltrapowerStage.Point U a α.ToType)
    {ν ν_all : θ.ord.ToType} (hle : ν ≤ ν_all)
    (g : Set θ.ord.ToType → α.ToType)
    (hg : Germ.ofFun (fun i => g (boundedFiber θ a ν i)) = pt.val)
    (idx : (PSet.ordinalMk (ordinalImage U a α)).Type)
    (hidx : (indexEquiv U a α pt).toOrd.val = ordOfPSetIdx idx) :
    let VA := Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
    (⊤ : VA) ≤ Preparation.boundedAnonName U a
        (fun i => check (PSet.ordinalMk (g (boundedFiber θ a ν_all i ∩ Set.Iio ν)).toOrd.val)) =ᴮ
      check ((PSet.ordinalMk (ordinalImage U a α)).Func idx) := by
  intro VA
  let A := anonymousAlgebra κ
  have hs_lhs : Preparation.Supported U a
      (fun i => (check (PSet.ordinalMk (g (boundedFiber θ a ν_all i ∩ Set.Iio ν)).toOrd.val) : bSet A)) :=
    ⟨ν_all, fun S => check (PSet.ordinalMk (g (S ∩ Set.Iio ν)).toOrd.val), EventuallyEq.rfl⟩
  have hrepr_eq : ∀ᶠ i in U,
      (g (boundedFiber θ a ν_all i ∩ Set.Iio ν)).toOrd.val =
        (Erdos1172Shioya.UltrapowerStage.repr U a pt i).toOrd.val := by
    have h1 := Germ.coe_eq.mp (hg.trans (Erdos1172Shioya.UltrapowerStage.repr_eq U a pt).symm)
    filter_upwards [h1] with i hi
    rw [boundedFiber_restrict θ a hle i, hi]
  have hs_rhs : Preparation.Supported U a
      (fun i => (check (PSet.ordinalMk (Erdos1172Shioya.UltrapowerStage.repr U a pt i).toOrd.val) : bSet A)) :=
    ⟨ν, fun S => check (PSet.ordinalMk (g S).toOrd.val),
      (Germ.coe_eq.mp (hg.trans (Erdos1172Shioya.UltrapowerStage.repr_eq U a pt).symm)).mono
        fun _ hi => congrArg (fun x : α.ToType => (check (PSet.ordinalMk x.toOrd.val) : bSet A)) hi⟩
  have h1 : (⊤ : VA) ≤ Preparation.boundedAnonName U a
      (fun i => check (PSet.ordinalMk (g (boundedFiber θ a ν_all i ∩ Set.Iio ν)).toOrd.val)) =ᴮ
      Preparation.boundedAnonName U a
        (fun i => check (PSet.ordinalMk (Erdos1172Shioya.UltrapowerStage.repr U a pt i).toOrd.val)) := by
    rw [← Preparation.boundedAnonName_eq U a hk hf hn ht hκ _ _ hs_lhs hs_rhs,
      value_eq_of_eventuallyEq U (g := fun _ => ⊤)
        (hrepr_eq.mono fun _ hi => by rw [hi]; exact top_unique bv_refl),
      value_top]
  have h2 := boundedAnon_indexEquiv_ordinal U a hk hf hn ht hκ α pt
  rw [hidx] at h2
  exact bv_trans h1 (bv_trans h2 (check_bv_eq (PSet.Equiv.symm (ordOfPSetIdx_equiv idx))))

omit [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ] in
private theorem boundedAnon_q_raw_and_pos_eq
    (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a)
    (ht : FiberOrderType U κ θ a) (hκ : κ.IsInaccessible)
    {Idx : Type u} (k₀_def : Idx)
    (ζ : Idx → θ.ord.ToType) (hζ_inj : Function.Injective ζ)
    (ν_all : θ.ord.ToType)
    (Active : Set θ.ord.ToType → Set Idx)
    (hActive_mem : ∀ i (x : Active (boundedFiber θ a ν_all i)), ζ x.val ∈ a i)
    (elem_S : Set θ.ord.ToType → Idx → bSet (anonymousAlgebra κ))
    (wt_S : Set θ.ord.ToType → Idx → anonymousAlgebra κ)
    (triple_dst : Idx → PSet.{u})
    (hev_small : ∀ᶠ i in U, #↥(Active (boundedFiber θ a ν_all i)) < κ)
    (hev_active : ∀ k : Idx, ∀ᶠ i in U, k ∈ Active (boundedFiber θ a ν_all i))
    (helem_eq : ∀ k : Idx,
      (⊤ : Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)) ≤
        Preparation.boundedAnonName (κ := κ) U a (fun i => elem_S (boundedFiber θ a ν_all i) k) =ᴮ
        check (triple_dst k))
    (hwt_eq : ∀ k : Idx,
      value U (fun i => wt_S (boundedFiber θ a ν_all i) k) =
        ((check (PSet.ordinalMk (ζ k).toOrd.val) :
          bSet (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))) ∈ᴮ
          Preparation.boundedAnonName (κ := κ) U a (fun _ => anonymousSubset κ))) :
    let A := anonymousAlgebra κ
    let VA := Erdos1172BooleanUltrapower.Algebra U A
    let q_raw (S : Set θ.ord.ToType) : bSet A :=
      .mk (Active S) (fun k => elem_S S k.val) (fun k => wt_S S k.val)
    let q_pos (S : Set θ.ord.ToType) : bSet A :=
      if #↥(Active S) < κ then
        .mk (Active S) (fun k => elem_S S k.val) (fun k => wt_S S k.val ⊓ is_func (q_raw S))
      else ∅
    let Q_VA : bSet VA := .mk Idx (fun k => check (triple_dst k))
      (fun k => (check (PSet.ordinalMk (ζ k).toOrd.val) : bSet VA) ∈ᴮ
        Preparation.boundedAnonName (κ := κ) U a (fun _ => anonymousSubset κ))
    ((⊤ : VA) ≤ Preparation.boundedAnonName (κ := κ) U a
        (fun i => q_raw (boundedFiber θ a ν_all i)) =ᴮ Q_VA) ∧
    (value U (fun i => is_func (q_raw (boundedFiber θ a ν_all i))) ≤
      Preparation.boundedAnonName (κ := κ) U a (fun i => q_pos (boundedFiber θ a ν_all i)) =ᴮ
        Preparation.boundedAnonName (κ := κ) U a (fun i => q_raw (boundedFiber θ a ν_all i))) := by
  classical
  intro A VA q_raw q_pos Q_VA
  refine ⟨?_, ?_⟩
  · apply subset_ext
    · rw [Preparation.boundedAnonName_unfold (κ := κ) U a (fun i => q_raw (boundedFiber θ a ν_all i)),
        subset_unfold]
      refine le_iInf fun ch => deduction.mp ?_
      rw [top_inf_eq]
      let f_norm (i : I) : θ.ord.ToType :=
        if hi : i ∈ ch.val.carrier then ζ (ch.val.pick ⟨i, hi⟩).val else ζ k₀_def
      have hf_in_a : ∀ᶠ i in U, f_norm i ∈ a i := by
        filter_upwards [ch.val.large] with i hi
        simp only [f_norm, dif_pos hi]
        exact hActive_mem i (ch.val.pick ⟨i, hi⟩)
      obtain ⟨γ₀, hγ₀⟩ := hn f_norm hf_in_a
      have _ : NeBot (U : Filter I) := U.neBot
      have hboth : ∀ᶠ i in U, i ∈ ch.val.carrier ∧ f_norm i = γ₀ := by
        filter_upwards [ch.val.large, hγ₀] with i hi hfi
        exact ⟨hi, hfi⟩
      obtain ⟨i₀, hi₀_ch, hi₀_eq⟩ := hboth.exists
      let k₀ : Idx := (ch.val.pick ⟨i₀, hi₀_ch⟩).val
      have hγ₀_eq : γ₀ = ζ k₀ := by
        simp only [f_norm, dif_pos hi₀_ch] at hi₀_eq
        exact hi₀_eq.symm
      have hpick_const : ∀ᶠ i in U, ∃ hi : i ∈ ch.val.carrier, (ch.val.pick ⟨i, hi⟩).val = k₀ := by
        filter_upwards [ch.val.large, hγ₀] with i hi hfi
        refine ⟨hi, hζ_inj ?_⟩
        simp only [f_norm, dif_pos hi] at hfi
        exact hfi.trans hγ₀_eq
      have hw_le : value U (Erdos1172BooleanUltrapower.weight U
          (fun i => q_raw (boundedFiber θ a ν_all i)) ch.val) ≤
          ((check (PSet.ordinalMk (ζ k₀).toOrd.val) : bSet VA) ∈ᴮ
            Preparation.boundedAnonName (κ := κ) U a (fun _ => anonymousSubset κ)) := by
        rw [← hwt_eq k₀]
        apply (value_le_value_iff U).mpr
        filter_upwards [hpick_const] with i ⟨hi, hki⟩
        simp only [Erdos1172BooleanUltrapower.weight, selected, q_raw, bSet.bval, dif_pos hi, hki, le_rfl]
      have hch_eq : (⊤ : VA) ≤ Preparation.boundedAnonName (κ := κ) U a
          (Erdos1172BooleanUltrapower.child U (fun i => q_raw (boundedFiber θ a ν_all i)) ch.val) =ᴮ
          check (triple_dst k₀) := by
        refine bv_trans ?_ (helem_eq k₀)
        rw [← Preparation.boundedAnonName_eq U a hk hf hn ht hκ
          (Erdos1172BooleanUltrapower.child U (fun i => q_raw (boundedFiber θ a ν_all i)) ch.val)
          (fun i => elem_S (boundedFiber θ a ν_all i) k₀) ch.property
          ⟨ν_all, fun S => elem_S S k₀, EventuallyEq.rfl⟩,
          value_eq_of_eventuallyEq U (g := fun _ => ⊤) _, value_top]
        filter_upwards [hpick_const] with i ⟨hi, hki⟩
        simp only [Erdos1172BooleanUltrapower.child, q_raw, bSet.func, dif_pos hi, hki]
        exact top_unique bv_refl
      dsimp only [Q_VA]
      rw [mem_unfold]
      dsimp only [bSet.type, bSet.bval, bSet.func]
      exact le_iSup_of_le k₀ (le_inf hw_le (le_top.trans hch_eq))
    · dsimp only [Q_VA]
      rw [subset_unfold]
      dsimp only [bSet.type, bSet.bval, bSet.func]
      refine le_iInf fun k => deduction.mp ?_
      rw [top_inf_eq]
      have hmem_VA : value U (fun i => wt_S (boundedFiber θ a ν_all i) k) ≤
          Preparation.boundedAnonName (κ := κ) U a (fun i => elem_S (boundedFiber θ a ν_all i) k) ∈ᴮ
            Preparation.boundedAnonName (κ := κ) U a (fun i => q_raw (boundedFiber θ a ν_all i)) := by
        rw [← Preparation.boundedAnonName_mem U a hk hf hn ht hκ
          (fun i => elem_S (boundedFiber θ a ν_all i) k)
          (fun i => q_raw (boundedFiber θ a ν_all i))
          ⟨ν_all, fun S => elem_S S k, EventuallyEq.rfl⟩
          ⟨ν_all, q_raw, EventuallyEq.rfl⟩]
        apply (value_le_value_iff U).mpr
        filter_upwards [hev_active k] with i hki
        dsimp only [q_raw]
        rw [mem_unfold]
        dsimp only [bSet.type, bSet.bval, bSet.func]
        exact le_iSup_of_le ⟨k, hki⟩ (le_inf le_rfl bv_refl)
      rw [hwt_eq k] at hmem_VA
      exact mem_congr (le_top.trans (helem_eq k)) bv_refl hmem_VA
  · rw [← Preparation.boundedAnonName_eq U a hk hf hn ht hκ
      (fun i => q_pos (boundedFiber θ a ν_all i))
      (fun i => q_raw (boundedFiber θ a ν_all i))
      ⟨ν_all, q_pos, EventuallyEq.rfl⟩ ⟨ν_all, q_raw, EventuallyEq.rfl⟩]
    apply (value_le_value_iff U).mpr
    filter_upwards [hev_small] with i hsmall
    dsimp only [q_pos]
    rw [if_pos hsmall]
    dsimp only [q_raw]
    apply subset_ext
    · rw [subset_unfold]
      refine le_iInf fun k => deduction.mp ?_
      rw [mem_unfold]
      exact le_iSup_of_le k (le_inf (inf_le_right.trans inf_le_left) bv_refl)
    · rw [subset_unfold]
      refine le_iInf fun k => deduction.mp ?_
      rw [mem_unfold]
      exact le_iSup_of_le k (le_inf (le_inf inf_le_right inf_le_left) bv_refl)

omit [CardinalInterFilter (U : Filter I) κ] in
/-- Abstract coding of a `SmallGroundLevyGraph U a θ α R` into a lifted stage-`α` Lévy condition
`q_mid` on a refined first-stage Cohen condition `p_mid ⊇ᴮ p`. -/
theorem code_small_ground_func_into_stage_gen
    {R : Type u} [NontrivialCompleteBooleanAlgebra R]
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (cc : StrictCC R θ)
    (hθ_w1 : (⊤ : R) ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaOne)
    {m₀ p : bSet R}
    (hm₀ : (⊤ : R) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : R) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : R) ≤ m₀ ⊆ᴮ p)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))
      (LocalizedSourceCohen R m₀ hm₀))
    (hj₀_sub : (⊤ : LocalizedSourceCohen R m₀ hm₀) ≤
      mapNames j₀ (Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) =ᴮ
        mapNames (LocalizedBelow.restrict (masterPositive m₀ hm₀))
          (Erdos1172CohenIteration.subsetName (B := R) (PSet.ordinalMk θ.ord)))
    (α : Ordinal.{u})
    (G : SmallGroundLevyGraph U a θ α R) :
    ∃ (p_mid : bSet R) (hp_mid : (⊤ : R) ≤ ErdosCohen.condition omegaOne p_mid)
      (hsub_mid : (⊤ : R) ≤ p ⊆ᴮ p_mid)
      (q_mid : bSet (LocalizedSourceCohen R m₀ hm₀)),
      coneInMaster hm₀ hp_mid (subset_trans' hsub hsub_mid) ≤
        q_mid ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α)) ∧
      coneInMaster hm₀ hp_mid (subset_trans' hsub hsub_mid) ≤
        q_mid =ᴮ mapNames (localizedFirstStageHom hm₀) G.toBSet := by
  classical
  let A := anonymousAlgebra κ
  let VA := Erdos1172BooleanUltrapower.Algebra U A
  let W₁ := LocalizedSourceCohen R m₀ hm₀
  let j_R := localizedFirstStageHom hm₀
  -- Boundary case: `G.Idx` is empty (covers `α = 0` as well).
  by_cases hemp : IsEmpty G.Idx
  · have hemp_mem : (⊤ : W₁) ≤ (∅ : bSet W₁) ∈ᴮ
        mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α)) := by
      have hVA_mem : (⊤ : VA) ≤ Preparation.boundedAnonName U a (fun _ => (∅ : bSet A)) ∈ᴮ
          Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α) := by
        have hemp_A : ∀ _ : I, (⊤ : A) ≤ (∅ : bSet A) ∈ᴮ internalLevyPoset κ α :=
          fun _ => empty_mem_internalLevyCollapse (ordinalCarrier κ.ord) (ordinalCarrier α)
        rw [← Preparation.boundedAnonName_mem U a hk.le hf hn ht hκ
          (fun _ => (∅ : bSet A)) (fun _ => internalLevyPoset κ α)
          (Preparation.Supported.const _) (Preparation.Supported.const _),
          value_eq_of_eventuallyEq U (g := fun _ => ⊤)
            (Eventually.of_forall fun i => top_unique (hemp_A i)),
          value_top]
      have hm := OrderHomClass.mono j₀
        (mem_congr (Preparation.boundedAnonName_empty U a) bv_refl hVA_mem)
      rwa [TopHomClass.map_top, map_mem, ErdosNameTransport.map_empty] at hm
    have hG_emp : (⊤ : R) ≤ G.toBSet =ᴮ (∅ : bSet R) := by
      apply subset_ext _ empty_subset
      dsimp only [SmallGroundLevyGraph.toBSet]
      rw [subset_unfold]
      exact le_iInf fun k => (hemp.false k).elim
    have hmap_emp : (⊤ : W₁) ≤ (∅ : bSet W₁) =ᴮ mapNames j_R G.toBSet := by
      have hm := OrderHomClass.mono j_R (bv_symm hG_emp)
      rwa [TopHomClass.map_top, map_bv_eq, ErdosNameTransport.map_empty] at hm
    exact ⟨p, hp, subset_self, ∅, le_top.trans hemp_mem, le_top.trans hmap_emp⟩
  · have hne_Idx : Nonempty G.Idx := not_isEmpty_iff.mp hemp
    obtain ⟨ν_ζ, ζ, p_mid, hp_mid, hsub_mid, hζ_lt_ν, hζ_inj, hbit_agree⟩ :=
      exists_fresh_cohen_bit_coding U a hθ cc hθ_w1 hm₀ hp hsub j₀ hj₀_sub G
    let hsub_m₀_mid : (⊤ : R) ≤ m₀ ⊆ᴮ p_mid := subset_trans' hsub hsub_mid
    let c_mid := coneInMaster hm₀ hp_mid hsub_m₀_mid
    -- Step 3: Common support bound `ν_all` for `ζ` and all triple coordinates of `G.triple`.
    let toImg (idx : (PSet.ordinalMk (ordinalImage U a α)).Type) : (ordinalImage U a α).ToType :=
      Ordinal.ToType.mk ⟨ordOfPSetIdx idx, ordOfPSetIdx_lt _⟩
    let ptOf (idx : (PSet.ordinalMk (ordinalImage U a α)).Type) := (indexEquiv U a α).symm (toImg idx)
    have hexPt (idx : (PSet.ordinalMk (ordinalImage U a α)).Type) :
        ∃ p : θ.ord.ToType × (Set θ.ord.ToType → α.ToType),
          Germ.ofFun (fun i => p.2 (boundedFiber θ a p.1 i)) = (ptOf idx).val :=
      let ⟨ν, g, hg⟩ := (ptOf idx).property; ⟨(ν, g), hg⟩
    let fgPt (idx : (PSet.ordinalMk (ordinalImage U a α)).Type) := Classical.choose (hexPt idx)
    have hgPt (idx : (PSet.ordinalMk (ordinalImage U a α)).Type) := Classical.choose_spec (hexPt idx)
    let t_ξ (k : G.Idx) := toImg (G.triple k).val.1.1
    let t_y (k : G.Idx) := toImg (G.triple k).val.2
    let pt_ξ (k : G.Idx) := ptOf (G.triple k).val.1.1
    let pt_y (k : G.Idx) := ptOf (G.triple k).val.2
    let η_t (k : G.Idx) : θ.ord.ToType :=
      Ordinal.ToType.mk ⟨ordOfPSetIdx (G.triple k).val.1.2, ordOfPSetIdx_lt _⟩
    let ν_ξ (k : G.Idx) : θ.ord.ToType := (fgPt (G.triple k).val.1.1).1
    let g_ξ (k : G.Idx) : Set θ.ord.ToType → α.ToType := (fgPt (G.triple k).val.1.1).2
    let ν_y (k : G.Idx) : θ.ord.ToType := (fgPt (G.triple k).val.2).1
    let g_y (k : G.Idx) : Set θ.ord.ToType → α.ToType := (fgPt (G.triple k).val.2).2
    have hg_ξ (k : G.Idx) := hgPt (G.triple k).val.1.1
    have hg_y (k : G.Idx) := hgPt (G.triple k).val.2
    let bound_k (k : G.Idx) : θ.ord.ToType := max (max ν_ζ (η_t k)) (max (ν_ξ k) (ν_y k))
    obtain ⟨ν_all, hν_all_raw⟩ := strict_upper_bound_theta' hθ.isRegular G.card_lt bound_k
    let k₀_def := Classical.choice hne_Idx
    have hν_ζ_lt_all : ν_ζ < ν_all :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans_lt (hν_all_raw k₀_def)
    have hζ_lt_all (k : G.Idx) : ζ k < ν_all := (hζ_lt_ν k).trans hν_ζ_lt_all
    have hη_lt_all (k : G.Idx) : η_t k < ν_all :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans_lt (hν_all_raw k)
    have hν_ξ_le_all (k : G.Idx) : ν_ξ k ≤ ν_all :=
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt (hν_all_raw k)).le
    have hν_y_le_all (k : G.Idx) : ν_y k ≤ ν_all :=
      (((le_max_right _ _).trans (le_max_right _ _)).trans_lt (hν_all_raw k)).le
    -- Step 4: Fiberwise active indices and `q_pos S : bSet A`.
    let ξ_S (S : Set θ.ord.ToType) (k : G.Idx) : Ordinal.{u} :=
      (g_ξ k (S ∩ Set.Iio (ν_ξ k))).toOrd.val
    let y_S (S : Set θ.ord.ToType) (k : G.Idx) : Ordinal.{u} :=
      (g_y k (S ∩ Set.Iio (ν_y k))).toOrd.val
    let η_S (S : Set θ.ord.ToType) (k : G.Idx) : Ordinal.{u} := typeLT ↥(S ∩ Set.Iio (η_t k))
    let rk_ζ (S : Set θ.ord.ToType) (k : G.Idx) : Ordinal.{u} := typeLT ↥(S ∩ Set.Iio (ζ k))
    let Active (S : Set θ.ord.ToType) : Set G.Idx :=
      {k : G.Idx | ζ k ∈ S ∧ y_S S k < ξ_S S k ∧ η_S S k < κ.ord}
    let elem_S (S : Set θ.ord.ToType) (k : G.Idx) : bSet A :=
      pair (pair (check (PSet.ordinalMk (ξ_S S k))) (check (PSet.ordinalMk (η_S S k))))
        (check (PSet.ordinalMk (y_S S k)))
    let wt_S (S : Set θ.ord.ToType) (k : G.Idx) : A :=
      check (PSet.ordinalMk (rk_ζ S k)) ∈ᴮ anonymousSubset κ
    let q_raw (S : Set θ.ord.ToType) : bSet A :=
      .mk (Active S) (fun k => elem_S S k.val) (fun k => wt_S S k.val)
    let q_pos (S : Set θ.ord.ToType) : bSet A :=
      if #↥(Active S) < κ then
        .mk (Active S) (fun k => elem_S S k.val) (fun k => wt_S S k.val ⊓ is_func (q_raw S))
      else ∅
    have hq_raw_sub (S : Set θ.ord.ToType) :
        (⊤ : A) ≤ q_raw S ⊆ᴮ prod (prod (ordinalCarrier α) (ordinalCarrier κ.ord)) (ordinalCarrier α) := by
      dsimp only [q_raw]
      rw [subset_unfold]
      refine le_iInf fun k => deduction.mp ?_
      exact le_top.trans (mem_prod
        (mem_prod (check_mem (PSet.mk_mem_mk_of_lt (toOrd_lt _)))
          (check_mem (PSet.mk_mem_mk_of_lt k.property.2.2)))
        (check_mem (PSet.mk_mem_mk_of_lt (toOrd_lt _))))
    have hq_pos_mem (S : Set θ.ord.ToType) : (⊤ : A) ≤ q_pos S ∈ᴮ internalLevyPoset κ α := by
      dsimp only [q_pos]
      split_ifs with hcard_S
      · let q_p : bSet A := .mk (Active S) (fun k => elem_S S k.val)
          (fun k => wt_S S k.val ⊓ is_func (q_raw S))
        have hsub_raw : (⊤ : A) ≤ q_p ⊆ᴮ q_raw S := by
          dsimp only [q_p, q_raw]
          rw [subset_unfold]
          refine le_iInf fun k => deduction.mp ?_
          rw [mem_unfold]
          exact le_iSup_of_le k (le_inf (inf_le_right.trans inf_le_left) bv_refl)
        have hsub_prod : (⊤ : A) ≤ q_p ⊆ᴮ
            prod (prod (ordinalCarrier α) (ordinalCarrier κ.ord)) (ordinalCarrier α) :=
          subset_trans' hsub_raw (hq_raw_sub S)
        have hfn_qp : (⊤ : A) ≤ is_func q_p := by
          have h1 : is_func (q_raw S) ≤ is_func q_p :=
            is_func_of_subset (le_top.trans hsub_raw) le_rfl
          have h2 : (is_func (q_raw S))ᶜ ≤ is_func q_p := by
            have hemp_qp : (is_func (q_raw S))ᶜ ≤ q_p =ᴮ (∅ : bSet A) := by
              apply subset_ext _ empty_subset
              dsimp only [q_p]
              rw [subset_unfold]
              refine le_iInf fun k => deduction.mp ?_
              have h0 : (is_func (q_raw S))ᶜ ⊓ (wt_S S k.val ⊓ is_func (q_raw S)) ≤ ⊥ :=
                (inf_le_inf_left _ inf_le_right).trans compl_inf_eq_bot.le
              exact h0.trans bot_le
            exact is_func_of_subset (bSet.subset_of_eq hemp_qp)
              (le_top.trans (countableCollapse_mem.mp
                (mem_internalLevyCollapse.mp (empty_mem_internalLevyCollapse
                  (ordinalCarrier κ.ord) (ordinalCarrier α))).1).2.1)
          rw [← sup_compl_eq_top (x := is_func (q_raw S))]
          exact sup_le h1 h2
        have hcnt_qp : (⊤ : A) ≤ injects_into q_p omega := by
          let μ_S := #↥(Active S)
          have h1 : (⊤ : A) ≤ injects_into q_p (check (PSet.ordinalMk μ_S.ord)) :=
            ErdosGroundIndexNameBound.injects_checked_cardinal_of_index_cardinal_le μ_S q_p le_rfl
          have h2 : (⊤ : A) ≤ check (PSet.ordinalMk μ_S.ord) ∈ᴮ omegaOne :=
            mem_congr bv_refl (anonymous_checked_upper_eq_omegaOne κ hκ)
              (check_mem (PSet.mk_mem_mk_of_lt (Cardinal.ord_lt_ord.mpr hcard_S)))
          exact injects_into_trans h1 (omegaOne_member_injects h2)
        have hbd_qp : (⊤ : A) ≤ levyAllBounded (ordinalCarrier κ.ord) (ordinalCarrier α) q_p := by
          have hbd_elem (k : Active S) :
              (⊤ : A) ≤ levyBoundPred (ordinalCarrier κ.ord) (ordinalCarrier α) (elem_S S k.val) :=
            le_iSup_of_le (check (PSet.ordinalMk (ξ_S S k.val)))
              (le_inf (check_mem (PSet.mk_mem_mk_of_lt (toOrd_lt _)))
                (le_iSup_of_le (check (PSet.ordinalMk (η_S S k.val)))
                  (le_inf (check_mem (PSet.mk_mem_mk_of_lt k.property.2.2))
                    (le_iSup_of_le (check (PSet.ordinalMk (y_S S k.val)))
                      (le_inf (check_mem (PSet.mk_mem_mk_of_lt k.property.2.1)) bv_refl)))))
          refine allIn_intro fun {Δ} _ z hz => ?_
          dsimp only [q_p] at hz
          rw [mem_unfold] at hz
          refine hz.trans (iSup_le fun k => ?_)
          exact bv_rw' inf_le_right (h_congr := levyBoundPred_ext _ _)
            (H_new := le_top.trans (hbd_elem k))
        exact mem_internalLevyCollapse.mpr ⟨countableCollapse_mem.mpr ⟨hsub_prod, hfn_qp, hcnt_qp⟩, hbd_qp⟩
      · exact empty_mem_internalLevyCollapse _ _
    have hev_small : ∀ᶠ i in U, #↥(Active (boundedFiber θ a ν_all i)) < κ := by
      filter_upwards [ht, hf ν_all] with i hti hν_mem
      let iso := Classical.choice hti
      let m₀ := iso.symm ⟨ν_all, hν_mem⟩
      let emb (x : Active (boundedFiber θ a ν_all i)) : Set.Iio m₀ :=
        ⟨iso.symm ⟨ζ x.val, x.property.1.1⟩, iso.symm.strictMono x.property.1.2⟩
      have hinj : Function.Injective emb := by
        intro x₁ x₂ heq
        have hsub := iso.symm.injective (congrArg Subtype.val heq)
        exact Subtype.ext (hζ_inj (congrArg Subtype.val hsub))
      exact (Cardinal.mk_le_of_injective hinj).trans_lt
        ((Cardinal.mk_Iio_lt m₀ (by simp)).trans_eq (Cardinal.mk_ord_toType κ))
    -- Step 5: Coordinate and weight agreement between `liftA (q_raw ∘ ...)` and `Q_VA`.
    have helem_eq (k : G.Idx) :
        (⊤ : VA) ≤ Preparation.boundedAnonName U a
          (fun i => elem_S (boundedFiber θ a ν_all i) k) =ᴮ
          check ((liftedTriplePSet U a θ α).Func (G.triple k).val) := by
      have hs_ξ : Preparation.Supported U a
          (fun i => (check (PSet.ordinalMk (ξ_S (boundedFiber θ a ν_all i) k)) : bSet A)) :=
        ⟨ν_all, fun S => check (PSet.ordinalMk (ξ_S S k)), EventuallyEq.rfl⟩
      have hs_η : Preparation.Supported U a
          (fun i => (check (PSet.ordinalMk (η_S (boundedFiber θ a ν_all i) k)) : bSet A)) :=
        ⟨ν_all, fun S => check (PSet.ordinalMk (η_S S k)), EventuallyEq.rfl⟩
      have hs_y : Preparation.Supported U a
          (fun i => (check (PSet.ordinalMk (y_S (boundedFiber θ a ν_all i) k)) : bSet A)) :=
        ⟨ν_all, fun S => check (PSet.ordinalMk (y_S S k)), EventuallyEq.rfl⟩
      have hpt_lift (idx : (PSet.ordinalMk (ordinalImage U a α)).Type)
          (hν_le : (fgPt idx).1 ≤ ν_all) :
          (⊤ : VA) ≤ Preparation.boundedAnonName U a
            (fun i => check (PSet.ordinalMk (((fgPt idx).2 (boundedFiber θ a ν_all i ∩ Set.Iio (fgPt idx).1)).toOrd.val))) =ᴮ
            check ((PSet.ordinalMk (ordinalImage U a α)).Func idx) := by
        refine boundedAnon_restricted_point_ordinal U a hk.le hf hn ht hκ (ptOf idx) hν_le
          (fgPt idx).2 (hgPt idx) idx ?_
        dsimp only [ptOf, toImg]; rw [Equiv.apply_symm_apply]
        exact congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
      have hξ_lift := hpt_lift (G.triple k).val.1.1 (hν_ξ_le_all k)
      have hy_lift := hpt_lift (G.triple k).val.2 (hν_y_le_all k)
      have hη_lift : (⊤ : VA) ≤ Preparation.boundedAnonName U a
          (fun i => check (PSet.ordinalMk (η_S (boundedFiber θ a ν_all i) k))) =ᴮ
          check ((PSet.ordinalMk θ.ord).Func (G.triple k).val.1.2) := by
        have h1 := boundedAnon_fineRank_ordinal U a hk.le hf hn ht hκ (η_t k) (hη_lt_all k).le
        have h2 : (η_t k).toOrd.val = ordOfPSetIdx (G.triple k).val.1.2 :=
          congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
        rw [h2] at h1
        exact bv_trans h1 (check_bv_eq (PSet.Equiv.symm (ordOfPSetIdx_equiv _)))
      refine bv_trans (Preparation.boundedAnonName_pair U a hk.le hf hn ht hκ
        (fun i => pair (check (PSet.ordinalMk (ξ_S (boundedFiber θ a ν_all i) k)))
          (check (PSet.ordinalMk (η_S (boundedFiber θ a ν_all i) k))))
        (fun i => check (PSet.ordinalMk (y_S (boundedFiber θ a ν_all i) k)))
        (hs_ξ.combine hs_η pair) hs_y) ?_
      refine bv_trans (pair_congr
        (bv_trans (Preparation.boundedAnonName_pair U a hk.le hf hn ht hκ
          (fun i => (check (PSet.ordinalMk (ξ_S (boundedFiber θ a ν_all i) k)) : bSet A))
          (fun i => (check (PSet.ordinalMk (η_S (boundedFiber θ a ν_all i) k)) : bSet A)) hs_ξ hs_η)
          (pair_congr hξ_lift hη_lift)) hy_lift)
        (bv_symm (check_liftedTriplePSet_func U a θ α (G.triple k).val))
    have hwt_eq (k : G.Idx) :
        value U (fun i => wt_S (boundedFiber θ a ν_all i) k) =
          ((check (PSet.ordinalMk (ζ k).toOrd.val) : bSet VA) ∈ᴮ
            Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) := by
      have hchk := boundedAnon_fineRank_ordinal U a hk.le hf hn ht hκ (ζ k) (hζ_lt_all k).le
      have heq_chk : ((check (PSet.ordinalMk (ζ k).toOrd.val) : bSet VA) ∈ᴮ
          Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) =
          (Preparation.boundedAnonName U a
            (fun i => (check (PSet.ordinalMk (rk_ζ (boundedFiber θ a ν_all i) k)) : bSet A)) ∈ᴮ
            Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) :=
        le_antisymm
          (mem_congr (le_top.trans (bv_symm hchk)) bv_refl le_rfl)
          (mem_congr (le_top.trans hchk) bv_refl le_rfl)
      rw [heq_chk]
      exact Preparation.boundedAnonName_mem U a hk.le hf hn ht hκ
        (fun i => (check (PSet.ordinalMk (rk_ζ (boundedFiber θ a ν_all i) k)) : bSet A))
        (fun _ => anonymousSubset κ)
        ⟨ν_all, fun S => check (PSet.ordinalMk (rk_ζ S k)), EventuallyEq.rfl⟩
        (Preparation.Supported.const (anonymousSubset κ))
    have hev_active (k : G.Idx) : ∀ᶠ i in U, k ∈ Active (boundedFiber θ a ν_all i) := by
      have hy_lt_ξ_ev : ∀ᶠ i in U, y_S (boundedFiber θ a ν_all i) k < ξ_S (boundedFiber θ a ν_all i) k := by
        have h1 : (t_y k).toOrd.val.toZFSet ∈ (t_ξ k).toOrd.val.toZFSet := by
          have ho_y : (t_y k).toOrd.val = ordOfPSetIdx (G.triple k).val.2 :=
            congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
          have ho_ξ : (t_ξ k).toOrd.val = ordOfPSetIdx (G.triple k).val.1.1 :=
            congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)
          rw [ho_y, ho_ξ]
          exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (G.triple k).property
        have h2 : Erdos1172Shioya.UltrapowerStage.pointCode U a
            Erdos1172Shioya.UltrapowerStage.ordinalLabel (pt_y k) ∈
            Erdos1172Shioya.UltrapowerStage.pointCode U a
            Erdos1172Shioya.UltrapowerStage.ordinalLabel (pt_ξ k) := by
          have l_y := indexEquiv_label U a α (pt_y k)
          have l_ξ := indexEquiv_label U a α (pt_ξ k)
          dsimp only [pt_y, pt_ξ] at l_y l_ξ
          rw [Equiv.apply_symm_apply] at l_y l_ξ
          rwa [← l_y, ← l_ξ]
        have hmem_rel : memRel U
            (Germ.map Erdos1172Shioya.UltrapowerStage.ordinalLabel (pt_y k).val)
            (Germ.map Erdos1172Shioya.UltrapowerStage.ordinalLabel (pt_ξ k).val) :=
          (boundedCollapse_mem_boundedCollapse_iff U θ a _ _).mp h2
        rw [← hg_y k, ← hg_ξ k] at hmem_rel
        filter_upwards [hmem_rel] with i hm
        have hm' : (y_S (boundedFiber θ a ν_all i) k).toZFSet ∈ (ξ_S (boundedFiber θ a ν_all i) k).toZFSet := by
          dsimp only [y_S, ξ_S]
          rw [boundedFiber_restrict θ a (hν_y_le_all k) i,
            boundedFiber_restrict θ a (hν_ξ_le_all k) i]
          exact hm
        exact Ordinal.toZFSet_mem_toZFSet_iff.mp hm'
      filter_upwards [hf (ζ k), hy_lt_ξ_ev, ht, hf (η_t k),
        Germ.coe_eq.mp (fineRankGerm_eq_prefix U κ θ a (η_t k) hf ht)] with i hζ_i hyξ_i hti hη_i hpref
      refine ⟨⟨hζ_i, hζ_lt_all k⟩, hyξ_i, ?_⟩
      dsimp only [η_S]
      rw [boundedFiber_restrict θ a (hη_lt_all k).le i]
      have hcond : Nonempty (κ.ord.ToType ≃o a i) ∧ η_t k ∈ a i := ⟨hti, hη_i⟩
      have hpref' : (if h : Nonempty (κ.ord.ToType ≃o a i) ∧ η_t k ∈ a i then
          ((Classical.choice h.1).symm ⟨η_t k, h.2⟩).toOrd.val.toZFSet else ∅) =
          (typeLT ↥(a i ∩ Set.Iio (η_t k))).toZFSet := hpref
      rw [dif_pos hcond] at hpref'
      change typeLT ↥(a i ∩ Set.Iio (η_t k)) < κ.ord
      rw [← Ordinal.toZFSet_injective hpref']
      exact toOrd_lt _
    let Q_VA : bSet VA := .mk G.Idx
      (fun k => check ((liftedTriplePSet U a θ α).Func (G.triple k).val))
      (fun k => (check (PSet.ordinalMk (ζ k).toOrd.val) : bSet VA) ∈ᴮ
        Preparation.boundedAnonName (κ := κ) U a (fun _ => anonymousSubset κ))
    obtain ⟨hq_raw_QVA, hq_pos_eq⟩ := boundedAnon_q_raw_and_pos_eq U a hk.le hf hn ht hκ
      k₀_def ζ hζ_inj ν_all Active (fun _ x => x.property.1.1) elem_S wt_S
      (fun k => (liftedTriplePSet U a θ α).Func (G.triple k).val)
      hev_small hev_active helem_eq hwt_eq
    -- Step 6: Identify `mapNames j₀ Q_VA =ᴮ mapNames j_R G.toBSet` on `c_mid`, deduce `is_func`, and conclude!
    have hQVA_G : c_mid ≤ mapNames j₀ Q_VA =ᴮ mapNames j_R G.toBSet := by
      dsimp only [Q_VA, SmallGroundLevyGraph.toBSet]
      rw [mapNames_mk, mapNames_mk]
      have hdir {f₁ f₂ : G.Idx → bSet (LocalizedSourceCohen R m₀ hm₀)}
          {w₁ w₂ : G.Idx → LocalizedSourceCohen R m₀ hm₀}
          (hw : ∀ k, c_mid ⊓ w₁ k ≤ w₂ k) (hf : ∀ k, (⊤ : _) ≤ f₁ k =ᴮ f₂ k) :
          c_mid ≤ (.mk G.Idx f₁ w₁ : bSet _) ⊆ᴮ .mk G.Idx f₂ w₂ := by
        rw [subset_unfold]; refine le_iInf fun k => deduction.mp ?_
        rw [mem_unfold]; exact le_iSup_of_le k (le_inf (hw k) (le_top.trans (hf k)))
      exact subset_ext
        (hdir (fun k => (hbit_agree k).le.trans inf_le_right) (fun _ => by rw [map_check, map_check]; exact bv_refl))
        (hdir (fun k => (hbit_agree k).ge.trans inf_le_right) (fun _ => by rw [map_check, map_check]; exact bv_refl))
    obtain ⟨hq_mid_poset, hq_mid_eq⟩ := code_stage_step6 U a hk.le hκ hf hn ht j₀ j_R
      c_mid α G ν_all q_raw q_pos hq_raw_sub hq_pos_mem hq_pos_eq Q_VA hq_raw_QVA hQVA_G
    exact ⟨p_mid, hp_mid, hsub_mid, _, hq_mid_poset, hq_mid_eq⟩

omit [CardinalInterFilter (U : Filter I) κ] in
/-- Specialization of `code_small_ground_func_into_stage_gen` to `R := AmbientInternalLevy κ θ`. -/
theorem code_small_ground_func_into_stage
    (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
    (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    {m₀ p : bSet (AmbientInternalLevy κ θ)}
    (hm₀ : (⊤ : AmbientInternalLevy κ θ) ≤ ErdosCohen.condition omegaOne m₀)
    (hp : (⊤ : AmbientInternalLevy κ θ) ≤ ErdosCohen.condition omegaOne p)
    (hsub : (⊤ : AmbientInternalLevy κ θ) ≤ m₀ ⊆ᴮ p)
    (j₀ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ))
      (LocalizedSourceCohen (AmbientInternalLevy κ θ) m₀ hm₀))
    (hj₀_sub : (⊤ : LocalizedSourceCohen (AmbientInternalLevy κ θ) m₀ hm₀) ≤
      mapNames j₀ (Preparation.boundedAnonName U a (fun _ => anonymousSubset κ)) =ᴮ
        mapNames (LocalizedBelow.restrict (masterPositive m₀ hm₀))
          (Erdos1172CohenIteration.subsetName (B := AmbientInternalLevy κ θ) (PSet.ordinalMk θ.ord)))
    (α : Ordinal.{u})
    (G : SmallGroundLevyGraph U a θ α (AmbientInternalLevy κ θ)) :
    ∃ (p_mid : bSet (AmbientInternalLevy κ θ))
      (hp_mid : (⊤ : AmbientInternalLevy κ θ) ≤ ErdosCohen.condition omegaOne p_mid)
      (hsub_mid : (⊤ : AmbientInternalLevy κ θ) ≤ p ⊆ᴮ p_mid)
      (q_mid : bSet (LocalizedSourceCohen (AmbientInternalLevy κ θ) m₀ hm₀)),
      coneInMaster hm₀ hp_mid (subset_trans' hsub hsub_mid) ≤
        q_mid ∈ᴮ mapNames j₀ (Preparation.boundedAnonName U a (fun _ => internalLevyPoset κ α)) ∧
      coneInMaster hm₀ hp_mid (subset_trans' hsub hsub_mid) ≤
        q_mid =ᴮ mapNames (localizedFirstStageHom hm₀) G.toBSet :=
  code_small_ground_func_into_stage_gen (R := AmbientInternalLevy κ θ) U a hk hκ hθ hf hn ht
    (ambientInternalLevy_strictCC hk hκ hθ)
    (ambientInternalLevy_theta_eq_omegaOne hk hκ hθ)
    hm₀ hp hsub j₀ hj₀_sub α G

end CodeSmallGroundFunc

end Erdos1172AnonymousInternalLevy
