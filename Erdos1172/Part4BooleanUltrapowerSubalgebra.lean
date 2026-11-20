/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanUltrapowerScalar
public import Erdos1172.Part4LevyPreparationBoundedSeed
public import Erdos1172.Part4ShioyaInterpretedMasterLift

@[expose] public section

/-! # Bounded hereditary ultrapower names over `anonymousAlgebra κ`

Using injectivity of `scalarHom U (inclusion (anonymousAlgebra κ))` together with the `≤ κ`-sized
dense presentation `exists_dense_presentation κ hκ` of `Erdos1172LevyCohen.Algebra κ` and bounded
representative selection (`exists_bounded_representative`), we prove that bounded child selections
suffice for existential and universal quantifiers over `Supported U a` names in
`anonymousAlgebra κ`. This yields `boundedAnonName` and full Δ₀ Łoś transfer (`boundedAnon_formula_eval`)
directly in `Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)` while matching the bounded
ground embedding `boundedGroundEmbedding U θ a` on checked sets and ordinals.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter
universe u

namespace Erdos1172BooleanUltrapower

section ScalarInjective
open Lattice Erdos1172PosetCompletion Erdos1172PositiveBoolean
variable {I B C : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable (U : Ultrafilter I) (e : CompleteLatticeHom B C)

/-- An injective complete Boolean homomorphism induces an injective `scalarHom` on Boolean
ultrapower completions. -/
theorem scalarHom_injective (he : Function.Injective e) :
    Function.Injective (scalarHom U e) := by
  intro x y hxy
  have ref {a b : Algebra U B} (hle : scalarHom U e a ≤ scalarHom U e b) : a ≤ b := by
    apply le_of_dense_conditions_le Set.univ (fun p => ⟨p, Set.mem_univ _, le_rfl⟩)
    rintro ⟨p, _⟩ hp
    obtain ⟨f, hf⟩ : ∃ f : I → B, Germ.ofFun f = p.val :=
      Germ.inductionOn p.val fun f => ⟨f, rfl⟩
    have hval : condition p = value U f := by
      apply le_antisymm
      · apply condition_le_iff.mpr
        change p.val ≤ Germ.ofFun f
        exact hf.symm.le
      · intro q hq
        exact (mem_condition_iff p q).mpr fun r hr =>
          ⟨r, le_rfl, (show r.val ≤ q.val from hr).trans ((show q.val ≤ Germ.ofFun f from hq).trans hf.le)⟩
    have hle' : value U (fun i => e (f i)) ≤ scalarHom U e b := by
      rw [← scalarHom_value]
      exact (OrderHomClass.mono (scalarHom U e) (hval.symm.le.trans hp)).trans hle
    by_contra hnb
    have hpos : condition p ⊓ bᶜ ≠ ⊥ := fun h0 =>
      hnb (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    obtain ⟨q, hq⟩ := exists_condition_le hpos
    obtain ⟨g, hg⟩ : ∃ g : I → B, Germ.ofFun g = q.val :=
      Germ.inductionOn q.val fun g => ⟨g, rfl⟩
    have hqg : value U g ≤ condition q := by
      intro r hr
      exact (mem_condition_iff q r).mpr fun s hs =>
        ⟨s, le_rfl, (show s.val ≤ r.val from hs).trans ((show r.val ≤ Germ.ofFun g from hr).trans hg.le)⟩
    have hgf : value U g ≤ value U f := (hqg.trans (hq.trans inf_le_left)).trans hval.le
    have hgb : value U g ≤ bᶜ := hqg.trans (hq.trans inf_le_right)
    have hegb : value U (fun i => e (g i)) ≤ (scalarHom U e b)ᶜ := by
      rw [← scalarHom_value, ← map_compl' (scalarHom U e)]
      exact OrderHomClass.mono (scalarHom U e) hgb
    have heg_bot : value U (fun i => e (g i)) ≤ ⊥ := by
      have h1 : value U (fun i => e (g i)) ≤ scalarHom U e b :=
        ((value_le_value_iff U).mpr (((value_le_value_iff U).mp hgf).mono fun _ hi =>
          OrderHomClass.mono e hi)).trans hle'
      exact (le_inf h1 hegb).trans inf_compl_eq_bot.le
    rw [← value_bot U] at heg_bot
    have hzero : ∀ᶠ i in U, g i = ⊥ := ((value_le_value_iff U).mp heg_bot).mono fun i hi =>
      he ((bot_unique hi).trans (BotHomClass.map_bot e).symm)
    exact q.property (hg.symm.trans (Germ.coe_eq.mpr hzero))
  exact le_antisymm (ref hxy.le) (ref hxy.ge)

end ScalarInjective

end Erdos1172BooleanUltrapower

namespace Erdos1172LevyCollapse.Preparation

section LevyCohenSupportedLowerBound
open Erdos1172GroundUltrapower Erdos1172PosetCompletion Erdos1172LevyCohen
open Erdos1172BooleanUltrapower Erdos1172Shioya.UltrapowerStage
variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)

/-- Every nonzero element of `Algebra U (Erdos1172LevyCohen.Algebra κ)` lies above a nonzero
`Supported U a` value, obtained by refining pointwise into the `≤ κ`-sized dense presentation. -/
theorem exists_supported_lower_bound_levyCohen
    (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
    (hκ : κ.IsInaccessible) {z : Erdos1172BooleanUltrapower.Algebra U (Erdos1172LevyCohen.Algebra κ)}
    (hz : z ≠ ⊥) :
    ∃ g : I → Erdos1172LevyCohen.Algebra κ,
      Supported U a g ∧ (∀ᶠ i in U, g i ≠ ⊥) ∧ value U g ≤ z := by
  classical
  let C := Erdos1172LevyCohen.Algebra κ
  obtain ⟨D, hDsize, hDdense⟩ := exists_dense_presentation κ hκ
  obtain ⟨p₀, _⟩ := exists_condition_le (top_ne_bot : (⊤ : C) ≠ ⊥)
  obtain ⟨d₀, hd₀D, _⟩ := hDdense p₀
  let defaultD : D := ⟨d₀, hd₀D⟩
  obtain ⟨q, hqz⟩ := exists_condition_le hz
  obtain ⟨f, hf_eq⟩ : ∃ f : I → C, Germ.ofFun f = q.val :=
    Germ.inductionOn q.val fun f => ⟨f, rfl⟩
  have hf_pos : ∀ᶠ i in U, f i ≠ ⊥ := U.eventually_not.mpr fun h0 =>
    q.property (hf_eq.symm.trans (Germ.coe_eq.mpr h0))
  let pickD (c : C) : D :=
    if hc : c ≠ ⊥ then
      let p := (exists_condition_le hc).choose
      let hd := hDdense p
      ⟨hd.choose, hd.choose_spec.1⟩
    else defaultD
  have hpick_le {c : C} (hc : c ≠ ⊥) : condition (pickD c).val ≤ c := by
    simp only [pickD, dif_pos hc]
    let p := (exists_condition_le hc).choose
    exact (condition_mono (hDdense p).choose_spec.2).trans (exists_condition_le hc).choose_spec
  obtain ⟨pt, hpt⟩ := exists_bounded_representative U a hk hf hn ht hDsize (fun i => pickD (f i))
  obtain ⟨η, F, hF⟩ := pt.property
  let g (i : I) : C := condition (repr U a pt i).val
  have hg_supp : Supported U a g := by
    refine ⟨η, fun S => condition (F S).val, ?_⟩
    exact (Germ.coe_eq.mp (hF.trans (repr_eq U a pt).symm)).mono fun _ hi =>
      congrArg (fun d : D => condition d.val) hi
  have hrepr : repr U a pt =ᶠ[U] fun i => pickD (f i) :=
    Germ.coe_eq.mp ((repr_eq U a pt).trans hpt)
  have hg_le_f : g ≤ᶠ[U] f := (hrepr.and hf_pos).mono fun i ⟨hri, hfi⟩ => by
    change condition (repr U a pt i).val ≤ f i
    rw [hri]
    exact hpick_le hfi
  have hval_f_le_q : value U f ≤ condition q := by
    intro r hr
    exact (mem_condition_iff q r).mpr fun s hs =>
      ⟨s, le_rfl, (show s.val ≤ r.val from hs).trans ((show r.val ≤ Germ.ofFun f from hr).trans hf_eq.le)⟩
  refine ⟨g, hg_supp, Eventually.of_forall fun i => condition_ne_bot _, ?_⟩
  exact ((value_le_value_iff U).mpr hg_le_f).trans (hval_f_le_q.trans hqz)

end LevyCohenSupportedLowerBound

section BoundedAnonymousNames
open bSet Lattice ErdosNameTransport ErdosOmegaTwo ErdosShioyaInternal
open Erdos1172GroundUltrapower Erdos1172CompleteSubalgebra
open Erdos1172LevyCohen Erdos1172BooleanUltrapower Erdos1172Shioya.UltrapowerStage
open scoped Flypitch

instance anonSubalgebraUltrapowerNontrivial
    {I B : Type u} [CompleteBooleanAlgebra B] [Nontrivial B]
    (U : Ultrafilter I) (S : CompleteSubalgebra B) :
    NontrivialCompleteBooleanAlgebra (Erdos1172BooleanUltrapower.Algebra U S) where
  toCompleteBooleanAlgebra := Erdos1172PosetCompletion.completionCompleteBooleanAlgebra
  bot_lt_top :=
    let _ : Nonempty (Erdos1172PositiveBoolean.Positive (Germ (U : Filter I) S)) :=
      ⟨⟨⊤, top_ne_bot⟩⟩
    bot_lt_top

private theorem completeHom_map_inf {X Y : Type u} [CompleteLattice X] [CompleteLattice Y]
    (e : CompleteLatticeHom X Y) (x y : X) : e (x ⊓ y) = e x ⊓ e y := by
  rw [← sInf_pair, sInfHomClass.map_sInf, Set.image_pair, sInf_pair]

variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)

local notation "A" => anonymousAlgebra κ
local notation "C" => Erdos1172LevyCohen.Algebra κ
local notation "VA" => Erdos1172BooleanUltrapower.Algebra U (anonymousAlgebra κ)
local notation "VC" => Erdos1172BooleanUltrapower.Algebra U (Erdos1172LevyCohen.Algebra κ)

abbrev BoundedAnonChildren (X : I → bSet A) := {t : Children U X // Supported U a (child U X t)}

/-- Pack a parameter family that factors through a single bounded fiber. -/
def SupportedEnv {V : Type*} (env : I → V → bSet A) : Prop :=
  ∃ η : θ.ord.ToType, ∃ G : Set θ.ord.ToType → V → bSet A,
    ∀ᶠ i in U, env i = G (boundedFiber θ a η i)

namespace SupportedEnv
variable {U a}

theorem atVar {V : Type*} {env : I → V → bSet A}
    (h : SupportedEnv U a env) (v : V) : Supported U a (fun i => env i v) := by
  obtain ⟨η, G, hG⟩ := h
  exact ⟨η, fun S => G S v, hG.mono fun _ hi => (congrFun hi v).symm⟩

theorem extend {V : Type*} {env : I → V → bSet A}
    (h : SupportedEnv U a env) {X : I → bSet A} (hX : Supported U a X) :
    SupportedEnv U a (fun i (o : Option V) => o.elim (X i) (env i)) := by
  obtain ⟨η, G, hG⟩ := h
  obtain ⟨ν, F, hF⟩ := hX
  refine ⟨max η ν, fun S o => o.elim (F (S ∩ Set.Iio ν)) (G (S ∩ Set.Iio η)), ?_⟩
  filter_upwards [hG, hF] with i hi hxi
  ext o
  cases o with
  | none =>
    simp only [Option.elim, boundedFiber_restrict θ a (le_max_right η ν), hxi]
  | some v =>
    simp only [Option.elim, boundedFiber_restrict θ a (le_max_left η ν), hi]

end SupportedEnv

variable [CountableInterFilter (U : Filter I)]

/-- Bounded hereditary ultrapower name over `anonymousAlgebra κ`. -/
def boundedAnonName : (I → bSet A) → bSet VA :=
  (familyChild_wf U).fix fun X rec => .mk (BoundedAnonChildren U a X)
    (fun t => rec (child U X t.val) (child_lt U X t.val)) (fun t => value U (weight U X t.val))

theorem boundedAnonName_unfold (X : I → bSet A) :
    boundedAnonName U a X = .mk (BoundedAnonChildren U a X)
      (fun t => boundedAnonName U a (child U X t.val)) (fun t => value U (weight U X t.val)) :=
  WellFounded.fix_eq _ _ _

local notation "liftA" => boundedAnonName (κ := κ) U a

def badAnonChild (x : bSet A) (P : bSet A → A) (c : C) : Prop :=
  ∃ k : x.type, c ⊓ inclusion A (x.bval k ⊓ P (x.func k)) ≠ ⊥

variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
variable (hκ : κ.IsInaccessible)

omit [CountableInterFilter (U : Filter I)] in
include hk hf hn ht hκ in
theorem bounded_child_exists_anonymous (X : I → bSet A) (P : I → bSet A → A)
    (hX : Supported U a X) (hP : Supported U a P) :
    value U (fun i => ⨆ k, (X i).bval k ⊓ P i ((X i).func k)) =
      ⨆ t : BoundedAnonChildren U a X,
        value U (weight U X t.val) ⊓ value U (fun i => P i (child U X t.val i)) := by
  classical
  let ι := inclusion A
  let sHom := scalarHom U ι
  let term (t : Children U X) : VA :=
    value U (weight U X t) ⊓ value U (fun i => P i (child U X t i))
  let lhs : VA := value U (fun i => ⨆ k, (X i).bval k ⊓ P i ((X i).func k))
  let rhs : VA := ⨆ t : BoundedAnonChildren U a X, term t.val
  apply le_antisymm
  · by_contra hnot
    have hdiff : lhs ⊓ rhsᶜ ≠ ⊥ := fun h0 =>
      hnot (disjoint_compl_right_iff.mp (disjoint_iff.mpr h0))
    have hsdiff : sHom (lhs ⊓ rhsᶜ) ≠ ⊥ := fun h0 =>
      hdiff ((scalarHom_injective U ι (inclusion_injective A)) (h0.trans (BotHomClass.map_bot sHom).symm))
    obtain ⟨g, hg_supp, hg_pos, hg_le⟩ := exists_supported_lower_bound_levyCohen U a hk hf hn ht hκ hsdiff
    have hs_lhs : sHom (lhs ⊓ rhsᶜ) ≤ sHom lhs := OrderHomClass.mono sHom inf_le_left
    have hs_rhs_disj : sHom (lhs ⊓ rhsᶜ) ⊓ sHom rhs ≤ ⊥ :=
      (completeHom_map_inf sHom (lhs ⊓ rhsᶜ) rhs).symm.le.trans
        ((OrderHomClass.mono sHom ((inf_le_inf inf_le_right le_rfl).trans compl_inf_eq_bot.le)).trans_eq
          (BotHomClass.map_bot sHom))
    have hg_lhs : ∀ᶠ i in U, g i ≤ ⨆ k, ι ((X i).bval k ⊓ P i ((X i).func k)) := by
      have h1 : value U g ≤ value U (fun i => ι (⨆ k, (X i).bval k ⊓ P i ((X i).func k))) :=
        (hg_le.trans hs_lhs).trans_eq (scalarHom_value U ι _)
      exact ((value_le_value_iff U).mp h1).mono fun i hi => hi.trans_eq (_root_.map_iSup ι _)
    have hbad : ∀ᶠ i in U, badAnonChild (X i) (P i) (g i) := (hg_pos.and hg_lhs).mono fun i ⟨hgi, hli⟩ => by
      by_contra hno
      have hall_compl : ∀ k, ι ((X i).bval k ⊓ P i ((X i).func k)) ≤ (g i)ᶜ := fun k =>
        le_compl_iff_disjoint_left.mpr (disjoint_iff.mpr (by_contra fun hk => hno ⟨k, hk⟩))
      have hgi_compl : g i ≤ (g i)ᶜ := hli.trans (iSup_le hall_compl)
      exact hgi (le_bot_iff.mp ((le_inf le_rfl hgi_compl).trans inf_compl_eq_bot.le))
    let t : Children U X := ⟨{i | badAnonChild (X i) (P i) (g i)}, hbad, fun i => i.property.choose⟩
    let pick (x : bSet A) (p : bSet A → A) (c : C) : bSet A :=
      if h : badAnonChild x p c then x.func h.choose else ∅
    have hsel : Supported U a (child U X t) := by
      apply ((hX.combine hP (fun x p => (x, p))).combine hg_supp (fun zp c => pick zp.1 zp.2 c)).congr
      filter_upwards [hbad] with i hi
      simp only [pick, dif_pos hi, child, t, Set.mem_ofPred_eq]
    have hterm_le : sHom (term t) ≤ sHom rhs :=
      OrderHomClass.mono sHom (le_iSup (fun s : BoundedAnonChildren U a X => term s.val) ⟨t, hsel⟩)
    have hterm_val : sHom (term t) = value U (fun i => ι (weight U X t i ⊓ P i (child U X t i))) := by
      change sHom (value U (weight U X t) ⊓ value U (fun i => P i (child U X t i))) = _
      rw [← value_inf, scalarHom_value]
    have hg_disj : value U g ⊓ sHom (term t) ≤ ⊥ :=
      (inf_le_inf hg_le hterm_le).trans hs_rhs_disj
    rw [hterm_val, ← value_inf, ← value_bot U] at hg_disj
    obtain ⟨i, hi_bad, hi_bot⟩ := (hbad.and ((value_le_value_iff U).mp hg_disj)).exists
    apply hi_bad.choose_spec
    change g i ⊓ ι (weight U X t i ⊓ P i (child U X t i)) ≤ ⊥ at hi_bot
    simpa only [weight, selected, child, t, Set.mem_ofPred_eq, dif_pos hi_bad, le_bot_iff] using hi_bot
  · exact (iSup_le fun t : BoundedAnonChildren U a X => le_iSup term t.val).trans_eq (value_bounded_exists U X P).symm

omit [CountableInterFilter (U : Filter I)] in
include hk hf hn ht hκ in
theorem bounded_child_forall_anonymous (X : I → bSet A) (P : I → bSet A → A)
    (hX : Supported U a X) (hP : Supported U a P) :
    value U (fun i => ⨅ k, (X i).bval k ⟹ P i ((X i).func k)) =
      ⨅ t : BoundedAnonChildren U a X,
        value U (weight U X t.val) ⟹ value U (fun i => P i (child U X t.val i)) := by
  apply compl_injective
  rw [← value_compl]
  simp only [compl_iInf, _root_.imp, compl_sup, compl_compl]
  exact (bounded_child_exists_anonymous U a hk hf hn ht hκ X (fun i y => (P i y)ᶜ) hX
    (hP.map (fun p y => (p y)ᶜ))).trans
    (iSup_congr fun t => congrArg (_ ⊓ ·) (value_compl U (fun i => P i (child U X t.val i))))

def halfAnon {D : Type u} [NontrivialCompleteBooleanAlgebra D]
    (x y : bSet D) (r : bSet D → bSet D → D) : D :=
  ⨅ k, x.bval k ⟹ ⨆ l, y.bval l ⊓ r (x.func k) (y.func l)

private theorem eq_halvesAnon {D : Type u} [NontrivialCompleteBooleanAlgebra D] (x y : bSet D) :
    (x =ᴮ y) = halfAnon x y bv_eq ⊓ halfAnon y x (fun w v => v =ᴮ w) := by cases x; cases y; rfl

omit [CountableInterFilter (U : Filter I)] in
include hk hf hn ht hκ in
private theorem bounded_half_anonymous (X Y : I → bSet A) (hX : Supported U a X) (hY : Supported U a Y)
    (r : bSet A → bSet A → A) :
    value U (fun i => halfAnon (X i) (Y i) r) =
      ⨅ t : BoundedAnonChildren U a X, value U (weight U X t.val) ⟹
        ⨆ s : BoundedAnonChildren U a Y, value U (weight U Y s.val) ⊓
          value U (fun i => r (child U X t.val i) (child U Y s.val i)) := by
  unfold halfAnon
  let P (y : bSet A) (v : bSet A) := ⨆ l, y.bval l ⊓ r v (y.func l)
  apply (bounded_child_forall_anonymous U a hk hf hn ht hκ X (fun i => P (Y i)) hX (hY.map P)).trans
  apply iInf_congr
  intro t
  exact congrArg (imp _) (bounded_child_exists_anonymous U a hk hf hn ht hκ Y
    (fun i => r (child U X t.val i)) hY (t.property.map r))

private theorem lifted_half_anonymous (X Y : I → bSet A) (r : bSet VA → bSet VA → VA) :
    halfAnon (liftA X) (liftA Y) r =
      ⨅ t : BoundedAnonChildren U a X, value U (weight U X t.val) ⟹
        ⨆ s : BoundedAnonChildren U a Y, value U (weight U Y s.val) ⊓
          r (liftA (child U X t.val)) (liftA (child U Y s.val)) := by
  conv_lhs => rw [boundedAnonName_unfold (κ := κ) U a X, boundedAnonName_unfold (κ := κ) U a Y]
  rfl

include hk hf hn ht hκ in
theorem boundedAnonName_eq (X Y : I → bSet A) (hX : Supported U a X) (hY : Supported U a Y) :
    value U (fun i => X i =ᴮ Y i) = (liftA X =ᴮ liftA Y) := by
  let goal (X : I → bSet A) := ∀ Y : I → bSet A, Supported U a X → Supported U a Y →
    value U (fun i => X i =ᴮ Y i) = (liftA X =ᴮ liftA Y)
  suffices all : ∀ X, goal X from all X Y hX hY
  intro X
  apply (familyChild_wf («B» := A) U).induction X
  intro X ih
  show goal X
  intro Y hX hY
  rw [eq_halvesAnon (liftA X) (liftA Y), lifted_half_anonymous U a X Y,
    lifted_half_anonymous U a Y X]
  simp only [eq_halvesAnon (X _) (Y _), value_inf,
    bounded_half_anonymous U a hk hf hn ht hκ X Y hX hY,
    bounded_half_anonymous U a hk hf hn ht hκ Y X hY hX]
  apply congrArg₂ (· ⊓ ·)
  · apply iInf_congr
    intro t
    apply congrArg (imp _)
    apply iSup_congr
    intro s
    exact congrArg (_ ⊓ ·) (ih _ (child_lt U X t.val) _ t.property s.property)
  · apply iInf_congr
    intro s
    apply congrArg (imp _)
    apply iSup_congr
    intro t
    exact congrArg (_ ⊓ ·) (ih _ (child_lt U X t.val) _ t.property s.property)

include hk hf hn ht hκ in
theorem boundedAnonName_mem (X Y : I → bSet A) (hX : Supported U a X) (hY : Supported U a Y) :
    value U (fun i => X i ∈ᴮ Y i) = (liftA X ∈ᴮ liftA Y) := by
  simp only [mem_unfold]
  apply (bounded_child_exists_anonymous U a hk hf hn ht hκ Y (fun i y => X i =ᴮ y) hY (hX.map bv_eq)).trans
  conv_rhs => rw [boundedAnonName_unfold (κ := κ) U a Y]
  apply iSup_congr
  intro t
  exact congrArg (_ ⊓ ·) (boundedAnonName_eq U a hk hf hn ht hκ X _ hX t.property)

include hk hf hn ht hκ in
theorem boundedAnonName_subset (X Y : I → bSet A) (hX : Supported U a X) (hY : Supported U a Y) :
    value U (fun i => X i ⊆ᴮ Y i) = (liftA X ⊆ᴮ liftA Y) := by
  simp only [subset_unfold]
  apply (bounded_child_forall_anonymous U a hk hf hn ht hκ X (fun i x => x ∈ᴮ Y i) hX
    (hY.map (fun y x => x ∈ᴮ y))).trans
  conv_rhs => rw [boundedAnonName_unfold (κ := κ) U a X]
  apply iInf_congr
  intro t
  exact congrArg (imp _) (boundedAnonName_mem U a hk hf hn ht hκ _ Y t.property hY)

private theorem boundedAnonName_subset_test (X : I → bSet A) (Z : bSet VA)
    (h : ∀ W : I → bSet A, Supported U a W → value U (fun i => W i ∈ᴮ X i) ≤ liftA W ∈ᴮ Z) :
    (⊤ : VA) ≤ liftA X ⊆ᴮ Z := by
  rw [boundedAnonName_unfold (κ := κ) U a X, subset_unfold]
  apply le_iInf
  intro t
  rw [← deduction]
  apply inf_le_right.trans ((value_le_value_iff U).mpr ?_ |>.trans (h (child U X t.val) t.property))
  filter_upwards [t.val.large] with i hi
  simpa only [weight, selected, child, dif_pos hi] using (mem_mk' (X i) (t.val.pick ⟨i, hi⟩))

theorem boundedAnonName_empty :
    (⊤ : VA) ≤ liftA (fun _ => (∅ : bSet A)) =ᴮ (∅ : bSet VA) := by
  apply subset_ext _ empty_subset
  apply boundedAnonName_subset_test
  intro W _
  have hemp (z : bSet A) : (z ∈ᴮ (∅ : bSet A)) = ⊥ := bot_unique (bot_of_mem_empty le_rfl)
  simp only [hemp, value_bot, bot_le]

include hk hf hn ht hκ in
theorem boundedAnonName_insert (X Y : I → bSet A) (hX : Supported U a X) (hY : Supported U a Y) :
    (⊤ : VA) ≤ liftA (fun i => insert (X i) (Y i)) =ᴮ insert (liftA X) (liftA Y) := by
  let F := fun i => insert (X i) (Y i)
  have hF : Supported U a F := hX.combine hY insert
  apply subset_ext
  · apply boundedAnonName_subset_test
    intro W hW
    simp only [mem_insert1, value_sup,
      boundedAnonName_eq U a hk hf hn ht hκ W X hW hX,
      boundedAnonName_mem U a hk hf hn ht hκ W Y hW hY]
    exact le_rfl
  · have hx : (⊤ : VA) ≤ liftA X ∈ᴮ liftA F := by
      rw [← boundedAnonName_mem U a hk hf hn ht hκ X F hX hF, ← value_top U]
      apply (value_le_value_iff U).mpr (Eventually.of_forall fun i => ?_)
      change (⊤ : A) ≤ X i ∈ᴮ insert (X i) (Y i)
      rw [mem_insert1, bv_eq_refl, top_sup_eq]
    have hy : (⊤ : VA) ≤ liftA Y ⊆ᴮ liftA F := by
      rw [← boundedAnonName_subset U a hk hf hn ht hκ Y F hY hF, ← value_top U]
      apply (value_le_value_iff U).mpr (Eventually.of_forall fun i => ?_)
      rw [subset_unfold']
      refine le_iInf fun y => ?_
      rw [← deduction, top_inf_eq, show F i = _ from rfl, mem_insert1]
      exact le_sup_right
    rw [subset_unfold']
    refine le_iInf fun z => ?_
    rw [← deduction, top_inf_eq, mem_insert1]
    exact sup_le (bv_rw' le_rfl (h_congr := B_ext_mem_left) (H_new := le_top.trans hx))
      (mem_of_mem_subset (le_top.trans hy) le_rfl)

include hk hf hn ht hκ in
private theorem boundedAnon_insert_congr (X Y : I → bSet A) {x y : bSet VA}
    (hX : Supported U a X) (hY : Supported U a Y)
    (hx : (⊤ : VA) ≤ liftA X =ᴮ x) (hy : (⊤ : VA) ≤ liftA Y =ᴮ y) :
    (⊤ : VA) ≤ liftA (fun i => insert (X i) (Y i)) =ᴮ insert x y :=
  bv_trans (boundedAnonName_insert U a hk hf hn ht hκ X Y hX hY)
    (bv_trans (B_congr_insert1_left hx) (B_congr_insert1_right hy))

include hk hf hn ht hκ in
theorem boundedAnonName_pair [Nonempty θ.ord.ToType]
    (X Y : I → bSet A) (hX : Supported U a X) (hY : Supported U a Y) :
    (⊤ : VA) ≤ liftA (fun i => pair (X i) (Y i)) =ᴮ pair (liftA X) (liftA Y) := by
  have single (W : I → bSet A) (hW : Supported U a W) :
      (⊤ : VA) ≤ liftA (fun i => ({W i} : bSet A)) =ᴮ {liftA W} :=
    boundedAnon_insert_congr U a hk hf hn ht hκ W (fun _ => ∅) hW (Supported.const _)
      bv_refl (boundedAnonName_empty U a)
  exact boundedAnon_insert_congr U a hk hf hn ht hκ _ _
    (hX.map fun w => ({w} : bSet A))
    ((hX.combine hY fun w z => insert w ({z} : bSet A)).map fun u => insert u (∅ : bSet A))
    (single X hX)
    (boundedAnon_insert_congr U a hk hf hn ht hκ _ _
      (hX.combine hY fun w z => insert w ({z} : bSet A)) (Supported.const _)
      (boundedAnon_insert_congr U a hk hf hn ht hκ X _ hX (hY.map fun z => ({z} : bSet A))
        bv_refl (single Y hY))
      (boundedAnonName_empty U a))

include hk hf hn ht hκ in
theorem boundedAnonName_edge [Nonempty θ.ord.ToType]
    (R X Y : I → bSet A)
    (hR : Supported U a R) (hX : Supported U a X) (hY : Supported U a Y) :
    value U (fun i => edge (R i) (X i) (Y i)) = edge (liftA R) (liftA X) (liftA Y) := by
  unfold edge
  rw [boundedAnonName_mem U a hk hf hn ht hκ (fun i => pair (X i) (Y i)) R (hX.combine hY pair) hR]
  exact (bv_rw (top_unique (boundedAnonName_pair U a hk hf hn ht hκ X Y hX hY))
    (fun z => z ∈ᴮ liftA R) (h_congr := B_ext_mem_left)).symm

include hk hf hn ht hκ in
theorem boundedAnonName_allIn (F : I → bSet A) (P : I → bSet A → A) (Q : bSet VA → VA)
    (hF : Supported U a F) (hP : Supported U a P)
    (pExt : ∀ i, B_ext (P i)) (qExt : B_ext Q)
    (commutes : ∀ X : I → bSet A, Supported U a X → value U (fun i => P i (X i)) = Q (liftA X)) :
    value U (fun i => allIn (F i) (P i)) = allIn (liftA F) Q := by
  have source (i : I) : allIn (F i) (P i) =
      ⨅ k : (F i).type, (F i).bval k ⟹ P i ((F i).func k) :=
    (bounded_forall (h_congr := pExt i)).symm
  have target : allIn (liftA F) Q =
      ⨅ t : BoundedAnonChildren U a F, value U (weight U F t.val) ⟹ Q (liftA (child U F t.val)) := by
    apply (bounded_forall (v := liftA F) (h_congr := qExt)).symm.trans
    conv_lhs => rw [boundedAnonName_unfold (κ := κ) U a F]
    rfl
  rw [target]
  calc
    _ = _ := congrArg (value U) (_root_.funext source)
    _ = _ := bounded_child_forall_anonymous U a hk hf hn ht hκ F P hF hP
    _ = _ := iInf_congr fun t => congrArg (value U (weight U F t.val) ⟹ ·)
      (commutes (child U F t.val) t.property)

include hk hf hn ht hκ in
theorem boundedAnonName_someIn (F : I → bSet A) (P : I → bSet A → A) (Q : bSet VA → VA)
    (hF : Supported U a F) (hP : Supported U a P)
    (pExt : ∀ i, B_ext (P i)) (qExt : B_ext Q)
    (commutes : ∀ X : I → bSet A, Supported U a X → value U (fun i => P i (X i)) = Q (liftA X)) :
    value U (fun i => someIn (F i) (P i)) = someIn (liftA F) Q := by
  have source (i : I) : someIn (F i) (P i) =
      ⨆ k : (F i).type, (F i).bval k ⊓ P i ((F i).func k) :=
    (bounded_exists (h_congr := pExt i)).symm
  have target : someIn (liftA F) Q =
      ⨆ t : BoundedAnonChildren U a F, value U (weight U F t.val) ⊓ Q (liftA (child U F t.val)) := by
    apply (bounded_exists (v := liftA F) (h_congr := qExt)).symm.trans
    conv_lhs => rw [boundedAnonName_unfold (κ := κ) U a F]
    rfl
  rw [target]
  calc
    _ = _ := congrArg (value U) (_root_.funext source)
    _ = _ := bounded_child_exists_anonymous U a hk hf hn ht hκ F P hF hP
    _ = _ := iSup_congr fun t => congrArg (value U (weight U F t.val) ⊓ ·)
      (commutes (child U F t.val) t.property)

variable [Nonempty θ.ord.ToType]

include hk hf hn ht hκ in
/-- Full Δ₀ Łoś transfer for `InterpretedMaster.Formula` under `boundedAnonName` on any
uniformly `SupportedEnv` environment. -/
theorem boundedAnon_formula_eval {V : Type*} (p : InterpretedMaster.Formula V) :
    ∀ (env : I → V → bSet A), SupportedEnv U a env →
      value U (fun i => p.eval (env i)) = p.eval (fun v => liftA (fun i => env i v)) := by
  induction p with
  | mem x y =>
    intro env henv
    exact boundedAnonName_mem U a hk hf hn ht hκ _ _ (henv.atVar x) (henv.atVar y)
  | eq x y =>
    intro env henv
    exact boundedAnonName_eq U a hk hf hn ht hκ _ _ (henv.atVar x) (henv.atVar y)
  | edge r x y =>
    intro env henv
    exact boundedAnonName_edge U a hk hf hn ht hκ _ _ _ (henv.atVar r) (henv.atVar x) (henv.atVar y)
  | imp p q hp hq =>
    intro env henv
    exact (value_imp U _ _).trans (congrArg₂ _ (hp env henv) (hq env henv))
  | both p q hp hq =>
    intro env henv
    exact (value_inf U _ _).trans (congrArg₂ _ (hp env henv) (hq env henv))
  | either p q hp hq =>
    intro env henv
    exact (value_sup U _ _).trans (congrArg₂ _ (hp env henv) (hq env henv))
  | neg p hp =>
    intro env henv
    exact (value_compl U _).trans (congrArg (·ᶜ) (hp env henv))
  | @allIn W t p hp =>
    intro env henv
    have hP : Supported U a (fun i z => p.eval (fun o => o.elim z (env i))) := by
      obtain ⟨η, G, hG⟩ := henv
      exact ⟨η, fun S z => p.eval (fun o => o.elim z (G S)),
        hG.mono fun _ hi => _root_.funext fun z => congrArg p.eval (_root_.funext fun o => by
          cases o <;> simp [hi])⟩
    have boundExt {D : Type u} [NontrivialCompleteBooleanAlgebra D] (e : W → bSet D) :
        B_ext (fun z => p.eval (fun o => o.elim z e)) :=
      p.eval_ext _ (fun o => by cases o with
        | none => exact id_congr
        | some v => exact const_congr _)
    apply boundedAnonName_allIn U a hk hf hn ht hκ (fun i => env i t)
      (fun i z => p.eval (fun o => o.elim z (env i)))
      (fun z => p.eval (fun o => o.elim z (fun v => liftA (fun i => env i v))))
      (henv.atVar t) hP (fun i => boundExt (env i)) (boundExt _)
    intro X hX
    apply (hp (fun i o => o.elim (X i) (env i)) (henv.extend hX)).trans
    exact congrArg p.eval (_root_.funext fun o => by cases o <;> rfl)
  | @someIn W t p hp =>
    intro env henv
    have hP : Supported U a (fun i z => p.eval (fun o => o.elim z (env i))) := by
      obtain ⟨η, G, hG⟩ := henv
      exact ⟨η, fun S z => p.eval (fun o => o.elim z (G S)),
        hG.mono fun _ hi => _root_.funext fun z => congrArg p.eval (_root_.funext fun o => by
          cases o <;> simp [hi])⟩
    have boundExt {D : Type u} [NontrivialCompleteBooleanAlgebra D] (e : W → bSet D) :
        B_ext (fun z => p.eval (fun o => o.elim z e)) :=
      p.eval_ext _ (fun o => by cases o with
        | none => exact id_congr
        | some v => exact const_congr _)
    apply boundedAnonName_someIn U a hk hf hn ht hκ (fun i => env i t)
      (fun i z => p.eval (fun o => o.elim z (env i)))
      (fun z => p.eval (fun o => o.elim z (fun v => liftA (fun i => env i v))))
      (henv.atVar t) hP (fun i => boundExt (env i)) (boundExt _)
    intro X hX
    apply (hp (fun i o => o.elim (X i) (env i)) (henv.extend hX)).trans
    exact congrArg p.eval (_root_.funext fun o => by cases o <;> rfl)

omit [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] in
private theorem supportedZFAnon {F : I → ZFSet.{u}} (hF : Supported U a F) :
    BoundedSupport U θ a (Germ.ofFun F) :=
  let ⟨η, f, h⟩ := hF
  ⟨η, f, Germ.coe_eq.mpr h⟩

omit [Nonempty θ.ord.ToType] in
include hk hf hn ht hκ in
private theorem boundedAnon_congr {X Y : I → bSet A} (hx : Supported U a X) (hy : Supported U a Y)
    (he : ∀ᶠ i in U, (X i =ᴮ Y i) = ⊤) : (⊤ : VA) ≤ liftA X =ᴮ liftA Y := by
  rw [← boundedAnonName_eq U a hk hf hn ht hκ _ _ hx hy,
    value_eq_of_eventuallyEq U (g := fun _ => ⊤) he, value_top]

omit [Nonempty θ.ord.ToType] in
include hk hf hn ht hκ in
/-- `boundedAnonName` of a `Supported U a` family of checked sets equals the check of its
`boundedCollapse` image. -/
theorem boundedAnon_checked_family (v : BoundedHull U θ a) :
    ∀ (F : I → PSet.{u}), Supported U a F → Germ.ofFun (fun i => ZFSet.mk (F i)) = v.val →
      (⊤ : VA) ≤ liftA (fun i => check (F i)) =ᴮ check (boundedCollapse U θ a v).out := by
  classical
  induction v using (boundedMem_wf U θ a).induction with
  | h v ih =>
    intro F hF hv
    let X (i : I) : bSet A := check (F i)
    have hx : Supported U a X := hF.map check
    apply subset_ext
    · rw [boundedAnonName_unfold (κ := κ) U a (fun i => check (F i)), subset_unfold]
      apply le_iInf
      intro t
      rw [← deduction, top_inf_eq]
      let ch := child U X t.val
      let good (x : bSet A) (P : PSet.{u}) := ∃ H : PSet.{u}, x = check H ∧ H ∈ P
      let get (x : bSet A) (P : PSet.{u}) := if h : good x P then h.choose else ∅
      let D (i : I) := get (ch i) (F i)
      have hd : Supported U a D := t.property.combine hF get
      have ok : ∀ᶠ i in U, ch i = check (D i) ∧ D i ∈ F i := by
        filter_upwards [t.val.large] with i hi
        have g : good (ch i) (F i) := by
          change good (child U X t.val i) (F i)
          rw [child, dif_pos hi]
          let k := t.val.pick ⟨i, hi⟩
          exact ⟨(F i).Func (check_cast k), check_func, PSet.func_mem _ _⟩
        simpa only [D, get, dif_pos g] using g.choose_spec
      let w : BoundedHull U θ a := ⟨Germ.ofFun (fun i => ZFSet.mk (D i)), supportedZFAnon U a (hd.map ZFSet.mk)⟩
      have mem : boundedMem U θ a w v := by
        change memRel U _ v.val
        rw [← hv]
        exact ok.mono fun _ hi => ZFSet.mk_mem_iff.mpr hi.2
      have hc := boundedAnon_congr U a hk hf hn ht hκ t.property (hd.map check)
        (ok.mono fun i hi => by rw [show child U X t.val i = check (D i) from hi.1]; exact top_unique bv_refl)
      have eq := bv_trans hc (ih w mem D hd rfl)
      have hw : (boundedCollapse U θ a w).out ∈ (boundedCollapse U θ a v).out := by
        apply PSet.mem_iff.mpr
        simpa only [ZFSet.mk_out] using (mem_boundedCollapse_iff U θ a _ _).mpr ⟨w, mem, rfl⟩
      exact subst_congr_mem_left' (bv_symm (le_top.trans eq)) (check_mem hw)
    · rw [subset_unfold]
      apply le_iInf
      intro k
      rw [← deduction, top_inf_eq]
      let x := (boundedCollapse U θ a v).out.Func (check_cast k)
      have hx' : ZFSet.mk x ∈ boundedCollapse U θ a v := by
        have h := PSet.mem_iff.mp (PSet.func_mem (boundedCollapse U θ a v).out (check_cast k))
        simpa only [ZFSet.mk_out] using h
      obtain ⟨w, hm, he⟩ := (mem_boundedCollapse_iff U θ a _ _).mp hx'
      obtain ⟨η, g, hg⟩ := w.property
      let D (i : I) := (g (boundedFiber θ a η i)).out
      have hd : Supported U a D := ⟨η, fun S => (g S).out, EventuallyEq.rfl⟩
      have hw : Germ.ofFun (fun i => ZFSet.mk (D i)) = w.val := by simpa only [D, ZFSet.mk_out] using hg
      have truth : ∀ᶠ i in U, D i ∈ F i := by
        change memRel U w.val v.val at hm
        rw [← hw, ← hv] at hm
        exact hm.mono fun _ hi => ZFSet.mk_mem_iff.mp hi
      have hit : (⊤ : VA) ≤ liftA (fun i => check (D i)) ∈ᴮ liftA X := by
        rw [← boundedAnonName_mem U a hk hf hn ht hκ _ _ (hd.map check) hx]
        rw [value_eq_of_eventuallyEq U (g := fun _ => ⊤) (truth.mono fun _ hi => check_mem_iff.mp hi), value_top]
      have topEq := ih w hm D hd hw
      have groundEq : PSet.Equiv (boundedCollapse U θ a w).out x := PSet.equiv_iff_eq.mpr ((ZFSet.mk_out _).trans he)
      have eq := bv_trans topEq (check_bv_eq groundEq)
      rw [show (check (boundedCollapse U θ a v).out : bSet VA).func k = check x from check_func]
      exact le_top.trans (subst_congr_mem_left' eq hit)

include hk hf hn ht hκ in
theorem boundedAnon_checked (x : PSet.{u}) :
    (⊤ : VA) ≤ liftA (fun _ => check x) =ᴮ
      check (boundedCollapse U θ a (boundedConst U θ a (ZFSet.mk x))).out :=
  boundedAnon_checked_family U a hk hf hn ht hκ (boundedConst U θ a (ZFSet.mk x))
    (fun _ => x) (Supported.const _) rfl

include hk hf hn ht hκ in
theorem boundedAnon_ordinal (o : Ordinal.{u}) :
    (⊤ : VA) ≤ liftA (fun _ => check (PSet.ordinalMk o)) =ᴮ
      check (PSet.ordinalMk (ordinalImage U a o)) := by
  apply bv_trans (boundedAnon_checked U a hk hf hn ht hκ (PSet.ordinalMk o))
  apply check_bv_eq
  apply PSet.equiv_iff_eq.mpr
  exact (ZFSet.mk_out _).trans (ordinalImage_code U a o).symm

include hk hf hn ht hκ in
theorem boundedAnon_fix_below [CardinalInterFilter (U : Filter I) κ]
    {α : Ordinal.{u}} (hα : α < κ.ord) :
    (⊤ : VA) ≤ liftA (fun _ => check (PSet.ordinalMk α)) =ᴮ check (PSet.ordinalMk α) := by
  apply bv_trans (boundedAnon_ordinal U a hk hf hn ht hκ α)
  have heq : ordinalImage U a α = α :=
    Ordinal.toZFSet_injective ((ordinalImage_code U a α).trans
      (boundedGroundEmbedding_fix_below U κ θ a α hα))
  rw [heq]
  exact bv_refl

include hf hn ht hκ in
theorem boundedAnon_seed (hk' : κ < θ) :
    let seed := criticalOrdinalPoint U a hf hn ht hk'
    (⊤ : VA) ≤ liftA (fun i => check (PSet.ordinalMk (repr U a seed i).toOrd.val)) =ᴮ
      check (PSet.ordinalMk κ.ord) := by
  intro seed
  let S (i : I) := PSet.ordinalMk (repr U a seed i).toOrd.val
  have supp : Supported U a S := ⟨seed.property.choose,
    fun t => PSet.ordinalMk ((seed.property.choose_spec.choose t).toOrd.val), EventuallyEq.rfl⟩
  let v : BoundedHull U θ a := ⟨Germ.map Erdos1172Shioya.UltrapowerStage.ordinalLabel seed.val, by
    obtain ⟨η, g, hg⟩ := seed.property
    exact ⟨η, Erdos1172Shioya.UltrapowerStage.ordinalLabel ∘ g,
      congrArg (Germ.map Erdos1172Shioya.UltrapowerStage.ordinalLabel) hg⟩⟩
  have hw : Germ.ofFun (fun i => ZFSet.mk (S i)) = v.val :=
    congrArg (Germ.map Erdos1172Shioya.UltrapowerStage.ordinalLabel) (repr_eq U a seed)
  have hv : boundedCollapse U θ a v = κ.ord.toZFSet :=
    (indexEquiv_label U a _ seed).symm.trans
      (congrArg Ordinal.toZFSet (criticalOrdinalPoint_ord U a hf hn ht hk'))
  apply bv_trans (boundedAnon_checked_family U a hk'.le hf hn ht hκ v S supp hw)
  exact check_bv_eq (PSet.equiv_iff_eq.mpr ((ZFSet.mk_out _).trans hv))

include hk hf hn ht hκ in
theorem boundedAnon_omegaOne :
    (⊤ : VA) ≤ liftA (fun _ => (omegaOne : bSet A)) =ᴮ check (PSet.ordinalMk θ.ord) := by
  have heq_ord : ordinalImage U a κ.ord = θ.ord :=
    Ordinal.toZFSet_injective ((ordinalImage_code U a κ.ord).trans
      (boundedDiagonal_critical_image U κ θ a hf hn ht))
  have h1 : (⊤ : VA) ≤ liftA (fun _ => (omegaOne : bSet A)) =ᴮ
      liftA (fun _ => check (PSet.ordinalMk κ.ord)) :=
    boundedAnon_congr U a hk hf hn ht hκ (Supported.const _) (Supported.const _)
      (Eventually.of_forall fun _ =>
        top_unique (bv_symm (anonymous_checked_upper_eq_omegaOne κ hκ)))
  have h2 := boundedAnon_ordinal U a hk hf hn ht hκ κ.ord
  rw [heq_ord] at h2
  exact bv_trans h1 h2

end BoundedAnonymousNames

end Erdos1172LevyCollapse.Preparation
