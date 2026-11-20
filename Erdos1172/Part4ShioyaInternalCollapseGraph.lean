/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCollapseLift
public import Erdos1172.Part4ShioyaInternalCohenInfima

@[expose] public section

/-! # The named graph of the native collapse path projection -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosBoundedFunctionValue ErdosBoundedImageRecursion ErdosRelationGraph ErdosPartialInjection
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def paths (K P : N) : N :=
  comprehend (fun f => ⨆ l : N, (l ∈ᴮ K) ⊓ is_function l P f) (bv_powerset (prod K P))

theorem paths_mem {Γ : B} {K P f : N} (ord : Γ ≤ Ord K) :
    Γ ≤ f ∈ᴮ paths K P ↔ ∃ l : N, Γ ≤ l ∈ᴮ K ∧ Γ ≤ is_function l P f := by
  rw [paths,mem_comprehend_and (B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_is_function_right))]
  constructor
  · intro h
    obtain ⟨l,hl⟩ := exists_convert h.2 (B_ext_inf B_ext_mem_left B_ext_is_function_left)
    exact ⟨l,hl.trans inf_le_left,hl.trans inf_le_right⟩
  · rintro ⟨l,hl,hf⟩
    exact ⟨mem_powerset_iff.mpr (subset_trans' (subset_prod_of_is_function hf)
      (prod_domain_mono (subset_of_mem_transitive (ord.trans inf_le_right) hl))),le_iSup_of_le l (le_inf hl hf)⟩

def finalTest (P R l h p : N) : B := (p ∈ᴮ P) ⊓ allIn P (fun x =>
  let kept := survives (image l (bv_powerset P) h) x
  (kept ⟹ edge R x p) ⊓ (edge R x p ⟹ kept))

theorem finalTest_iff {P R l h p : N} {Γ : B} : Γ ≤ finalTest P R l h p ↔ Represents Γ P R l h p := by
  constructor
  · intro y
    refine ⟨y.trans inf_le_left,?_⟩
    intro Δ hd x hx
    have v := allIn_elim (hd.trans (y.trans inf_le_right)) hx
    exact ⟨projection_imp.mp (v.trans inf_le_left) Δ le_rfl,projection_imp.mp (v.trans inf_le_right) Δ le_rfl⟩
  · rintro ⟨hp,h⟩
    exact le_inf hp (allIn_intro fun hd x hx => le_inf
      (projection_imp.mpr fun _ hb => (h (hb.trans hd) (hb.trans hx)).mp)
      (projection_imp.mpr fun _ hb => (h (hb.trans hd) (hb.trans hx)).mpr))

def branch (K P R f p l h : N) : B := (l ∈ᴮ K) ⊓ (is_function l P f ⊓
  (is_function l (bv_powerset P) h ⊓ (trace P R f h ⊓ finalTest P R l h p)))

def value (K P R f p : N) : B := ⨆ l : N, ⨆ h : N, branch K P R f p l h

private theorem value_left (K P R p : N) : B_ext (fun f => value K P R f p) := by
  have tr (h : N) : B_ext (fun f => trace P R f h) := B_ext_iInf (h := fun i => B_ext_iInf (h := fun y =>
    B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_term (fun z => y =ᴮ z) _ B_ext_bv_eq_right
      (fun eq => next_congr (graphValue_congr_graph P i eq) bv_refl))))
  exact B_ext_iSup (h := fun _ => B_ext_iSup (h := fun h => B_ext_inf B_ext_const
    (B_ext_inf B_ext_is_function_right (B_ext_inf B_ext_const (B_ext_inf (tr h) B_ext_const)))))

private theorem value_right (K P R f : N) : B_ext (value K P R f) := by
  have fin (l h : N) : B_ext (finalTest P R l h) := B_ext_inf B_ext_mem_left (allIn_ext (const_congr P)
    (fun _ => B_ext_inf (B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_pair_mem_right))
      (B_ext_imp (h₁ := B_ext_pair_mem_right) (h₂ := B_ext_const))))
  exact B_ext_iSup (h := fun l => B_ext_iSup (h := fun h => B_ext_inf B_ext_const (B_ext_inf B_ext_const
    (B_ext_inf B_ext_const (B_ext_inf B_ext_const (fin l h))))))

theorem value_of_trace {Γ : B} {K P R f p l h : N} (hl : Γ ≤ l ∈ᴮ K) (hf : Γ ≤ is_function l P f)
    (hh : Γ ≤ is_function l (bv_powerset P) h) (law : Γ ≤ trace P R f h) (out : Represents Γ P R l h p) :
    Γ ≤ value K P R f p := le_iSup_of_le l (le_iSup_of_le h (le_inf hl (le_inf hf (le_inf hh
      (le_inf law (finalTest_iff.mpr out))))))

theorem value_cases {Γ goal : B} {K P R f p : N} (v : Γ ≤ value K P R f p)
    (step : ∀ {d : B}, d ≤ Γ → ∀ l h : N, d ≤ l ∈ᴮ K → d ≤ is_function l P f →
      d ≤ is_function l (bv_powerset P) h → d ≤ trace P R f h → Represents d P R l h p → d ≤ goal) : Γ ≤ goal := by
  apply (le_inf le_rfl v).trans
  rw [value,inf_iSup_eq]
  apply iSup_le
  intro l
  rw [inf_iSup_eq]
  apply iSup_le
  intro h
  have r := (inf_le_right : Γ ⊓ branch K P R f p l h ≤ branch K P R f p l h)
  have p₁ := r.trans inf_le_right
  have p₂ := p₁.trans inf_le_right
  have p₃ := p₂.trans inf_le_right
  exact step inf_le_left l h (r.trans inf_le_left) (p₁.trans inf_le_left) (p₂.trans inf_le_left)
    (p₃.trans inf_le_left) (finalTest_iff.mp (p₃.trans inf_le_right))

private theorem Represents.mono {Γ Δ : B} {P R l h p : N} (v : Represents Γ P R l h p) (hd : Δ ≤ Γ) :
    Represents Δ P R l h p := ⟨hd.trans v.1,fun e _ hx => v.2 (e.trans hd) hx⟩

theorem value_monotone {Γ : B} {K P R f g x y : N} (ok : Γ ≤ Ord K) (po : Γ ≤ partialOrderValue P R)
    (sub : Γ ≤ f ⊆ᴮ g) (old : Γ ≤ value K P R f x) (new : Γ ≤ value K P R g y) : Γ ≤ edge R y x := by
  apply value_cases old
  intro d hd a h ha hf hh hl out
  apply value_cases (hd.trans new)
  intro c hc b k _ hg hk kl out'
  have cg := hc.trans hd
  exact evaluation_mono (cg.trans po) (Ord_of_mem_Ord (hc.trans ha) (cg.trans ok)) (hc.trans hf) hg
    (cg.trans sub) (hc.trans hh) hk (hc.trans hl) kl (out.mono hc) out'

def graph (K P R : N) : N := relationGraph (paths K P) P (value K P R)

theorem graph_pair {Γ : B} {K P R f p : N} : Γ ≤ edge (graph K P R) f p ↔
    Γ ≤ f ∈ᴮ paths K P ∧ Γ ≤ p ∈ᴮ P ∧ Γ ≤ value K P R f p :=
  mem_relationGraph_iff (value_left K P R) (value_right K P R)

theorem graph_function {Γ : B} {K P R : N} (ok : Γ ≤ Ord K) (po : Γ ≤ partialOrderValue P R)
    (cl : Γ ≤ shortInfimaValue K P R) : Γ ≤ is_function (paths K P) P (graph K P R) := by
  apply relationGraph_is_function (value_left K P R) (value_right K P R)
  · refine le_iInf fun f => projection_imp.mpr ?_
    intro Δ hd h
    obtain ⟨l,hl,hf⟩ := (paths_mem (hd.trans ok)).mp h
    obtain ⟨k,p,hk,law,hp,char⟩ := exists_evaluation (hd.trans po) (hd.trans cl) (hd.trans ok) hl hf
    exact le_iSup_of_le p (le_inf hp (value_of_trace hl hf hk law ⟨hp,char⟩))
  · intro f g x y Δ hd _ _ hx hy old new eq
    have both := allIn_elim (allIn_elim ((hd.trans po).trans (inf_le_right.trans (inf_le_right.trans inf_le_left))) hx) hy
    exact projection_imp.mp both Δ le_rfl (le_inf
      (value_monotone (hd.trans ok) (hd.trans po) (subset_of_eq (bv_symm eq)) new old)
      (value_monotone (hd.trans ok) (hd.trans po) (subset_of_eq eq) old new))

theorem graph_lifts {Γ : B} {K P R : N} (ok : Γ ≤ Ord K) (po : Γ ≤ partialOrderValue P R)
    (lim : ∀ {Δ : B}, Δ ≤ Γ → ∀ {a : N}, Δ ≤ a ∈ᴮ K → Δ ≤ succ a ∈ᴮ K) :
    Γ ≤ projectionLifts P (extensionOrder (paths K P)) R (graph K P R) := by
  refine le_iInf fun f => le_iInf fun x => le_iInf fun q => projection_imp.mpr ?_
  intro Δ hd h
  have e := graph_pair.mp (h.trans (inf_le_left.trans inf_le_left))
  apply value_cases e.2.2
  intro d dd l k hl hf hk law out
  have base := dd.trans hd
  have hq := dd.trans (h.trans (inf_le_left.trans inf_le_right))
  obtain ⟨g,t,fg,hs,hg,ht,htr,rep⟩ := exists_exact_lift (base.trans po) (Ord_of_mem_Ord hl (base.trans ok))
    (lim base hl) hf hk law out hq (dd.trans (h.trans inf_le_right))
  have member := (paths_mem (base.trans ok)).mpr ⟨_,hs,hg⟩
  exact le_iSup_of_le g (le_iSup_of_le q (le_inf (le_inf (graph_pair.mpr ⟨member,hq,value_of_trace hs hg ht htr rep⟩)
    (extensionOrder_iff.mpr ⟨member,dd.trans e.1,fg⟩)) (allIn_elim (f := fun z => edge R z z)
      ((base.trans po).trans (inf_le_right.trans inf_le_left)) hq)))

theorem graph_reaches {Γ : B} {K P R : N} (ok : Γ ≤ Ord K) (po : Γ ≤ partialOrderValue P R)
    (cl : Γ ≤ shortInfimaValue K P R) (zero : Γ ≤ (∅ : N) ∈ᴮ K) (one : Γ ≤ succ (∅ : N) ∈ᴮ K) :
    Γ ≤ projectionReaches P R (graph K P R) := by
  refine le_iInf fun q => projection_imp.mpr ?_
  intro Δ hd hq
  have empty : Δ ≤ is_function (∅ : N) P ∅ := le_inf is_func'_empty empty_subset
  obtain ⟨h,x,hh,law,hx,rep⟩ := exists_evaluation (hd.trans po) (hd.trans cl) (hd.trans ok) (hd.trans zero) empty
  have below : Δ ≤ edge R q x := by
    apply (rep le_rfl hq).mp
    apply allIn_intro
    intro c _ D hD
    obtain ⟨j,hj⟩ := exists_convert (mem_image_iff.mp hD).2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact (bot_of_mem_empty (hj.trans inf_le_left)).trans bot_le
  obtain ⟨g,k,_,hs,hg,hk,kl,out⟩ := exists_exact_lift (hd.trans po)
    (Ord_of_mem_Ord (hd.trans zero) (hd.trans ok)) (hd.trans one) empty hh law ⟨hx,rep⟩ hq below
  have member := (paths_mem (hd.trans ok)).mpr ⟨_,hs,hg⟩
  exact le_iSup_of_le g (le_iSup_of_le q (le_inf (graph_pair.mpr ⟨member,hq,value_of_trace hs hg hk kl out⟩)
    (allIn_elim (f := fun z => edge R z z) ((hd.trans po).trans (inf_le_right.trans inf_le_left)) hq)))

theorem graph_monotone {Γ : B} {K P R : N} (ok : Γ ≤ Ord K) (po : Γ ≤ partialOrderValue P R) :
    Γ ≤ projectionMonotone (extensionOrder (paths K P)) R (graph K P R) := by
  refine le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => projection_imp.mpr ?_
  intro Δ hd h
  exact value_monotone (hd.trans ok) (hd.trans po) (extensionOrder_iff.mp (h.trans inf_le_right)).2.2
    (graph_pair.mp (h.trans (inf_le_left.trans inf_le_right))).2.2
    (graph_pair.mp (h.trans (inf_le_left.trans inf_le_left))).2.2

end bSet.ErdosShioyaInternal.CollapsePath
