/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalCollapsePath
public import Erdos1172.Part4InternalImageRecursionInvariant

@[expose] public section

/-! # Principal limits of the nested cones of a native collapse path -/

set_option autoImplicit false
noncomputable section
universe u
open scoped Flypitch
open Lattice
namespace bSet.ErdosShioyaInternal.CollapsePath
open ErdosBoundedFunctionValue ErdosBoundedImageRecursion ErdosRelationGraph
open ErdosFusionHistoryCongruence ErdosImageRecursionInvariant
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def cone (P R p : N) : N := comprehend (edge R · p) P
theorem cone_mem {P R p x : N} {Γ : B} : Γ ≤ x ∈ᴮ cone P R p ↔ Γ ≤ x ∈ᴮ P ∧ Γ ≤ edge R x p :=
  mem_comprehend_and B_ext_pair_mem_left

private theorem cone_congr (P R : N) : B_congr (cone P R) :=
  comprehend_parameter_congr P (fun a x => edge R x a) (fun _ => B_ext_pair_mem_left) (fun _ => B_ext_pair_mem_right)

private theorem cone_self {P R x : N} {Γ : B} (po : Γ ≤ partialOrderValue P R) (hx : Γ ≤ x ∈ᴮ P) :
    Γ ≤ x ∈ᴮ cone P R x := cone_mem.mpr ⟨hx,allIn_elim (f := fun p => edge R p p)
      (po.trans (inf_le_right.trans inf_le_left)) hx⟩

private theorem cone_inj {P R x y : N} {Γ : B} (po : Γ ≤ partialOrderValue P R)
    (hx : Γ ≤ x ∈ᴮ P) (hy : Γ ≤ y ∈ᴮ P) (eq : Γ ≤ cone P R x =ᴮ cone P R y) : Γ ≤ x =ᴮ y := by
  have xy := (cone_mem.mp (mem_congr bv_refl eq (cone_self po hx))).2
  have yx := (cone_mem.mp (mem_congr bv_refl (bv_symm eq) (cone_self po hy))).2
  exact projection_imp.mp (allIn_elim (allIn_elim (po.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
    hx) hy) Γ le_rfl (le_inf xy yx)

def principal (P R C : N) : B := someIn P (fun x => C =ᴮ cone P R x)
private theorem principal_ext (P R : N) : B_ext (principal P R) :=
  someIn_ext (const_congr _) (fun _ => B_ext_bv_eq_left)

def generators (i P R h : N) : N := relationGraph i P (fun j p => edge h j (cone P R p))

private theorem generators_pair {Γ : B} {i P R h j p : N} :
    Γ ≤ edge (generators i P R h) j p ↔ Γ ≤ j ∈ᴮ i ∧ Γ ≤ p ∈ᴮ P ∧ Γ ≤ edge h j (cone P R p) :=
  mem_relationGraph_iff (fun _ => B_ext_pair_mem_left) (fun j =>
    B_ext_term (fun C => edge h j C) (cone P R) B_ext_pair_mem_right (cone_congr P R))

private theorem generator_function {Γ : B} {i P R h length : N} (po : Γ ≤ partialOrderValue P R)
    (hf : Γ ≤ is_function length (bv_powerset P) h) (hlen : Γ ≤ i ⊆ᴮ length)
    (good : Γ ≤ allGood (principal P R) (image i (bv_powerset P) h)) :
    Γ ≤ is_function i P (generators i P R h) := by
  apply relationGraph_is_function (fun _ => B_ext_pair_mem_left) (fun j =>
    B_ext_term (fun C => edge h j C) (cone P R) B_ext_pair_mem_right (cone_congr P R))
  · refine le_iInf fun j => projection_imp.mpr ?_
    intro Δ hd hj
    have val := graphValue_spec (hd.trans hf) (mem_of_mem_subset (hd.trans hlen) hj)
    have pr := allGood_apply (hd.trans good) (mem_image (val.trans inf_le_right) hj (val.trans inf_le_left))
    obtain ⟨p,hp⟩ := exists_convert pr (B_ext_inf B_ext_mem_left
      (B_ext_term (fun C => graphValue (bv_powerset P) h j =ᴮ C) (cone P R) B_ext_bv_eq_right (cone_congr P R)))
    exact le_iSup_of_le p (le_inf (hp.trans inf_le_left) (mem_congr (pair_congr bv_refl (hp.trans inf_le_right))
      bv_refl (val.trans inf_le_right)))
  · intro j k p q Δ hd _ _ hp hq jp kq eq
    exact cone_inj (hd.trans po) hp hq (eq_of_is_function_of_eq (hd.trans hf) eq jp kq)

private theorem generator_desc {Γ : B} {P R input h length i : N} (po : Γ ≤ partialOrderValue P R)
    (hf : Γ ≤ is_function length (bv_powerset P) h) (law : Γ ≤ trace P R input h) :
    Γ ≤ descendingValue i (generators i P R h) R := by
  refine le_iInf fun a => le_iInf fun b => le_iInf fun x => le_iInf fun y => projection_imp.mpr ?_
  intro Δ hd hs
  have hx := generators_pair.mp (hs.trans (inf_le_right.trans inf_le_left))
  have hy := generators_pair.mp (hs.trans (inf_le_right.trans inf_le_right))
  have sub := nested (hd.trans hf) (hd.trans law) hx.2.2 hy.2.2 (hs.trans (inf_le_left.trans inf_le_right))
  exact (cone_mem.mp (mem_of_mem_subset sub (cone_self (hd.trans po) hy.2.1))).2

private theorem survives_iff_lower {Γ : B} {P R h length i x : N} (hx : Γ ≤ x ∈ᴮ P)
    (hf : Γ ≤ is_function length (bv_powerset P) h) (hg : Γ ≤ is_function i P (generators i P R h)) :
    Γ ≤ survives (image i (bv_powerset P) h) x ↔ Γ ≤ lowerBoundValue i (generators i P R h) R x := by
  constructor
  · intro hs
    apply rowForall_iff.mpr
    intro j p Δ hd hj hp
    have row := (generators_pair.mp hp).2.2
    exact (cone_mem.mp (allIn_elim (hd.trans hs)
      (mem_image row hj (projection_function_bounds (hd.trans hf) row).2))).2
  · intro hl
    apply allIn_intro
    intro Δ hd C hc
    obtain ⟨j,hj⟩ := exists_convert (mem_image_iff.mp hc).2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    have jp := graphValue_pair_mem (hd.trans hg) (hj.trans inf_le_left)
    have row := (generators_pair.mp jp).2.2
    have eq := eq_of_is_function_of_eq (hd.trans hf) bv_refl row (hj.trans inf_le_right)
    exact mem_congr bv_refl eq (cone_mem.mpr ⟨hd.trans hx,
      rowForall_iff.mp hl j _ Δ hd (hj.trans inf_le_left) jp⟩)

theorem exists_past_meet {Γ : B} {P R K input h length i : N} (po : Γ ≤ partialOrderValue P R)
    (cl : Γ ≤ shortInfimaValue K P R) (hf : Γ ≤ is_function length (bv_powerset P) h)
    (law : Γ ≤ trace P R input h) (hlen : Γ ≤ i ⊆ᴮ length) (hi : Γ ≤ i ∈ᴮ K)
    (good : Γ ≤ allGood (principal P R) (image i (bv_powerset P) h)) :
    ∃ p : N, Γ ≤ p ∈ᴮ P ∧ ∀ {Δ : B}, Δ ≤ Γ → ∀ {x : N}, Δ ≤ x ∈ᴮ P →
      (Δ ≤ survives (image i (bv_powerset P) h) x ↔ Δ ≤ edge R x p) := by
  have hg := generator_function po hf hlen good
  obtain ⟨p,hp⟩ := shortInfimaValue_iff.mp cl i _ Γ le_rfl hi hg (generator_desc po hf law)
  refine ⟨p,hp.trans (inf_le_left.trans inf_le_left),?_⟩
  intro Δ hd x hx
  rw [survives_iff_lower (R := R) hx (hd.trans hf) (hd.trans hg)]
  constructor
  · intro hl
    exact projection_imp.mp ((hp.trans inf_le_right).trans (iInf_le _ x)) Δ hd (le_inf hx hl)
  · intro hxp
    apply rowForall_iff.mpr
    intro j y d dΔ hj hy
    exact internalOrder_trans ((dΔ.trans hd).trans po) (dΔ.trans hxp)
      (rowForall_iff.mp (hp.trans (inf_le_left.trans inf_le_right)) j y d (dΔ.trans hd) hj hy)

private theorem next_principal {Γ : B} {P R input i H p : N} (po : Γ ≤ partialOrderValue P R)
    (hp : Γ ≤ p ∈ᴮ P) (label : Γ ≤ graphValue P input i ∈ᴮ P)
    (surv : ∀ {Δ : B}, Δ ≤ Γ → ∀ {x : N}, Δ ≤ x ∈ᴮ P → (Δ ≤ survives H x ↔ Δ ≤ edge R x p)) :
    Γ ≤ principal P R (next P R input i H) := by
  let q := graphValue P input i
  let b := survives H q
  have split : Γ = (Γ ⊓ b) ⊔ (Γ ⊓ bᶜ) := by rw [← inf_sup_left,sup_compl_eq_top,inf_top_eq]
  apply split.le.trans
  apply sup_le
  · apply le_iSup_of_le q
    refine le_inf (inf_le_left.trans label) (mem_ext ?_ ?_)
    · refine le_iInf fun x => projection_imp.mpr ?_
      intro Δ hd hx
      have nv := next_mem.mp hx
      exact cone_mem.mpr ⟨nv.1,projection_imp.mp nv.2.2 Δ le_rfl (hd.trans inf_le_right)⟩
    · refine le_iInf fun x => projection_imp.mpr ?_
      intro Δ hd hx
      have xv := cone_mem.mp hx
      have dg := hd.trans inf_le_left
      have qp := (surv dg (dg.trans label)).mp (hd.trans inf_le_right)
      exact next_mem.mpr ⟨xv.1,(surv dg xv.1).mpr (internalOrder_trans (dg.trans po) xv.2 qp),
        projection_imp.mpr fun _ h _ => h.trans xv.2⟩
  · apply le_iSup_of_le p
    refine le_inf (inf_le_left.trans hp) (mem_ext ?_ ?_)
    · refine le_iInf fun x => projection_imp.mpr ?_
      intro Δ hd hx
      have nv := next_mem.mp hx
      exact cone_mem.mpr ⟨nv.1,(surv (hd.trans inf_le_left) nv.1).mp nv.2.1⟩
    · refine le_iInf fun x => projection_imp.mpr ?_
      intro Δ hd hx
      have xv := cone_mem.mp hx
      exact next_mem.mpr ⟨xv.1,(surv (hd.trans inf_le_left) xv.1).mpr xv.2,
        projection_imp.mpr fun _ dz yes => (bv_absurd _ yes ((dz.trans hd).trans inf_le_right)).trans bot_le⟩

/-- All cones on the full mixed path are principal, including rows
following an infinite recursion. -/
theorem trace_principal {Γ : B} {P R K input h length : N} (po : Γ ≤ partialOrderValue P R)
    (cl : Γ ≤ shortInfimaValue K P R) (ok : Γ ≤ Ord K) (short : Γ ≤ length ∈ᴮ K)
    (labels : Γ ≤ is_function length P input) (hf : Γ ≤ is_function length (bv_powerset P) h)
    (law : Γ ≤ trace P R input h) :
    Γ ≤ allGood (principal P R) (image length (bv_powerset P) h) := by
  have ord := Ord_of_mem_Ord short ok
  apply image_allGood_of_imageRecLaw ord hf law (principal_ext P R)
  refine le_iInf fun i => projection_imp.mpr ?_
  intro Δ hd hi
  have mem := hi.trans inf_le_left
  have hlen := subset_of_mem_transitive ((hd.trans ord).trans inf_le_right) mem
  have iK := mem_of_mem_subset (subset_of_mem_transitive ((hd.trans ok).trans inf_le_right) (hd.trans short)) mem
  obtain ⟨p,hp,eq⟩ := exists_past_meet (hd.trans po) (hd.trans cl) (hd.trans hf)
    (hd.trans law) hlen iK (hi.trans inf_le_right)
  exact next_principal (hd.trans po) hp (graphValue_mem (hd.trans labels) mem) eq

/-- Every short collapsing string has an actual final evaluation. Below
the final value are exactly the points which survived every row. -/
theorem exists_evaluation {Γ : B} {P R K input length : N} (po : Γ ≤ partialOrderValue P R)
    (cl : Γ ≤ shortInfimaValue K P R) (ok : Γ ≤ Ord K) (short : Γ ≤ length ∈ᴮ K)
    (labels : Γ ≤ is_function length P input) :
    ∃ h p : N, Γ ≤ is_function length (bv_powerset P) h ∧ Γ ≤ trace P R input h ∧ Γ ≤ p ∈ᴮ P ∧
      ∀ {Δ : B}, Δ ≤ Γ → ∀ {x : N}, Δ ≤ x ∈ᴮ P →
        (Δ ≤ survives (image length (bv_powerset P) h) x ↔ Δ ≤ edge R x p) := by
  obtain ⟨h,hf,law⟩ := exists_trace P R input (Ord_of_mem_Ord short ok)
  obtain ⟨p,hp,e⟩ := exists_past_meet po cl hf law subset_self short (trace_principal po cl ok short labels hf law)
  exact ⟨h,p,hf,law,hp,e⟩

end bSet.ErdosShioyaInternal.CollapsePath
