/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalWordExtension
public import Erdos1172.Part4ShioyaInternalProjectionRefinement

@[expose] public section

/-! # Pulling a named regular-open word back along an internal partial projection -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosShioyaInternal
open ErdosRelationGraph ErdosBoundedFunctionValue
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def fiber (R F bits p i : N) : B :=
  ⨅ x : N, ⨅ y : N, (edge F x y ⊓ edge R x p) ⟹ edge bits y i

def projectedBits (P R F L bits : N) : N := relationGraph P L (fiber R F bits)

private theorem projectedBits_iff {Γ : B} {P R F L bits x i : N} :
    Γ ≤ edge (projectedBits P R F L bits) x i ↔ Γ ≤ x ∈ᴮ P ∧ Γ ≤ i ∈ᴮ L ∧
      ∀ {Δ : B}, Δ ≤ Γ → ∀ {u v : N}, Δ ≤ edge F u v → Δ ≤ edge R u x → Δ ≤ edge bits v i := by
  have left (j : N) : B_ext (fun z => fiber R F bits z j) := B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_inf B_ext_const B_ext_pair_mem_right) (h₂ := B_ext_const)))
  have right (p : N) : B_ext (fiber R F bits p) := B_ext_iInf (h := fun _ =>
    B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_pair_mem_right)))
  change (Γ ≤ pair x i ∈ᴮ relationGraph P L (fiber R F bits)) ↔ _
  rw [mem_relationGraph_iff left right]
  constructor
  · rintro ⟨hx,hi,h⟩
    exact ⟨hx,hi,fun hd u v huv hux => projection_imp.mp
      (h.trans (iInf_le _ u) |>.trans (iInf_le _ v)) _ hd (le_inf huv hux)⟩
  · rintro ⟨hx,hi,h⟩
    exact ⟨hx,hi,le_iInf fun _ => le_iInf fun _ => projection_imp.mpr fun _ hd both =>
      h hd (both.trans inf_le_left) (both.trans inf_le_right)⟩

private theorem regular_down {Γ : B} {Q S bits i a b : N}
    (reg : Γ ≤ regularColumnValue Q S bits i) (ha : Γ ≤ a ∈ᴮ Q) (hb : Γ ≤ b ∈ᴮ Q)
    (hab : Γ ≤ edge S a b) (hbit : Γ ≤ edge bits b i) : Γ ≤ edge bits a i :=
  projection_imp.mp (allIn_elim (allIn_elim (reg.trans inf_le_left) ha) hb) Γ le_rfl (le_inf hab hbit)

private theorem denseColumn_witness {Γ : B} {P R bits i p q : N}
    (den : Γ ≤ denseBelowColumn P R bits i p) (hq : Γ ≤ q ∈ᴮ P) (hqp : Γ ≤ edge R q p) :
    ∃ t : N, Γ ≤ t ∈ᴮ P ∧ Γ ≤ edge R t q ∧ Γ ≤ edge bits t i := by
  have hs := projection_imp.mp (allIn_elim den hq) Γ le_rfl hqp
  obtain ⟨t,ht⟩ := exists_convert hs (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_left B_ext_pair_mem_left))
  exact ⟨t,ht.trans inf_le_left,ht.trans (inf_le_right.trans inf_le_left),ht.trans (inf_le_right.trans inf_le_right)⟩

theorem projectedBits_at {Γ : B} {K P R Q S D F L bits x y i : N}
    (π : ProjectionLaws Γ K P R Q S D F) (po : Γ ≤ partialOrderValue P R)
    (reg : Γ ≤ regularColumnValue Q S bits i) (hi : Γ ≤ i ∈ᴮ L) (xy : Γ ≤ edge F x y) :
    Γ ≤ edge (projectedBits P R F L bits) x i ↔ Γ ≤ edge bits y i := by
  have bound := projection_function_bounds π.func xy
  have hx := mem_of_mem_subset π.sub bound.1
  constructor
  · intro h
    exact (projectedBits_iff.mp h).2.2 le_rfl xy
      (allIn_elim (f := fun z => edge R z z) (po.trans (inf_le_right.trans inf_le_left)) hx)
  · intro h
    apply projectedBits_iff.mpr ⟨hx,hi,?_⟩
    intro Δ hd a b hab hax
    exact regular_down (hd.trans reg) (projection_function_bounds (hd.trans π.func) hab).2
      (hd.trans bound.2) (π.mono hd hab (hd.trans xy) hax) (hd.trans h)

theorem projectedBits_regular {Γ : B} {K P R Q S D F L bits : N}
    (π : ProjectionLaws Γ K P R Q S D F) (po : Γ ≤ partialOrderValue P R) (qo : Γ ≤ partialOrderValue Q S)
    (reg : Γ ≤ regularColumnsValue Q S L bits) :
    Γ ≤ regularColumnsValue P R L (projectedBits P R F L bits) := by
  refine le_inf relationGraph_subset (allIn_intro ?_)
  intro Δ hd i hi
  have old := allIn_elim (hd.trans (reg.trans inf_le_right)) hi
  apply le_inf
  · apply allIn_intro
    intro a ha p hp
    apply allIn_intro
    intro b hb q _
    apply projection_imp.mpr
    intro c hc h
    refine projectedBits_iff.mpr ⟨(hc.trans hb).trans hp,((hc.trans hb).trans ha).trans hi,?_⟩
    intro d hdc x y xy xp
    exact (projectedBits_iff.mp (h.trans inf_le_right)).2.2 hdc xy
      (internalOrder_trans (((((hdc.trans hc).trans hb).trans ha).trans hd).trans po) xp
        (hdc.trans (h.trans inf_le_left)))
  · apply allIn_intro
    intro a ha p hp
    apply projection_imp.mpr
    intro b hb dense
    refine projectedBits_iff.mpr ⟨hb.trans hp,(hb.trans ha).trans hi,?_⟩
    intro c hc x y xy xp
    have cΓ := ((hc.trans hb).trans ha).trans hd
    have hy := (projection_function_bounds (cΓ.trans π.func) xy).2
    apply projection_imp.mp (allIn_elim (((hc.trans hb).trans ha).trans (old.trans inf_le_right)) hy) c le_rfl
    apply allIn_intro
    intro d hd' q hq
    apply projection_imp.mpr
    intro z hz hqy
    have zc := hz.trans hd'
    have base := zc.trans cΓ
    obtain ⟨t,v,htv,htx,hvq⟩ := π.lifts base (zc.trans xy) (hz.trans hq) hqy
    have ht := mem_of_mem_subset (base.trans π.sub) (projection_function_bounds (base.trans π.func) htv).1
    obtain ⟨r,hr,hrt,hbit⟩ := denseColumn_witness ((zc.trans hc).trans dense) ht
      (internalOrder_trans (base.trans po) htx (zc.trans xp))
    obtain ⟨s,hs,hsr⟩ := π.dense base hr
    have hsw := graphValue_pair_mem (base.trans π.func) hs
    have swQ := (projection_function_bounds (base.trans π.func) hsw).2
    have swv := π.mono base hsw htv (internalOrder_trans (base.trans po) hsr hrt)
    exact le_iSup_of_le _ (le_inf swQ (le_inf (internalOrder_trans (base.trans qo) swv hvq)
      ((projectedBits_iff.mp hbit).2.2 le_rfl hsw hsr)))

/-- Replacing the presentation by an internally projected one yields a
refinement in the named forcing order, with the old word on every
projecting domain point. The refining point is selected on the full guard. -/
theorem exists_projected_refinement {Γ : B} {K P R D F : N} {θ : Cardinal.{u}} (s : Fields B)
    (valid : Γ ≤ s.code ∈ᴮ conditionSet K θ)
    (hsize : Γ ≤ P ∈ᴮ check (PSet.ordinalMk θ.ord))
    (po : Γ ≤ partialOrderValue P R) (sep : Γ ≤ separativeValue P R) (cl : Γ ≤ shortInfimaValue K P R)
    (proj : Γ ≤ partialProjectionValue K P R s.carrier s.order D F) :
    ∃ x y : N, Γ ≤ x ∈ᴮ D ∧ Γ ≤ edge F x y ∧ Γ ≤ edge s.order y s.point ∧
      Γ ≤ edge (orderSet K θ)
        (Fields.mk P R x s.length (projectedBits P R F s.length s.bits)).code s.code := by
  have hv := valid.trans_eq (code_mem_conditionSet K θ s)
  have law := hv.trans inf_le_right
  have shape := hv.trans inf_le_left
  have oldPoint := shape.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have oldOrder := law.trans inf_le_left
  have columns := law.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have π := projectionLaws_iff.mp proj
  obtain ⟨x,y,xy,below⟩ := π.reaches le_rfl oldPoint
  have xd := (projection_function_bounds π.func xy).1
  refine ⟨x,y,xd,xy,below,?_⟩
  let t : Fields B := ⟨P,R,x,s.length,projectedBits P R F s.length s.bits⟩
  have bits := projectedBits_regular π po oldOrder columns
  have tv : Γ ≤ t.code ∈ᴮ conditionSet K θ := by
    rw [code_mem_conditionSet]
    exact le_inf (le_inf hsize (le_inf (shape.trans (inf_le_right.trans inf_le_left))
      (le_inf (mem_of_mem_subset π.sub xd) (le_inf (po.trans inf_le_left) (bits.trans inf_le_left)))))
      (le_inf po (le_inf sep (le_inf cl bits)))
  apply mem_orderSet.mpr ⟨tv,valid,le_iSup_of_le t (le_iSup_of_le s (le_inf (le_inf bv_refl bv_refl) ?_))⟩
  apply le_iSup_of_le D
  apply le_iSup_of_le F
  refine le_inf (le_inf proj ?_) (le_inf subset_self ?_)
  · refine le_iInf fun a => le_iInf fun b => projection_imp.mpr ?_
    intro Δ hd h
    exact internalOrder_trans (hd.trans oldOrder)
      (π.mono hd (h.trans inf_le_left) (hd.trans xy) (h.trans inf_le_right)) (hd.trans below)
  · refine le_iInf fun a => le_iInf fun b => le_iInf fun i => projection_imp.mpr ?_
    intro Δ hd h
    have agrees {c : B} (hc : c ≤ Δ) :
        c ≤ edge t.bits a i ↔ c ≤ edge s.bits b i :=
      projectedBits_at (projectionLaws_iff.mp ((hc.trans hd).trans proj)) ((hc.trans hd).trans po)
        (allIn_elim ((hc.trans hd).trans (columns.trans inf_le_right)) (hc.trans (h.trans inf_le_right)))
        (hc.trans (h.trans inf_le_right)) (hc.trans (h.trans (inf_le_left.trans inf_le_left)))
    exact le_inf (projection_imp.mpr fun _ hc => (agrees hc).mp)
      (projection_imp.mpr fun _ hc => (agrees hc).mpr)

end bSet.ErdosShioyaInternal
