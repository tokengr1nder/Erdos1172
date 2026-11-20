/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCoverGenericString
public import Erdos1172.Part4ShioyaSimultaneousDecision
public import Erdos1172.Part4ShioyaUniformization

@[expose] public section

/-! # Ground reading of short uniformization data in the Shioya model -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
open bSet Erdos1172PosetCompletion Lattice
universe u
namespace Erdos1172Shioya

private theorem lower_cone_of_meet {P : Type u} [Preorder P] (p : P) (a : Completion P)
    (h : condition p ⊓ a ≠ ⊥) : ∃ q ≤ p, condition q ≤ a := by
  obtain ⟨r,hr⟩ := exists_condition_le h
  obtain ⟨q,hqr,hqp⟩ := (mem_condition_iff p r).mp (condition_le_iff.mp (hr.trans inf_le_left)) r le_rfl
  exact ⟨q,hqp,(condition_mono hqr).trans (hr.trans inf_le_right)⟩

theorem choose_below {P I : Type u} [Preorder P] (p : P) (c : I → Completion P)
    (hc : condition p ≤ ⨆ i, c i) : ∃ q ≤ p, ∃ i, condition q ≤ c i := by
  have hn : condition p ⊓ (⨆ i, c i) ≠ ⊥ := fun hz => condition_ne_bot p ((inf_eq_left.mpr hc).symm.trans hz)
  erw [inf_iSup_eq] at hn
  obtain ⟨i,hi⟩ := nonzero_wit (bot_lt_iff_ne_bot.mpr hn)
  obtain ⟨q,hqp,hq⟩ := lower_cone_of_meet p _ hi.ne'
  exact ⟨q,hqp,i,hq⟩

private theorem order_reflected {A D : Type u} [CompleteLattice A] [CompleteLattice D]
    (e : CompleteLatticeHom A D) (inj : Function.Injective e) {x y : A} (h : e x ≤ e y) : x ≤ y := by
  apply inf_eq_left.mp
  apply inj
  rw [← sInf_pair, map_sInf, Set.image_pair, sInf_pair, inf_eq_left.mpr h]

private theorem closed_reading {P I : Type u} [PartialOrder P] {J : I → Type u} {κ : Cardinal.{u}}
    (hP : ShortInfima κ P) (hI : Cardinal.mk I < κ) (a : ∀ i, J i → Completion P) (p : P)
    (hc : ∀ i, condition p ≤ ⨆ j, a i j) : ∃ q ≤ p, ∃ f : ∀ i, J i, ∀ i, condition q ≤ a i (f i) := by
  classical
  obtain ⟨_lo, _wf⟩ := exists_wellFoundedLT I
  letI := _lo
  haveI : WellFoundedLT (I) := _wf
  let D (i : I) : Set P := {q | condition q ≤ (⨆ j, a i j)ᶜ ∨ ∃ j, condition q ≤ a i j}
  have down (i : I) : IsLowerSet (D i) := by
    intro q r hqr hr
    rcases hr with h | ⟨j,h⟩
    · exact Or.inl ((condition_mono hqr).trans h)
    · exact Or.inr ⟨j,(condition_mono hqr).trans h⟩
  have dense (i : I) (r : P) : ∃ q ≤ r, q ∈ D i := by
    by_cases hh : condition r ⊓ (⨆ j, a i j) = ⊥
    · exact ⟨r,le_rfl,Or.inl (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hh.le))⟩
    · erw [inf_iSup_eq] at hh
      obtain ⟨j,hj⟩ := nonzero_wit (bot_lt_iff_ne_bot.mpr hh)
      obtain ⟨q,hqr,hq⟩ := lower_cone_of_meet r _ hj.ne'
      exact ⟨q,hqr,Or.inr ⟨j,hq⟩⟩
  obtain ⟨q,hqp,hq⟩ := exists_short_dense_intersection hP hI D down dense p
  have read (i : I) : ∃ j, condition q ≤ a i j := by
    rcases hq i with h | h
    · exact (condition_ne_bot q (bot_unique ((le_inf ((condition_mono hqp).trans (hc i)) h).trans inf_compl_eq_bot.le))).elim
    · exact h
  choose f hf using read
  exact ⟨q,hqp,f,hf⟩

namespace LevyProduct

variable {κ θ : Cardinal.{u}}
variable (hκ : κ.IsRegular) (hk : κ < θ) (hθ : θ.IsInaccessible)

include hκ hk hθ in
private theorem mixed_reading {I : Type u} {J : I → Type u} (hI : Cardinal.mk I < κ)
    [Nonempty (Full κ θ)] (p : CohenCover.Condition θ (Completion (Full κ θ)))
    (a : ∀ i, J i → Completion (CohenCover.Condition θ (Completion (Full κ θ))))
    (hc : ∀ i, condition p ≤ ⨆ j, a i j) :
    ∃ t ≤ p, ∃ f : ∀ i, J i, ∀ i, condition t ≤ a i (f i) := by
  classical
  obtain ⟨_lo, _wf⟩ := exists_wellFoundedLT I
  letI := _lo
  haveI : WellFoundedLT (I) := _wf
  obtain ⟨q,hqp,hv,hr⟩ := CohenCover.exists_short_row_reading hθ.isRegular
    (fun w hp hd => full_completion_disjoint_family_cardinal_lt hθ hk hκ.aleph0_le w hp hd)
    (hI.trans hk) p a hc
  obtain ⟨r,hrp⟩ := exists_condition_le p.positive
  obtain ⟨s,hsr,f,hf⟩ := closed_reading (shortInfima hκ) hI (fun i j => q.read (a i j)) r (fun i => hrp.trans (hr i))
  have hsq : condition s ≤ q.value := (condition_mono hsr).trans (hrp.trans_eq hv.symm)
  let t := q.withValue (condition s) (condition_ne_bot s)
  have htq : t ≤ q := q.withValue_le _ _ hsq
  refine ⟨t,htq.trans hqp,f,fun i => ?_⟩
  exact (le_inf (condition_mono htq) ((CohenCover.condition_le_firstStageHom_iff t _).mpr (hf i))).trans
    (q.inf_firstStageHom_read (a i (f i)))

variable [Fact (Cardinal.aleph0 < κ)]

include hκ hk hθ in
/-- The Shioya completion satisfies the full distributive law on fewer than κ
rows, including rows with different sets of alternatives. -/
theorem short_choice {I : Type u} {J : I → Type u} (hI : Cardinal.mk I < κ) (a : ∀ i, J i → Algebra κ θ) :
    (⨅ i, ⨆ j, a i j) ≤ ⨆ f : ∀ i, J i, ⨅ i, a i (f i) := by
  let _ : Nonempty (Full κ θ) := ⟨empty hκ.pos⟩
  let B := Completion (Full κ θ)
  let C := CohenCover.Condition θ B
  let _ : Nonempty C := ⟨CohenCover.Condition.empty hθ.pos ⊤ top_ne_bot⟩
  let e := levyCohenCoverHom hκ hk hθ
  let x := ⨅ i, ⨆ j, a i j
  let y := ⨆ f : ∀ i, J i, ⨅ i, a i (f i)
  have he : e x ≤ e y := by
    by_contra h
    have hn : e x ⊓ (e y)ᶜ ≠ ⊥ := fun hh => h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr hh.le))
    obtain ⟨p,hp⟩ := exists_condition_le hn
    have hc (i : I) : condition p ≤ ⨆ j, e (a i j) := by
      rw [← map_iSup]
      exact hp.trans (inf_le_left.trans (OrderHomClass.mono e (iInf_le _ i)))
    obtain ⟨t,htp,f,hf⟩ := mixed_reading hκ hk hθ hI p (fun i j => e (a i j)) hc
    have hy : condition t ≤ e y := by
      change condition t ≤ e (⨆ f : ∀ i, J i, ⨅ i, a i (f i))
      rw [map_iSup]
      apply le_iSup_of_le f
      rw [map_iInf]
      exact le_iInf hf
    exact condition_ne_bot t (bot_unique ((le_inf hy ((condition_mono htp).trans (hp.trans inf_le_right))).trans inf_compl_eq_bot.le))
  exact order_reflected e (levyCohenCoverHom_injective hκ hk hθ) he

end LevyProduct

namespace Uniformization

def groundGraph (X Y : PSet.{u}) (g : X.Type → Y.Type) : PSet.{u} :=
  .mk X.Type (fun i => PSet.pSet_pair (X.Func i) (Y.Func (g i)))

private theorem row {B : Type u} [NontrivialCompleteBooleanAlgebra B] {Γ : B}
    (X Y : PSet.{u}) (f : bSet B) (hf : Γ ≤ is_function (check X) (check Y) f) (i : X.Type) :
    Γ ≤ ⨆ j : Y.Type, pair (check (X.Func i)) (check (Y.Func j)) ∈ᴮ f := by
  have hm : Γ ≤ check (X.Func i) ∈ᴮ check X := check_mem (PSet.func_mem X i)
  have h : Γ ≤ ⨆ v : bSet B, v ∈ᴮ check Y ⊓ pair (check (X.Func i)) v ∈ᴮ f :=
    (le_inf ((is_total_of_is_function hf).trans (iInf_le _ (check (X.Func i)))) hm).trans bv_imp_elim
  rw [← @bounded_exists B _ (check Y) (fun v => pair (check (X.Func i)) v ∈ᴮ f)
    (h_congr := B_ext_pair_mem_right)] at h
  cases Y
  exact h.trans (iSup_mono fun _ => inf_le_right)

private theorem graph_of_selected_rows {B : Type u} [NontrivialCompleteBooleanAlgebra B] {Γ : B}
    (X Y : PSet.{u}) (f : bSet B) (g : X.Type → Y.Type) (hf : Γ ≤ is_function (check X) (check Y) f)
    (hp : ∀ i, Γ ≤ pair (check (X.Func i)) (check (Y.Func (g i))) ∈ᴮ f) :
    Γ ≤ f =ᴮ check (groundGraph X Y g) := by
  cases X with | mk I x =>
  cases Y with | mk J y =>
  let graph := groundGraph (.mk I x) (.mk J y) g
  apply subset_ext
  · rw [subset_unfold']
    apply le_iInf
    intro z
    rw [← deduction]
    have hz := mem_of_mem_subset (inf_le_left.trans (subset_prod_of_is_function hf))
      (show Γ ⊓ (z ∈ᴮ f) ≤ z ∈ᴮ f from inf_le_right)
    apply (le_inf le_rfl hz).trans
    rw [mem_unfold (u := z) (v := prod (check (.mk I x)) (check (.mk J y))),inf_iSup_eq]
    apply iSup_le
    rintro ⟨i,j⟩
    let d := (Γ ⊓ (z ∈ᴮ f)) ⊓ ((⊤ ⊓ (⊤ : B)) ⊓ (z =ᴮ pair (check (x i)) (check (y j))))
    have hd : d ≤ Γ := inf_le_left.trans inf_le_left
    have he : d ≤ z =ᴮ pair (check (x i)) (check (y j)) := inf_le_right.trans inf_le_right
    have hm : d ≤ pair (check (x i)) (check (y j)) ∈ᴮ f := mem_congr he bv_refl (inf_le_left.trans inf_le_right)
    have hy := eq_of_is_function_of_eq (hd.trans hf) bv_refl hm (hd.trans (hp i))
    have he' : d ≤ z =ᴮ check (graph.Func i) := bv_trans he (bv_trans (pair_congr bv_refl hy) (bv_symm check_pset_pair))
    exact mem_congr (bv_symm he') bv_refl (check_mem (PSet.func_mem graph i))
  · rw [subset_unfold]
    apply le_iInf
    intro i
    change Γ ≤ _root_.imp (⊤ : B) (check (graph.Func i) ∈ᴮ f)
    rw [top_imp]
    exact mem_congr (bv_symm check_pset_pair) bv_refl (hp i)

variable {κ θ : Cardinal.{u}} [Fact (Cardinal.aleph0 < κ)] [Nonempty (Condition κ θ)]
variable (hκ : κ.IsRegular) (hk : κ < θ) (hθ : θ.IsInaccessible)

include hκ hk hθ in
/-- All of a name for a short function in W is locally a single checked graph. -/
theorem checked_graph_cover (X Y : PSet.{u}) (hX : Cardinal.mk X.Type < κ) (f : bSet (Algebra κ θ))
    {Γ : Algebra κ θ} (hf : Γ ≤ is_function (check X) (check Y) f) :
    Γ ≤ ⨆ g : X.Type → Y.Type, f =ᴮ check (groundGraph X Y g) := by
  let a (i : X.Type) (j : Y.Type) : Algebra κ θ := pair (check (X.Func i)) (check (Y.Func j)) ∈ᴮ f
  have hc : Γ ≤ ⨅ i, ⨆ j, a i j := le_iInf (row X Y f hf)
  apply (le_inf le_rfl (hc.trans (LevyProduct.short_choice hκ hk hθ hX a))).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro g
  exact le_iSup_of_le g (graph_of_selected_rows X Y f g (inf_le_left.trans hf)
    (fun i => inf_le_right.trans (iInf_le _ i)))

include hκ hk hθ in
theorem exists_checked_graph_below (X Y : PSet.{u}) (hX : Cardinal.mk X.Type < κ)
    (f : bSet (Algebra κ θ)) (p : Condition κ θ) (hf : condition p ≤ is_function (check X) (check Y) f) :
    ∃ q ≤ p, ∃ g : X.Type → Y.Type, condition q ≤ f =ᴮ check (groundGraph X Y g) := by
  exact choose_below p _ (checked_graph_cover hκ hk hθ X Y hX f hf)

include hκ hk hθ in
/-- Both a mixed short ordinal and the entire function on it are read on
the same Boolean piece. -/
theorem mixed_short_graph_cover (D : bSet (Algebra κ θ)) (Y : PSet.{u}) (f : bSet (Algebra κ θ))
    {Γ : Algebra κ θ} (hD : Γ ≤ D ∈ᴮ check (PSet.ordinalMk κ.ord)) (hf : Γ ≤ is_function D (check Y) f) :
    Γ ≤ ⨆ k : κ.ord.ToType, ⨆ g : (PSet.ordinalMk k.toOrd.val).Type → Y.Type,
      (D =ᴮ check (PSet.ordinalMk k.toOrd.val)) ⊓ (f =ᴮ check (groundGraph (PSet.ordinalMk k.toOrd.val) Y g)) := by
  apply (le_inf le_rfl hD).trans
  rw [PSet.ordinalMk_eq_def κ.ord,check_unfold,mem_unfold,inf_iSup_eq]
  apply iSup_le
  intro k
  let A := PSet.ordinalMk (show κ.ord.ToType from k).toOrd.val
  let d := Γ ⊓ ((⊤ : Algebra κ θ) ⊓ (D =ᴮ check A))
  have he : d ≤ D =ᴮ check A := inf_le_right.trans inf_le_right
  have hA : Cardinal.mk A.Type < κ := by
    simpa only [A,PSet.ordinalMk_type,Cardinal.mk_toType] using Cardinal.lt_ord.mp (show
      (show κ.ord.ToType from k).toOrd.val < κ.ord from k.toOrd.property)
  have hd : d ≤ is_function (check A) (check Y) f := bv_rw'' he (inf_le_left.trans hf) B_ext_is_function_left
  apply le_iSup_of_le (show κ.ord.ToType from k)
  apply (le_inf he (checked_graph_cover hκ hk hθ A Y hA f hd)).trans
  rw [inf_iSup_eq]
  exact le_rfl

include hκ hk hθ in
theorem exists_mixed_short_graph_below (D : bSet (Algebra κ θ)) (Y : PSet.{u})
    (f : bSet (Algebra κ θ)) (p : Condition κ θ) (hD : condition p ≤ D ∈ᴮ check (PSet.ordinalMk κ.ord))
    (hf : condition p ≤ is_function D (check Y) f) :
    ∃ q ≤ p, ∃ k : κ.ord.ToType, ∃ g : (PSet.ordinalMk k.toOrd.val).Type → Y.Type, condition q ≤
      (D =ᴮ check (PSet.ordinalMk k.toOrd.val)) ⊓ (f =ᴮ check (groundGraph (PSet.ordinalMk k.toOrd.val) Y g)) := by
  obtain ⟨r,hrp,k,hk'⟩ := choose_below p _ (mixed_short_graph_cover hκ hk hθ D Y f hD hf)
  obtain ⟨q,hqr,g,hq⟩ := choose_below r _ hk'
  exact ⟨q,hqr.trans hrp,k,g,hq⟩

/-- Codes distinguish all ground values, including projections with
different domains and different source points. -/
def labels (T : Type u) : PSet.{u} :=
  let e := (Cardinal.eq.mp (Cardinal.mk_ord_toType (Cardinal.mk T)).symm).some
  .mk T (fun t => PSet.ordinalMk (e t).toOrd.val)

theorem labels_separated (T : Type u) (i j : T)
    (h : PSet.Equiv ((labels T).Func i) ((labels T).Func j)) : i = j := by
  let e := (Cardinal.eq.mp (Cardinal.mk_ord_toType (Cardinal.mk T)).symm).some
  have he : (e i).toOrd.val = (e j).toOrd.val := PSet.eq_of_mk_equiv h
  exact e.injective (Ordinal.ToType.mk.symm.injective (Subtype.ext he))

abbrev EdgeData (κ θ : Cardinal.{u}) := Σ p : Condition κ θ, Σ q : Condition κ θ, Edge p q

include hκ hk hθ in
/-- One W-condition reads both mixed lengths, all stages, and all projection edges. -/
theorem exists_stage_edge_reading (I J s e : bSet (Algebra κ θ)) (p : Condition κ θ)
    (hI : condition p ≤ I ∈ᴮ check (PSet.ordinalMk κ.ord)) (hJ : condition p ≤ J ∈ᴮ check (PSet.ordinalMk κ.ord))
    (hs : condition p ≤ is_function I (check (labels (Condition κ θ))) s)
    (he : condition p ≤ is_function J (check (labels (EdgeData κ θ))) e) :
    ∃ q ≤ p, ∃ i j : κ.ord.ToType,
      ∃ stages : (PSet.ordinalMk i.toOrd.val).Type → Condition κ θ,
      ∃ edges : (PSet.ordinalMk j.toOrd.val).Type → EdgeData κ θ, condition q ≤
        ((I =ᴮ check (PSet.ordinalMk i.toOrd.val)) ⊓
          (s =ᴮ check (groundGraph (PSet.ordinalMk i.toOrd.val) (labels (Condition κ θ)) stages))) ⊓
        ((J =ᴮ check (PSet.ordinalMk j.toOrd.val)) ⊓
          (e =ᴮ check (groundGraph (PSet.ordinalMk j.toOrd.val) (labels (EdgeData κ θ)) edges))) := by
  obtain ⟨r,hrp,i,stages,hr⟩ := exists_mixed_short_graph_below hκ hk hθ I _ s p hI hs
  obtain ⟨q,hqr,j,edges,hq⟩ := exists_mixed_short_graph_below hκ hk hθ J _ e r
    ((condition_mono hrp).trans hJ) ((condition_mono hrp).trans he)
  exact ⟨q,hqr.trans hrp,i,j,stages,edges,le_inf ((condition_mono hqr).trans hr) hq⟩

end Uniformization
end Erdos1172Shioya
