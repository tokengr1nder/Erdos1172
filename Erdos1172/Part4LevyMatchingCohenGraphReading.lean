/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingAnchoredArrays
public import Erdos1172.Part4LevyPreparationCohenConditions

@[expose] public section

/-! # Recovering all upper Cohen conditions in the matched source extension -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal bSet Lattice ErdosNameTransport ErdosOmegaTwo ErdosPartialInjection ErdosCheckedIndicator
open Erdos1172LevyCohen Erdos1172BooleanFactor
open scoped Flypitch
namespace Erdos1172LevyCollapse.Matching
variable {V R E : Type u} [NontrivialCompleteBooleanAlgebra V]
  [NontrivialCompleteBooleanAlgebra R] [NontrivialCompleteBooleanAlgebra E]

private theorem hom_inf' {U T : Type u} [CompleteLattice U] [CompleteLattice T]
    (k : CompleteLatticeHom U T) (a b : U) : k (a ⊓ b) = k a ⊓ k b := by
  rw [← sInf_pair,map_sInf,Set.image_pair,sInf_pair]

private theorem underCover {T : Type*} {s : T → E} {a goal : E}
    (cover : a ≤ ⨆ t, s t) (localLe : ∀ i, a ⊓ s i ≤ goal) : a ≤ goal :=
  ((inf_eq_left.mpr cover).symm.trans (inf_iSup_eq _ _)).le.trans (iSup_le localLe)

variable (f : CompleteLatticeHom V E) (g : CompleteLatticeHom R E)

/-- Short-array agreement recovers whole mixed subsets of a checked set,
retaining their original truth value. -/
theorem ArrayRead.subset_names (S : PSet.{u}) (read : ∀ x : S.Type → V, ArrayRead f g x) (x : bSet V) :
    f (x ⊆ᴮ check S) ≤ ⨆ y : bSet R, g (y ⊆ᴮ check S) ⊓ (mapNames f x =ᴮ mapNames g y) := by
  let b (i : S.Type) := check (S.Func i) ∈ᴮ x
  have rep : x ⊆ᴮ check S ≤ x =ᴮ checkedIndicator S b := by
    rw [show checkedIndicator S b = _ from checkedIndicator_membership_eq S x]
    exact eq_membership_indicator_of_subset le_rfl
  apply underCover (le_top.trans (read b))
  intro t
  let y := checkedIndicator S t.val.2
  refine le_iSup_of_le y (le_inf (le_top.trans ((map_top g).ge.trans (OrderHomClass.mono g (checkedIndicator_subset S _)))) ?_)
  have transported := (OrderHomClass.mono f rep).trans_eq (map_bv_eq f _ _)
  apply bv_trans (inf_le_left.trans transported)
  rw [map_checkedIndicator,show mapNames g y = _ from map_checkedIndicator g S t.val.2]
  apply le_trans inf_le_right
  exact subset_ext (checkedIndicator_subset_of_coefficients S (fun i => (t.property i).le.trans inf_le_right))
    (checkedIndicator_subset_of_coefficients S (fun i => (t.property i).ge.trans inf_le_right))

variable {θ : Cardinal.{u}}
local notation "Z" => FirstAlgebra θ

/-- Every checked ordinal below θ belongs to the internal omega one of a
source having cofinally many of the prescribed collapsing stages. -/
theorem source_bounded_ordinal_mem_omegaOne {B : θ.ord.ToType → Type u}
    [∀ i, NontrivialCompleteBooleanAlgebra (B i)] (h : ∀ i, CompleteLatticeHom (B i) R)
    (stages : RegularCollapsingStages B) (β : Ordinal.{u}) (lt : β < θ.ord) :
    (⊤ : R) ≤ check (PSet.ordinalMk β) ∈ᴮ omegaOne := by
  obtain ⟨μ,hm,hμ,_,_,_,collapsed⟩ := stages _ (Cardinal.lt_ord.mp lt)
  let k := h (cardinalStage hm)
  have target : k (⊤ : B (cardinalStage hm)) ≤ Ord (mapNames k omega) := by
    simpa only [map_top,omega,map_check] using (Ord_omega (Γ := (⊤ : R)))
  have count := map_injects_into_of_ordinal k collapsed target
  simp only [map_top,omega,map_check] at count
  have mem : (⊤ : R) ≤ check (PSet.ordinalMk β) ∈ᴮ check (PSet.ordinalMk μ.ord) :=
    check_mem (PSet.mk_mem_mk_of_lt (Cardinal.lt_ord.mpr hμ))
  apply ErdosOmegaOneCountablyBounded.countable_ordinal_mem_omegaOne (check_Ord (PSet.Ord_mk β))
  exact injects_into_trans (injects_into_of_subset (subset_of_mem_Ord mem (check_Ord (PSet.Ord_mk μ.ord)))) count

private theorem source_condition {δ D q : bSet R} {t : R} (hδ : t ≤ δ ∈ᴮ omegaOne)
    (hd : t ≤ D ⊆ᴮ δ) (hf : t ≤ is_function D two q) : t ≤ ErdosCohen.condition omegaOne q := by
  have dom : t ≤ D ⊆ᴮ omegaOne := subset_trans' hd (subset_of_mem_Ord hδ omegaOne_Ord)
  have eq := graphDomain_eq_of_function dom hf
  exact le_inf (subset_trans' (subset_prod_of_is_function hf) (prod_domain_mono dom))
    (le_inf (hf.trans (inf_le_left.trans inf_le_left)) (le_iSup_of_le δ
      (le_inf hδ (injects_into_of_subset (subset_trans' (subset_of_eq eq) hd)))))

theorem cohen_domain_bound_of_height (height : (⊤ : V) ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaOne)
    (q : bSet V) :
    ErdosCohen.condition omegaOne q ≤ ⨆ i : θ.ord.ToType,
      graphDomain omegaOne two q ⊆ᴮ check (PSet.ordinalMk i.toOrd.val) := by
  let v := ErdosCohen.condition (omegaOne : bSet V) q
  let D := graphDomain (omegaOne : bSet V) two q
  have sub : v ≤ D ⊆ᴮ omegaOne := graphDomain_subset
  have count : v ≤ injects_into D omega :=
    ErdosCohen.countable_of_smallDomain omegaOne_property (inf_le_right.trans inf_le_right)
  obtain ⟨b,hb⟩ := ErdosOmegaOneCountablyBounded.exists_bound_of_countable sub count
  let S := PSet.ordinalMk θ.ord
  have h : v ≤ ⨆ t : bSet V, t ∈ᴮ check S ⊓ D ⊆ᴮ t :=
    le_iSup_of_le b (le_inf (mem_congr bv_refl (bv_symm (le_top.trans height)) (hb.trans inf_le_left))
      (hb.trans inf_le_right))
  have reduce (T : PSet.{u}) (hT : v ≤ ⨆ t : bSet V, t ∈ᴮ check T ⊓ D ⊆ᴮ t) :
      v ≤ ⨆ i : T.Type, D ⊆ᴮ check (T.Func i) := by
    cases T with
    | mk I x =>
      rw [← bounded_exists (v := check (PSet.mk I x)) (ϕ := fun t : bSet V => D ⊆ᴮ t)
        (h_congr := B_ext_subset_right)] at hT
      change v ≤ ⨆ i : I, (⊤ : V) ⊓ D ⊆ᴮ check (x i) at hT
      change v ≤ ⨆ i : I, D ⊆ᴮ check (x i)
      simpa only [top_inf_eq] using hT
  have out := reduce S h
  dsimp only [S] at out
  rwa [PSet.ordinalMk_eq_def] at out

variable (K : CompleteLatticeHom V E)
variable (read : ∀ (X : Type u), #X < θ → ∀ v : X → V, ArrayRead K g v)
variable (count : ∀ β : Ordinal.{u}, β < θ.ord → (⊤ : R) ≤ check (PSet.ordinalMk β) ∈ᴮ omegaOne)

include read count in
theorem cohen_graph_reading_of_height (hθ : ℵ₀ < θ)
    (height : (⊤ : V) ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaOne) (q : bSet V) :
    K (ErdosCohen.condition omegaOne q) ≤ ⨆ y : bSet R,
      g (ErdosCohen.condition omegaOne y) ⊓ (mapNames K q =ᴮ mapNames g y) := by
  let val := ErdosCohen.condition (omegaOne : bSet V) q
  let D := graphDomain (omegaOne : bSet V) two q
  let bound (i : θ.ord.ToType) := D ⊆ᴮ check (PSet.ordinalMk i.toOrd.val)
  have cover : K val ≤ ⨆ i, K (bound i) := (OrderHomClass.mono K
    (cohen_domain_bound_of_height height q)).trans_eq (map_iSup K _)
  apply underCover cover
  intro i
  let δ := PSet.ordinalMk i.toOrd.val
  let S := PSet.pSet_prod δ (PSet.ofNat 2)
  have small : #δ.Type < θ := by
    rw [PSet.ordinalMk_type,Cardinal.mk_toType]
    exact Cardinal.lt_ord.mp i.toOrd.property
  have smallS : #S.Type < θ := by
    rw [show S.Type = (δ.Type × (PSet.ofNat 2).Type) from rfl,Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt hθ.le small
      ((show #(Option (Option PEmpty.{u+1})) < ℵ₀ from Cardinal.mk_lt_aleph0).trans hθ)
  let w := K val ⊓ K (bound i)
  have box : val ⊓ bound i ≤ q ⊆ᴮ check S :=
    subset_trans' (subset_trans' (subset_prod_of_is_function (ErdosCohen.condition_function inf_le_left))
      (prod_domain_mono inf_le_right)) (subset_of_eq (bv_symm (check_pset_prod (x := δ) (y := PSet.ofNat 2))))
  have ww : w ≤ K (val ⊓ bound i) := by
    change K val ⊓ K (bound i) ≤ K (val ⊓ bound i)
    exact (hom_inf' K val (bound i)).ge
  have qcov := (ww.trans (OrderHomClass.mono K box)).trans (ArrayRead.subset_names K g S (read _ smallS) q)
  have dcov : w ≤ _ := inf_le_right.trans (ArrayRead.subset_names K g δ (read _ small) D)
  apply underCover qcov
  intro y
  apply underCover (inf_le_left.trans dcov)
  intro T
  let t := (w ⊓ (g (y ⊆ᴮ check S) ⊓ (mapNames K q =ᴮ mapNames g y))) ⊓
    (g (T ⊆ᴮ check δ) ⊓ (mapNames K D =ᴮ mapNames g T))
  have valid : t ≤ K (is_function D two q) :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (OrderHomClass.mono K (ErdosCohen.condition_function le_rfl))))
  have hv : t ≤ is_function (mapNames K D) two (mapNames K q) := by
    simpa only [map_is_function,show (two : bSet V) = check (PSet.ofNat 2) from rfl,map_check] using valid
  have ey : t ≤ mapNames K q =ᴮ mapNames g y := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have et : t ≤ mapNames K D =ᴮ mapNames g T := inf_le_right.trans inf_le_right
  have hv' := bv_rw'' (ϕ := fun d => is_function d two (mapNames g y)) et
    (bv_rw'' ey hv B_ext_is_function_right) B_ext_is_function_left
  have srcf : lowerProjection g t ≤ is_function T two y := by
    apply lowerProjection_le
    simpa only [map_is_function,show (two : bSet R) = check (PSet.ofNat 2) from rfl,map_check] using hv'
  have srcd : lowerProjection g t ≤ T ⊆ᴮ check δ := lowerProjection_le g (inf_le_right.trans inf_le_left)
  have ok := source_condition (le_top.trans (count _ i.toOrd.property)) srcd srcf
  exact le_iSup_of_le y (le_inf ((lowerProjection_le_iff g).mp ok) ey)

end Erdos1172LevyCollapse.Matching
