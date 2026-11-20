/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyPreparationSmallNames
public import Erdos1172.Part4BooleanUltrapowerNormality

@[expose] public section

/-! # The prepared embedding fixes every mixed lower-collapse Cohen condition -/

set_option autoImplicit false
noncomputable section
open Filter bSet ErdosNameTransport Erdos1172GroundUltrapower Erdos1172BooleanUltrapower Erdos1172LevyCohen
open ErdosOmegaTwo ErdosPartialInjection
open scoped Flypitch
universe u
namespace Erdos1172LevyCollapse.Preparation
variable {I : Type u} {κ θ : Cardinal.{u}} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
variable [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]
variable (hk : κ ≤ θ) (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
local notation "A" => FirstAlgebra κ
local notation "B" => FirstAlgebra θ
local notation "j" => preparedName U a hk hf hn ht
local notation "inc" => initialCollapseHom hk
variable (hκ : κ.IsRegular) (hu : Cardinal.aleph0 < κ)

include hκ hu in
private theorem fixed_pair {x y : PSet.{u}} (hx : (⊤ : B) ≤ j (check x) =ᴮ check x)
    (hy : (⊤ : B) ≤ j (check y) =ᴮ check y) :
    (⊤ : B) ≤ j (check (PSet.pSet_pair x y)) =ᴮ check (PSet.pSet_pair x y) := by
  let φ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U A) B := collapseCompletionIso U a hk hf hn ht
  have hp := OrderHomClass.mono φ (hereditary_pair U (fun _ => (check x : bSet A)) (fun _ => check y))
  rw [TopHomClass.map_top φ,map_bv_eq φ,map_pair] at hp
  have eq := (OrderHomClass.mono inc (check_pset_pair (x := x) (y := y) (Γ := (⊤ : A))))
  rw [TopHomClass.map_top,← prepared_eq U a hk hf hn ht hκ hu] at eq
  exact bv_trans eq (bv_trans hp (bv_trans (pair_congr hx hy) (bv_symm check_pset_pair)))

include hu in
private theorem fixed_numeral (n : ℕ) : (⊤ : B) ≤ j (check (PSet.ofNat n)) =ᴮ check (PSet.ofNat n) := by
  have natCode (m : ℕ) : ZFSet.mk (PSet.ofNat m) = (m : Ordinal.{u}).toZFSet := by
    induction m with
    | zero => exact Ordinal.toZFSet_zero.symm
    | succ m ih => rw [Nat.cast_succ,Ordinal.toZFSet_add_one,← ih]; rfl
  have lt : (n : Ordinal.{u}) < κ.ord := (Ordinal.natCast_lt_omega0 n).trans
    (by simpa only [← Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hu)
  have fixed : (⊤ : Erdos1172BooleanUltrapower.Algebra U A) ≤
      hereditary U (fun _ => (check (PSet.ofNat n) : bSet A)) =ᴮ check (PSet.ofNat n) := by
    apply bv_trans (liftName_checked U (fun _ => PSet.ofNat n))
    apply check_bv_eq
    apply PSet.equiv_iff_eq.mpr
    rw [mk_groundPSet]
    change diagonal U (ZFSet.mk (PSet.ofNat n)) = _
    rw [natCode,diagonal_fix_of_cardinalInterFilter U κ _ lt]
  let φ : CompleteLatticeHom (Erdos1172BooleanUltrapower.Algebra U A) B := collapseCompletionIso U a hk hf hn ht
  have h := OrderHomClass.mono φ fixed
  rwa [TopHomClass.map_top φ,map_bv_eq φ,map_check] at h

include hκ hu in
theorem prepared_bounded_binary_graph (β : Ordinal.{u}) (hβ : β < κ.ord) (X : bSet A) :
    inc (X ⊆ᴮ prod (check (PSet.ordinalMk β)) two) ≤ j X =ᴮ mapNames inc X := by
  let S := PSet.pSet_prod (PSet.ordinalMk β) (PSet.ofNat 2)
  have small : Cardinal.mk S.Type < κ := by
    rw [show S.Type = ((PSet.ordinalMk β).Type × (PSet.ofNat 2).Type) from rfl,Cardinal.mk_prod,
      Cardinal.lift_id,Cardinal.lift_id,PSet.ordinalMk_type,Cardinal.mk_toType]
    exact Cardinal.mul_lt_of_lt hu.le (Cardinal.lt_ord.mp hβ)
      ((show Cardinal.mk (Option (Option PEmpty.{u+1})) < Cardinal.aleph0 from Cardinal.mk_lt_aleph0).trans hu)
  have childOrd : ∀ i : (PSet.ordinalMk β).Type, (⊤ : B) ≤ j (check ((PSet.ordinalMk β).Func i)) =ᴮ check ((PSet.ordinalMk β).Func i) := by
    rw [PSet.ordinalMk_eq_def β]
    exact fun i => prepared_fixed_ordinal U a hk hf hn ht i.toOrd.val (i.toOrd.property.trans hβ)
  have fixed (k : S.Type) : (⊤ : B) ≤ j (check (S.Func k)) =ᴮ check (S.Func k) := by
    rcases k with ⟨i,k⟩
    apply fixed_pair U a hk hf hn ht hκ hu
    · exact childOrd i
    · cases k with
      | none => exact fixed_numeral U a hk hf hn ht hu 1
      | some k =>
        cases k with
        | none => exact fixed_numeral U a hk hf hn ht hu 0
        | some z => exact z.elim
  have incl : (X ⊆ᴮ prod (check (PSet.ordinalMk β)) two) ≤ X ⊆ᴮ check S :=
    subset_trans' le_rfl (subset_of_eq (bv_symm (check_pset_prod (x := PSet.ordinalMk β) (y := PSet.ofNat 2))))
  exact (OrderHomClass.mono inc incl).trans (prepared_fixed_small_subset U a hk hf hn ht hκ hu S small fixed X)

include hκ hu in
/-- A valid lower-collapse condition has a bounded binary graph on a cover
of its full support. The prepared image agrees with ordinary transport there. -/
theorem prepared_cohen_condition (q : bSet A) :
    inc (ErdosCohen.condition omegaOne q) ≤ j q =ᴮ mapNames inc q := by
  let v := ErdosCohen.condition (omegaOne : bSet A) q
  let dom := graphDomain (omegaOne : bSet A) two q
  let bound (i : κ.ord.ToType) := dom ⊆ᴮ check (PSet.ordinalMk i.toOrd.val)
  have cov : v ≤ ⨆ i, bound i := firstStage_condition_domain_bound_cover κ hκ hu le_rfl
  have refine : v ≤ ⨆ i, v ⊓ bound i := (le_inf le_rfl cov).trans_eq (inf_iSup_eq _ _)
  apply (OrderHomClass.mono inc refine).trans
  rw [_root_.map_iSup]
  apply iSup_le
  intro i
  have sub : v ⊓ bound i ≤ q ⊆ᴮ prod (check (PSet.ordinalMk i.toOrd.val)) two :=
    subset_trans' (subset_prod_of_is_function (ErdosCohen.condition_function inf_le_left)) (prod_domain_mono inf_le_right)
  exact (OrderHomClass.mono inc sub).trans (prepared_bounded_binary_graph U a hk hf hn ht hκ hu _ i.toOrd.property q)

end Erdos1172LevyCollapse.Preparation
