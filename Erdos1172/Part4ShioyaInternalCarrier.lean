/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanCheckedIndicatorAgreement
public import Erdos1172.Part4LevyPreparationCohenConditions
public import Erdos1172.Part4InternalRelationGraph

@[expose] public section

/-! # A set of forcing names for mixed Shioya presentations in the preparing extension -/

set_option autoImplicit false
noncomputable section
universe u
open bSet ErdosCheckedIndicator ErdosRelationGraph Lattice
open scoped Flypitch
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

/-- The two relation names code the order and the incidence relation
between a point of the presentation and a coordinate of its binary word. -/
structure Fields (B : Type u) [NontrivialCompleteBooleanAlgebra B] where
  carrier : bSet B
  order : bSet B
  point : bSet B
  length : bSet B
  bits : bSet B

def Fields.code (t : Fields B) : N :=
  pair t.carrier (pair t.order (pair t.point (pair t.length t.bits)))

def Fields.shape (t : Fields B) (H : N) : B :=
  (t.carrier ∈ᴮ H) ⊓ ((t.length ∈ᴮ H) ⊓ ((t.point ∈ᴮ t.carrier) ⊓
    ((t.order ⊆ᴮ prod t.carrier t.carrier) ⊓ (t.bits ⊆ᴮ prod t.carrier t.length))))

abbrev ord (o : Ordinal.{u}) := PSet.ordinalMk o
abbrev rect (i j : Ordinal.{u}) := PSet.pSet_prod (PSet.ordinalMk i) (PSet.ordinalMk j)

/-- Only the two ordinal lengths and the distinguished ordinal point are
checked. Both tables contain arbitrary coefficients of the preparing algebra. -/
abbrev Table (B : Type u) (θ : Cardinal.{u}) :=
  Σ i : θ.ord.ToType, Σ j : θ.ord.ToType, i.toOrd.val.ToType ×
    ((rect i.toOrd.val i.toOrd.val).Type → B) × ((rect i.toOrd.val j.toOrd.val).Type → B)

def Table.fields {θ : Cardinal.{u}} (c : Table B θ) : Fields B :=
  ⟨check (ord c.1.toOrd.val), checkedIndicator _ c.2.2.2.1,
    check (ord c.2.2.1.toOrd.val),check (ord c.2.1.toOrd.val),checkedIndicator _ c.2.2.2.2⟩

theorem Table.shape {θ : Cardinal.{u}} (c : Table B θ) :
    (⊤ : B) ≤ (Table.fields c).shape (check (PSet.ordinalMk θ.ord)) := by
  have sub (i j : Ordinal.{u}) (w : (rect i j).Type → B) :
      (⊤ : B) ≤ checkedIndicator _ w ⊆ᴮ prod (check (ord i)) (check (ord j)) :=
    subset_trans' (checkedIndicator_subset _ w) (subset_of_eq (check_pset_prod (x := ord i) (y := ord j)))
  exact le_inf (check_mem (PSet.mk_mem_mk_of_lt c.1.toOrd.property))
    (le_inf (check_mem (PSet.mk_mem_mk_of_lt c.2.1.toOrd.property))
      (le_inf (check_mem (PSet.mk_mem_mk_of_lt c.2.2.1.toOrd.property)) (le_inf (sub _ _ _) (sub _ _ _))))

def tableSpace (B : Type u) [NontrivialCompleteBooleanAlgebra B] (θ : Cardinal.{u}) : bSet B :=
  .mk (Table B θ) (fun c => (Table.fields c).code) (fun _ => ⊤)

private theorem ordinal_members (o : Ordinal.{u}) (x : N) :
    (x ∈ᴮ check (ord o)) = ⨆ i : o.ToType, x =ᴮ check (ord i.toOrd.val) := by
  change (x ∈ᴮ check (PSet.ordinalMk o)) = _
  rw [PSet.ordinalMk_eq_def o,check_unfold,mem_unfold]
  change (⨆ i : o.ToType, ⊤ ⊓ (x =ᴮ check (ord i.toOrd.val))) = _
  simp only [top_inf_eq]

private theorem under_join {J : Type*} {d a : B} {b : J → B} (h : d ≤ ⨆ i, b i)
    (step : ∀ i, d ⊓ b i ≤ a) : d ≤ a :=
  ((inf_eq_left.mpr h).symm.trans (inf_iSup_eq _ _)).le.trans (iSup_le step)

private theorem recover_table (i j : Ordinal.{u}) (x : N) {d : B}
    (sub : d ≤ x ⊆ᴮ prod (check (ord i)) (check (ord j))) :
    ∃ w : (rect i j).Type → B, d ≤ x =ᴮ checkedIndicator _ w := by
  refine ⟨fun k => check ((rect i j).Func k) ∈ᴮ x,?_⟩
  rw [checkedIndicator_membership_eq]
  exact eq_membership_indicator_of_subset (subset_trans' sub
    (subset_of_eq (bv_symm (check_pset_prod (x := ord i) (y := ord j)))))

/-- Every internally sized tuple of mixed names is covered by actual table
codes, on its entire shape value. This includes orders and bit relations
introduced by the preparation itself. -/
theorem Fields.mem_tableSpace (θ : Cardinal.{u}) (t : Fields B) :
    t.shape (check (ord θ.ord)) ≤ t.code ∈ᴮ tableSpace B θ := by
  let v := t.shape (check (ord θ.ord))
  have carrier : v ≤ t.carrier ∈ᴮ check (ord θ.ord) := inf_le_left
  have len : v ≤ t.length ∈ᴮ check (ord θ.ord) := inf_le_right.trans inf_le_left
  have pt : v ≤ t.point ∈ᴮ t.carrier := inf_le_right.trans (inf_le_right.trans inf_le_left)
  have ro : v ≤ t.order ⊆ᴮ prod t.carrier t.carrier := inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have bits : v ≤ t.bits ⊆ᴮ prod t.carrier t.length := inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  apply under_join (carrier.trans_eq (ordinal_members _ _))
  intro i
  let a := v ⊓ (t.carrier =ᴮ check (ord i.toOrd.val))
  apply under_join ((show a ≤ v from inf_le_left).trans (len.trans_eq (ordinal_members _ _)))
  intro j
  let b := a ⊓ (t.length =ᴮ check (ord j.toOrd.val))
  have ai : b ≤ t.carrier =ᴮ check (ord i.toOrd.val) := inf_le_left.trans inf_le_right
  have bv : b ≤ v := inf_le_left.trans inf_le_left
  have bi : b ≤ t.point ∈ᴮ check (ord i.toOrd.val) := mem_congr bv_refl ai (bv.trans pt)
  apply under_join (bi.trans_eq (ordinal_members _ _))
  intro k
  let d := b ⊓ (t.point =ᴮ check (ord k.toOrd.val))
  have di : d ≤ t.carrier =ᴮ check (ord i.toOrd.val) := inf_le_left.trans ai
  have dj : d ≤ t.length =ᴮ check (ord j.toOrd.val) := inf_le_left.trans inf_le_right
  have dv : d ≤ v := inf_le_left.trans bv
  obtain ⟨R,hR⟩ := recover_table i.toOrd.val i.toOrd.val t.order
    (subset_trans' (dv.trans ro) (subset_of_eq (prod_congr di di)))
  obtain ⟨M,hM⟩ := recover_table i.toOrd.val j.toOrd.val t.bits
    (subset_trans' (dv.trans bits) (subset_of_eq (prod_congr di dj)))
  let c : Table B θ := ⟨i,j,k,R,M⟩
  have eq : d ≤ t.code =ᴮ (Table.fields c).code :=
    pair_congr di (pair_congr hR (pair_congr inf_le_right (pair_congr dj hM)))
  rw [mem_unfold]
  exact le_iSup_of_le c (le_inf le_top eq)

/-- Separation by a property of the five fields, evaluated in the
preparing universe, defines an actual set of all admissible tuple codes. -/
def fieldValue (θ : Cardinal.{u}) (law : Fields B → B) (z : N) : B :=
  ⨆ t : Fields B, (z =ᴮ t.code) ⊓ (t.shape (check (ord θ.ord)) ⊓ law t)

theorem fieldValue_ext (θ : Cardinal.{u}) (law : Fields B → B) : B_ext (fieldValue θ law) :=
  B_ext_iSup (h := fun _ => B_ext_inf B_ext_bv_eq_left B_ext_const)

def namedCarrier (θ : Cardinal.{u}) (law : Fields B → B) : N :=
  comprehend (fieldValue θ law) (tableSpace B θ)

theorem mem_namedCarrier (θ : Cardinal.{u}) (law : Fields B → B) (z : N) :
    (z ∈ᴮ namedCarrier θ law) = fieldValue θ law z := by
  apply le_antisymm ((mem_comprehend_and (fieldValue_ext θ law)).mp le_rfl).2
  apply (mem_comprehend_and (fieldValue_ext θ law)).mpr
  refine ⟨iSup_le fun t => ?_,le_rfl⟩
  exact mem_congr (bv_symm inf_le_left) bv_refl
    ((inf_le_right.trans inf_le_left).trans (Fields.mem_tableSpace θ t))

end bSet.ErdosShioyaInternal
