/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalRelationGraph
public import Erdos1172.Part4BooleanCheckedIndicatorAgreement

@[expose] public section

/-! # Partial orders, separativity, and regular-open columns on named carriers -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
universe u
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def allIn (P : N) (f : N → B) : B := ⨅ x : N, (x ∈ᴮ P) ⟹ f x
def someIn (P : N) (f : N → B) : B := ⨆ x : N, (x ∈ᴮ P) ⊓ f x
def edge (R p q : N) : B := pair p q ∈ᴮ R

def compatibleValue (P R p q : N) : B := someIn P (fun t => edge R t p ⊓ edge R t q)

def partialOrderValue (P R : N) : B :=
  (R ⊆ᴮ prod P P) ⊓ (allIn P (fun p => edge R p p) ⊓
    (allIn P (fun p => allIn P (fun q => (edge R p q ⊓ edge R q p) ⟹ (p =ᴮ q))) ⊓
     allIn P (fun p => allIn P (fun q => allIn P (fun t => (edge R p q ⊓ edge R q t) ⟹ edge R p t)))))

def separatesValue (P R p q : N) : B := someIn P (fun t => edge R t p ⊓ (compatibleValue P R t q)ᶜ)
def separativeValue (P R : N) : B :=
  allIn P (fun p => allIn P (fun q => (edge R p q)ᶜ ⟹ separatesValue P R p q))

def denseBelowColumn (P R bits i p : N) : B :=
  allIn P (fun q => edge R q p ⟹ someIn P (fun t => edge R t q ⊓ edge bits t i))

def regularColumnValue (P R bits i : N) : B :=
  allIn P (fun p => allIn P (fun q => (edge R p q ⊓ edge bits q i) ⟹ edge bits p i)) ⊓
  allIn P (fun p => denseBelowColumn P R bits i p ⟹ edge bits p i)

/-- Column i represents the regular open where bit i is positive. -/
def regularColumnsValue (P R L bits : N) : B :=
  (bits ⊆ᴮ prod P L) ⊓ allIn L (fun i => regularColumnValue P R bits i)

theorem const_congr (p : N) : B_congr (fun _ : N => p) := fun _ => bv_refl
theorem id_congr : B_congr (fun x : N => x) := fun h => h

theorem allIn_ext {P : N → N} {f : N → N → B} (hp : B_congr P)
    (h : ∀ y, B_ext (fun x => f x y)) : B_ext (fun x => allIn (P x) (f x)) :=
  B_ext_iInf (h := fun y => B_ext_imp (h₁ := B_ext_term _ _ B_ext_mem_right hp) (h₂ := h y))

theorem someIn_ext {P : N → N} {f : N → N → B} (hp : B_congr P)
    (h : ∀ y, B_ext (fun x => f x y)) : B_ext (fun x => someIn (P x) (f x)) :=
  B_ext_iSup (h := fun y => B_ext_inf (B_ext_term _ _ B_ext_mem_right hp) (h y))

theorem edge_ext {R p q : N → N} (hr : B_congr R) (hp : B_congr p) (hq : B_congr q) :
    B_ext (fun x => edge (R x) (p x) (q x)) :=
  fun _ _ => mem_congr (pair_congr (hp inf_le_left) (hq inf_le_left)) (hr inf_le_left) inf_le_right

theorem compatibleValue_ext {P R p q : N → N} (hP : B_congr P) (hR : B_congr R)
    (hp : B_congr p) (hq : B_congr q) : B_ext (fun x => compatibleValue (P x) (R x) (p x) (q x)) :=
  someIn_ext hP (fun t => B_ext_inf (edge_ext hR (const_congr t) hp) (edge_ext hR (const_congr t) hq))

theorem separatesValue_ext {P R p q : N → N} (hP : B_congr P) (hR : B_congr R)
    (hp : B_congr p) (hq : B_congr q) : B_ext (fun x => separatesValue (P x) (R x) (p x) (q x)) :=
  someIn_ext hP (fun t => B_ext_inf (edge_ext hR (const_congr t) hp)
    (B_ext_neg (h := compatibleValue_ext hP hR (const_congr t) hq)))

private theorem subprod_ext {R P L : N → N} (hr : B_congr R) (hp : B_congr P) (hl : B_congr L) :
    B_ext (fun x => R x ⊆ᴮ prod (P x) (L x)) := fun x y => by
  let Γ := (x =ᴮ y) ⊓ (R x ⊆ᴮ prod (P x) (L x))
  have h₁ : Γ ≤ R y ⊆ᴮ R x := bSet.subset_of_eq (bv_symm (hr inf_le_left))
  have h₂ : Γ ≤ prod (P x) (L x) ⊆ᴮ prod (P y) (L y) := bSet.subset_of_eq (prod_congr (hp inf_le_left) (hl inf_le_left))
  exact subset_trans' h₁ (subset_trans' inf_le_right h₂)

theorem partialOrderValue_ext {P R : N → N} (hP : B_congr P) (hR : B_congr R) :
    B_ext (fun x => partialOrderValue (P x) (R x)) :=
  B_ext_inf (subprod_ext hR hP hP) (B_ext_inf (allIn_ext hP (fun p => edge_ext hR (const_congr p) (const_congr p)))
    (B_ext_inf (allIn_ext hP (fun p => allIn_ext hP (fun q => B_ext_imp
      (h₁ := B_ext_inf (edge_ext hR (const_congr p) (const_congr q)) (edge_ext hR (const_congr q) (const_congr p)))
      (h₂ := B_ext_const))))
      (allIn_ext hP (fun p => allIn_ext hP (fun q => allIn_ext hP (fun t => B_ext_imp
        (h₁ := B_ext_inf (edge_ext hR (const_congr p) (const_congr q)) (edge_ext hR (const_congr q) (const_congr t)))
        (h₂ := edge_ext hR (const_congr p) (const_congr t))))))))

theorem separativeValue_ext {P R : N → N} (hP : B_congr P) (hR : B_congr R) :
    B_ext (fun x => separativeValue (P x) (R x)) :=
  allIn_ext hP (fun p => allIn_ext hP (fun q => B_ext_imp
    (h₁ := B_ext_neg (h := edge_ext hR (const_congr p) (const_congr q)))
    (h₂ := separatesValue_ext hP hR (const_congr p) (const_congr q))))

theorem denseBelowColumn_ext {P R bits i p : N → N} (hP : B_congr P) (hR : B_congr R)
    (hb : B_congr bits) (hi : B_congr i) (hp : B_congr p) :
    B_ext (fun x => denseBelowColumn (P x) (R x) (bits x) (i x) (p x)) :=
  allIn_ext hP (fun q => B_ext_imp (h₁ := edge_ext hR (const_congr q) hp) (h₂ :=
    someIn_ext hP (fun t => B_ext_inf (edge_ext hR (const_congr t) (const_congr q)) (edge_ext hb (const_congr t) hi))))

theorem regularColumnValue_ext {P R bits i : N → N} (hP : B_congr P) (hR : B_congr R) (hb : B_congr bits)
    (hi : B_congr i) : B_ext (fun x => regularColumnValue (P x) (R x) (bits x) (i x)) :=
  B_ext_inf (allIn_ext hP (fun p => allIn_ext hP (fun q => B_ext_imp
    (h₁ := B_ext_inf (edge_ext hR (const_congr p) (const_congr q)) (edge_ext hb (const_congr q) hi))
    (h₂ := edge_ext hb (const_congr p) hi))))
    (allIn_ext hP (fun p => B_ext_imp (h₁ := denseBelowColumn_ext hP hR hb hi (const_congr p))
      (h₂ := edge_ext hb (const_congr p) hi)))

theorem regularColumnsValue_ext {P R L bits : N → N} (hP : B_congr P) (hR : B_congr R)
    (hL : B_congr L) (hb : B_congr bits) : B_ext (fun x => regularColumnsValue (P x) (R x) (L x) (bits x)) :=
  B_ext_inf (subprod_ext hb hP hL) (allIn_ext hL (fun i => regularColumnValue_ext hP hR hb (const_congr i)))

end bSet.ErdosShioyaInternal
