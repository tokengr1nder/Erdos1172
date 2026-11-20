/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalCountableProduct
public import Erdos1172.Part4InternalCountableSuccessor
public import Erdos1172.Part4InternalSimultaneousRunLaws
public import Erdos1172.Part4InternalCountableImage

@[expose] public section

/-!
# The actual countable active triangle through a stopping stage

The index set contains pairs `(ξ, σ)` with `ξ ≤ ρ` and `σ < ξ`.
In particular it includes the active coordinates of the failed stage `ρ`,
not just the strict past. The history is the exact restriction of the fixed
coordinate decoder to this index set. Its internal countability follows
from countability of the index set and functionality, not an external
enumeration or an assertion that the entire rectangular decoder is small.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosStoppedCoordinateTriangle

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosRelationGraph ErdosSimultaneousHistory ErdosSimultaneousRun
open ErdosSimultaneousEntry ErdosCountableImage

def firstCoordinate (e a : bSet 𝔹) : 𝔹 :=
  ⨆ b, e =ᴮ pair a b

private theorem firstCoordinate_ext_left (a : bSet 𝔹) :
    B_ext (fun e => firstCoordinate e a) :=
  B_ext_iSup (h := fun _ => B_ext_bv_eq_left)

private theorem firstCoordinate_ext_right (e : bSet 𝔹) : B_ext (firstCoordinate e) :=
  B_ext_iSup (h := fun _ => B_ext_pair_left B_ext_bv_eq_right)

private theorem firstCoordinate_exists {e a : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ firstCoordinate e a) : ∃ b : bSet 𝔹, Γ ≤ e =ᴮ pair a b :=
  exists_convert H (B_ext_pair_right B_ext_bv_eq_right)

def graphProjection (A f : bSet 𝔹) : bSet 𝔹 :=
  relationGraph f A firstCoordinate

private theorem mem_graphProjection_iff {A f e a : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair e a ∈ᴮ graphProjection A f ↔
      Γ ≤ e ∈ᴮ f ∧ Γ ≤ a ∈ᴮ A ∧ Γ ≤ firstCoordinate e a :=
  mem_relationGraph_iff firstCoordinate_ext_left firstCoordinate_ext_right

private theorem graphProjection_is_function {A B f : bSet 𝔹} {Γ : 𝔹}
    (Hsub : Γ ≤ f ⊆ᴮ prod A B) : Γ ≤ is_function f A (graphProjection A f) := by
  apply relationGraph_is_function (P := firstCoordinate)
    firstCoordinate_ext_left firstCoordinate_ext_right
  · apply le_iInf
    intro e
    rw [← deduction]
    have Hprod : Γ ⊓ e ∈ᴮ f ≤ e ∈ᴮ prod A B :=
      mem_of_mem_subset (inf_le_left.trans Hsub) inf_le_right
    obtain ⟨a, Ha, b, _, He⟩ := mem_prod_iff₂.mp Hprod
    exact le_iSup_of_le a (le_inf Ha (le_iSup_of_le b He))
  · intro e₁ e₂ a₁ a₂ Δ _ _ _ _ _ H₁ H₂ Heq
    obtain ⟨b₁, Hb₁⟩ := firstCoordinate_exists H₁
    obtain ⟨b₂, Hb₂⟩ := firstCoordinate_exists H₂
    exact eq_of_eq_pair_left' (bv_trans (bv_symm Hb₁) (bv_trans Heq Hb₂))

private theorem graphProjection_is_inj {A f : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func f) : Γ ≤ is_inj (graphProjection A f) := by
  apply le_iInf
  intro e₁
  apply le_iInf
  intro e₂
  apply le_iInf
  intro a₁
  apply le_iInf
  intro a₂
  rw [← deduction]
  let Δ := Γ ⊓ (pair e₁ a₁ ∈ᴮ graphProjection A f ⊓
    pair e₂ a₂ ∈ᴮ graphProjection A f ⊓ a₁ =ᴮ a₂)
  have H₁ := mem_graphProjection_iff.mp
    (show Δ ≤ pair e₁ a₁ ∈ᴮ graphProjection A f from
      inf_le_right.trans (inf_le_left.trans inf_le_left))
  have H₂ := mem_graphProjection_iff.mp
    (show Δ ≤ pair e₂ a₂ ∈ᴮ graphProjection A f from
      inf_le_right.trans (inf_le_left.trans inf_le_right))
  obtain ⟨b₁, Hb₁⟩ := firstCoordinate_exists H₁.2.2
  obtain ⟨b₂, Hb₂⟩ := firstCoordinate_exists H₂.2.2
  have Hbeq : Δ ≤ b₁ =ᴮ b₂ :=
    eq_of_is_func_of_eq (inf_le_left.trans Hfunc) (inf_le_right.trans inf_le_right)
      (mem_congr Hb₁ bv_refl H₁.1) (mem_congr Hb₂ bv_refl H₂.1)
  exact bv_trans Hb₁
    (bv_trans (pair_congr (inf_le_right.trans inf_le_right) Hbeq) (bv_symm Hb₂))

/-- A supported functional relation injects into its domain by the first
coordinate. Totality and injectivity of the original relation are not needed. -/
theorem graph_injects_into_domain {A B f : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func f) (Hsub : Γ ≤ f ⊆ᴮ prod A B) :
    Γ ≤ injects_into f A :=
  injects_into_of_injection_into (le_iSup_of_le (graphProjection A f)
    (le_inf (graphProjection_is_function Hsub) (graphProjection_is_inj Hfunc)))

theorem graph_countable_of_domain {A B f : bSet 𝔹} {Γ : 𝔹}
    (Hfunc : Γ ≤ is_func f) (Hsub : Γ ≤ f ⊆ᴮ prod A B)
    (HA : Γ ≤ injects_into A bSet.omega) : Γ ≤ injects_into f bSet.omega :=
  injects_into_trans (graph_injects_into_domain Hfunc Hsub) HA

def triangleDomain (ρ : bSet 𝔹) : bSet 𝔹 :=
  relationGraph (succ ρ) (succ ρ) (fun ξ σ => σ ∈ᴮ ξ)

theorem triangleDomain_subset_square {ρ : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ triangleDomain ρ ⊆ᴮ prod (succ ρ) (succ ρ) := relationGraph_subset

theorem mem_triangleDomain_iff {ρ ξ σ : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ Ord ρ) :
    Γ ≤ pair ξ σ ∈ᴮ triangleDomain ρ ↔
      Γ ≤ ξ ∈ᴮ succ ρ ∧ Γ ≤ σ ∈ᴮ ξ := by
  unfold triangleDomain
  rw [mem_relationGraph_iff (fun _ => B_ext_mem_right) (fun _ => B_ext_mem_left)]
  constructor
  · rintro ⟨Hξ, _, Hσ⟩
    exact ⟨Hξ, Hσ⟩
  · rintro ⟨Hξ, Hσ⟩
    exact ⟨Hξ, mem_of_mem_Ord Hσ Hξ (Ord_succ Hρ), Hσ⟩

theorem triangleDomain_subset_omegaOne_square {ρ : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ ∈ᴮ omegaOne) :
    Γ ≤ triangleDomain ρ ⊆ᴮ prod omegaOne omegaOne := by
  rw [subset_unfold']
  apply le_iInf
  intro q
  rw [← deduction]
  let Δ := Γ ⊓ q ∈ᴮ triangleDomain ρ
  have Hprod : Δ ≤ q ∈ᴮ prod (succ ρ) (succ ρ) :=
    mem_of_mem_subset triangleDomain_subset_square inf_le_right
  obtain ⟨ξ, Hξ, σ, Hσ, Hq⟩ := mem_prod_iff₂.mp Hprod
  have Hsub : Δ ≤ succ ρ ⊆ᴮ omegaOne :=
    Ord.succ_le_of_lt omegaOne_Ord (inf_le_left.trans Hρ)
  exact mem_congr (bv_symm Hq) bv_refl
    (mem_prod (mem_of_mem_subset Hsub Hξ) (mem_of_mem_subset Hsub Hσ))

theorem triangleDomain_countable {ρ : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ ∈ᴮ omegaOne) : Γ ≤ injects_into (triangleDomain ρ) bSet.omega :=
  injects_into_trans (injects_into_of_subset triangleDomain_subset_square)
    (ErdosCountableProduct.countable_square
      (ErdosCountableSuccessor.succ_countable (omegaOne_member_injects Hρ)))

/-- A name-independent supported restriction of the coordinate decoder.
The definition does not use a proof of totality or a chosen external row. -/
def stoppedCoordinateTriangle (ρ P : bSet 𝔹) : bSet 𝔹 :=
  relationGraph (triangleDomain ρ) omegaOne (fun q v => pair q v ∈ᴮ coordinateHistory P)

theorem mem_stoppedCoordinateTriangle_iff {ρ P q v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair q v ∈ᴮ stoppedCoordinateTriangle ρ P ↔
      Γ ≤ q ∈ᴮ triangleDomain ρ ∧ Γ ≤ v ∈ᴮ omegaOne ∧
        Γ ≤ pair q v ∈ᴮ coordinateHistory P :=
  mem_relationGraph_iff (fun _ => B_ext_pair_mem_left) (fun _ => B_ext_pair_mem_right)

/-- Exact triple membership retains the failed row `ξ = ρ`; the first
guard is membership in the successor, not membership in `ρ`. -/
theorem stoppedCoordinateTriangle_pair_iff {ρ P ξ σ v : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ Ord ρ) :
    Γ ≤ pair (pair ξ σ) v ∈ᴮ stoppedCoordinateTriangle ρ P ↔
      Γ ≤ ξ ∈ᴮ succ ρ ∧ Γ ≤ σ ∈ᴮ ξ ∧
        Γ ≤ pair (pair ξ σ) v ∈ᴮ coordinateHistory P := by
  rw [mem_stoppedCoordinateTriangle_iff, mem_triangleDomain_iff Hρ]
  constructor
  · rintro ⟨⟨Hξ, Hσ⟩, _, Hv⟩
    exact ⟨Hξ, Hσ, Hv⟩
  · rintro ⟨Hξ, Hσ, Hv⟩
    exact ⟨⟨Hξ, Hσ⟩, (coordinateHistory_pair_iff.mp Hv).2.2.1, Hv⟩

theorem stoppedCoordinateTriangle_failed_row_iff {ρ P σ v : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ Ord ρ) :
    Γ ≤ pair (pair ρ σ) v ∈ᴮ stoppedCoordinateTriangle ρ P ↔
      Γ ≤ σ ∈ᴮ ρ ∧ Γ ≤ pair (pair ρ σ) v ∈ᴮ coordinateHistory P := by
  rw [stoppedCoordinateTriangle_pair_iff Hρ]
  constructor
  · rintro ⟨_, Hσ, Hv⟩
    exact ⟨Hσ, Hv⟩
  · rintro ⟨Hσ, Hv⟩
    refine ⟨?_, Hσ, Hv⟩
    rw [show ρ ∈ᴮ succ ρ = ρ =ᴮ ρ ⊔ ρ ∈ᴮ ρ from mem_insert1]
    exact bv_refl.trans le_sup_left

theorem stoppedCoordinateTriangle_subset_product {ρ P : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ stoppedCoordinateTriangle ρ P ⊆ᴮ prod (triangleDomain ρ) omegaOne :=
  relationGraph_subset

theorem stoppedCoordinateTriangle_subset_history {ρ P : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ stoppedCoordinateTriangle ρ P ⊆ᴮ coordinateHistory P := by
  rw [subset_unfold']
  apply le_iInf
  intro e
  rw [← deduction]
  let Δ := Γ ⊓ e ∈ᴮ stoppedCoordinateTriangle ρ P
  have Hprod : Δ ≤ e ∈ᴮ prod (triangleDomain ρ) omegaOne :=
    mem_of_mem_subset stoppedCoordinateTriangle_subset_product inf_le_right
  obtain ⟨q, _, v, _, He⟩ := mem_prod_iff₂.mp Hprod
  have Hparts := mem_stoppedCoordinateTriangle_iff.mp (mem_congr He bv_refl
    (show Δ ≤ e ∈ᴮ stoppedCoordinateTriangle ρ P from inf_le_right))
  exact mem_congr (bv_symm He) bv_refl Hparts.2.2

theorem stoppedCoordinateTriangle_is_func {ρ P : bSet 𝔹} {Γ : 𝔹}
    (HX : Γ ≤ is_func (coordinateHistory P)) :
    Γ ≤ is_func (stoppedCoordinateTriangle ρ P) :=
  is_func_subset_of_is_func HX stoppedCoordinateTriangle_subset_history

/-- The triangular restriction is total on precisely the entire active
triangle whenever the decoded coordinate graph is total on the square. -/
theorem stoppedCoordinateTriangle_is_function {ρ P : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ ∈ᴮ omegaOne)
    (HX : Γ ≤ is_function (prod omegaOne omegaOne) omegaOne (coordinateHistory P)) :
    Γ ≤ is_function (triangleDomain ρ) omegaOne (stoppedCoordinateTriangle ρ P) := by
  apply relationGraph_is_function (P := fun q v => pair q v ∈ᴮ coordinateHistory P)
    (fun _ => B_ext_pair_mem_left) (fun _ => B_ext_pair_mem_right)
  · exact is_total_of_is_func' (is_func'_subset_of_is_func'
      (is_func'_of_is_function HX) (triangleDomain_subset_omegaOne_square Hρ))
  · intro q₁ q₂ v₁ v₂ Δ HΔ _ _ _ _ H₁ H₂ Heq
    exact eq_of_is_func_of_eq
      (HΔ.trans (HX.trans (inf_le_left.trans inf_le_left))) Heq H₁ H₂

theorem stoppedCoordinateTriangle_countable {ρ P : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ ∈ᴮ omegaOne) (HX : Γ ≤ is_func (coordinateHistory P)) :
    Γ ≤ injects_into (stoppedCoordinateTriangle ρ P) bSet.omega :=
  graph_countable_of_domain (stoppedCoordinateTriangle_is_func HX)
    stoppedCoordinateTriangle_subset_product (triangleDomain_countable Hρ)

def stoppedCoordinateValues (ρ P : bSet 𝔹) : bSet 𝔹 :=
  image (triangleDomain ρ) omegaOne (coordinateHistory P)

theorem mem_stoppedCoordinateValues_iff {ρ P v : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ v ∈ᴮ stoppedCoordinateValues ρ P ↔ Γ ≤ v ∈ᴮ omegaOne ∧
      Γ ≤ ⨆ q, q ∈ᴮ triangleDomain ρ ⊓ pair q v ∈ᴮ coordinateHistory P :=
  mem_image_iff

theorem stoppedCoordinateValues_subset {ρ P : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ stoppedCoordinateValues ρ P ⊆ᴮ omegaOne := image_subset

theorem stoppedCoordinateTriangle_image_eq {ρ P : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ image (triangleDomain ρ) omegaOne (stoppedCoordinateTriangle ρ P) =ᴮ
      stoppedCoordinateValues ρ P := by
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_image_iff.mp
      (show Γ ⊓ v ∈ᴮ image (triangleDomain ρ) omegaOne (stoppedCoordinateTriangle ρ P) ≤
        v ∈ᴮ image (triangleDomain ρ) omegaOne (stoppedCoordinateTriangle ρ P) from inf_le_right)
    obtain ⟨q, Hq⟩ := exists_convert Hv.2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_stoppedCoordinateValues_iff.mpr ⟨Hv.1, le_iSup_of_le q
      (le_inf (Hq.trans inf_le_left)
        (mem_stoppedCoordinateTriangle_iff.mp (Hq.trans inf_le_right)).2.2)⟩
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_stoppedCoordinateValues_iff.mp
      (show Γ ⊓ v ∈ᴮ stoppedCoordinateValues ρ P ≤
        v ∈ᴮ stoppedCoordinateValues ρ P from inf_le_right)
    obtain ⟨q, Hq⟩ := exists_convert Hv.2 (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_image_iff.mpr ⟨Hv.1, le_iSup_of_le q (le_inf (Hq.trans inf_le_left)
      (mem_stoppedCoordinateTriangle_iff.mpr
        ⟨Hq.trans inf_le_left, Hv.1, Hq.trans inf_le_right⟩))⟩

theorem stoppedCoordinateValues_countable {ρ P : bSet 𝔹} {Γ : 𝔹}
    (Hρ : Γ ≤ ρ ∈ᴮ omegaOne)
    (HX : Γ ≤ is_function (prod omegaOne omegaOne) omegaOne (coordinateHistory P)) :
    Γ ≤ injects_into (stoppedCoordinateValues ρ P) bSet.omega :=
  restricted_image_countable (is_func'_of_is_function HX)
    (triangleDomain_subset_omegaOne_square Hρ) (triangleDomain_countable Hρ)

/-- The actual full run supplies the required coordinate functionality;
neither stopping nor successful vertex choice is needed for this bound. -/
theorem stoppedCoordinateTriangle_of_run
    {color : Bool} {R S top P ρ : bSet 𝔹} {Γ : 𝔹}
    (HP : Γ ≤ is_function omegaOne entrySpace P)
    (Hlaw : Γ ≤ runLaw color R S top P) (Hρ : Γ ≤ ρ ∈ᴮ omegaOne) :
    Γ ≤ is_function (triangleDomain ρ) omegaOne (stoppedCoordinateTriangle ρ P) ⊓
      (injects_into (stoppedCoordinateTriangle ρ P) bSet.omega ⊓
        injects_into (stoppedCoordinateValues ρ P) bSet.omega) := by
  have HX := coordinateHistory_is_function_of_run HP Hlaw
  exact le_inf (stoppedCoordinateTriangle_is_function Hρ HX)
    (le_inf (stoppedCoordinateTriangle_countable Hρ
      (HX.trans (inf_le_left.trans inf_le_left))) (stoppedCoordinateValues_countable Hρ HX))

end bSet.ErdosStoppedCoordinateTriangle
