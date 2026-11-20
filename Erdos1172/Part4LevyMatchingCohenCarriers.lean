/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingCohenGraphReading
public import Erdos1172.Part4LevyMatchingCommonPreparation
public import Erdos1172.Part4BooleanQuotientDenseSets

@[expose] public section

/-! # Equality of the full matched Cohen forcings and descent of named dense sets -/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal bSet Lattice ErdosNameTransport ErdosOmegaTwo Erdos1172BooleanFactor Erdos1172BooleanQuotient
open scoped Flypitch
namespace Erdos1172LevyCollapse.Matching
variable {V R E : Type u} [NontrivialCompleteBooleanAlgebra V] [NontrivialCompleteBooleanAlgebra R]
    [NontrivialCompleteBooleanAlgebra E]
variable (f : CompleteLatticeHom V E) (g : CompleteLatticeHom R E)
local notation "Pos" => ErdosCohen.conditions omegaOne

private theorem mapped_subset (X : bSet V) (Y : bSet E)
    (h : ∀ x : bSet V, f (x ∈ᴮ X) ≤ mapNames f x ∈ᴮ Y) :
    (⊤ : E) ≤ mapNames f X ⊆ᴮ Y := by
  cases X with
  | mk I z w =>
    rw [subset_unfold]
    apply le_iInf
    intro i
    rw [← deduction]
    exact inf_le_right.trans ((OrderHomClass.mono f (mem_mk' (bSet.mk I z w) i)).trans (h _))

private theorem carrier_subset {θ : Cardinal.{u}} (unc : ℵ₀ < θ)
    (left : (⊤ : V) ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaOne)
    (right : (⊤ : R) ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaOne)
    (read : ∀ (X : Type u), #X < θ → ∀ v : X → V, ArrayRead f g v) :
    (⊤ : E) ≤ mapNames f Pos ⊆ᴮ mapNames g Pos := by
  apply mapped_subset f
  intro x
  have count (β : Ordinal.{u}) (small : β < θ.ord) : (⊤ : R) ≤ check (PSet.ordinalMk β) ∈ᴮ omegaOne :=
    mem_congr bv_refl right (check_mem (PSet.mk_mem_mk_of_lt small))
  have valid : x ∈ᴮ Pos ≤ ErdosCohen.condition omegaOne x := ErdosCohen.mem_conditions_iff.mp le_rfl
  apply ((OrderHomClass.mono f valid).trans (cohen_graph_reading_of_height g f read count unc left x)).trans
  apply iSup_le
  intro y
  apply bv_rw' (ϕ := fun z => z ∈ᴮ mapNames g Pos) inf_le_right (h_congr := B_ext_mem_left)
  exact inf_le_left.trans ((OrderHomClass.mono g (ErdosCohen.mem_conditions_iff.mpr
    (le_rfl : ErdosCohen.condition omegaOne y ≤ _))).trans_eq (map_mem g y Pos))

/-- The hereditary images of the complete internal Cohen condition
carriers are equal with truth value top, including arbitrary mixed graphs. -/
theorem matched_cohen_conditions_eq {θ : Cardinal.{u}} (unc : ℵ₀ < θ)
    (left : (⊤ : V) ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaOne)
    (right : (⊤ : R) ≤ check (PSet.ordinalMk θ.ord) =ᴮ omegaOne)
    (forward : ∀ (X : Type u), #X < θ → ∀ v : X → V, ArrayRead f g v)
    (back : ∀ (X : Type u), #X < θ → ∀ v : X → R, ArrayRead g f v) :
    (⊤ : E) ≤ mapNames f Pos =ᴮ mapNames g Pos :=
  subset_ext (carrier_subset f g unc left right forward) (carrier_subset g f unc right left back)

end Erdos1172LevyCollapse.Matching
