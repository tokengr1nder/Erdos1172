/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingCohenDenseTests

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

private theorem dense_bounded (Q D : bSet V) : denseValue Q (fun z => z ∈ᴮ D) =
    ⨅ i : Q.type, _root_.imp (Q.bval i) (⨆ j : Q.type, Q.bval j ⊓ ((Q.func i ⊆ᴮ Q.func j) ⊓ (Q.func j ∈ᴮ D))) := by
  unfold denseValue
  rw [← bounded_forall (h_congr := B_ext_iSup (h := fun _ =>
    B_ext_inf B_ext_const (B_ext_inf B_ext_subset_left B_ext_const)))]
  apply iInf_congr
  intro i
  rw [← bounded_exists (h_congr := B_ext_inf B_ext_subset_right B_ext_mem_left)]

theorem map_named_density (Q D : bSet V) : f (denseValue Q (fun z => z ∈ᴮ D)) =
    denseValue (mapNames f Q) (fun z => z ∈ᴮ mapNames f D) := by
  cases Q with
  | mk I z w =>
    rw [dense_bounded,dense_bounded]
    simp only [mapNames_mk,bSet.type,bSet.bval,bSet.func,map_iInf,map_iSup,map_imp,map_inf,map_mem,map_subset]

private theorem dense_ext_carrier (D : bSet E) : B_ext (fun Q => denseValue Q (fun z => z ∈ᴮ D)) := by
  unfold denseValue
  exact B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right)
    (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)))

private theorem dense_ext_set (Q : bSet E) : B_ext (fun D => denseValue Q (fun z => z ∈ᴮ D)) := by
  unfold denseValue
  exact B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
    (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const (B_ext_inf B_ext_const B_ext_mem_right))))

/-- A local source reading of a target dense set is genuinely dense in the
source Cohen forcing, on the lower projection of that same joint context. -/
theorem descend_named_cohen_density
    (same : (⊤ : E) ≤ mapNames f Pos =ᴮ mapNames g Pos) (D : bSet V) (U : bSet R) (Γ : E)
    (hd : Γ ≤ f (denseValue Pos (fun x => x ∈ᴮ D)))
    (reads : Γ ≤ mapNames f D =ᴮ mapNames g U) :
    lowerProjection g Γ ≤ denseValue Pos (fun x => x ∈ᴮ U) := by
  apply lowerProjection_le
  rw [map_named_density]
  exact bv_rw'' reads (bv_rw'' (le_top.trans same) (hd.trans_eq (map_named_density f _ _))
    (dense_ext_carrier (mapNames f D))) (dense_ext_set (mapNames g Pos))

end Erdos1172LevyCollapse.Matching
