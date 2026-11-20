/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4GroundUltrapower
public import Mathlib.ModelTheory.Ultraproducts
public import Mathlib.ModelTheory.ElementaryMaps

@[expose] public section

/-! # The elementary embedding into the transitive ground ultrapower

Łoś's theorem gives elementarity for the diagonal map into the abstract
ultrapower. The collapse then identifies that structure with an actual
transitive class of sets carrying ordinary membership.
-/

set_option autoImplicit false
noncomputable section
open FirstOrder Filter
universe u

namespace Erdos1172GroundUltrapower

inductive MemSymbol : ℕ → Type
  | mem : MemSymbol 2

def setLanguage : Language := ⟨fun _ => Empty, MemSymbol⟩
  deriving Language.IsRelational

instance baseStructure : setLanguage.Structure ZFSet.{u} where
  RelMap | .mem => fun x => x 0 ∈ x 1

variable {I : Type u} (U : Ultrafilter I) [CountableInterFilter (U : Filter I)]

abbrev AbstractModel := (U : Filter I).Product (fun _ : I => ZFSet.{u})
def targetClass : Set ZFSet.{u} := Set.range (collapse U)

theorem targetClass_transitive {x y : ZFSet.{u}} (hx : x ∈ targetClass U) (hy : y ∈ x) :
    y ∈ targetClass U := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, _, hb⟩ := (mem_collapse_iff U _ a).mp hy
  exact ⟨b, hb⟩

instance targetStructure : setLanguage.Structure (targetClass U) where
  RelMap | .mem => fun x => (x 0).val ∈ (x 1).val

def collapseIso : AbstractModel U ≃[setLanguage] targetClass U where
  toEquiv := Equiv.ofInjective (collapse U) (collapse_injective U)
  map_fun' := fun f => nomatch f
  map_rel' := by
    intro n r v
    cases r
    have rep (i : Fin 2) : ∃ w : I → ZFSet.{u}, (w : AbstractModel U) = v i := by
      exact Quotient.exists_rep (v i)
    choose w hw using rep
    rw [← funext hw]
    change collapse U (Germ.ofFun (w 0)) ∈ collapse U (Germ.ofFun (w 1)) ↔ _
    rw [collapse_mem_collapse_iff, memRel_rep]
    symm
    apply Language.relMap_quotient_mk'

def abstractDiagonal : ZFSet.{u} ↪ₑ[setLanguage] AbstractModel U where
  toFun a := (fun _ : I => a : AbstractModel U)
  map_formula' := by
    intro n φ v
    have h := Language.Ultraproduct.realize_formula_cast
      (M := fun _ : I => ZFSet.{u}) (u := U) φ (fun j _ => v j)
    exact h.trans eventually_const

def groundEmbedding : ZFSet.{u} ↪ₑ[setLanguage] targetClass U :=
  (collapseIso U).toElementaryEmbedding.comp (abstractDiagonal U)

theorem groundEmbedding_val (x : ZFSet.{u}) :
    (groundEmbedding U x).val = diagonal U x := rfl

end Erdos1172GroundUltrapower
