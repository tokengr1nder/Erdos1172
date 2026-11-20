/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousEntry
public import Erdos1172.Part4InternalSimultaneousCandidateCongruence
public import Erdos1172.Part4InternalSimultaneousVertexCongruence
public import Erdos1172.Part4InternalFunctionRestriction

@[expose] public section

/-!
# Preservation of a complete entry under history extension

The stage and both decoded histories are extensional parameters of the
entry law. A functional extension of already-total guarded histories
preserves the actual row-candidate and future-candidate names. Therefore
it preserves the complete entry, including the same row graph and the
same least-or-sentinel vertex. No successful branch or injectivity
assumption is introduced.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosSimultaneousEntry

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosOrdinalLeast ErdosOrdinalFallback
open ErdosSimultaneousCandidates ErdosSimultaneousRowChoice ErdosSimultaneousVertex

theorem simultaneousRowLaw_ext_stage (S Y X top Z : bSet 𝔹) :
    B_ext (fun δ => simultaneousRowLaw δ S Y X top Z) :=
  B_ext_iInf (h := fun σ => B_ext_iInf (h := fun v =>
    B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_term (ϕ := fun C => leastIn C v)
        (t := fun δ => simultaneousCandidates δ S Y X top σ)
        (leastIn_ext_set v) (simultaneousCandidates_congr_stage S Y X top σ))))

theorem simultaneousRowLaw_ext_vertices (δ S X top Z : bSet 𝔹) :
    B_ext (fun Y => simultaneousRowLaw δ S Y X top Z) :=
  B_ext_iInf (h := fun σ => B_ext_iInf (h := fun v =>
    B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_term (ϕ := fun C => leastIn C v)
        (t := fun Y => simultaneousCandidates δ S Y X top σ)
        (leastIn_ext_set v) (simultaneousCandidates_congr_vertices δ S X top σ))))

theorem simultaneousRowLaw_ext_history (δ S Y top Z : bSet 𝔹) :
    B_ext (fun X => simultaneousRowLaw δ S Y X top Z) :=
  B_ext_iInf (h := fun σ => B_ext_iInf (h := fun v =>
    B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_term (ϕ := fun C => leastIn C v)
        (t := fun X => simultaneousCandidates δ S Y X top σ)
        (leastIn_ext_set v) (simultaneousCandidates_congr_history δ S Y top σ))))

theorem entryValid_ext_stage (color : Bool) (R S Y X top y Z : bSet 𝔹) :
    B_ext (fun δ => entryValid color δ R S Y X top y Z) :=
  B_ext_inf B_ext_const (B_ext_inf (simultaneousRowLaw_ext_stage S Y X top Z)
    (B_ext_term (ϕ := fun C => leastOrTop C top y)
      (t := fun δ => futureCandidates color δ R S Y X Z top)
      (leastOrTop_ext_set top y) (futureCandidates_congr_stage color R S Y X Z top)))

theorem entryValid_ext_vertices (color : Bool) (δ R S X top y Z : bSet 𝔹) :
    B_ext (fun Y => entryValid color δ R S Y X top y Z) :=
  B_ext_inf B_ext_const (B_ext_inf (simultaneousRowLaw_ext_vertices δ S X top Z)
    (B_ext_term (ϕ := fun C => leastOrTop C top y)
      (t := fun Y => futureCandidates color δ R S Y X Z top)
      (leastOrTop_ext_set top y) (futureCandidates_congr_vertices color δ R S X Z top)))

theorem entryValid_ext_history (color : Bool) (δ R S Y top y Z : bSet 𝔹) :
    B_ext (fun X => entryValid color δ R S Y X top y Z) :=
  B_ext_inf B_ext_const (B_ext_inf (simultaneousRowLaw_ext_history δ S Y top Z)
    (B_ext_term (ϕ := fun C => leastOrTop C top y)
      (t := fun X => futureCandidates color δ R S Y X Z top)
      (leastOrTop_ext_set top y) (futureCandidates_congr_history color δ R S Y Z top)))

/-- Every row retains precisely its previous least candidate after a
functional extension of the histories on which it depends. -/
theorem simultaneousRowLaw_of_history_extension
    {δ S Y X Y' X' top Z : bSet 𝔹} {Γ : 𝔹}
    (HsubY : Γ ≤ Y ⊆ᴮ Y') (HsubX : Γ ≤ X ⊆ᴮ X')
    (HfuncY' : Γ ≤ is_func Y') (HfuncX' : Γ ≤ is_func X')
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hlaw : Γ ≤ simultaneousRowLaw δ S Y X top Z) :
    Γ ≤ simultaneousRowLaw δ S Y' X' top Z := by
  apply le_iInf
  intro σ
  apply le_iInf
  intro v
  rw [← deduction]
  let Δ := Γ ⊓ (σ ∈ᴮ omegaOne ⊓ pair σ v ∈ᴮ Z)
  have HΔ : Δ ≤ Γ := inf_le_left
  have Hσ : Δ ≤ σ ∈ᴮ omegaOne := inf_le_right.trans inf_le_left
  have Hpair : Δ ≤ pair σ v ∈ᴮ Z := inf_le_right.trans inf_le_right
  have Heq : Δ ≤ simultaneousCandidates δ S Y X top σ =ᴮ
      simultaneousCandidates δ S Y' X' top σ :=
    simultaneousCandidates_eq_of_extension (HΔ.trans HsubY) (HΔ.trans HsubX)
      (HΔ.trans HfuncY') (HΔ.trans HfuncX') (HΔ.trans HY) (HΔ.trans HX) Hσ
  exact bv_rw'' (ϕ := fun C => leastIn C v) Heq
    (simultaneousRowLaw_apply (HΔ.trans Hlaw) Hσ Hpair) (leastIn_ext_set v)

/-- An already valid entry remains valid for larger functional histories
that extend the old total prefix. The current row graph is unchanged;
its own totality supplies the active-prefix condition of the vertex law. -/
theorem entryValid_of_history_extension
    {color : Bool} {δ R S Y X Y' X' top y Z : bSet 𝔹} {Γ : 𝔹}
    (HsubY : Γ ≤ Y ⊆ᴮ Y') (HsubX : Γ ≤ X ⊆ᴮ X')
    (HfuncY' : Γ ≤ is_func Y') (HfuncX' : Γ ≤ is_func X')
    (HY : Γ ≤ is_func' δ omegaTwo Y)
    (HX : Γ ≤ is_func' (prod δ omegaOne) omegaOne X)
    (Hδ : Γ ≤ δ ⊆ᴮ omegaOne)
    (Hentry : Γ ≤ entryValid color δ R S Y X top y Z) :
    Γ ≤ entryValid color δ R S Y' X' top y Z := by
  have HZ : Γ ≤ is_function omegaOne omegaOne Z := Hentry.trans inf_le_left
  have HZprefix : Γ ≤ is_func' δ omegaOne Z :=
    ErdosFunctionRestriction.is_func'_restrict_domain Hδ HZ
  have Heq : Γ ≤ futureCandidates color δ R S Y X Z top =ᴮ
      futureCandidates color δ R S Y' X' Z top :=
    futureCandidates_eq_of_extension HsubY HsubX subset_self HfuncY' HfuncX'
      (HZ.trans (inf_le_left.trans inf_le_left)) HY HX HZprefix Hδ
  exact le_inf HZ
    (le_inf (simultaneousRowLaw_of_history_extension HsubY HsubX HfuncY' HfuncX'
      HY HX (Hentry.trans (inf_le_right.trans inf_le_left)))
      (bv_rw'' (ϕ := fun C => leastOrTop C top y) Heq
        (Hentry.trans (inf_le_right.trans inf_le_right)) (leastOrTop_ext_set top y)))

end bSet.ErdosSimultaneousEntry
