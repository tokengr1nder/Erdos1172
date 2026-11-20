/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSimultaneousRunPartial

@[expose] public section

/-!
# Endpoint congruence of the exact stopped-run law

The endpoint occurs in the seed requirements, the next-vertex candidate
bound, and the empty-candidate fallback. All three occurrences are
transported together. The results are unconditional on the histories:
no functionality, ordinal, nonemptiness, or successful-run premise is used.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

namespace ErdosSimultaneousCandidates

theorem rowRequirements_ext_top (δ S Y X σ v : bSet 𝔹) :
    B_ext (fun top => rowRequirements δ S Y X top σ v) :=
  B_ext_inf
    (B_ext_iInf (h := fun _ => B_ext_imp
      (h₁ := B_ext_pair_right B_ext_pair_mem_left) (h₂ := B_ext_const)))
    B_ext_const

theorem simultaneousCandidates_congr_top (δ S Y X σ : bSet 𝔹) :
    B_congr (fun top => simultaneousCandidates δ S Y X top σ) := by
  intro a b Γ H
  apply mem_ext
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_simultaneousCandidates_iff.mp
      (show Γ ⊓ v ∈ᴮ simultaneousCandidates δ S Y X a σ ≤
        v ∈ᴮ simultaneousCandidates δ S Y X a σ from inf_le_right)
    exact mem_simultaneousCandidates_iff.mpr ⟨Hv.1,
      bv_rw'' (ϕ := fun top => rowRequirements δ S Y X top σ v)
        (inf_le_left.trans H) Hv.2 (rowRequirements_ext_top δ S Y X σ v)⟩
  · apply le_iInf
    intro v
    rw [← deduction]
    have Hv := mem_simultaneousCandidates_iff.mp
      (show Γ ⊓ v ∈ᴮ simultaneousCandidates δ S Y X b σ ≤
        v ∈ᴮ simultaneousCandidates δ S Y X b σ from inf_le_right)
    exact mem_simultaneousCandidates_iff.mpr ⟨Hv.1,
      bv_rw'' (ϕ := fun top => rowRequirements δ S Y X top σ v)
        (inf_le_left.trans (bv_symm H)) Hv.2 (rowRequirements_ext_top δ S Y X σ v)⟩

end ErdosSimultaneousCandidates

namespace ErdosSimultaneousRowChoice

open ErdosSimultaneousCandidates ErdosOrdinalLeast

theorem simultaneousRowLaw_ext_top (δ S Y X Z : bSet 𝔹) :
    B_ext (fun top => simultaneousRowLaw δ S Y X top Z) :=
  B_ext_iInf (h := fun σ => B_ext_iInf (h := fun v =>
    B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_term (ϕ := fun C => leastIn C v)
        (t := fun top => simultaneousCandidates δ S Y X top σ)
        (leastIn_ext_set v) (simultaneousCandidates_congr_top δ S Y X σ))))

end ErdosSimultaneousRowChoice

namespace ErdosSimultaneousVertex

open ErdosPartition ErdosOrdinalFallback

theorem futureRequirements_ext_top (color : Bool) (δ R S Y X Z y : bSet 𝔹) :
    B_ext (fun top => futureRequirements color δ R S Y X Z top y) :=
  B_ext_inf B_ext_const (B_ext_inf (graphColor_ext_right color R y) B_ext_const)

/-- Endpoint transport changes the comprehension bound as well as its
predicate. In particular, it is not just predicate congruence. -/
theorem futureCandidates_congr_top (color : Bool) (δ R S Y X Z : bSet 𝔹) :
    B_congr (fun top => futureCandidates color δ R S Y X Z top) := by
  intro a b Γ H
  apply mem_ext
  · apply le_iInf
    intro y
    rw [← deduction]
    have Hy := mem_futureCandidates_iff.mp
      (show Γ ⊓ y ∈ᴮ futureCandidates color δ R S Y X Z a ≤
        y ∈ᴮ futureCandidates color δ R S Y X Z a from inf_le_right)
    exact mem_futureCandidates_iff.mpr
      ⟨mem_congr bv_refl (inf_le_left.trans H) Hy.1,
        bv_rw'' (ϕ := fun top => futureRequirements color δ R S Y X Z top y)
          (inf_le_left.trans H) Hy.2 (futureRequirements_ext_top color δ R S Y X Z y)⟩
  · apply le_iInf
    intro y
    rw [← deduction]
    have Hy := mem_futureCandidates_iff.mp
      (show Γ ⊓ y ∈ᴮ futureCandidates color δ R S Y X Z b ≤
        y ∈ᴮ futureCandidates color δ R S Y X Z b from inf_le_right)
    exact mem_futureCandidates_iff.mpr
      ⟨mem_congr bv_refl (inf_le_left.trans (bv_symm H)) Hy.1,
        bv_rw'' (ϕ := fun top => futureRequirements color δ R S Y X Z top y)
          (inf_le_left.trans (bv_symm H)) Hy.2
          (futureRequirements_ext_top color δ R S Y X Z y)⟩

/-- Both the candidate set and the fallback value depend on the endpoint. -/
theorem nextVertexChoice_ext_top (color : Bool) (δ R S Y X Z y : bSet 𝔹) :
    B_ext (fun top => leastOrTop (futureCandidates color δ R S Y X Z top) top y) := by
  intro a b
  let Γ := a =ᴮ b ⊓ leastOrTop (futureCandidates color δ R S Y X Z a) a y
  have HC : Γ ≤ futureCandidates color δ R S Y X Z a =ᴮ
      futureCandidates color δ R S Y X Z b :=
    futureCandidates_congr_top color δ R S Y X Z inf_le_left
  have Hmid : Γ ≤ leastOrTop (futureCandidates color δ R S Y X Z b) a y :=
    bv_rw'' (ϕ := fun C => leastOrTop C a y) HC inf_le_right (leastOrTop_ext_set a y)
  exact bv_rw'' (ϕ := fun top => leastOrTop (futureCandidates color δ R S Y X Z b) top y)
    inf_le_left Hmid (leastOrTop_ext_top (futureCandidates color δ R S Y X Z b) y)

end ErdosSimultaneousVertex

namespace ErdosSimultaneousEntry

open ErdosSimultaneousRowChoice ErdosSimultaneousVertex

theorem entryValid_ext_top (color : Bool) (δ R S Y X y Z : bSet 𝔹) :
    B_ext (fun top => entryValid color δ R S Y X top y Z) :=
  B_ext_inf B_ext_const (B_ext_inf (simultaneousRowLaw_ext_top δ S Y X Z)
    (nextVertexChoice_ext_top color δ R S Y X Z y))

end ErdosSimultaneousEntry

namespace ErdosSimultaneousRun

open ErdosSimultaneousEntry ErdosSimultaneousHistory

/-- Extensionality in the endpoint holds for every graph name, including
partial histories and arbitrary mixed Boolean conditions. -/
theorem runLaw_ext_top (color : Bool) (R S P : bSet 𝔹) :
    B_ext (fun top => runLaw color R S top P) :=
  B_ext_iInf (h := fun i => B_ext_iInf (h := fun y => B_ext_iInf (h := fun Z =>
    B_ext_imp (h₁ := B_ext_const)
      (h₂ := entryValid_ext_top color i R S (vertexHistory P) (coordinateHistory P) y Z))))

theorem runPartial_ext_top (color : Bool) (R S P : bSet 𝔹) :
    B_ext (fun top => runPartial color R S top P) :=
  B_ext_inf B_ext_const (runLaw_ext_top color R S P)

end ErdosSimultaneousRun

end bSet
