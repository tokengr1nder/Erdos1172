/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaCoverPreservation

@[expose] public section

/-! # Completions of forcing covers reflecting compatibility -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion
universe u
namespace Erdos1172Shioya.ForcingCover

variable {S T : Type u} [Preorder S] [Preorder T] (f : S →o T) (hl : Lifts f)
variable (hc : ∀ a b : S, f a ≤ f b → ∃ z ≤ a, z ≤ b)

include hc in
theorem booleanHom_condition (s : S) : booleanHom f hl (condition (f s)) = condition s := by
  refine le_antisymm ?_ (condition_le_iff.mpr (show f s ∈ (condition (f s)).val from mem_condition_self _))
  intro x hx
  apply (mem_condition_iff s x).mpr
  intro y hy
  obtain ⟨t, hty, hts⟩ := (mem_condition_iff (f s) (f x)).mp hx (f y) (f.monotone hy)
  obtain ⟨v, hvy, hvt⟩ := hl y t hty
  obtain ⟨z, hzv, hzs⟩ := hc v s (hvt.trans hts)
  exact ⟨z, hzv.trans hvy, hzs⟩

include hc in
theorem booleanHom_surjective : Function.Surjective (booleanHom f hl) := by
  intro b
  let A := {p : S // condition p ≤ b}
  refine ⟨⨆ p : A, condition (f p.val), ?_⟩
  simp only [map_iSup, booleanHom_condition f hl hc]
  refine le_antisymm (iSup_le (fun p : A => p.property)) ?_
  intro x hx
  have hm : condition x ≤ b := condition_le_iff.mpr hx
  exact condition_le_iff.mp (le_iSup (fun p : A => condition p.val) ⟨x, hm⟩)

def completionIso (hd : ∀ t, ∃ s, f s ≤ t) : Completion T ≃o Completion S where
  toEquiv := Equiv.ofBijective _ ⟨booleanHom_injective f hl hd, booleanHom_surjective f hl hc⟩
  map_rel_iff' := by
    intro b c
    change booleanHom f hl b ≤ booleanHom f hl c ↔ b ≤ c
    refine ⟨fun h => ?_, fun h => OrderHomClass.mono (booleanHom f hl) h⟩
    apply le_of_dense_conditions_le (Set.range f) (fun t => by
      obtain ⟨s, hs⟩ := hd t
      exact ⟨f s, Set.mem_range_self s, hs⟩)
    rintro ⟨_, s, rfl⟩ hb
    have hm : f s ∈ b.val := condition_le_iff.mp hb
    exact condition_le_iff.mpr (h (show s ∈ (booleanHom f hl b).val from hm))

end Erdos1172Shioya.ForcingCover
