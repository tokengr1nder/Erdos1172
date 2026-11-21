/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4InternalSmallCodomainPigeonhole

@[expose] public section

/-!
# A full-sized fiber of internally bounded pointwise labels

An actual bounded selector is constructed from pointwise internal
existence, then the internal small-codomain pigeonhole theorem supplies
one label and its omega-two-large fiber at the original condition. No
stationarity, supplied coherent choice, or external case distinction is
used. The label predicate may retain additional witnesses internally.
-/

set_option autoImplicit false

open scoped Flypitch
open Lattice

universe u

namespace bSet.ErdosLargeHistoryFiber

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

open ErdosOmegaTwo ErdosFiberInjection ErdosSmallFiberBound
open ErdosSmallCodomainPigeonhole

/-- Internal pointwise labels in a small actual set become constant on
an actual full-sized subfamily, without changing the Boolean context. -/
theorem exists_large_constant_label
    {S K : bSet 𝔹} {P : bSet 𝔹 → bSet 𝔹 → 𝔹} {Γ : 𝔹}
    (HCH : Γ ≤ (CH : 𝔹)) (HS : Γ ≤ injects_into omegaTwo S)
    (HK : Γ ≤ injects_into K omegaOne)
    (Hleft : ∀ k, B_ext (fun top => P top k))
    (Hright : ∀ top, B_ext (P top))
    (Hex : Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ S) (⨆ k, k ∈ᴮ K ⊓ P top k)) :
    ∃ k T : bSet 𝔹, (Γ ≤ k ∈ᴮ K) ∧ (Γ ≤ T ⊆ᴮ S) ∧
      (Γ ≤ injects_into omegaTwo T) ∧
      Γ ≤ ⨅ top, _root_.imp (top ∈ᴮ T) (P top k) := by
  obtain ⟨f, Hf⟩ := exists_selector_of_pointwise Hleft Hright Hex
  have Hfunction := Hf.trans inf_le_left
  have Hchoice := Hf.trans inf_le_right
  obtain ⟨k, Hk⟩ := exists_convert
    (omegaTwo_pigeonhole_of_small_codomain HCH Hfunction HK HS)
    (B_ext_inf B_ext_mem_left
      (B_ext_term (ϕ := fun T => injects_into omegaTwo T) (t := fiber S f)
        B_ext_injects_into_right (fiber_congr S f)))
  refine ⟨k, fiber S f k, Hk.trans inf_le_left, fiber_subset, Hk.trans inf_le_right, ?_⟩
  apply le_iInf
  intro top
  rw [← deduction]
  have Hparts := mem_fiber_iff.mp
    (show Γ ⊓ top ∈ᴮ fiber S f k ≤ top ∈ᴮ fiber S f k from inf_le_right)
  exact (le_inf
    (inf_le_left.trans (Hchoice.trans ((iInf_le _ top).trans (iInf_le _ k))))
    (le_inf Hparts.1 Hparts.2)).trans bv_imp_elim

end bSet.ErdosLargeHistoryFiber
