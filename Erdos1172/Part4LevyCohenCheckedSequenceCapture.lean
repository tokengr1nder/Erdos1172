/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4BooleanCountableGroundCapture
public import Erdos1172.Part4CohenCheckedSequenceReading
public import Erdos1172.Part4InternalIndependentHomogeneous

@[expose] public section

/-!
# Small ground ranges for recovered checked-value omega sequences

An actual first-stage supported omega function has internally countable
image. The strict first-stage kappa-chain condition captures this image
inside a ground subfamily of cardinal below kappa. Factoring through the
image then narrows the codomain of the SAME supported graph.

Apply this construction at each source function's entire validity value
in the ambient reading cover. The result preserves the original ambient
Boolean condition and both source validity and full graph equality. It is
a joined cover over small ground subfamilies and source graph names, not
one globally chosen representative. No strict kappa-chain condition for
the final algebra, anonymous recovery, or ideal construction is asserted.
-/

set_option autoImplicit false

noncomputable section

open scoped Flypitch
open Lattice

universe u

namespace Erdos1172LevyCohen

open bSet bSet.ErdosNameTransport

/-- The same actual source graph takes all its values in a genuinely small
ground subfamily at the unchanged first-stage Boolean condition. -/
theorem firstStage_function_ground_capture (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (A : PSet.{u}) {g : bSet (FirstAlgebra κ)} {Γ : FirstAlgebra κ}
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    (Hg : Γ ≤ is_function omega (check A) g) :
    ∃ A₀ : PSet.{u}, Cardinal.mk A₀.Type < κ ∧ A₀ ⊆ A ∧ Γ ≤ is_function omega (check A₀) g := by
  have Hcount : Γ ≤ injects_into (image omega (check A) g) omega :=
    ErdosCountableImage.image_countable_of_function Hg injects_into_refl
  obtain ⟨A₀, Hsmall, Hsub, Hcapture⟩ :=
    firstStage_exists_countable_ground_capture κ Hκ Hunc A Hsep Hcount image_subset
  exact ⟨A₀, Hsmall, Hsub,
    ErdosIndependentHomogeneous.is_function_codomain_mono Hcapture (factor_image_is_function Hg)⟩

/-- Arbitrary ambient supported checked-value omega sequences are covered
at their original condition by source functions into small ground
subfamilies. The source validity guard remains inside every Boolean piece. -/
theorem checked_sequence_small_ground_capture_cover (κ : Cardinal.{u})
    (Hκ : κ.IsRegular) (Hunc : Cardinal.aleph0 < κ)
    (A : PSet.{u})
    (Hsep : ∀ i j : A.Type, i ≠ j → ¬ PSet.Equiv (A.Func i) (A.Func j))
    {f : bSet (Algebra κ)} {Γ : Algebra κ}
    (Hf : Γ ≤ is_function omega (check A) f) :
    Γ ≤ ⨆ A₀ : {C : PSet.{u} // Cardinal.mk C.Type < κ ∧ C ⊆ A},
      ⨆ g : bSet (FirstAlgebra κ),
        firstStageHom κ (is_function omega (check A₀.val) g) ⊓
          (f =ᴮ mapNames (firstStageHom κ) g) := by
  have Hreading : Γ ≤ ⨆ g : bSet (FirstAlgebra κ),
      firstStageHom κ (is_function omega (check A) g) ⊓ (f =ᴮ mapNames (firstStageHom κ) g) :=
    Erdos1172CohenIteration.checked_sequence_reading_cover (B := FirstAlgebra κ) A Hf
  apply Hreading.trans
  apply iSup_le
  intro g
  obtain ⟨A₀, Hsmall, Hsub, Hg⟩ :=
    firstStage_function_ground_capture κ Hκ Hunc A Hsep
      (show is_function omega (check A) g ≤ is_function omega (check A) g from le_rfl)
  apply le_iSup_of_le ⟨A₀, Hsmall, Hsub⟩
  apply le_iSup_of_le g
  exact inf_le_inf (OrderHomClass.mono (firstStageHom κ) Hg) le_rfl

end Erdos1172LevyCohen
