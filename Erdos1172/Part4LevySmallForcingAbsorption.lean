/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaDenseCoverIso

@[expose] public section

/-! # Absorption of a small forcing by one countable Lévy collapse -/

set_option autoImplicit false
noncomputable section
open Erdos1172PosetCompletion Erdos1172PositiveBoolean Erdos1172Collapse Cardinal
universe u
namespace Erdos1172LevyCollapse.Absorption

variable {B X : Type u} [CompleteBooleanAlgebra B] (d : X → Positive B)
local notation "Tree" => Erdos1172Collapse.Condition X
local notation "Target" => Positive B × Erdos1172Collapse.Condition X

variable (hX : ℵ₀ ≤ #X)

end Erdos1172LevyCollapse.Absorption
