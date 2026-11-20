/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part3CofinalPowerCoverCoverage

@[expose] public section

/-!
# Constructed monotone cofinal covers at every finite power

Strong induction supplies all lower-dimensional cover families. The
assembled two-dimensional profile is coded into one omegaOne function.
Thus every small well-order with a cofinal omegaOne^(n+1) subset has a
monotone family of exact cofinal covers containing every such subset.
There is no CH, domination, or lower-cover hypothesis in the final result.
-/

open Cardinal Ordinal Set Order

namespace Erdos1172Part3CofinalPowerCovers

open ErdosRadoCHAsym (W1)
open Erdos1172Part3CofinalPowerEndpoints (below)
open Erdos1172Part3CofinalPowerCoverAssembly (LowerCovers)
open Erdos1172Part3CofinalCoverSupport (FinitelySupported)

structure CofinalCovers (n : ℕ) (V : Type) [LinearOrder V] [WellFoundedLT V] where
  family : (W1 → W1) → Set V
  mono : Monotone family
  supported : FinitelySupported family
  cofinal : ∀ f, IsCofinal (family f)
  orderType : ∀ f, typeLT (family f) = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal)
  covers : ∀ A : Set V, IsCofinal A →
    typeLT A = (ω_ 1 : Ordinal.{0}) ^ ((n + 1 : ℕ) : Ordinal) →
      ∃ f : W1 → W1, A ⊆ family f

end Erdos1172Part3CofinalPowerCovers
