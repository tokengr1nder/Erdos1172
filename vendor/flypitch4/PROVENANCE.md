# Flypitch Boolean-Valued ZFC Foundation

Upstream source:
[ianklatzco/flypitch](https://github.com/ianklatzco/flypitch/tree/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4),
commit `ad649f89e9f3107b7e2ea97a58b2eafdfc80b815` (Lean 4 port by Ian Klatzco of the
Lean 3 [Flypitch](https://github.com/flypitch/flypitch) development by Jesse Han and Floris van Doorn, 2019).
Original copyright notices are retained in the vendored files, and the upstream Apache License 2.0
text appears at the repository root in [LICENSE](../../LICENSE).

## Vendored Subset and Local Modifications

Only the eight modules required for the Boolean-valued set-theoretic model `bSet` and its
first-order `ZFC` soundness theorem are retained:

- `Flypitch4.ToMathlib`
- `Flypitch4.PSetOrdinal`
- `Flypitch4.Fol`
- `Flypitch4.Bfol`
- `Flypitch4.Bvm`
- `Flypitch4.BvmExtras`
- `Flypitch4.BvmExtras2`
- `Flypitch4.ZfcCore` (extracted from upstream `Zfc.lean` through `bSet_models_ZFC` and `ZFC_consistent`, retaining all eight fixed ZFC axioms, the unrestricted strong collection schema, and the least-limit clause of infinity)

Unused upstream files (`BvTauto.lean`, `AlephOne.lean`, `CohenPoset.lean`, `Summary.lean`, and the specialized CH forcing half of `Zfc.lean`) are omitted.

Local changes are limited to:

1. **Statement deduplication**: The first-order syntax (`DVec`, `Arity'`, `Fol.Language`, `Fol.prf`, bounded terms/formulas, `SentTheory.is_consistent`) and `L_ZFC` / `ZFC` axiom definitions shared with [Challenge.lean](../../Challenge.lean) live in [Erdos1172/Statement.lean](../../Erdos1172/Statement.lean) and are re-exported via `public import Erdos1172.Statement`, ensuring single-definition identity across the library.
2. **Lean 4.35 module-system and Mathlib compatibility**: `module` headers, `public import` declarations, `@[expose] public section` visibility annotations, explicit model/type arguments, and updates to ordinal recursion branch names (`add_one`). Mathematical definitions and theorem statements are preserved unchanged.

## Internal Cardinal Extensions in `Erdos1172`

Rather than using upstream `bSet.Card`, the `Erdos1172` Part 4 modules (`Part4InternalCardinalLanguage`, `Part4InternalHartogsRelations`, `Part4InternalHartogs`, `Part4InternalHartogsInitial`, `Part4InternalHartogsUniqueness`, and `Part4InternalOmegaTwo`) generalize the Boolean-valued Hartogs construction of upstream `AlephOne.lean` to arbitrary Boolean-valued base names and characterize internal successor cardinals (`ω₁`, `ω₂`, and `κ⁺`) directly via `least_noninjecting_ordinal_f` (`Ord(α) ∧ ¬(α ↪ κ) ∧ ∀ γ ∈ α, γ ↪ κ`).
