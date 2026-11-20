/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalOrderMatrix

@[expose] public section

/-! # Checked-index matrix characterization of mixed regular-open word columns -/

set_option autoImplicit false
noncomputable section
open scoped Flypitch
universe u
namespace bSet.ErdosShioyaInternal
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
local notation "N" => bSet B

def matrixDenseBelow {V L : Type u} (r : V → V → B) (b : V → L → B) (i : L) (p : V) : B :=
  ⨅ q, r q p ⟹ ⨆ t, r t q ⊓ b t i

def matrixRegularColumn {V L : Type u} (r : V → V → B) (b : V → L → B) (i : L) : B :=
  (⨅ p, ⨅ q, (r p q ⊓ b q i) ⟹ b p i) ⊓ (⨅ p, matrixDenseBelow r b i p ⟹ b p i)

theorem denseBelowColumn_checked (α β : Ordinal.{u}) (R bits : N) (i : β.ToType) (p : α.ToType) :
    denseBelowColumn (ordinalCarrier α) R bits (ordinalLabel i) (ordinalLabel p) =
      matrixDenseBelow (checkedEdge R) (checkedEdge bits) i p := by
  apply (allIn_checked α (fun q => edge R q (ordinalLabel p) ⟹
    someIn (ordinalCarrier α) (fun t => edge R t q ⊓ edge bits t (ordinalLabel i)))
    (B_ext_imp (h₁ := B_ext_pair_mem_left) (h₂ := someIn_ext (const_congr _)
      (fun _ => B_ext_inf B_ext_pair_mem_right B_ext_const)))).trans
  apply iInf_congr
  intro q
  exact congrArg (imp _) (someIn_checked α _ (B_ext_inf B_ext_pair_mem_left B_ext_pair_mem_left))

theorem regularColumnValue_checked (α β : Ordinal.{u}) (R bits : N) (i : β.ToType) :
    regularColumnValue (ordinalCarrier α) R bits (ordinalLabel i) =
      matrixRegularColumn (checkedEdge R) (checkedEdge (α := α) bits) i := by
  let P : N := ordinalCarrier α
  apply congrArg₂ (· ⊓ ·)
  · exact allIn_checked₂ α (fun p q => (edge R p q ⊓ edge bits q (ordinalLabel i)) ⟹ edge bits p (ordinalLabel i))
      (fun _ => B_ext_imp (h₁ := B_ext_inf B_ext_pair_mem_left B_ext_const) (h₂ := B_ext_pair_mem_left))
      (fun _ => B_ext_imp (h₁ := B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left) (h₂ := B_ext_const))
  · apply (allIn_checked α (fun p => denseBelowColumn P R bits (ordinalLabel i) p ⟹ edge bits p (ordinalLabel i))
      (B_ext_imp (h₁ := denseBelowColumn_ext (const_congr P) (const_congr R) (const_congr bits)
        (const_congr _) id_congr) (h₂ := B_ext_pair_mem_left))).trans
    exact iInf_congr fun p => congrArg (fun d => imp d _) (denseBelowColumn_checked α β R bits i p)

/-- The regular-open fibers of every mixed word are computed by its incidence
matrix on checked points and bit coordinates. Its support is tested separately. -/
theorem regularColumnsValue_checked (α β : Ordinal.{u}) (R bits : N) :
    regularColumnsValue (ordinalCarrier α) R (ordinalCarrier β) bits =
      (bits ⊆ᴮ prod (ordinalCarrier α) (ordinalCarrier β)) ⊓
        ⨅ i : β.ToType, matrixRegularColumn (checkedEdge R) (checkedEdge (α := α) bits) i := by
  apply congrArg (_ ⊓ ·)
  apply (allIn_checked β _ (regularColumnValue_ext (const_congr (ordinalCarrier α))
    (const_congr R) (const_congr bits) id_congr)).trans
  exact iInf_congr (regularColumnValue_checked α β R bits)

end bSet.ErdosShioyaInternal
