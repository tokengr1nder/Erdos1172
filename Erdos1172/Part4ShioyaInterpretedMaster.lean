/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInternalOrder

@[expose] public section

/-! # Interpreting the source-row tests in the small residual extension -/

set_option autoImplicit false
noncomputable section
universe u v
open bSet Lattice
open scoped Flypitch
namespace bSet.ErdosShioyaInternal.InterpretedMaster

/-- Bound variables are represented by `none`; previous variables are under `some`. -/
inductive Formula : Type v → Type (v+1) where
  | mem {V} (x y : V) : Formula V
  | eq {V} (x y : V) : Formula V
  | edge {V} (r x y : V) : Formula V
  | imp {V} (p q : Formula V) : Formula V
  | both {V} (p q : Formula V) : Formula V
  | either {V} (p q : Formula V) : Formula V
  | neg {V} (p : Formula V) : Formula V
  | allIn {V} (x : V) (p : Formula (Option V)) : Formula V
  | someIn {V} (x : V) (p : Formula (Option V)) : Formula V

def Formula.eval {B : Type u} [NontrivialCompleteBooleanAlgebra B] {V : Type v}
    (p : Formula V) (env : V → bSet B) : B :=
  match p with
  | .mem x y => env x ∈ᴮ env y
  | .eq x y => env x =ᴮ env y
  | .edge r x y => ErdosShioyaInternal.edge (env r) (env x) (env y)
  | .imp p q => p.eval env ⟹ q.eval env
  | .both p q => p.eval env ⊓ q.eval env
  | .either p q => p.eval env ⊔ q.eval env
  | .neg p => (p.eval env)ᶜ
  | .allIn x p => ErdosShioyaInternal.allIn (env x) (fun z => p.eval (fun a => a.elim z env))
  | .someIn x p => ErdosShioyaInternal.someIn (env x) (fun z => p.eval (fun a => a.elim z env))

end bSet.ErdosShioyaInternal.InterpretedMaster
