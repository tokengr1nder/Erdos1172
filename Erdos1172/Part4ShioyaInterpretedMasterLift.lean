/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4ShioyaInterpretedMaster
public import Erdos1172.Part4ShioyaSeedOpenScalar
public import Erdos1172.Part4ShioyaHereditaryDenseOpen
public import Erdos1172.Part4BooleanUltrapowerBoundedEval
public import Erdos1172.Part4BooleanFunctionTransport

@[expose] public section

/-! # Bounded Łoś transfer for the interpreted master parameters -/

set_option autoImplicit false
noncomputable section
universe u v
open Filter Lattice bSet ErdosNameTransport Erdos1172BooleanUltrapower
open scoped Flypitch
namespace bSet.ErdosShioyaInternal.InterpretedMaster

variable {B S I : Type u} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra S]
variable {T : Type v}

theorem Formula.eval_ext (p : Formula T) (env : bSet B → T → bSet B)
    (h : ∀ t, B_congr (fun z => env z t)) : B_ext (fun z => p.eval (env z)) := by
  induction p with
  | mem x y => exact fun _ _ => mem_congr (h x inf_le_left) (h y inf_le_left) inf_le_right
  | eq x y => exact fun _ _ => bv_trans (bv_symm (h x inf_le_left)) (bv_trans inf_le_right (h y inf_le_left))
  | edge r x y => exact edge_ext (h r) (h x) (h y)
  | imp p q hp hq => exact B_ext_imp (h₁ := hp env h) (h₂ := hq env h)
  | both p q hp hq => exact B_ext_inf (hp env h) (hq env h)
  | either p q hp hq => exact B_ext_sup (h₁ := hp env h) (h₂ := hq env h)
  | neg p hp => exact B_ext_neg (h := hp env h)
  | allIn t p hp =>
    apply allIn_ext (h t)
    intro z
    exact hp (fun x a => a.elim z (env x)) (fun a => by cases a with
      | none => exact const_congr _
      | some i => exact h i)
  | someIn t p hp =>
    apply someIn_ext (h t)
    intro z
    exact hp (fun x a => a.elim z (env x)) (fun a => by cases a with
      | none => exact const_congr _
      | some i => exact h i)

private theorem Formula.bound_ext (p : Formula (Option T)) (env : T → bSet B) :
    B_ext (fun z => p.eval (fun a => a.elim z env)) :=
  p.eval_ext _ (fun a => by cases a with
    | none => exact id_congr
    | some i => exact const_congr _)

/-- Evaluation of bounded formulas commutes with every complete scalar map. -/
theorem Formula.map_eval (p : Formula T) (d : CompleteLatticeHom B S) (env : T → bSet B) :
    d (p.eval env) = p.eval (fun t => mapNames d (env t)) := by
  induction p with
  | mem x y => exact map_mem d _ _
  | eq x y => exact map_bv_eq d _ _
  | edge r x y => simp only [Formula.eval,ErdosShioyaInternal.edge,map_mem,map_pair]
  | imp p q hp hq => exact (map_imp d _ _).trans (congrArg₂ _ (hp env) (hq env))
  | both p q hp hq => exact (InfHomClass.map_inf d _ _).trans (congrArg₂ _ (hp env) (hq env))
  | either p q hp hq => exact (SupHomClass.map_sup d _ _).trans (congrArg₂ _ (hp env) (hq env))
  | neg p hp => exact (map_compl' d _).trans (congrArg (·ᶜ) (hp env))
  | allIn t p hp =>
    apply map_named_allIn d (env t) _ _ (p.bound_ext _) (p.bound_ext _)
    intro y
    apply (hp (fun a => a.elim y env)).trans
    exact congrArg p.eval (_root_.funext fun a => by cases a <;> rfl)
  | someIn t p hp =>
    apply map_named_someIn d (env t) _ _ (p.bound_ext _) (p.bound_ext _)
    intro y
    apply (hp (fun a => a.elim y env)).trans
    exact congrArg p.eval (_root_.funext fun a => by cases a <;> rfl)

variable (U : Ultrafilter I) [CountableInterFilter (U : Filter I)]

/-- Simultaneous parameters may vary arbitrarily over the ultrafilter index. -/
theorem Formula.hereditary_eval (p : Formula T) (env : I → T → bSet B) :
    value U (fun i => p.eval (env i)) = p.eval (fun t => hereditary U (fun i => env i t)) := by
  induction p with
  | mem x y => exact value_name_mem U _ _
  | eq x y => exact value_name_eq U _ _
  | edge r x y => exact hereditary_edge_value U _ _ _
  | imp p q hp hq => exact (value_imp U _ _).trans (congrArg₂ _ (hp env) (hq env))
  | both p q hp hq => exact (value_inf U _ _).trans (congrArg₂ _ (hp env) (hq env))
  | either p q hp hq => exact (value_sup U _ _).trans (congrArg₂ _ (hp env) (hq env))
  | neg p hp => exact (value_compl U _).trans (congrArg (·ᶜ) (hp env))
  | allIn t p hp =>
    apply hereditary_allIn U (fun i => env i t) _ _ (fun i => p.bound_ext (env i)) (p.bound_ext _)
    intro Y
    apply (hp (fun i a => a.elim (Y i) (env i))).trans
    exact congrArg p.eval (_root_.funext fun a => by cases a <;> rfl)
  | someIn t p hp =>
    apply hereditary_bounded_evaluation U (fun i => env i t) _ _ (fun i => p.bound_ext (env i)) (p.bound_ext _)
    intro Y
    apply (hp (fun i a => a.elim (Y i) (env i))).trans
    exact congrArg p.eval (_root_.funext fun a => by cases a <;> rfl)

end bSet.ErdosShioyaInternal.InterpretedMaster
