/-
Copyright 2026 Tokengrinder.
Licensed under the Apache License, Version 2.0.
-/
module

public import Erdos1172.Part4LevyMatchingCommonPreparation

@[expose] public section

/-! # The Cohen master graph is already a name in the matching source -/

noncomputable section
set_option autoImplicit false
universe u
open Filter Cardinal bSet ErdosCohen ErdosNameTransport ErdosOmegaTwo ErdosPartialInjection
open Erdos1172GroundUltrapower Erdos1172LevyCohen Erdos1172PosetCompletion Erdos1172BooleanUltrapower
open scoped Flypitch Erdos1172LevyCollapse
namespace Erdos1172LevyCollapse.Matching

section BinaryNames
variable {V Z E : Type u} [NontrivialCompleteBooleanAlgebra V]
  [NontrivialCompleteBooleanAlgebra Z] [NontrivialCompleteBooleanAlgebra E]
variable (S : PSet.{u}) (sep : ∀ i j : S.Type, i ≠ j → ¬PSet.Equiv (S.Func i) (S.Func j))
variable (f : CompleteLatticeHom V E) (g : CompleteLatticeHom Z E)
variable (x : S.Type → V) (y : S.Type → Z)
local notation "graph" => indexedBinaryAssignment S

private theorem mapped_one (i : S.Type) :
    f (x i) ≤ pair (check (S.Func i)) (1 : bSet E) ∈ᴮ mapNames f (graph x sep) := by
  simpa only [map_mem,map_pair,map_check,show mapNames f (1 : bSet V) = 1 from map_check f (PSet.ofNat 1)]
    using OrderHomClass.mono f (indexedBinaryAssignment_one S x sep i)

private theorem mapped_zero (i : S.Type) :
    (f (x i))ᶜ ≤ pair (check (S.Func i)) (0 : bSet E) ∈ᴮ mapNames f (graph x sep) := by
  simpa only [map_mem,map_pair,map_check,map_compl',show mapNames f (0 : bSet V) = 0 from map_check f (PSet.ofNat 0)]
    using OrderHomClass.mono f (indexedBinaryAssignment_zero S x sep i)

private theorem binary_subset (d : E) (h : ∀ i, d ⊓ f (x i) = d ⊓ g (y i)) :
    d ≤ mapNames f (graph x sep) ⊆ᴮ mapNames g (graph y sep) := by
  have func : (⊤ : E) ≤ is_function (check S) two (mapNames f (graph x sep)) := by
    simpa only [TopHomClass.map_top,map_check,show (two : bSet V) = check (PSet.ofNat 2) from rfl]
      using map_is_function_of f (indexedBinaryAssignment_is_function S x sep)
  apply Preparation.subset_by_binary_pairs S _ _ d (le_top.trans (subset_prod_of_is_function func))
  · intro i
    let m := pair (check (S.Func i)) (1 : bSet E) ∈ᴮ mapNames f (graph x sep)
    have hm : m ≤ f (x i) := by
      apply disjoint_compl_right_iff.mp
      apply disjoint_iff_inf_le.mpr
      exact bot_of_zero_eq_one (eq_of_is_function_of_eq (le_top.trans func) bv_refl
        (inf_le_right.trans (mapped_zero S sep f x i)) inf_le_left)
    exact ((inf_le_inf_left d hm).trans_eq (h i)).trans (inf_le_right.trans (mapped_one S sep g y i))
  · intro i
    let m := pair (check (S.Func i)) (0 : bSet E) ∈ᴮ mapNames f (graph x sep)
    have hm : m ≤ (f (x i))ᶜ := by
      apply le_compl_iff_disjoint_right.mpr
      apply disjoint_iff_inf_le.mpr
      exact bot_of_zero_eq_one (eq_of_is_function_of_eq (le_top.trans func) bv_refl
        inf_le_left (inf_le_right.trans (mapped_one S sep f x i)))
    have mask (v : E) : d ⊓ vᶜ = d ⊓ (d ⊓ v)ᶜ := by rw [compl_inf,inf_sup_left,inf_compl_eq_bot,bot_sup_eq]
    have eq := (mask (f (x i))).trans ((congrArg (fun t => d ⊓ tᶜ) (h i)).trans (mask (g (y i))).symm)
    exact ((inf_le_inf_left d hm).trans_eq eq).trans (inf_le_right.trans (mapped_zero S sep g y i))

/-- Agreement of all bits on one Boolean piece identifies the actual two
hereditary function names on that piece. -/
theorem indexed_binary_eq_of_matched_bits (d : E) (h : ∀ i, d ⊓ f (x i) = d ⊓ g (y i)) :
    d ≤ mapNames f (graph x sep) =ᴮ mapNames g (graph y sep) :=
  subset_ext (binary_subset S sep f g x y d h) (binary_subset S sep g f y x d (fun i => (h i).symm))
end BinaryNames

variable {κ θ : Cardinal.{u}} {R : Type u} [NontrivialCompleteBooleanAlgebra R]
  {B : θ.ord.ToType → Type u} [∀ i, NontrivialCompleteBooleanAlgebra (B i)]
  (b : ∀ {i j : θ.ord.ToType}, i ≤ j → CompleteLatticeHom (B i) (B j))
  (g : ∀ i, CompleteLatticeHom (B i) R)
local notation "A" => FirstAlgebra κ
local notation "Z" => FirstAlgebra θ
local notation "E" => JointForcing R θ.ord.ToType
local notation "src" => jointSourceHom (R := R) θ.ord.ToType
local notation "S" => PSet.ordinalMk κ.ord
local notation "Low" => Erdos1172CohenIteration.Conditions (omegaOne : bSet A)
local notation "nm" => Erdos1172BooleanNameIteration.name

/-- The graph is defined before the external collapse used in the matching construction. -/
def sourceCohenMaster (u : CompleteLatticeHom (Erdos1172LevyCohen.Algebra κ) R) : bSet R :=
  indexedBinaryAssignment S (fun i => u (Erdos1172CohenIteration.bitValue (omegaOne : bSet A)
    (check ((S).Func i)) 1)) (PSet.ordinalMk_inj κ.ord)

variable {I : Type u} (U : Ultrafilter I) (a : I → Set θ.ord.ToType)
  [CountableInterFilter (U : Filter I)] [Nonempty θ.ord.ToType] [CardinalInterFilter (U : Filter I) κ]
  (hk : κ < θ) (hκ : κ.IsInaccessible) (hθ : θ.IsInaccessible)
  (hf : FineOn U a) (hn : NormalOn U a) (ht : FiberOrderType U κ θ a)
  (u : CompleteLatticeHom (Erdos1172LevyCohen.Algebra κ) R)
local notation "prep" => Preparation.preparedName U a hk.le hf hn ht

include hκ hθ in
/-- One fixed source name extends every prepared lower condition, and locally
is an actual valid upper-collapse condition. The choice of a matching at later
stages does not occur in the definition of the source name. -/
theorem exists_matching_source_master
    (cc : StrictCC R θ) (dense : DenseStageUnion g) (good : RegularCollapsingStages B)
    (ginj : ∀ i, Function.Injective (g i)) (gg : ∀ {i j} (h : i ≤ j) x, g j (b h x) = g i x)
    (uinj : Function.Injective u) :
    ∃ K : CompleteLatticeHom Z E, Function.Injective K ∧
      (∀ x, K (initialCollapseHom hk.le x) = src (u (firstStageHom κ x))) ∧
      (∀ (X : Type u), #X < θ → ∀ x : X → R, ArrayRead (src) K x) ∧
      (∀ (X : Type u), #X < θ → ∀ x : X → Z, ArrayRead K (src) x) ∧
      (∀ p : Low, src (u (condition p)) ≤ mapNames K (prep (nm p)) ⊆ᴮ mapNames (src) (sourceCohenMaster u)) ∧
      (⊤ : E) ≤ ⨆ m : {m : bSet Z // (⊤ : Z) ≤ ErdosCohen.condition omegaOne m},
        (mapNames (src) (sourceCohenMaster u) =ᴮ mapNames K m.val) := by
  let l := (src).comp u
  obtain ⟨K,kin,square,read,readBack⟩ := exists_levy_matching_over_preparation b g hk hκ hθ cc dense good ginj gg
    (u.comp (firstStageHom κ)) (uinj.comp (firstStageHom_injective κ))
  let bit (i : (S).Type) := Erdos1172CohenIteration.bitValue (omegaOne : bSet A) (check ((S).Func i)) 1
  have size : #((S).Type) < θ := by simpa only [PSet.ordinalMk_type,Cardinal.mk_ord_toType] using hk
  have covered := read (S).Type size (fun i => u (bit i))
  let upper (y : (S).Type → Z) := indexedBinaryAssignment S y (PSet.ordinalMk_inj κ.ord)
  have valid (y) : (⊤ : Z) ≤ ErdosCohen.condition omegaOne (upper y) :=
    Preparation.master_binary_condition hk hκ.aleph0_lt hθ.isRegular y
  refine ⟨K,kin,square,read,readBack,?_,?_⟩
  · intro p
    calc
      _ = (⊤ : E) ⊓ l (condition p) := (top_inf_eq _).symm
      _ ≤ _ := (inf_le_inf_right _ covered).trans ?_
    rw [iSup_inf_eq]
    apply iSup_le
    intro w
    have eq := indexed_binary_eq_of_matched_bits S (PSet.ordinalMk_inj κ.ord) (src) K
      (fun i => u (bit i)) w.val.2 w.val.1 w.property
    have cone := Preparation.indexed_cohen_master_extends U a hk hf hn ht hκ.isRegular hκ.aleph0_lt l K
      (fun x => (square x).symm) w.val.1 w.val.2 w.property p
    exact subset_trans' cone (subset_of_eq (bv_symm (inf_le_left.trans eq)))
  · apply covered.trans (iSup_le fun w => ?_)
    exact le_iSup_of_le ⟨upper w.val.2,valid _⟩ (indexed_binary_eq_of_matched_bits S (PSet.ordinalMk_inj κ.ord)
      (src) K (fun i => u (bit i)) w.val.2 w.val.1 w.property)

end Erdos1172LevyCollapse.Matching
