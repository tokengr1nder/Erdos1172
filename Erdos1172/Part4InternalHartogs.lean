/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license; see the project's vendor/flypitch4/LICENSE.
Adapted from AlephOne.lean at upstream ad649f89e9f3107b7e2ea97a58b2eafdfc80b815.
Local change: replace the codomain omega by arbitrary kappa. The final specification
requires one to inject into kappa; its omega1 and omega2 instances supply this.
-/
module

public import Erdos1172.Part4InternalHartogsRelations

@[expose] public section

open scoped Flypitch
open Lattice
universe u
namespace bSet.ErdosHartogs
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {κ : bSet 𝔹}

/-- The least ordinal not admitting an internal injection into the given name. -/
def leastNoninjectingOrdinal (κ x : bSet 𝔹) : 𝔹 :=
  (injects_into x κ)ᶜ ⊓
    (Ord x ⊓ ⨅ y, _root_.imp (Ord y) (_root_.imp (injects_into y κ)ᶜ (x ⊆ᴮ y)))

lemma zero_injects {Γ : 𝔹} : Γ ≤ injects_into (0 : bSet 𝔹) κ := by
  apply injects_into_of_subset
  exact bv_rw' (H := zero_eq_empty) (H_new := empty_subset)
    (h_congr := B_ext_subset_left)

noncomputable def hartogs' : bSet 𝔹 :=
  comprehend
    (fun x : bSet 𝔹 => ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η κ f ⊓
      (image (mem_rel η) (prod κ κ) (prod_map_self η κ f) =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ)
    (bv_powerset (prod κ κ))

-- src/aleph_one.lean:612
lemma hartogs'_AE {Γ : 𝔹} : Γ ≤ ⨅ z, z ∈ᴮ (hartogs' (κ := κ)) ⟹
    ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η κ f ⊓
    image (mem_rel η) (prod κ κ) (prod_map_self η κ f) =ᴮ z ⊓ (z =ᴮ ∅)ᶜ := by
  -- B_ext for ϕ (changing the last argument x)
  have H_congr : B_ext (fun x : bSet 𝔹 =>
      ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η κ f ⊓
      (image (mem_rel η) (prod κ κ) (prod_map_self η κ f) =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ) :=
    B_ext_iSup (h := fun η => B_ext_inf (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun f => B_ext_inf
        (h₁ := B_ext_inf (h₁ := B_ext_const) (h₂ := B_ext_bv_eq_right))
        (h₂ := B_ext_neg (h := B_ext_bv_eq_left)))))
  apply le_iInf; intro z; rw [← deduction]
  -- From z ∈ (hartogs' (κ := κ)) (= comprehend ϕ' (bv_powerset...)), use mem_comprehend_iff
  have H_from : Γ ⊓ z ∈ᴮ ((hartogs' (κ := κ)) : bSet 𝔹) ≤ z ∈ᴮ ((hartogs' (κ := κ)) : bSet 𝔹) := inf_le_right
  -- (hartogs' (κ := κ)) is definitionally equal to comprehend ϕ' (bv_powerset (prod ω ω))
  -- Use mem_comprehend_iff to convert z ∈ (hartogs' (κ := κ)) to ⨆ χ, ...
  -- Since (hartogs' (κ := κ)) = comprehend ... by def, mem_comprehend_iff applies directly
  rw [show ((hartogs' (κ := κ)) : bSet 𝔹) = comprehend
      (fun x : bSet 𝔹 => ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η κ f ⊓
        (image (mem_rel η) (prod κ κ) (prod_map_self η κ f) =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ)
      (bv_powerset (prod κ κ)) from rfl] at H_from
  rw [mem_comprehend_iff] at H_from
  apply le_trans (le_inf H_from le_rfl)
  apply bv_cases_left; intro χ
  -- ctx: (bv_powerset...).bval χ ⊓ (z =ᴮ w ⊓ ϕ' w) ⊓ Γ, where w = (bv_powerset...).func χ
  -- The type is: (bv_powerset (prod κ κ)).bval χ ⊓
  --   (z =ᴮ (bv_powerset (prod κ κ)).func χ ⊓ (⨆ η, ...)) ⊓ Γ ≤ ⨆ η, ...
  -- h_zeq: ctx ≤ z =ᴮ w  (from the left ⊓ part)
  -- h_phi: ctx ≤ ϕ' w (the nested ⨆ expression)
  -- Apply H_congr: ϕ' w ≤ ϕ' z given w =ᴮ z
  refine le_trans (le_inf ?_ ?_) (H_congr ((bv_powerset (prod κ κ)).func χ) z)
  · -- Need: ctx ≤ (bv_powerset...).func χ =ᴮ z
    -- from inf_le_left (bval ⊓ (z=w ⊓ ϕ'w)) gives z=w; bv_symm gives w=z
    exact bv_symm (inf_le_left.trans (inf_le_right.trans inf_le_left))
  · -- Need: ctx ≤ ϕ' w (the outer ⨆ at w = func χ)
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)

-- src/aleph_one.lean:597: the predicate: (hartogs_ψ (κ := κ)) v x holds when x is an ordinal injecting into ω
-- with induced epsilon relation on ω equal to v, and v ≠ ∅
def hartogs_ψ {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {κ : bSet 𝔹} (v x : bSet 𝔹) : 𝔹 :=
  Ord x ⊓ (⨆ f, is_injective_function x κ f ⊓
    image (mem_rel x) (prod κ κ) (prod_map_self x κ f) =ᴮ v) ⊓ (v =ᴮ ∅)ᶜ

lemma B_ext_hartogs_ψ {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {κ : bSet 𝔹}
    {v : bSet 𝔹} : B_ext ((hartogs_ψ (κ := κ)) v) := by
  unfold hartogs_ψ
  refine B_ext_inf (h₁ := B_ext_inf (h₁ := B_ext_Ord) (h₂ := ?_)) (h₂ := B_ext_const)
  -- B_ext (fun x => ⨆ f, is_injective_function x κ f ⊓
  --                  image (mem_rel x) (prod κ κ) (prod_map_self x κ f) =ᴮ v)
  -- For each fixed f (iSup variable), show B_ext in x
  apply B_ext_iSup; intro f
  apply B_ext_inf B_ext_is_injective_function_left
  -- B_ext (fun x => image (mem_rel x) (prod κ κ) (prod_map_self x κ f) =ᴮ v)
  -- = B_ext_term with ϕ = (fun w => w =ᴮ v) and t = (fun x => image(mem_rel x)(prod ω ω)(pm(x,ω,f)))
  apply B_ext_term (ϕ := fun w => w =ᴮ v) (t := fun x => image (mem_rel x) (prod κ κ) (prod_map_self x κ f)) B_ext_bv_eq_left
  -- B_congr (fun x => image (mem_rel x) (prod κ κ) (prod_map_self x κ f))
  intro x₁ x₂ Γ Hxy
  -- Step 1: image(mem_rel x₁)(prod ω ω)(pm(x₁)) =ᴮ image(mem_rel x₂)(prod ω ω)(pm(x₁))
  have h1 : Γ ≤ image (mem_rel x₁) (prod κ κ) (prod_map_self x₁ κ f) =ᴮ
      image (mem_rel x₂) (prod κ κ) (prod_map_self x₁ κ f) :=
    B_congr_image_left (B_congr_mem_rel Hxy)
  -- Step 2: image(mem_rel x₂)(prod ω ω)(pm(x₁)) =ᴮ image(mem_rel x₂)(prod ω ω)(pm(x₂))
  have h2 : Γ ≤ image (mem_rel x₂) (prod κ κ) (prod_map_self x₁ κ f) =ᴮ
      image (mem_rel x₂) (prod κ κ) (prod_map_self x₂ κ f) :=
    B_congr_image_right (B_congr_prod_map_self_left Hxy)
  exact le_trans (le_inf h1 h2) bv_eq_trans

-- src/aleph_one.lean:620
-- (hartogs_func (κ := κ)) χ: the ordinal x such that (hartogs_ψ (κ := κ)) ((hartogs' (κ := κ)).func χ) x holds
noncomputable def hartogs_func (χ : ((hartogs' (κ := κ))).type) : bSet 𝔹 :=
  (AE_convert' ((hartogs_ψ (κ := κ))) (fun _v => B_ext_hartogs_ψ) (hartogs' (κ := κ)) (((hartogs' (κ := κ))).func χ)).choose

-- Convert hartogs'_AE to the form needed by AE_convert'
private lemma hartogs'_AE_psi {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {κ : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ ⨅ z, z ∈ᴮ ((hartogs' (κ := κ))) ⟹ ⨆ w, (hartogs_ψ (κ := κ)) z w := by
  apply le_iInf; intro z; rw [← deduction]
  -- Get ⨆ η, Ord η ⊓ ⨆ f, ...(η)... ⊓ (z=∅)ᶜ from hartogs'_AE
  have H : Γ ⊓ z ∈ᴮ ((hartogs' (κ := κ))) ≤ ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η κ f ⊓
      image (mem_rel η) (prod κ κ) (prod_map_self η κ f) =ᴮ z ⊓ (z =ᴮ ∅)ᶜ :=
    le_trans (le_inf (hartogs'_AE.trans (iInf_le _ z)) inf_le_right) bv_imp_elim
  apply le_trans H; apply iSup_le; intro η; apply le_iSup_of_le η
  -- Convert: Ord η ⊓ (⨆ f, A f ⊓ C) ≤ (hartogs_ψ (κ := κ)) z η = Ord η ⊓ (⨆ f, A f) ⊓ C
  -- where C = (z =ᴮ ∅)ᶜ (doesn't depend on f)
  unfold hartogs_ψ
  -- LHS: Ord η ⊓ (⨆ f, (inj_fun η ω f ⊓ img =ᴮ z) ⊓ (z=∅)ᶜ)
  -- RHS: Ord η ⊓ (⨆ f, inj_fun ω f ⊓ img =ᴮ z) ⊓ (z=∅)ᶜ
  refine le_inf (le_inf inf_le_left (le_trans inf_le_right ?_)) (le_trans inf_le_right ?_)
  · -- ⨆ f, (A f ⊓ C) ≤ ⨆ f, A f
    exact iSup_le (fun f => le_iSup_of_le f inf_le_left)
  · -- ⨆ f, (A f ⊓ C) ≤ C
    exact iSup_le (fun f => inf_le_right)

-- Spec for (hartogs_func (κ := κ))
lemma hartogs_func_spec {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {κ : bSet 𝔹}
    {χ : ((hartogs' (κ := κ))).type} {Γ : 𝔹}
    (H_mem : Γ ≤ ((hartogs' (κ := κ))).func χ ∈ᴮ ((hartogs' (κ := κ)))) :
    Γ ≤ (hartogs_ψ (κ := κ)) (((hartogs' (κ := κ))).func χ) ((hartogs_func (κ := κ)) χ) :=
  (AE_convert' ((hartogs_ψ (κ := κ))) (fun _v => B_ext_hartogs_ψ) (hartogs' (κ := κ)) (((hartogs' (κ := κ))).func χ)).choose_spec
    hartogs'_AE_psi H_mem

-- src/aleph_one.lean:630
noncomputable def hartogs_aux : bSet 𝔹 := ⟨((hartogs' (κ := κ))).type, (hartogs_func (κ := κ)), ((hartogs' (κ := κ))).bval⟩

-- src/aleph_one.lean:632
lemma Ord_of_mem_hartogs_aux {Γ : 𝔹} {η : bSet 𝔹} (H_mem : Γ ≤ η ∈ᴮ (hartogs_aux (κ := κ))) : Γ ≤ Ord η := by
  rw [mem_unfold] at H_mem; apply le_trans H_mem; apply iSup_le; intro χ
  -- (hartogs_aux (κ := κ)).func χ = (hartogs_func (κ := κ)) χ (the ordinal extracted by classical choice)
  -- (hartogs' (κ := κ)).bval χ ≤ ((hartogs' (κ := κ)).func χ) ∈ (hartogs' (κ := κ)) → (hartogs_ψ (κ := κ)) ((hartogs' (κ := κ)).func χ) ((hartogs_func (κ := κ)) χ)
  -- (hartogs_ψ (κ := κ)) includes Ord ((hartogs_func (κ := κ)) χ), so we get Ord ((hartogs_func (κ := κ)) χ)
  -- We need: (hartogs' (κ := κ)).bval χ ⊓ η =ᴮ (hartogs_func (κ := κ)) χ ≤ Ord η
  -- From hartogs_func_spec (using H_mem' : (hartogs' (κ := κ)).func χ ∈ (hartogs' (κ := κ)) from mem_mk''):
  have H_mem' : ((hartogs' (κ := κ))).bval χ ≤ ((hartogs' (κ := κ))).func χ ∈ᴮ (hartogs' (κ := κ)) := mem_mk' (hartogs' (κ := κ)) χ
  have H_spec : ((hartogs' (κ := κ))).bval χ ≤ (hartogs_ψ (κ := κ)) (((hartogs' (κ := κ))).func χ) ((hartogs_func (κ := κ)) χ) :=
    hartogs_func_spec H_mem'
  have H_ord : ((hartogs' (κ := κ))).bval χ ≤ Ord ((hartogs_func (κ := κ)) χ) :=
    H_spec.trans (inf_le_left.trans inf_le_left)
  -- η =ᴮ (hartogs_func (κ := κ)) χ and Ord ((hartogs_func (κ := κ)) χ) → Ord η
  exact le_trans (le_inf (bv_symm inf_le_right) (le_trans inf_le_left H_ord)) (B_ext_Ord _ _)

-- src/aleph_one.lean:641
/-- Candidate containing zero and one. Its Hartogs specification requires
`1` to inject into the base; this premise is proved for both applications. -/
noncomputable def hartogs : bSet 𝔹 := insert 0 (insert 1 (hartogs_aux (κ := κ)))

-- src/aleph_one.lean:643
lemma mem_hartogs_iff₀ {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ (hartogs (κ := κ)) ↔ Γ ≤ z =ᴮ 0 ⊔ z =ᴮ 1 ⊔ z ∈ᴮ (hartogs_aux (κ := κ)) := by
  simp only [hartogs, mem_insert1, sup_assoc]

-- src/aleph_one.lean:646
lemma Ord_of_mem_hartogs {Γ : 𝔹} {η : bSet 𝔹} (H_mem : Γ ≤ η ∈ᴮ (hartogs (κ := κ))) : Γ ≤ Ord η := by
  rw [mem_hartogs_iff₀] at H_mem; apply le_trans H_mem; apply sup_le; apply sup_le
  · exact le_trans (le_inf (bv_symm le_rfl) (le_trans le_top (le_top.trans Ord_zero)))
      (B_ext_Ord _ _)
  · exact le_trans (le_inf (bv_symm le_rfl) (le_trans le_top (le_top.trans Ord_one)))
      (B_ext_Ord _ _)
  · exact Ord_of_mem_hartogs_aux le_rfl

-- src/aleph_one.lean:655
lemma eq_zero_iff_eq_empty {Γ : 𝔹} {u : bSet 𝔹} : Γ ≤ u =ᴮ 0 ↔ Γ ≤ u =ᴮ ∅ := by
  constructor
  · intro H
    exact le_trans (le_inf H (zero_eq_empty (Γ := Γ))) bv_eq_trans
  · intro H
    exact le_trans (le_inf H (bv_symm (zero_eq_empty (Γ := Γ)))) bv_eq_trans

-- src/aleph_one.lean:662
lemma induced_rel_empty_of_eq_zero {η f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function η κ f)
    (H_eq_zero : Γ ≤ η =ᴮ 0) : Γ ≤ induced_epsilon_rel η κ f =ᴮ ∅ := by
  rw [empty_iff_forall_not_mem]
  apply le_iInf; intro pr
  rw [← imp_bot, ← deduction]
  -- goal: Γ ⊓ pr ∈ᴮ induced_epsilon_rel η κ f ≤ ⊥
  set Γ' := Γ ⊓ pr ∈ᴮ induced_epsilon_rel η κ f
  have H_mem' : Γ' ≤ pr ∈ᴮ induced_epsilon_rel η κ f := inf_le_right
  have H_func' : Γ' ≤ is_function η κ f := le_trans inf_le_left H_func
  obtain ⟨a, _b, _, _, _, Hab⟩ := eq_pair_of_mem_induced_epsilon_rel H_mem'
  have Ha_img : Γ' ≤ a ∈ᴮ image η κ f :=
    induced_epsilon_rel_sub_image_left H_func' Hab
  rw [mem_image_iff] at Ha_img
  have H_eq_empty : Γ' ≤ η =ᴮ ∅ :=
    eq_zero_iff_eq_empty.mp (le_trans inf_le_left H_eq_zero)
  have H_notz : Γ' ≤ ⨅ z, (z ∈ᴮ η)ᶜ := empty_iff_forall_not_mem.mp H_eq_empty
  apply bv_absurd (⨆ z, z ∈ᴮ η ⊓ pair z a ∈ᴮ f) Ha_img.2
  rw [compl_iSup]
  apply le_iInf; intro z
  exact le_trans (le_trans H_notz (iInf_le _ z)) (compl_le_compl inf_le_left)

-- src/aleph_one.lean:679
lemma not_zero_of_induced_rel_nonempty {η f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function η κ f)
    (H' : Γ ≤ (induced_epsilon_rel η κ f =ᴮ ∅)ᶜ) : Γ ≤ (η =ᴮ 0)ᶜ := by
  rw [← imp_bot, ← deduction]
  -- goal: Γ ⊓ (η =ᴮ 0) ≤ ⊥
  have H_rel_empty : Γ ⊓ (η =ᴮ 0) ≤ induced_epsilon_rel η κ f =ᴮ ∅ :=
    induced_rel_empty_of_eq_zero (le_trans inf_le_left H_func) inf_le_right
  exact bv_absurd _ H_rel_empty (le_trans inf_le_left H')

-- src/aleph_one.lean:700
lemma not_one_of_induced_rel_nonempty {η f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function η κ f)
    (H : Γ ≤ (induced_epsilon_rel η κ f =ᴮ ∅)ᶜ) : Γ ≤ (η =ᴮ 1)ᶜ := by
  -- Proof: assume η = 1. Get pr ∈ induced_epsilon_rel. Get a', b' s.t. a' ∈ b'.
  -- Then a' ∈ η = 1 → a' = 0, b' ∈ η = 1 → b' = 0. So 0 ∈ 0, contradiction.
  rw [← imp_bot, ← deduction]
  -- Goal: Γ ⊓ (η =ᴮ 1) ≤ ⊥
  -- Extract pr from the nonempty induced_epsilon_rel
  have H' : Γ ⊓ (η =ᴮ 1) ≤ (induced_epsilon_rel η κ f =ᴮ ∅)ᶜ := inf_le_left.trans H
  rw [nonempty_iff_exists_mem] at H'
  apply le_trans (le_inf H' le_rfl)
  apply bv_cases_left; intro pr
  -- ctx₀ = pr ∈ ind_eps ⊓ (Γ ⊓ η=1)
  have H_pr_mem₀ := @inf_le_left 𝔹 _ (pr ∈ᴮ induced_epsilon_rel η κ f) (Γ ⊓ (η =ᴮ 1))
  have H_func₀ : (pr ∈ᴮ induced_epsilon_rel η κ f) ⊓ (Γ ⊓ (η =ᴮ 1)) ≤ is_function η κ f :=
    @inf_le_right 𝔹 _ (pr ∈ᴮ induced_epsilon_rel η κ f) (Γ ⊓ (η =ᴮ 1)) |>.trans
      (inf_le_left.trans H_func)
  obtain ⟨a, b, _, _, _, H_pair_mem⟩ := eq_pair_of_mem_induced_epsilon_rel H_pr_mem₀
  rw [mem_induced_epsilon_rel_iff H_func₀] at H_pair_mem
  obtain ⟨_, _, H_sup⟩ := H_pair_mem
  apply le_trans (le_inf H_sup le_rfl)
  apply bv_cases_left; intro a'
  apply le_trans (le_inf (inf_le_left.trans inf_le_right) le_rfl)
  apply bv_cases_left; intro b'
  -- ctx: (b'∈η ⊓ (pa'a∈f ⊓ pb'b∈f ⊓ a'∈b')) ⊓ ((a'∈η ⊓ ⨆b',...) ⊓ (pr∈ind_eps ⊓ (Γ⊓η=1)))
  -- Goal: this ctx ≤ ⊥
  -- Derive 0 ∈ 0:
  -- 1. a' ∈ η: ir.il.il, b' ∈ η: il.il
  -- 2. η = 1: ir.ir.ir.ir (to Γ⊓η=1, then right = η=1)
  -- 3. a' ∈ 1: from a'∈η and η=1
  -- 4. a' = 0, b' = 0: eq_zero_of_mem_one
  -- 5. a' ∈ b': il.ir.ir
  -- 6. 0 ∈ 0: mem_congr
  -- Derive 0 ∈ 0 and use bot_of_mem_self'
  -- Paths in ctx: (b'∈η ⊓ (pa'a∈f ⊓ pb'b∈f ⊓ a'∈b')) ⊓ ((a'∈η ⊓ ⨆b',...) ⊓ (pr∈ ⊓ (Γ ⊓ η=1)))
  -- a' ∈ η: ir.il.il (3 steps)
  -- b' ∈ η: il.il (2 steps)
  -- η = 1: ir.ir.ir.ir (4 steps)
  -- a' ∈ b': il.ir.ir (3 steps)
  apply bot_of_mem_self'
  apply mem_congr
  · -- ctx ≤ 0 =ᴮ 0 for the "element" (a' =ᴮ 0)
    exact eq_zero_of_mem_one (mem_congr bv_refl
      (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
      (inf_le_right.trans (inf_le_left.trans inf_le_left)))
  · -- ctx ≤ 0 =ᴮ 0 for the "set" (b' =ᴮ 0)
    exact eq_zero_of_mem_one (mem_congr bv_refl
      (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
      (inf_le_left.trans inf_le_left))
  · -- ctx ≤ a' ∈ b' (becomes 0 ∈ 0 after rewriting)
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)

-- src/aleph_one.lean:723
lemma nonempty_induced_rel_iff_not_zero_and_not_one {η f : bSet 𝔹} {Γ : 𝔹}
    (H_ord : Γ ≤ Ord η) (H_inj : Γ ≤ is_function η κ f) :
    Γ ≤ (induced_epsilon_rel η κ f =ᴮ ∅)ᶜ ↔
    (Γ ≤ (η =ᴮ 0)ᶜ ∧ Γ ≤ (η =ᴮ 1)ᶜ) := by
  constructor
  · intro H
    exact ⟨not_zero_of_induced_rel_nonempty H_inj H,
           not_one_of_induced_rel_nonempty H_inj H⟩
  · intro ⟨H₁, H₂⟩
    rw [nonempty_iff_exists_mem]
    -- Get 1 ∈ η (since η ≥ 2 ordinal-wise)
    have H_1_mem : Γ ≤ (1 : bSet 𝔹) ∈ᴮ η := one_mem_of_not_zero_and_not_one H_ord H₁ H₂
    -- Get 0 ∈ η (since 0 ∈ 1 ∈ η, and η is ordinal ↔ transitive)
    have H_0_mem : Γ ≤ (0 : bSet 𝔹) ∈ᴮ η := mem_of_mem_Ord zero_mem_one H_1_mem H_ord
    -- Apply mem_induced_epsilon_rel_of_mem with 0 ∈ η, 1 ∈ η, 0 ∈ 1
    -- Need is_function η κ f
    apply bv_use (pair (function_eval H_inj (0 : bSet 𝔹) H_0_mem) (function_eval H_inj 1 H_1_mem))
    exact mem_induced_epsilon_rel_of_mem H_0_mem H_1_mem zero_mem_one H_inj

-- src/aleph_one.lean:746
/-- (hartogs (κ := κ)) contains every ordinal η which injects into ω -/
lemma mem_hartogs_of_injects_into_omega_aux {Γ : 𝔹} {η : bSet 𝔹}
    (H_ord : Γ ≤ Ord η) (H_inj : Γ ≤ ⨆ f, is_injective_function η κ f)
    (H_not_zero : Γ ≤ (η =ᴮ 0)ᶜ) (H_not_one : Γ ≤ (η =ᴮ 1)ᶜ) :
    Γ ≤ η ∈ᴮ (hartogs_aux (κ := κ)) := by
  -- Step 1: Extract f from H_inj using maximum_principle
  obtain ⟨f, Hf_eq⟩ := maximum_principle (fun f => is_injective_function η κ f)
    (B_ext_inf B_ext_is_function_right (B_ext_iInf (h := fun w₁ => B_ext_iInf (h := fun w₂ =>
      B_ext_iInf (h := fun v₁ => B_ext_iInf (h := fun v₂ =>
        B_ext_imp (h₁ := B_ext_inf (h₁ := B_ext_inf (h₁ := B_ext_mem_right) (h₂ := B_ext_mem_right))
          (h₂ := B_ext_const)) (h₂ := B_ext_const)))))))
  have Hf : Γ ≤ is_injective_function η κ f := Hf_eq ▸ H_inj
  -- Step 2: Let R = induced_epsilon_rel η κ f
  set R := induced_epsilon_rel η κ f
  -- Step 3: Show R ∈ (hartogs' (κ := κ))
  -- Need: (i) R ∈ bv_powerset (prod κ κ), (ii) ϕ' R holds
  -- (i) induced_epsilon_rel ⊆ prod κ κ (subset.mk_subset)
  -- (ii) ϕ'(R) = ∃ η', Ord η' ∧ ∃ g, inj_fun η' ω g ∧ image(mem_rel η')(prod ω ω)(pm η' ω g) =ᴮ R ∧ R ≠ ∅
  have HR_mem_hartogs' : Γ ≤ R ∈ᴮ ((hartogs' (κ := κ)) : bSet 𝔹) := by
    -- (hartogs' (κ := κ)) = comprehend ϕ' (bv_powerset (prod ω ω))
    -- use mem_comprehend_iff₂ with ϕ' being the big predicate
    rw [show ((hartogs' (κ := κ))) = comprehend
        (fun x : bSet 𝔹 => ⨆ η', Ord η' ⊓ ⨆ f', is_injective_function η' κ f' ⊓
          (image (mem_rel η') (prod κ κ) (prod_map_self η' κ f') =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ)
        (bv_powerset (prod κ κ)) from rfl]
    rw [mem_comprehend_iff₂
      (H_congr := B_ext_iSup (h := fun η' => B_ext_inf (h₁ := B_ext_const) (h₂ :=
        B_ext_iSup (h := fun f' => B_ext_inf
          (h₁ := B_ext_inf (h₁ := B_ext_const) (h₂ := B_ext_bv_eq_right))
          (h₂ := B_ext_neg (h := B_ext_bv_eq_left))))))]
    -- Provide witness: R itself (R ∈ bv_powerset and ϕ'(R))
    apply le_iSup_of_le R
    refine le_inf ?_ (le_inf bv_refl ?_)
    · -- R ∈ bv_powerset (prod κ κ)
      rw [mem_powerset_iff]
      -- induced_epsilon_rel = image (...) (prod κ κ) (...) ⊆ prod κ κ
      exact le_trans (le_top) (le_trans le_top image_subset)
    · -- ϕ'(R) = ⨆ η', Ord η' ⊓ ...
      apply le_iSup_of_le η
      refine le_inf H_ord ?_
      apply le_iSup_of_le f
      refine le_inf (le_inf Hf bv_refl) ?_
      -- R ≠ ∅: use nonempty_induced_rel_iff_not_zero_and_not_one
      exact ((nonempty_induced_rel_iff_not_zero_and_not_one H_ord (Hf.trans inf_le_left)).mpr
        ⟨H_not_zero, H_not_one⟩)
  -- Step 4: Show η ∈ (hartogs_aux (κ := κ)) using the χ from R ∈ (hartogs' (κ := κ))
  -- Use bv_cases_left pattern to introduce χ while keeping Γ in context
  -- Goal: Γ ≤ η ∈ (hartogs_aux (κ := κ)) = ⨆ χ : (hartogs' (κ := κ)).type, (hartogs' (κ := κ)).bval χ ⊓ η =ᴮ (hartogs_func (κ := κ)) χ
  rw [mem_unfold] at HR_mem_hartogs'
  rw [mem_unfold]
  -- Transform: Γ ≤ (⨆ χ, bval χ ⊓ R =ᴮ func χ) → Γ ≤ (⨆ χ, bval χ ⊓ η =ᴮ (hartogs_func (κ := κ)) χ)
  -- via bv_cases_left keeping Γ in context
  apply le_trans (le_inf HR_mem_hartogs' le_rfl)
  apply bv_cases_left; intro χ
  -- Now ctx = ((hartogs' (κ := κ)).bval χ ⊓ R =ᴮ (hartogs' (κ := κ)).func χ) ⊓ Γ
  apply le_iSup_of_le χ
  apply le_inf (inf_le_left.trans inf_le_left)
  -- Goal: (bval χ ⊓ R =ᴮ func χ) ⊓ Γ ≤ η =ᴮ (hartogs_func (κ := κ)) χ
  -- Step 5: Use hartogs_func_spec
  have Hbval : ((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ ≤
      ((hartogs' (κ := κ))).bval χ := inf_le_left.trans inf_le_left
  have Hfunc_eq : ((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ ≤
      R =ᴮ ((hartogs' (κ := κ))).func χ := inf_le_left.trans inf_le_right
  have H_mem' : ((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ ≤
      ((hartogs' (κ := κ))).func χ ∈ᴮ ((hartogs' (κ := κ))) :=
    le_trans Hbval (mem_mk' _ _)
  have H_spec : ((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ ≤
      (hartogs_ψ (κ := κ)) (((hartogs' (κ := κ))).func χ) ((hartogs_func (κ := κ)) χ) := hartogs_func_spec H_mem'
  have H_afc_ord : ((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ ≤
      Ord ((hartogs_func (κ := κ)) χ) := H_spec.trans (inf_le_left.trans inf_le_left)
  have H_spec_inj : ((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ ≤
      ⨆ g, is_injective_function ((hartogs_func (κ := κ)) χ) κ g ⊓
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ :=
    H_spec.trans (inf_le_left.trans inf_le_right)
  have H_afc_nonempty : ((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ ≤
      (((hartogs' (κ := κ))).func χ =ᴮ ∅)ᶜ := H_spec.trans inf_le_right
  -- Step 6: For each g, derive η =ᴮ (hartogs_func (κ := κ)) χ
  apply le_trans (le_inf H_spec_inj le_rfl)
  apply bv_cases_left; intro g
  -- New ctx: (inj_fun(afc,ω,g) ⊓ img =ᴮ func χ) ⊓ ((bval χ ⊓ R =ᴮ func χ) ⊓ Γ)
  have Hg_inj : (is_injective_function ((hartogs_func (κ := κ)) χ) κ g ⊓
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ) ⊓
      (((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ) ≤
      is_injective_function ((hartogs_func (κ := κ)) χ) κ g :=
    inf_le_left.trans inf_le_left
  have Hg_img : (is_injective_function ((hartogs_func (κ := κ)) χ) κ g ⊓
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ) ⊓
      (((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ) ≤
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ :=
    inf_le_left.trans inf_le_right
  have HR_func_χ : (is_injective_function ((hartogs_func (κ := κ)) χ) κ g ⊓
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ) ⊓
      (((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ) ≤
      R =ᴮ ((hartogs' (κ := κ))).func χ :=
    inf_le_right.trans Hfunc_eq
  have H_afc_ord2 : (is_injective_function ((hartogs_func (κ := κ)) χ) κ g ⊓
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ) ⊓
      (((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ) ≤
      Ord ((hartogs_func (κ := κ)) χ) := inf_le_right.trans H_afc_ord
  have H_nonempty2 : (is_injective_function ((hartogs_func (κ := κ)) χ) κ g ⊓
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ) ⊓
      (((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ) ≤
      (((hartogs' (κ := κ))).func χ =ᴮ ∅)ᶜ := inf_le_right.trans H_afc_nonempty
  -- H_ord, Hf, H_not_one from Γ
  have H_ord2 := inf_le_right.trans (inf_le_right.trans H_ord) (a := (is_injective_function ((hartogs_func (κ := κ)) χ) κ g ⊓
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ) ⊓ (((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ))
  have Hf2 := inf_le_right.trans (inf_le_right.trans Hf) (a := (is_injective_function ((hartogs_func (κ := κ)) χ) κ g ⊓
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ) ⊓ (((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ))
  have H_not_one2 := inf_le_right.trans (inf_le_right.trans H_not_one) (a := (is_injective_function ((hartogs_func (κ := κ)) χ) κ g ⊓
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ) ⊓ (((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ))
  have H_ind_eq : (is_injective_function ((hartogs_func (κ := κ)) χ) κ g ⊓
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ) ⊓
      (((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ) ≤
      induced_epsilon_rel η κ f =ᴮ induced_epsilon_rel ((hartogs_func (κ := κ)) χ) κ g := by
    unfold induced_epsilon_rel at *
    exact le_trans (le_inf HR_func_χ (bv_symm Hg_img)) bv_eq_trans
  have H_exists_two_η := (exists_two_iff H_ord2).mpr H_not_one2
  have H_exists_two_afc : (is_injective_function ((hartogs_func (κ := κ)) χ) κ g ⊓
      image (mem_rel ((hartogs_func (κ := κ)) χ)) (prod κ κ) (prod_map_self ((hartogs_func (κ := κ)) χ) κ g) =ᴮ
      ((hartogs' (κ := κ))).func χ) ⊓
      (((hartogs' (κ := κ))).bval χ ⊓ R =ᴮ ((hartogs' (κ := κ))).func χ ⊓ Γ) ≤
      exists_two ((hartogs_func (κ := κ)) χ) := by
    rw [exists_two_iff H_afc_ord2]
    -- Use: not_one_of_induced_rel_nonempty + ind nonempty from H_nonempty2 + Hg_img
    apply not_one_of_induced_rel_nonempty (Hg_inj.trans inf_le_left)
    -- Need: (induced_epsilon_rel ((hartogs_func (κ := κ)) χ) κ g =ᴮ ∅)ᶜ
    -- From Hg_img: ind =ᴮ (hartogs' (κ := κ)).func χ and H_nonempty2: ((hartogs' (κ := κ)).func χ =ᴮ ∅)ᶜ
    apply bv_rw' (H := Hg_img) (ϕ := fun v => (v =ᴮ ∅)ᶜ)
      (h_congr := B_ext_neg (h := B_ext_bv_eq_left))
    exact H_nonempty2
  exact eq_of_eq_induced_epsilon_rel H_ord2 H_afc_ord2 Hf2 Hg_inj H_ind_eq
    H_exists_two_η H_exists_two_afc

-- src/aleph_one.lean:777
variable (Hone : (⊤ : 𝔹) ≤ injects_into (1 : bSet 𝔹) κ)
include Hone

lemma mem_hartogs_iff {Γ : 𝔹} {η : bSet 𝔹} (H_ord : Γ ≤ Ord η) :
    Γ ≤ η ∈ᴮ (hartogs (κ := κ)) ↔ Γ ≤ ⨆ f, is_injective_function η κ f := by
  constructor
  · -- Forward: η ∈ (hartogs (κ := κ)) → η injects into ω
    intro H_mem
    rw [mem_hartogs_iff₀] at H_mem
    -- Case split: η = 0, η = 1, or η ∈ (hartogs_aux (κ := κ))
    apply le_trans H_mem; apply sup_le; apply sup_le
    · -- Case η = 0: 0 injects into ω
      exact le_trans (le_inf (bv_symm le_rfl) (le_trans le_top
        (injection_into_of_injects_into (zero_injects (κ := κ)))))
        (B_ext_iSup (h := fun f => B_ext_is_injective_function_left) _ _)
    · -- Case η = 1: 1 injects into ω
      exact le_trans (le_inf (bv_symm le_rfl) (le_trans le_top
        (injection_into_of_injects_into Hone)))
        (B_ext_iSup (h := fun f => B_ext_is_injective_function_left) _ _)
    · -- Case η ∈ (hartogs_aux (κ := κ)): get (hartogs_func (κ := κ)) χ which injects into ω
      rw [mem_unfold]
      apply le_trans (b := ⨆ (i : ((hartogs' (κ := κ))).type), ((hartogs' (κ := κ))).bval i ⊓ η =ᴮ (hartogs_func (κ := κ)) i)
      · exact le_rfl
      apply iSup_le; intro χ
      -- (hartogs' (κ := κ)).bval χ ⊓ η =ᴮ (hartogs_func (κ := κ)) χ → η injects into ω
      -- hartogs_func_spec: Γ ≤ (hartogs_ψ (κ := κ)) ((hartogs' (κ := κ)).func χ) ((hartogs_func (κ := κ)) χ) includes ⨆ g, inj_fun((hartogs_func (κ := κ)) χ,ω,g)
      -- η =ᴮ (hartogs_func (κ := κ)) χ → η has same injections
      have H_mem' : ((hartogs' (κ := κ))).bval χ ⊓ η =ᴮ (hartogs_func (κ := κ)) χ ≤
          ((hartogs' (κ := κ))).func χ ∈ᴮ ((hartogs' (κ := κ))) :=
        le_trans inf_le_left (mem_mk' _ _)
      have H_spec : ((hartogs' (κ := κ))).bval χ ⊓ η =ᴮ (hartogs_func (κ := κ)) χ ≤
          (hartogs_ψ (κ := κ)) (((hartogs' (κ := κ))).func χ) ((hartogs_func (κ := κ)) χ) := hartogs_func_spec H_mem'
      have H_afc_inj : ((hartogs' (κ := κ))).bval χ ⊓ η =ᴮ (hartogs_func (κ := κ)) χ ≤
          ⨆ g, is_injective_function ((hartogs_func (κ := κ)) χ) κ g :=
        le_trans (H_spec.trans (inf_le_left.trans inf_le_right))
          (iSup_le (fun g => le_iSup_of_le g inf_le_left))
      -- Rewrite using η =ᴮ (hartogs_func (κ := κ)) χ
      exact le_trans (le_inf (bv_symm inf_le_right) H_afc_inj)
        (B_ext_iSup (h := fun g => B_ext_is_injective_function_left) _ _)
  · -- Backward: η injects into ω → η ∈ (hartogs (κ := κ))
    intro H_inj
    rw [mem_hartogs_iff₀]
    -- BA-valued case split on η = 1, then η = 0
    apply le_trans (b := (η =ᴮ 1 ⊔ (η =ᴮ 1)ᶜ) ⊓ Γ)
    · simp [sup_compl_eq_top]
    apply bv_or_elim_left
    · -- Case η = 1: → z =ᴮ 0 ⊔ z =ᴮ 1 ⊔ _
      exact le_trans inf_le_left (le_sup_of_le_left le_sup_right)
    · -- Case η ≠ 1: split on η = 0
      apply le_trans (b := (η =ᴮ 0 ⊔ (η =ᴮ 0)ᶜ) ⊓ ((η =ᴮ 1)ᶜ ⊓ Γ))
      · simp [sup_compl_eq_top]
      apply bv_or_elim_left
      · -- Case η = 0: → z =ᴮ 0 ⊔ ...
        exact le_trans inf_le_left (le_sup_of_le_left le_sup_left)
      · -- Case η ≠ 0, η ≠ 1: use mem_hartogs_of_injects_into_omega_aux
        -- Context: (η=0)ᶜ ⊓ ((η=1)ᶜ ⊓ Γ)
        apply le_sup_of_le_right
        apply mem_hartogs_of_injects_into_omega_aux
        · exact inf_le_right.trans (inf_le_right.trans H_ord)  -- Γ → Ord η
        · exact inf_le_right.trans (inf_le_right.trans H_inj)  -- Γ → H_inj
        · exact inf_le_left  -- (η=0)ᶜ
        · exact inf_le_right.trans inf_le_left  -- (η=1)ᶜ

-- src/aleph_one.lean:802
lemma hartogs_transitive {Γ : 𝔹} : Γ ≤ is_transitive (hartogs (κ := κ)) := by
  unfold is_transitive
  apply le_iInf; intro z; rw [← deduction]
  rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]
  -- Goal: Γ ⊓ z ∈ (hartogs (κ := κ)) ⊓ w ∈ z ≤ w ∈ (hartogs (κ := κ))
  -- Case-split on z ∈ (hartogs (κ := κ)) ↔ (z = 0 ⊔ z = 1) ⊔ z ∈ (hartogs_aux (κ := κ))  (left-assoc via mem_hartogs_iff₀)
  have H_cases : Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z ≤ z =ᴮ 0 ⊔ z =ᴮ 1 ⊔ z ∈ᴮ (hartogs_aux (κ := κ)) :=
    mem_hartogs_iff₀.mp (inf_le_left.trans inf_le_right)
  apply le_trans (b := (z =ᴮ 0 ⊔ z =ᴮ 1 ⊔ z ∈ᴮ (hartogs_aux (κ := κ))) ⊓ (Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z))
  · exact le_inf H_cases le_rfl
  -- Goal: ((z=0 ⊔ z=1) ⊔ z∈(hartogs_aux (κ := κ))) ⊓ ctx ≤ w ∈ (hartogs (κ := κ))  (left-assoc)
  -- Outer split: z=0 ⊔ z=1 vs z∈(hartogs_aux (κ := κ))
  · apply bv_or_elim_left
    · -- Case z = 0 ⊔ z = 1: inner split
      apply bv_or_elim_left
      · -- Case z = 0: z = ∅, so w ∈ ∅ → contradiction
        apply bv_exfalso
        apply bv_absurd (w ∈ᴮ (∅ : bSet 𝔹))
        · -- w ∈ ∅ from w ∈ z and z =ᴮ 0 =ᴮ ∅
          apply mem_congr bv_refl
          · exact le_trans (le_inf inf_le_left zero_eq_empty) bv_eq_trans
          · exact inf_le_right.trans inf_le_right
        · exact (empty_iff_forall_not_mem.mp bv_refl).trans (iInf_le _ w)
      · -- Case z = 1: w ∈ 1 → w = 0 → w ∈ (hartogs (κ := κ))
        rw [mem_hartogs_iff₀]
        apply le_trans _ (le_sup_left.trans le_sup_left)
        apply eq_zero_of_mem_one
        exact mem_congr bv_refl inf_le_left (inf_le_right.trans inf_le_right)
    · -- Case z ∈ (hartogs_aux (κ := κ)): z is an ordinal injecting into κ
      -- Show w ∈ (hartogs (κ := κ)) using mem_hartogs_iff Hone: w injects into κ too (via z's injection)
      -- Step 1: z injects into κ (from mem_hartogs_iff Hone forward on z ∈ (hartogs (κ := κ)))
      have Hz_hartogs : (z ∈ᴮ (hartogs_aux (κ := κ))) ⊓ (Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z) ≤ z ∈ᴮ (hartogs (κ := κ)) :=
        inf_le_right.trans (inf_le_left.trans inf_le_right)
      have Hz_ord : (z ∈ᴮ (hartogs_aux (κ := κ))) ⊓ (Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z) ≤ Ord z :=
        Ord_of_mem_hartogs Hz_hartogs
      have Hz_inj : (z ∈ᴮ (hartogs_aux (κ := κ))) ⊓ (Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z) ≤
          ⨆ f, is_injective_function z κ f :=
        (mem_hartogs_iff Hone Hz_ord).mp Hz_hartogs
      -- Step 2: w ⊆ z (from w ∈ z and Ord z is transitive)
      have Hw_z : (z ∈ᴮ (hartogs_aux (κ := κ))) ⊓ (Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z) ≤ w ∈ᴮ z :=
        inf_le_right.trans inf_le_right
      have Hw_sub : (z ∈ᴮ (hartogs_aux (κ := κ))) ⊓ (Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z) ≤ w ⊆ᴮ z :=
        subset_of_mem_transitive (Hz_ord.trans inf_le_right) Hw_z
      -- Step 3: w injects into κ (via injects_into_of_subset + injects_into_trans)
      have Hw_ord : (z ∈ᴮ (hartogs_aux (κ := κ))) ⊓ (Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z) ≤ Ord w :=
        Ord_of_mem_Ord Hw_z Hz_ord
      have Hw_inj_into_z : (z ∈ᴮ (hartogs_aux (κ := κ))) ⊓ (Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z) ≤ injects_into w z :=
        injects_into_of_subset Hw_sub
      have Hz_inj_into_omega : (z ∈ᴮ (hartogs_aux (κ := κ))) ⊓ (Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z) ≤
          injects_into z κ :=
        injects_into_of_injection_into Hz_inj
      have Hw_inj_into_omega : (z ∈ᴮ (hartogs_aux (κ := κ))) ⊓ (Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z) ≤
          injects_into w κ :=
        injects_into_trans Hw_inj_into_z Hz_inj_into_omega
      -- Convert injects_into to ⨆ f, is_injective_function w κ f
      have Hw_inj : (z ∈ᴮ (hartogs_aux (κ := κ))) ⊓ (Γ ⊓ z ∈ᴮ (hartogs (κ := κ)) ⊓ w ∈ᴮ z) ≤
          ⨆ f, is_injective_function w κ f :=
        injection_into_of_injects_into Hw_inj_into_omega
      -- Step 4: w ∈ (hartogs (κ := κ)) by mem_hartogs_iff Hone backward
      exact (mem_hartogs_iff Hone Hw_ord).mpr Hw_inj

-- src/aleph_one.lean:818
omit Hone in
lemma hartogs_ewo {Γ : 𝔹} : Γ ≤ ewo (hartogs (κ := κ)) := by
  unfold ewo epsilon_well_orders
  refine le_inf ?_ ?_
  · -- epsilon_trichotomy (hartogs (κ := κ)): all members of (hartogs (κ := κ)) are Ords and ordinals satisfy trichotomy
    apply epsilon_trichotomy_of_sub_Ord
    apply le_iInf; intro x; rw [← deduction]
    exact Ord_of_mem_hartogs inf_le_right
  · -- epsilon_well_founded (hartogs (κ := κ)): regularity gives well-foundedness for any sub-Ord
    exact epsilon_wf_of_sub_Ord (hartogs (κ := κ))

-- src/aleph_one.lean:826
lemma hartogs_Ord {Γ : 𝔹} : Γ ≤ Ord (hartogs (κ := κ)) := le_inf hartogs_ewo (hartogs_transitive Hone)

-- src/aleph_one.lean:828
lemma hartogs_not_le_omega {Γ : 𝔹} : Γ ≤ (injects_into (hartogs (κ := κ)) κ)ᶜ := by
  rw [← imp_bot, ← deduction]
  -- Goal: Γ ⊓ injects_into (hartogs (κ := κ)) κ ≤ ⊥
  apply bot_of_mem_self'
  -- Goal: Γ ⊓ injects_into (hartogs (κ := κ)) κ ≤ (hartogs (κ := κ)) ∈ (hartogs (κ := κ))
  apply (mem_hartogs_iff Hone (inf_le_left.trans (hartogs_Ord Hone))).mpr
  -- Goal: Γ ⊓ injects_into (hartogs (κ := κ)) κ ≤ ⨆ f, is_injective_function (hartogs (κ := κ)) κ f = injection_into (hartogs (κ := κ)) κ
  exact injects_into_iff_injection_into.mp inf_le_right

-- src/aleph_one.lean:834
lemma hartogs_spec {Γ : 𝔹} : Γ ≤ leastNoninjectingOrdinal κ (hartogs (κ := κ)) := by
  refine le_inf (hartogs_not_le_omega Hone) (le_inf (hartogs_Ord Hone) ?_)
  apply le_iInf; intro y; rw [← deduction, ← deduction]
  -- ctx := Γ ⊓ Ord y ⊓ (injects_into y κ)ᶜ, Goal: ctx ≤ (hartogs (κ := κ)) ⊆ y
  have H_Ord_y : Γ ⊓ Ord y ⊓ (injects_into y κ)ᶜ ≤ Ord y :=
    inf_le_left.trans inf_le_right
  have H_no_inj_y : Γ ⊓ Ord y ⊓ (injects_into y κ)ᶜ ≤ (injects_into y κ)ᶜ :=
    inf_le_right
  -- Show y ∉ (hartogs (κ := κ)) (if y ∈ (hartogs (κ := κ)) then injects_into y κ, contradiction)
  have H_not_mem_hartogs : Γ ⊓ Ord y ⊓ (injects_into y κ)ᶜ ≤ (y ∈ᴮ (hartogs (κ := κ)))ᶜ := by
    apply (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr _))
    apply bv_absurd (injects_into y κ)
    · exact injects_into_of_injection_into ((mem_hartogs_iff Hone (inf_le_left.trans H_Ord_y)).mp inf_le_right)
    · exact inf_le_left.trans H_no_inj_y
  -- Now prove (hartogs (κ := κ)) ⊆ y by trichotomy
  rw [Ord.le_iff_lt_or_eq (hartogs_Ord Hone) H_Ord_y]
  -- Goal: ctx ≤ (hartogs (κ := κ)) ∈ y ⊔ (hartogs (κ := κ)) = y
  have H_tri := Ord.trichotomy (hartogs_Ord Hone) H_Ord_y
  -- tri: ctx ≤ ((hartogs (κ := κ)) =ᴮ y ⊔ (hartogs (κ := κ)) ∈ᴮ y) ⊔ y ∈ᴮ (hartogs (κ := κ))
  apply le_trans (b := ((hartogs (κ := κ)) =ᴮ y ⊔ (hartogs (κ := κ)) ∈ᴮ y ⊔ y ∈ᴮ (hartogs (κ := κ))) ⊓
      (Γ ⊓ Ord y ⊓ (injects_into y κ)ᶜ))
  · exact le_inf H_tri le_rfl
  · apply bv_or_elim_left
    · -- Case ((hartogs (κ := κ))=y ⊔ (hartogs (κ := κ))∈y) ⊓ ctx
      apply bv_or_elim_left
      · -- (hartogs (κ := κ))=y: → (hartogs (κ := κ))∈y ⊔ (hartogs (κ := κ))=y (right branch)
        exact le_trans inf_le_left le_sup_right
      · -- (hartogs (κ := κ))∈y: → (hartogs (κ := κ))∈y ⊔ (hartogs (κ := κ))=y (left branch)
        exact le_trans inf_le_left le_sup_left
    · -- Case y∈(hartogs (κ := κ)) ⊓ ctx: contradicts H_not_mem_hartogs
      apply bv_exfalso
      exact bv_absurd _ inf_le_left (inf_le_right.trans H_not_mem_hartogs)

end bSet.ErdosHartogs
