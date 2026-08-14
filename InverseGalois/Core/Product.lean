/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core.Basic

/-!
# Direct Products of Inverse Galois Groups

We show that the inverse Galois property is closed under direct products of groups with
coprime orders.

## Strategy

The core algebraic result is: if `K` and `L` are Galois intermediate fields of `E/F` with
`K ⊔ L = ⊤` and `K ⊓ L = ⊥`, then `Gal(E/F) ≅ Gal(K/F) × Gal(L/F)`.

For inverse Galois groups with coprime orders, we embed the realizing fields into the algebraic
closure `AlgebraicClosure ℚ` and apply this result, using that coprime Galois extensions have
trivial intersection.

## Main results

* `galProdEquiv`: If `K ⊔ L = ⊤` and `K ⊓ L = ⊥` with both `K/F` and `L/F` Galois,
  then `Gal(E/F) ≅ Gal(K/F) × Gal(L/F)`.
* `IsInverseGalois.prod_of_coprime`: If `G₁` and `G₂` are inverse Galois groups with coprime
  orders, then `G₁ × G₂` is an inverse Galois group.
-/

open Polynomial IntermediateField Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The restriction map `Gal(E/F) →* Gal(K/F) × Gal(L/F)` that sends an automorphism
to its restrictions to two normal intermediate fields. -/
def galRestrictionProd (K L : IntermediateField F E) [Normal F K] [Normal F L] :
    Gal(E/F) →* Gal(K/F) × Gal(L/F) :=
  MonoidHom.prod (AlgEquiv.restrictNormalHom K) (AlgEquiv.restrictNormalHom L)

/-
The restriction to two intermediate fields is injective when their sup is the whole field.
-/
theorem galRestrictionProd_injective (K L : IntermediateField F E) [Normal F K] [Normal F L]
    (h_sup : K ⊔ L = ⊤) : Function.Injective (galRestrictionProd K L) := by
  intro σ τ h_eq
  have h_eq_K : ∀ x ∈ K, σ x = τ x := by
    intro x hx
    have h_restrict : (galRestrictionProd K L σ).1 ⟨x, hx⟩ = (galRestrictionProd K L τ).1 ⟨x, hx⟩ := by
      grind
    convert h_restrict using 1
    simp [galRestrictionProd]
    grind only [AlgEquiv.restrictNormalHom_apply]
  ext x
  have hx : x ∈ IntermediateField.adjoin F (K ∪ L) := by convert mem_top (x := x)
  induction hx using adjoin_induction with
  | mem x hx =>
    simp_all only [Set.mem_union, SetLike.mem_coe]
    cases hx with
    | inl h => simp_all only
    | inr h_1 =>
      replace h_eq := congr_arg (fun f => f.2 (⟨x, h_1⟩ : L)) h_eq
      simp_all [galRestrictionProd]
      grind only [AlgEquiv.restrictNormalHom_apply]
  | algebraMap r => simp [AlgEquiv.commutes]
  | add x y hx hy ihx ihy => simp_all only [map_add]
  | inv x hx ih => simp_all only [map_inv₀]
  | mul x y hx hy ihx ihy => simp [*, map_mul]

/-- If `K ⊔ L = ⊤` and `K ⊓ L = ⊥` with both `K/F` and `L/F` Galois, then
`Gal(E/F) ≅ Gal(K/F) × Gal(L/F)`. -/
def galProdEquiv [FiniteDimensional F E] [IsGalois F E]
    (K L : IntermediateField F E) [IsGalois F K] [IsGalois F L]
    (h_sup : K ⊔ L = ⊤) (h_inf : K ⊓ L = ⊥) :
    Gal(E/F) ≃* Gal(K/F) × Gal(L/F) :=
  MulEquiv.ofBijective (galRestrictionProd K L) <| by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨galRestrictionProd_injective K L h_sup, ?_⟩
    rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
      IsGalois.card_aut_eq_finrank]
    have := (IntermediateField.LinearDisjoint.of_inf_eq_bot h_inf).finrank_sup
    rwa [h_sup, finrank_top'] at this

/-
Coprime intermediate Galois extensions have trivial intersection.
-/
theorem IntermediateField.inf_eq_bot_of_isGalois_coprime [FiniteDimensional F E]
    (K L : IntermediateField F E) [IsGalois F K] [IsGalois F L]
    (hcop : Nat.Coprime (finrank F K) (finrank F L)) :
    K ⊓ L = ⊥ := by
  have h_deg_K : finrank F (↥(K ⊓ L)) ∣ finrank F K :=
    finrank_dvd_of_le_right inf_le_left
  have h_deg_L : finrank F (↥(K ⊓ L)) ∣ finrank F L :=
    finrank_dvd_of_le_right inf_le_right
  have := Nat.dvd_gcd h_deg_K h_deg_L
  simp_all

/-
Given a Galois extension `L/ℚ`, its image under an embedding into the algebraic closure
is a Galois intermediate field isomorphic to `L`.
-/
lemma IsInverseGalois.galois_image_in_algClosure
    (L : Type) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (i : L →ₐ[ℚ] AlgebraicClosure ℚ) :
    IsGalois ℚ i.fieldRange ∧
    Nonempty (Gal(L/ℚ) ≃* Gal(i.fieldRange / ℚ)) := by
  constructor
  · exact IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField i)
  · exact ⟨(AlgEquiv.ofInjective i i.injective).autCongr⟩

/-!
## Direct product via the compositum

Given two Galois intermediate fields `K₁`, `K₂` of `E / F` with coprime degrees,
we set up the algebra tower `F → Kᵢ → ↥(K₁ ⊔ K₂)` and use the restriction maps
to construct `Gal(↥(K₁ ⊔ K₂)/F) ≃* Gal(K₁/F) × Gal(K₂/F)`.
-/

section Compositum

variable {F' : Type*} [Field F'] {E' : Type*} [Field E'] [Algebra F' E']
variable (K₁' K₂' : IntermediateField F' E')

/-- Algebra structure on K₁ → ↥(K₁ ⊔ K₂) via inclusion. -/
instance algSupLeft : Algebra ↥K₁' ↥(K₁' ⊔ K₂') :=
  (IntermediateField.inclusion (le_sup_left : K₁' ≤ K₁' ⊔ K₂')).toAlgebra

/-- The action of `K₁` on the compositum, named to short-circuit the generic search: an
intermediate field is a subtype, so without this the search first tries every way of making the
compositum a module over a base of `E`. -/
instance (priority := high) smulSupLeft : SMul ↥K₁' ↥(K₁' ⊔ K₂') := Algebra.toSMul

/-- The module structure of the compositum over `K₁`, named for the same reason as
`smulSupLeft`. -/
instance (priority := high) moduleSupLeft : Module ↥K₁' ↥(K₁' ⊔ K₂') := Algebra.toModule

/-- Scalar tower F → K₁ → ↥(K₁ ⊔ K₂). -/
instance towerSupLeft : IsScalarTower F' ↥K₁' ↥(K₁' ⊔ K₂') :=
  IsScalarTower.of_algebraMap_eq fun x => by
    ext
    simp [RingHom.algebraMap_toAlgebra, IntermediateField.inclusion, Subalgebra.inclusion]

/-- Algebra structure on K₂ → ↥(K₁ ⊔ K₂) via inclusion. -/
instance algSupRight : Algebra ↥K₂' ↥(K₁' ⊔ K₂') :=
  (IntermediateField.inclusion (le_sup_right : K₂' ≤ K₁' ⊔ K₂')).toAlgebra

/-- The action of `K₂` on the compositum, named to short-circuit the generic search. -/
instance (priority := high) smulSupRight : SMul ↥K₂' ↥(K₁' ⊔ K₂') := Algebra.toSMul

/-- The module structure of the compositum over `K₂`, named for the same reason as
`smulSupRight`. -/
instance (priority := high) moduleSupRight : Module ↥K₂' ↥(K₁' ⊔ K₂') := Algebra.toModule

/-- Scalar tower F → K₂ → ↥(K₁ ⊔ K₂). -/
instance towerSupRight : IsScalarTower F' ↥K₂' ↥(K₁' ⊔ K₂') :=
  IsScalarTower.of_algebraMap_eq fun x => by
    ext
    simp [RingHom.algebraMap_toAlgebra, IntermediateField.inclusion, Subalgebra.inclusion]

/-- The restriction map from `Gal(↥(K₁ ⊔ K₂)/F)` to `Gal(K₁/F) × Gal(K₂/F)`. -/
def galSupRestrictionProd [Normal F' K₁'] [Normal F' K₂'] :
    Gal(↥(K₁' ⊔ K₂')/F') →* Gal(↥K₁'/F') × Gal(↥K₂'/F') :=
  MonoidHom.prod (AlgEquiv.restrictNormalHom ↥K₁') (AlgEquiv.restrictNormalHom ↥K₂')

/-- The restriction map from `Gal(↥(K₁ ⊔ K₂)/F)` to `Gal(K₁/F) × Gal(K₂/F)` is injective. -/
theorem galSupRestrictionProd_injective [Normal F' K₁'] [Normal F' K₂']
    [FiniteDimensional F' ↥(K₁' ⊔ K₂')] :
    Function.Injective (galSupRestrictionProd K₁' K₂') := by
  intro σ τ h_eq
  have hK₁ : σ.restrictNormal ↥K₁' = τ.restrictNormal ↥K₁' := congr_arg Prod.fst h_eq
  have hK₂ : σ.restrictNormal ↥K₂' = τ.restrictNormal ↥K₂' := congr_arg Prod.snd h_eq
  ext ⟨a, ha⟩
  have ha_adj : a ∈ IntermediateField.adjoin F' (↑K₁' ∪ ↑K₂') := by
    rw [← IntermediateField.sup_def]
    exact ha
  induction ha_adj using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · have commσ := AlgEquiv.restrictNormal_commutes σ ↥K₁' (⟨x, hx⟩ : ↥K₁')
      have commτ := AlgEquiv.restrictNormal_commutes τ ↥K₁' (⟨x, hx⟩ : ↥K₁')
      have key : (algebraMap ↥K₁' ↥(K₁' ⊔ K₂') ⟨x, hx⟩ : ↥(K₁' ⊔ K₂')) = ⟨x, ha⟩ := by
        ext
        simp [RingHom.algebraMap_toAlgebra, IntermediateField.inclusion, Subalgebra.inclusion]
      rw [key] at commσ commτ
      rw [hK₁] at commσ
      exact congr_arg (fun a => (a : ↥(K₁' ⊔ K₂')).val) (commσ.symm.trans commτ)
    · have commσ := AlgEquiv.restrictNormal_commutes σ ↥K₂' (⟨x, hx⟩ : ↥K₂')
      have commτ := AlgEquiv.restrictNormal_commutes τ ↥K₂' (⟨x, hx⟩ : ↥K₂')
      have key : (algebraMap ↥K₂' ↥(K₁' ⊔ K₂') ⟨x, hx⟩ : ↥(K₁' ⊔ K₂')) = ⟨x, ha⟩ := by
        ext
        simp [RingHom.algebraMap_toAlgebra, IntermediateField.inclusion, Subalgebra.inclusion]
      rw [key] at commσ commτ
      rw [hK₂] at commσ
      exact congr_arg (fun a => (a : ↥(K₁' ⊔ K₂')).val) (commσ.symm.trans commτ)
  | algebraMap r =>
    simp [AlgEquiv.commutes]
  | add x y hx hy ihx ihy =>
    have hx' : x ∈ K₁' ⊔ K₂' := IntermediateField.sup_def K₁' K₂' ▸ hx
    have hy' : y ∈ K₁' ⊔ K₂' := IntermediateField.sup_def K₁' K₂' ▸ hy
    show (σ (⟨x, hx'⟩ + ⟨y, hy'⟩) : ↥(K₁' ⊔ K₂')).val = (τ (⟨x, hx'⟩ + ⟨y, hy'⟩) : ↥(K₁' ⊔ K₂')).val
    simp only [map_add, AddMemClass.coe_add, ihx hx', ihy hy']
  | mul x y hx hy ihx ihy =>
    have hx' : x ∈ K₁' ⊔ K₂' := IntermediateField.sup_def K₁' K₂' ▸ hx
    have hy' : y ∈ K₁' ⊔ K₂' := IntermediateField.sup_def K₁' K₂' ▸ hy
    show (σ (⟨x, hx'⟩ * ⟨y, hy'⟩) : ↥(K₁' ⊔ K₂')).val = (τ (⟨x, hx'⟩ * ⟨y, hy'⟩) : ↥(K₁' ⊔ K₂')).val
    simp only [map_mul, MulMemClass.coe_mul, ihx hx', ihy hy']
  | inv x hx ih =>
    have hx' : x ∈ K₁' ⊔ K₂' := IntermediateField.sup_def K₁' K₂' ▸ hx
    show (σ (⟨x, hx'⟩⁻¹) : ↥(K₁' ⊔ K₂')).val = (τ (⟨x, hx'⟩⁻¹) : ↥(K₁' ⊔ K₂')).val
    simp only [map_inv₀]
    exact congr_arg Inv.inv (ih hx')

/-
The cardinality of `Gal(↥(K₁ ⊔ K₂)/F)` equals `Gal(K₁/F) × Gal(K₂/F)` when
    the two fields have coprime degrees.
-/
theorem galSup_card_eq [IsGalois F' K₁'] [IsGalois F' K₂']
    [FiniteDimensional F' ↥(K₁' ⊔ K₂')]
    (hcop : Nat.Coprime (finrank F' K₁') (finrank F' K₂')) :
    Nat.card Gal(↥(K₁' ⊔ K₂')/F') = Nat.card (Gal(↥K₁'/F') × Gal(↥K₂'/F')) := by
  -- Use the fact that the cardinality of the Galois group of a finite Galois extension is equal to the degree of the extension.
  have h_card_galois_sup : Nat.card (Gal(↥(K₁' ⊔ K₂')/F')) = finrank F' ↥(K₁' ⊔ K₂') := by
    apply IsGalois.card_aut_eq_finrank
  have h_card_galois_K1K2 : Nat.card (Gal(↥K₁'/F') × Gal(↥K₂'/F')) = finrank F' K₁' * finrank F' K₂' := by
    simp [Nat.card_prod]
    convert congr_arg₂ (· * ·) (IsGalois.card_aut_eq_finrank F' K₁')
      (IsGalois.card_aut_eq_finrank F' K₂') using 1
    · have h := IntermediateField.inclusion (le_sup_left : K₁' ≤ K₁' ⊔ K₂')
      exact FiniteDimensional.of_injective h.toLinearMap h.injective
    · have h := IntermediateField.inclusion (le_sup_right : K₂' ≤ K₁' ⊔ K₂')
      exact FiniteDimensional.of_injective h.toLinearMap h.injective
  convert IntermediateField.LinearDisjoint.finrank_sup _
  grind only [LinearDisjoint.of_finrank_coprime]

/-- If `K₁` and `K₂` are Galois intermediate fields with coprime degrees, then
`Gal(↥(K₁ ⊔ K₂)/F) ≃* Gal(K₁/F) × Gal(K₂/F)`. -/
def galSupProdEquiv [IsGalois F' K₁'] [IsGalois F' K₂']
    [IsGalois F' ↥(K₁' ⊔ K₂')]
    [FiniteDimensional F' ↥(K₁' ⊔ K₂')]
    (hcop : Nat.Coprime (finrank F' K₁') (finrank F' K₂')) :
    Gal(↥(K₁' ⊔ K₂')/F') ≃* Gal(↥K₁'/F') × Gal(↥K₂'/F') :=
  MulEquiv.ofBijective (galSupRestrictionProd K₁' K₂') <| by
    have : FiniteDimensional F' ↥K₁' := by
      have h := IntermediateField.inclusion (le_sup_left : K₁' ≤ K₁' ⊔ K₂')
      exact FiniteDimensional.of_injective h.toLinearMap h.injective
    have : FiniteDimensional F' ↥K₂' := by
      have h := IntermediateField.inclusion (le_sup_right : K₂' ≤ K₁' ⊔ K₂')
      exact FiniteDimensional.of_injective h.toLinearMap h.injective
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨galSupRestrictionProd_injective K₁' K₂', galSup_card_eq K₁' K₂' hcop⟩

end Compositum

/-- Helper: the compositum of two Galois intermediate fields in the algebraic closure, restricted
appropriately, gives a Galois extension whose Galois group is the product. -/
theorem IsInverseGalois.of_coprime_intermediate_fields
    (K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [hg₁ : IsGalois ℚ K₁] [hg₂ : IsGalois ℚ K₂]
    [FiniteDimensional ℚ K₁] [FiniteDimensional ℚ K₂]
    (hcop : Nat.Coprime (finrank ℚ K₁) (finrank ℚ K₂))
    {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (e₁ : Gal(K₁/ℚ) ≃* G₁) (e₂ : Gal(K₂/ℚ) ≃* G₂) :
    IsInverseGalois (G₁ × G₂) := by
  -- The compositum K₁ ⊔ K₂ is finite-dimensional and Galois over ℚ
  have : FiniteDimensional ℚ ↥(K₁ ⊔ K₂) := IntermediateField.finiteDimensional_sup K₁ K₂
  have : IsGalois ℚ ↥(K₁ ⊔ K₂) :=
    FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateFieldMax K₁ K₂
  -- Use the compositum as the realizing extension
  refine ⟨↥(K₁ ⊔ K₂), inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  -- Compose the product isomorphism with e₁ × e₂
  exact (galSupProdEquiv K₁ K₂ hcop).trans (MulEquiv.prodCongr e₁ e₂)

/-- If `G₁` and `G₂` are inverse Galois groups with coprime orders, then `G₁ × G₂` is also
an inverse Galois group. -/
theorem IsInverseGalois.prod_of_coprime {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (h₁ : IsInverseGalois G₁) (h₂ : IsInverseGalois G₂)
    (hcop : Nat.Coprime (Nat.card G₁) (Nat.card G₂)) :
    IsInverseGalois (G₁ × G₂) := by
  -- Obtain realizing fields and isomorphisms
  obtain ⟨L₁, _, _, _, _, ⟨φ₁⟩⟩ := h₁
  obtain ⟨L₂, _, _, _, _, ⟨φ₂⟩⟩ := h₂
  -- Embed into algebraic closure
  let i₁ : L₁ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let i₂ : L₂ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let K₁ := i₁.fieldRange
  let K₂ := i₂.fieldRange
  -- Get Galois instances and isomorphisms for the images
  obtain ⟨hg₁, ⟨ψ₁⟩⟩ := galois_image_in_algClosure L₁ i₁
  obtain ⟨hg₂, ⟨ψ₂⟩⟩ := galois_image_in_algClosure L₂ i₂
  -- FiniteDimensional instances for the images
  have : FiniteDimensional ℚ K₁ := FiniteDimensional.of_injective
    (AlgEquiv.ofInjectiveField i₁).symm.toLinearMap (AlgEquiv.ofInjectiveField i₁).symm.injective
  have : FiniteDimensional ℚ K₂ := FiniteDimensional.of_injective
    (AlgEquiv.ofInjectiveField i₂).symm.toLinearMap (AlgEquiv.ofInjectiveField i₂).symm.injective
  -- Show coprimality of the degrees
  have hcop' : Nat.Coprime (finrank ℚ K₁) (finrank ℚ K₂) := by
    rwa [show finrank ℚ K₁ = Nat.card G₁ from ?_, show finrank ℚ K₂ = Nat.card G₂ from ?_]
    · rw [← IsGalois.card_aut_eq_finrank]
      exact Nat.card_congr (ψ₂.symm.trans φ₂).toEquiv
    · rw [← IsGalois.card_aut_eq_finrank]
      exact Nat.card_congr (ψ₁.symm.trans φ₁).toEquiv
  -- Apply the helper
  exact of_coprime_intermediate_fields K₁ K₂ hcop' (ψ₁.symm.trans φ₁) (ψ₂.symm.trans φ₂)

/-!
## Generalized product without coprimality

The following variants use `K₁ ⊓ K₂ = ⊥` directly instead of requiring coprime degrees.
This is needed for examples like V₄ ≅ (ℤ/2ℤ) × (ℤ/2ℤ) where both factors have order 2.
-/

section DisjointProduct

variable {F' : Type*} [Field F'] {E' : Type*} [Field E'] [Algebra F' E']
variable (K₁' K₂' : IntermediateField F' E')

/-- If `K₁` and `K₂` are Galois intermediate fields with `K₁ ⊓ K₂ = ⊥`, then
`Gal(↥(K₁ ⊔ K₂)/F) ≃* Gal(K₁/F) × Gal(K₂/F)`.

This is a generalization of `galSupProdEquiv` that does not require coprime degrees,
but instead directly assumes the intersection is trivial. -/
def galSupProdEquiv' [IsGalois F' K₁'] [IsGalois F' K₂']
    [IsGalois F' ↥(K₁' ⊔ K₂')]
    [FiniteDimensional F' ↥(K₁' ⊔ K₂')]
    (h_inf : K₁' ⊓ K₂' = ⊥) :
    Gal(↥(K₁' ⊔ K₂')/F') ≃* Gal(↥K₁'/F') × Gal(↥K₂'/F') := by
  have : FiniteDimensional F' ↥K₁' := by
    have h := IntermediateField.inclusion (le_sup_left : K₁' ≤ K₁' ⊔ K₂')
    exact FiniteDimensional.of_injective h.toLinearMap h.injective
  have : FiniteDimensional F' ↥K₂' := by
    have h := IntermediateField.inclusion (le_sup_right : K₂' ≤ K₁' ⊔ K₂')
    exact FiniteDimensional.of_injective h.toLinearMap h.injective
  apply MulEquiv.ofBijective (galSupRestrictionProd K₁' K₂')
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨galSupRestrictionProd_injective K₁' K₂', ?_⟩
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    IsGalois.card_aut_eq_finrank]
  exact (IntermediateField.LinearDisjoint.of_inf_eq_bot h_inf).finrank_sup

end DisjointProduct

/-- Helper: if `K₁` and `K₂` are Galois intermediate fields of `AlgebraicClosure ℚ` with
`K₁ ⊓ K₂ = ⊥`, then `G₁ × G₂` is inverse Galois (where `Gᵢ ≅ Gal(Kᵢ/ℚ)`).

This generalizes `of_coprime_intermediate_fields` by not requiring coprime degrees. -/
theorem IsInverseGalois.of_disjoint_intermediate_fields
    (K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [hg₁ : IsGalois ℚ K₁] [hg₂ : IsGalois ℚ K₂]
    [FiniteDimensional ℚ K₁] [FiniteDimensional ℚ K₂]
    (h_inf : K₁ ⊓ K₂ = ⊥)
    {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (e₁ : Gal(K₁/ℚ) ≃* G₁) (e₂ : Gal(K₂/ℚ) ≃* G₂) :
    IsInverseGalois (G₁ × G₂) := by
  have : FiniteDimensional ℚ ↥(K₁ ⊔ K₂) := IntermediateField.finiteDimensional_sup K₁ K₂
  have : IsGalois ℚ ↥(K₁ ⊔ K₂) :=
    FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateFieldMax K₁ K₂
  refine ⟨↥(K₁ ⊔ K₂), inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (galSupProdEquiv' K₁ K₂ h_inf).trans (MulEquiv.prodCongr e₁ e₂)

end
