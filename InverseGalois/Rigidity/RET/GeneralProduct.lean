/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Core.Product
import InverseGalois.Rigidity.RET.Descent.ConstantDescent
import InverseGalois.Rigidity.RET.RegularProduct

/-!
# Regular inverse Galois groups are closed under products with no common quotient

`IsRegularInverseGalois.prod_of_coprime` realizes a direct product when the two factors have
coprime order.  Coprimality is far stronger than what the compositum argument needs, and it is
useless for the groups it would be most wanted for: `GL n 𝔽q` splits as `SL n 𝔽q × 𝔽qˣ`, and for
`n ≥ 2` the order of `𝔽qˣ` always divides the order of `SL n 𝔽q`.

The sharp hypothesis is **Goursat's**: a subgroup of `G₁ × G₂` projecting onto both factors is the
whole product as soon as `G₁` and `G₂` have no isomorphic nontrivial quotient (`NoCommonQuotient`).
That single hypothesis does both jobs the compositum needs.

*The Galois group is the product.*  Restriction `Gal(K₁K₂/F) → Gal(K₁/F) × Gal(K₂/F)` is injective,
and each component is surjective because each `Kᵢ/F` is normal.  Goursat turns the image into
everything.

*The compositum is regular.*  This is the delicate half — `ℚ(T)(√T)` and `ℚ(T)(√(-T))` are regular
and their compositum is not, because it contains `√(-1)`.  Write `c` for the constants of the
compositum `E`.  Restriction to the constants is a homomorphism `ρ : Gal(E/F) → Gal(c/ℚ)`, and the
subgroup `Gal(E/K₁)` already surjects onto `Gal(c/ℚ)`: its fixed field inside `c` is `c ∩ K₁`,
which is `ℚ` precisely because `K₁` is regular.  So `ker ρ` projects onto `Gal(K₁/F)`, and likewise
onto `Gal(K₂/F)`; Goursat makes `ker ρ` everything, `Gal(c/ℚ)` trivial, and `c = ℚ`.

The counterexample is exactly what the hypothesis excludes: the two quadratic fields there have the
common quotient `C₂`.

## Main definitions

* `Rigidity.RET.NoCommonQuotient` — no group is a nontrivial quotient of both factors.

## Main results

* `Rigidity.RET.NoCommonQuotient.eq_top` — Goursat: a subgroup projecting onto both factors of a
  product of two groups with no common quotient is the whole product.
* `Rigidity.RET.noCommonQuotient_of_commutator_eq_top` — a perfect group and a commutative group
  have no common quotient.
* `Rigidity.RET.galSupRestrictionProd_bijective` — the compositum realizes the direct product.
* `Rigidity.RET.algebraicClosure_sup_eq_bot_of_noCommonQuotient` — the compositum is regular.
* `IsRegularInverseGalois.prod_of_noCommonQuotient` — the direct product of two regular inverse
  Galois groups with no common quotient is a regular inverse Galois group.
* `IsRegularInverseGalois.prod_of_perfect` — the special case that reaches `GL n 𝔽q`: a perfect
  group times an abelian one.
-/

open Polynomial Module

open scoped IntermediateField

noncomputable section

namespace Rigidity.RET

/-! ## Groups with no common quotient -/

/-- Two groups **have no common quotient** when a group that is a quotient of both of them is
trivial.  Coprime orders are one way for this to happen, and a perfect group paired with a
commutative one is another. -/
def NoCommonQuotient (G₁ : Type*) (G₂ : Type*) [Group G₁] [Group G₂] : Prop :=
  ∀ (N₁ : Subgroup G₁) (N₂ : Subgroup G₂) (_ : N₁.Normal) (_ : N₂.Normal),
    Nonempty ((G₁ ⧸ N₁) ≃* (G₂ ⧸ N₂)) → N₁ = ⊤

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

/-- **A perfect group and a commutative group have no common quotient.**  A common quotient is
perfect, being a quotient of a perfect group, and commutative, being a quotient of a commutative
one; a perfect commutative group is trivial. -/
theorem noCommonQuotient_of_commutator_eq_top (h₁ : commutator G₁ = ⊤)
    (h₂ : ∀ a b : G₂, a * b = b * a) : NoCommonQuotient G₁ G₂ := by
  intro N₁ N₂ hN₁ hN₂ ⟨e⟩
  -- the quotient of `G₂` is commutative, hence so is the quotient of `G₁`
  have hcomm₂ : ∀ a b : G₂ ⧸ N₂, a * b = b * a := by
    refine Quotient.ind₂ fun a b => ?_
    exact congrArg (QuotientGroup.mk (s := N₂)) (h₂ a b)
  have hcomm₁ : ∀ a b : G₁ ⧸ N₁, a * b = b * a := fun a b =>
    e.injective (by rw [map_mul, map_mul, hcomm₂])
  -- a commutative quotient swallows the commutator subgroup
  have hle : commutator G₁ ≤ N₁ := by
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [← QuotientGroup.eq_one_iff]
    show QuotientGroup.mk' N₁ ⁅a, b⁆ = 1
    rw [commutatorElement_def]
    simp only [map_mul, map_inv]
    rw [hcomm₁ (QuotientGroup.mk' N₁ a) (QuotientGroup.mk' N₁ b)]
    group
  rw [← top_le_iff, ← h₁]
  exact hle

/-- **Goursat's lemma for groups with no common quotient.**  A subgroup of `G₁ × G₂` projecting
onto each factor is the whole product: Goursat produces an isomorphism between a quotient of `G₁`
and a quotient of `G₂`, which the hypothesis makes trivial, so both Goursat subgroups are
everything and their product — which the subgroup contains — is everything. -/
theorem NoCommonQuotient.eq_top (hnc : NoCommonQuotient G₁ G₂) {I : Subgroup (G₁ × G₂)}
    (h₁ : Function.Surjective (Prod.fst ∘ I.subtype))
    (h₂ : Function.Surjective (Prod.snd ∘ I.subtype)) :
    I = ⊤ := by
  haveI hn₁ := Subgroup.normal_goursatFst h₁
  haveI hn₂ := Subgroup.normal_goursatSnd h₂
  obtain ⟨e, -⟩ := Subgroup.goursat_surjective h₁ h₂
  have hfst : I.goursatFst = ⊤ := hnc _ _ hn₁ hn₂ ⟨e⟩
  haveI : Subsingleton (G₁ ⧸ I.goursatFst) := by
    rw [hfst]; exact QuotientGroup.subsingleton_quotient_top
  haveI : Subsingleton (G₂ ⧸ I.goursatSnd) := e.symm.injective.subsingleton
  have hsnd : I.goursatSnd = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun g => (QuotientGroup.eq_one_iff g).1 (Subsingleton.elim _ _)
  have hle := Subgroup.goursatFst_prod_goursatSnd_le I
  rw [hfst, hsnd, Subgroup.top_prod_top] at hle
  exact top_le_iff.1 hle

/-- The projections of a subgroup of a product, phrased for `NoCommonQuotient.eq_top`. -/
theorem surjective_fst_comp_subtype {I : Subgroup (G₁ × G₂)} (h : ∀ g : G₁, ∃ y, (g, y) ∈ I) :
    Function.Surjective (Prod.fst ∘ I.subtype) := fun g =>
  (h g).elim fun y hy => ⟨⟨(g, y), hy⟩, rfl⟩

/-- The projections of a subgroup of a product, phrased for `NoCommonQuotient.eq_top`. -/
theorem surjective_snd_comp_subtype {I : Subgroup (G₁ × G₂)} (h : ∀ g : G₂, ∃ x, (x, g) ∈ I) :
    Function.Surjective (Prod.snd ∘ I.subtype) := fun g =>
  (h g).elim fun x hx => ⟨⟨(x, g), hx⟩, rfl⟩

end Rigidity.RET

/-! ## The Galois group of the compositum -/

namespace Rigidity.RET

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- **The compositum of two Galois subextensions with no common quotient realizes the direct
product of their groups.**  Restriction to the two factors is injective, and each component is
surjective by normality; Goursat closes the gap. -/
theorem galSupRestrictionProd_bijective (K₁ K₂ : IntermediateField F Ω)
    [Normal F ↥K₁] [Normal F ↥K₂] [Normal F ↥(K₁ ⊔ K₂)] [FiniteDimensional F ↥(K₁ ⊔ K₂)]
    (hnc : NoCommonQuotient (↥K₁ ≃ₐ[F] ↥K₁) (↥K₂ ≃ₐ[F] ↥K₂)) :
    Function.Bijective (galSupRestrictionProd K₁ K₂) := by
  refine ⟨galSupRestrictionProd_injective K₁ K₂, ?_⟩
  rw [← MonoidHom.range_eq_top]
  refine hnc.eq_top (surjective_fst_comp_subtype ?_) (surjective_snd_comp_subtype ?_)
  · intro g
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (E := ↥(K₁ ⊔ K₂)) (K₁ := ↥K₁) g
    exact ⟨_, σ, by rw [← hσ]; rfl⟩
  · intro g
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (E := ↥(K₁ ⊔ K₂)) (K₁ := ↥K₂) g
    exact ⟨_, σ, by rw [← hσ]; rfl⟩

/-- The isomorphism `Gal(K₁K₂/F) ≃* Gal(K₁/F) × Gal(K₂/F)` supplied by
`galSupRestrictionProd_bijective`. -/
def galSupProdEquivOfNoCommonQuotient (K₁ K₂ : IntermediateField F Ω)
    [Normal F ↥K₁] [Normal F ↥K₂] [Normal F ↥(K₁ ⊔ K₂)] [FiniteDimensional F ↥(K₁ ⊔ K₂)]
    (hnc : NoCommonQuotient (↥K₁ ≃ₐ[F] ↥K₁) (↥K₂ ≃ₐ[F] ↥K₂)) :
    Gal(↥(K₁ ⊔ K₂)/F) ≃* Gal(↥K₁/F) × Gal(↥K₂/F) :=
  MulEquiv.ofBijective _ (galSupRestrictionProd_bijective K₁ K₂ hnc)

@[simp]
theorem galSupProdEquivOfNoCommonQuotient_apply (K₁ K₂ : IntermediateField F Ω)
    [Normal F ↥K₁] [Normal F ↥K₂] [Normal F ↥(K₁ ⊔ K₂)] [FiniteDimensional F ↥(K₁ ⊔ K₂)]
    (hnc : NoCommonQuotient (↥K₁ ≃ₐ[F] ↥K₁) (↥K₂ ≃ₐ[F] ↥K₂)) (σ : Gal(↥(K₁ ⊔ K₂)/F)) :
    galSupProdEquivOfNoCommonQuotient K₁ K₂ hnc σ = galSupRestrictionProd K₁ K₂ σ :=
  rfl

end Rigidity.RET

/-! ## Regularity of the compositum

The obstruction to regularity is a constant of the compositum that is *not* rational.  Restriction
to the constants `ρ : Gal(Ω/ℚ(T)) → Gal(k_Ω/ℚ)` measures exactly that, and the point is that each
regular factor already accounts for all of `Gal(k_Ω/ℚ)`. -/

namespace Rigidity.RET.Descent

variable (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω] [FiniteDimensional (RatFunc ℚ) Ω]
  [IsGalois (RatFunc ℚ) Ω] [CharZero Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω]

/-- **A regular intermediate field accounts for every automorphism of the constants.**

The automorphisms of `Ω` fixing a regular intermediate field `A` pointwise restrict to a subgroup
of `Gal(k_Ω/ℚ)` whose fixed field is `k_Ω ∩ A`; regularity of `A` makes that `ℚ`, so the subgroup
is everything. -/
theorem range_constRestrict_comp_fixingSubgroup (A : IntermediateField (RatFunc ℚ) Ω)
    (hA : algebraicClosure ℚ ↥A = ⊥) :
    ((constRestrict Ω).comp A.fixingSubgroup.subtype).range = ⊤ := by
  set Γ := ((constRestrict Ω).comp A.fixingSubgroup.subtype).range with hΓ
  have hfix : IntermediateField.fixedField Γ = ⊥ := by
    refine le_antisymm (fun y hy => ?_) bot_le
    -- the underlying element of `Ω` is fixed by everything fixing `A`, hence lies in `A`
    have hyA : (y : Ω) ∈ A := by
      have hmem : (y : Ω) ∈ IntermediateField.fixedField A.fixingSubgroup := by
        rw [IntermediateField.mem_fixedField_iff]
        intro σ hσ
        have hΓmem : (constRestrict Ω) σ ∈ Γ := ⟨⟨σ, hσ⟩, rfl⟩
        have hyfix := (IntermediateField.mem_fixedField_iff _ _).1 hy _ hΓmem
        have h2 := constRestrict_apply Ω σ y
        rw [hyfix] at h2
        exact h2.symm
      rwa [IsGalois.fixedField_fixingSubgroup] at hmem
    -- and it is algebraic over `ℚ`, so regularity of `A` makes it rational
    have hint : IsIntegral ℚ ((⟨(y : Ω), hyA⟩ : ↥A)) := by
      refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℚ ↥A Ω) ?_).1 ?_
      · exact (algebraMap ↥A Ω).injective
      · exact mem_algebraicClosure_iff'.1 y.2
    have hbot : (⟨(y : Ω), hyA⟩ : ↥A) ∈ (⊥ : IntermediateField ℚ ↥A) :=
      hA ▸ mem_algebraicClosure_iff'.2 hint
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.1 hbot
    refine IntermediateField.mem_bot.2 ⟨r, ?_⟩
    refine Subtype.ext ?_
    have : (algebraMap ℚ ↥A r : Ω) = (y : Ω) := congrArg Subtype.val hr
    rw [← this]
    exact (IsScalarTower.algebraMap_apply ℚ ↥A Ω r).symm
  rw [← IntermediateField.fixingSubgroup_fixedField Γ, hfix, IntermediateField.fixingSubgroup_bot]

end Rigidity.RET.Descent

namespace Rigidity.RET

open Rigidity.RET.Descent

variable (K₁ K₂ : IntermediateField (RatFunc ℚ) (AlgebraicClosure (RatFunc ℚ)))

/-- The copy of `K₁` inside the compositum. -/
def supLeftImage : IntermediateField (RatFunc ℚ) ↥(K₁ ⊔ K₂) :=
  (IsScalarTower.toAlgHom (RatFunc ℚ) ↥K₁ ↥(K₁ ⊔ K₂)).fieldRange

/-- The copy of `K₂` inside the compositum. -/
def supRightImage : IntermediateField (RatFunc ℚ) ↥(K₁ ⊔ K₂) :=
  (IsScalarTower.toAlgHom (RatFunc ℚ) ↥K₂ ↥(K₁ ⊔ K₂)).fieldRange

/-- `K₁` is isomorphic to its copy inside the compositum. -/
def supLeftImageEquiv : ↥K₁ ≃ₐ[RatFunc ℚ] ↥(supLeftImage K₁ K₂) :=
  AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom (RatFunc ℚ) ↥K₁ ↥(K₁ ⊔ K₂))

/-- `K₂` is isomorphic to its copy inside the compositum. -/
def supRightImageEquiv : ↥K₂ ≃ₐ[RatFunc ℚ] ↥(supRightImage K₁ K₂) :=
  AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom (RatFunc ℚ) ↥K₂ ↥(K₁ ⊔ K₂))

/-- An automorphism of the compositum fixing the copy of `K₁` pointwise restricts to the identity
on `K₁`. -/
theorem restrictNormal_eq_one_of_mem_fixingSubgroup [Normal (RatFunc ℚ) ↥K₁]
    [Normal (RatFunc ℚ) ↥K₂] {τ : Gal(↥(K₁ ⊔ K₂)/RatFunc ℚ)}
    (hτ : τ ∈ (supLeftImage K₁ K₂).fixingSubgroup) :
    (galSupRestrictionProd K₁ K₂ τ).1 = 1 := by
  refine AlgEquiv.ext fun x => ?_
  refine (algebraMap ↥K₁ ↥(K₁ ⊔ K₂)).injective ?_
  show algebraMap ↥K₁ ↥(K₁ ⊔ K₂) (τ.restrictNormal ↥K₁ x) = _
  rw [AlgEquiv.restrictNormal_commutes]
  exact (IntermediateField.mem_fixingSubgroup_iff _ τ).1 hτ _ ⟨x, rfl⟩

/-- An automorphism of the compositum fixing the copy of `K₂` pointwise restricts to the identity
on `K₂`. -/
theorem restrictNormal_eq_one_of_mem_fixingSubgroup' [Normal (RatFunc ℚ) ↥K₁]
    [Normal (RatFunc ℚ) ↥K₂] {τ : Gal(↥(K₁ ⊔ K₂)/RatFunc ℚ)}
    (hτ : τ ∈ (supRightImage K₁ K₂).fixingSubgroup) :
    (galSupRestrictionProd K₁ K₂ τ).2 = 1 := by
  refine AlgEquiv.ext fun x => ?_
  refine (algebraMap ↥K₂ ↥(K₁ ⊔ K₂)).injective ?_
  show algebraMap ↥K₂ ↥(K₁ ⊔ K₂) (τ.restrictNormal ↥K₂ x) = _
  rw [AlgEquiv.restrictNormal_commutes]
  exact (IntermediateField.mem_fixingSubgroup_iff _ τ).1 hτ _ ⟨x, rfl⟩

end Rigidity.RET

namespace Rigidity.RET.Descent

variable (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω] [FiniteDimensional (RatFunc ℚ) Ω]
  [IsGalois (RatFunc ℚ) Ω] [CharZero Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω]

/-- **Every automorphism agrees on the constants with one fixing a prescribed regular subfield.**
This is `range_constRestrict_comp_fixingSubgroup` read as a surjectivity statement. -/
theorem exists_mem_fixingSubgroup_constRestrict_eq (A : IntermediateField (RatFunc ℚ) Ω)
    (hA : algebraicClosure ℚ ↥A = ⊥) (σ : Gal(Ω/RatFunc ℚ)) :
    ∃ τ ∈ A.fixingSubgroup, constRestrict Ω τ = constRestrict Ω σ := by
  have hmem : constRestrict Ω σ ∈ ((constRestrict Ω).comp A.fixingSubgroup.subtype).range := by
    rw [range_constRestrict_comp_fixingSubgroup Ω A hA]
    trivial
  obtain ⟨⟨τ, hτ⟩, hτeq⟩ := hmem
  exact ⟨τ, hτ, hτeq⟩

/-- The same statement in the form used by the Goursat argument: every automorphism differs from
one fixing a regular subfield by something acting trivially on the constants. -/
theorem exists_mem_fixingSubgroup_mul_inv_mem_ker (A : IntermediateField (RatFunc ℚ) Ω)
    (hA : algebraicClosure ℚ ↥A = ⊥) (σ : Gal(Ω/RatFunc ℚ)) :
    ∃ τ ∈ A.fixingSubgroup, σ * τ⁻¹ ∈ (constRestrict Ω).ker := by
  obtain ⟨τ, hτ, h⟩ := exists_mem_fixingSubgroup_constRestrict_eq Ω A hA σ
  exact ⟨τ, hτ, by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]⟩

/-- **If restriction to the constants is trivial on a Galois extension containing a regular
subfield, the extension itself is regular.**  The subfield makes restriction surjective, and the
hypothesis makes it trivial, so `Gal(k_Ω/ℚ)` is trivial and `k_Ω = ℚ`. -/
theorem algebraicClosure_eq_bot_of_ker_constRestrict_eq_top
    (A : IntermediateField (RatFunc ℚ) Ω) (hA : algebraicClosure ℚ ↥A = ⊥)
    (h : (constRestrict Ω).ker = ⊤) :
    algebraicClosure ℚ Ω = ⊥ := by
  have htriv : ∀ a : ↥(algebraicClosure ℚ Ω) ≃ₐ[ℚ] ↥(algebraicClosure ℚ Ω), a = 1 := by
    intro a
    have ha : a ∈ ((constRestrict Ω).comp A.fixingSubgroup.subtype).range := by
      rw [range_constRestrict_comp_fixingSubgroup Ω A hA]
      trivial
    obtain ⟨⟨τ, hτmem⟩, hτ⟩ := ha
    rw [← show constRestrict Ω τ = a from hτ]
    exact MonoidHom.mem_ker.1 (by rw [h]; trivial)
  haveI : Subsingleton (↥(algebraicClosure ℚ Ω) ≃ₐ[ℚ] ↥(algebraicClosure ℚ Ω)) :=
    ⟨fun a b => by rw [htriv a, htriv b]⟩
  refine IntermediateField.finrank_eq_one_iff.1 ?_
  rw [← IsGalois.card_aut_eq_finrank ℚ ↥(algebraicClosure ℚ Ω)]
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩

end Rigidity.RET.Descent

namespace Rigidity.RET

open Rigidity.RET.Descent

variable (K₁ K₂ : IntermediateField (RatFunc ℚ) (AlgebraicClosure (RatFunc ℚ)))

set_option maxHeartbeats 1000000 in
/-- **The compositum of two regular Galois subextensions with no common quotient is regular.**

Restriction to the constants `ρ : Gal(E/ℚ(T)) → Gal(k_E/ℚ)` already sends the subgroup fixing
either factor onto all of `Gal(k_E/ℚ)`, because that factor is regular.  So `ker ρ` projects onto
both `Gal(K₁/ℚ(T))` and `Gal(K₂/ℚ(T))`; having no common quotient, Goursat's lemma forces `ker ρ`
to be everything, `Gal(k_E/ℚ)` to be trivial, and the constants to be rational. -/
theorem algebraicClosure_sup_eq_bot_of_noCommonQuotient
    [IsGalois (RatFunc ℚ) ↥K₁] [IsGalois (RatFunc ℚ) ↥K₂]
    (hreg₁ : algebraicClosure ℚ ↥K₁ = ⊥) (hreg₂ : algebraicClosure ℚ ↥K₂ = ⊥)
    (hnc : NoCommonQuotient (↥K₁ ≃ₐ[RatFunc ℚ] ↥K₁) (↥K₂ ≃ₐ[RatFunc ℚ] ↥K₂))
    [FiniteDimensional (RatFunc ℚ) ↥(K₁ ⊔ K₂)] :
    algebraicClosure ℚ ↥(K₁ ⊔ K₂) = ⊥ := by
  haveI : IsGalois (RatFunc ℚ) ↥(K₁ ⊔ K₂) :=
    FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateFieldMax K₁ K₂
  haveI : CharZero ↥(K₁ ⊔ K₂) := charZero_of_ratFunc _
  haveI : IsScalarTower ℚ (RatFunc ℚ) ↥(K₁ ⊔ K₂) := isScalarTower_rat_ratFunc _
  -- the two copies inside the compositum are again regular
  have hA₁ : algebraicClosure ℚ ↥(supLeftImage K₁ K₂) = ⊥ :=
    algebraicClosure_eq_bot_of_ringHom (supLeftImageEquiv K₁ K₂).symm.toRingHom hreg₁
  have hA₂ : algebraicClosure ℚ ↥(supRightImage K₁ K₂) = ⊥ :=
    algebraicClosure_eq_bot_of_ringHom (supRightImageEquiv K₁ K₂).symm.toRingHom hreg₂
  refine Descent.algebraicClosure_eq_bot_of_ker_constRestrict_eq_top ↥(K₁ ⊔ K₂)
    (supLeftImage K₁ K₂) hA₁ ?_
  -- `ker ρ` projects onto both factors, so Goursat's lemma makes it everything
  have hD : ((constRestrict ↥(K₁ ⊔ K₂)).ker).map (galSupRestrictionProd K₁ K₂) = ⊤ := by
    refine hnc.eq_top (surjective_fst_comp_subtype ?_) (surjective_snd_comp_subtype ?_)
    · intro g
      obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (E := ↥(K₁ ⊔ K₂)) (K₁ := ↥K₁) g
      obtain ⟨τ, hτ, hd⟩ := Descent.exists_mem_fixingSubgroup_mul_inv_mem_ker ↥(K₁ ⊔ K₂)
        (supLeftImage K₁ K₂) hA₁ σ
      have h1 : (galSupRestrictionProd K₁ K₂ τ).1 = 1 :=
        restrictNormal_eq_one_of_mem_fixingSubgroup K₁ K₂ hτ
      have hfst : (galSupRestrictionProd K₁ K₂ (σ * τ⁻¹)).1 = g := by
        rw [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, h1, inv_one, mul_one, ← hσ]
        rfl
      exact ⟨_, σ * τ⁻¹, hd, Prod.ext hfst rfl⟩
    · intro g
      obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (E := ↥(K₁ ⊔ K₂)) (K₁ := ↥K₂) g
      obtain ⟨τ, hτ, hd⟩ := Descent.exists_mem_fixingSubgroup_mul_inv_mem_ker ↥(K₁ ⊔ K₂)
        (supRightImage K₁ K₂) hA₂ σ
      have h1 : (galSupRestrictionProd K₁ K₂ τ).2 = 1 :=
        restrictNormal_eq_one_of_mem_fixingSubgroup' K₁ K₂ hτ
      have hsnd : (galSupRestrictionProd K₁ K₂ (σ * τ⁻¹)).2 = g := by
        rw [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, h1, inv_one, mul_one, ← hσ]
        rfl
      exact ⟨_, σ * τ⁻¹, hd, Prod.ext rfl hsnd⟩
  refine (Subgroup.eq_top_iff' _).2 fun σ => ?_
  have hmem : galSupRestrictionProd K₁ K₂ σ ∈
      ((constRestrict ↥(K₁ ⊔ K₂)).ker).map (galSupRestrictionProd K₁ K₂) := by
    rw [hD]; trivial
  obtain ⟨d, hd, hdeq⟩ := hmem
  rwa [← galSupRestrictionProd_injective K₁ K₂ hdeq]

end Rigidity.RET

namespace Rigidity.RET

/-- Having no common quotient only depends on the isomorphism types of the two groups. -/
theorem NoCommonQuotient.congr {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (h : NoCommonQuotient G₁ G₂) (e₁ : H₁ ≃* G₁) (e₂ : H₂ ≃* G₂) : NoCommonQuotient H₁ H₂ := by
  intro N₁ N₂ hN₁ hN₂ ⟨f⟩
  haveI : (N₁.map (e₁ : H₁ →* G₁)).Normal := hN₁.map _ e₁.surjective
  haveI : (N₂.map (e₂ : H₂ →* G₂)).Normal := hN₂.map _ e₂.surjective
  have key : N₁.map (e₁ : H₁ →* G₁) = ⊤ :=
    h _ _ inferInstance inferInstance
      ⟨((QuotientGroup.congr N₁ (N₁.map (e₁ : H₁ →* G₁)) e₁ rfl).symm.trans f).trans
        (QuotientGroup.congr N₂ (N₂.map (e₂ : H₂ →* G₂)) e₂ rfl)⟩
  have hcomap := congrArg (Subgroup.comap (e₁ : H₁ →* G₁)) key
  rwa [Subgroup.comap_map_eq_self_of_injective e₁.injective, Subgroup.comap_top] at hcomap

/-- **The compositum of two regular Galois subextensions of `ℚ̄(T) / ℚ(T)` whose groups have no
common quotient realizes the direct product of those groups, regularly.** -/
theorem isRegularInverseGalois_of_noCommonQuotient_intermediate_fields
    (K₁ K₂ : IntermediateField (RatFunc ℚ) (AlgebraicClosure (RatFunc ℚ)))
    [IsGalois (RatFunc ℚ) ↥K₁] [IsGalois (RatFunc ℚ) ↥K₂]
    [FiniteDimensional (RatFunc ℚ) ↥K₁] [FiniteDimensional (RatFunc ℚ) ↥K₂]
    (hreg₁ : algebraicClosure ℚ ↥K₁ = ⊥) (hreg₂ : algebraicClosure ℚ ↥K₂ = ⊥)
    {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (e₁ : (↥K₁ ≃ₐ[RatFunc ℚ] ↥K₁) ≃* G₁) (e₂ : (↥K₂ ≃ₐ[RatFunc ℚ] ↥K₂) ≃* G₂)
    (hnc : NoCommonQuotient G₁ G₂) :
    IsRegularInverseGalois (G₁ × G₂) := by
  haveI : FiniteDimensional (RatFunc ℚ) ↥(K₁ ⊔ K₂) :=
    IntermediateField.finiteDimensional_sup K₁ K₂
  haveI : IsGalois (RatFunc ℚ) ↥(K₁ ⊔ K₂) :=
    FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateFieldMax K₁ K₂
  exact ⟨↥(K₁ ⊔ K₂), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    isScalarTower_rat_ratFunc _,
    algebraicClosure_sup_eq_bot_of_noCommonQuotient K₁ K₂ hreg₁ hreg₂ (hnc.congr e₁ e₂),
    ⟨(galSupProdEquivOfNoCommonQuotient K₁ K₂ (hnc.congr e₁ e₂)).trans
      (MulEquiv.prodCongr e₁ e₂)⟩⟩

end Rigidity.RET

/-- **The direct product of two regular inverse Galois groups with no common quotient is a regular
inverse Galois group.**  Embed the two realizing extensions into an algebraic closure of `ℚ(T)`
and take their compositum.  Goursat's lemma identifies its Galois group with the product, and the
same lemma applied to the kernel of restriction-to-the-constants shows the compositum is again
regular. -/
theorem IsRegularInverseGalois.prod_of_noCommonQuotient {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (h₁ : IsRegularInverseGalois G₁) (h₂ : IsRegularInverseGalois G₂)
    (hnc : Rigidity.RET.NoCommonQuotient G₁ G₂) :
    IsRegularInverseGalois (G₁ × G₂) := by
  obtain ⟨L₁, _, _, _, _, _, _, hreg₁, ⟨φ₁⟩⟩ := h₁
  obtain ⟨L₂, _, _, _, _, _, _, hreg₂, ⟨φ₂⟩⟩ := h₂
  haveI : Algebra.IsAlgebraic (RatFunc ℚ) L₁ := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (RatFunc ℚ) L₂ := Algebra.IsAlgebraic.of_finite _ _
  let i₁ : L₁ →ₐ[RatFunc ℚ] AlgebraicClosure (RatFunc ℚ) := IsAlgClosed.lift
  let i₂ : L₂ →ₐ[RatFunc ℚ] AlgebraicClosure (RatFunc ℚ) := IsAlgClosed.lift
  let ψ₁ := AlgEquiv.ofInjectiveField i₁
  let ψ₂ := AlgEquiv.ofInjectiveField i₂
  haveI : IsGalois (RatFunc ℚ) ↥i₁.fieldRange := IsGalois.of_algEquiv ψ₁
  haveI : IsGalois (RatFunc ℚ) ↥i₂.fieldRange := IsGalois.of_algEquiv ψ₂
  haveI : FiniteDimensional (RatFunc ℚ) ↥i₁.fieldRange :=
    FiniteDimensional.of_injective ψ₁.symm.toLinearMap ψ₁.symm.injective
  haveI : FiniteDimensional (RatFunc ℚ) ↥i₂.fieldRange :=
    FiniteDimensional.of_injective ψ₂.symm.toLinearMap ψ₂.symm.injective
  have hregK₁ : algebraicClosure ℚ ↥i₁.fieldRange = ⊥ :=
    Rigidity.RET.algebraicClosure_eq_bot_of_ringHom ψ₁.symm.toRingHom hreg₁
  have hregK₂ : algebraicClosure ℚ ↥i₂.fieldRange = ⊥ :=
    Rigidity.RET.algebraicClosure_eq_bot_of_ringHom ψ₂.symm.toRingHom hreg₂
  exact Rigidity.RET.isRegularInverseGalois_of_noCommonQuotient_intermediate_fields
    i₁.fieldRange i₂.fieldRange hregK₁ hregK₂
    (ψ₁.autCongr.symm.trans φ₁) (ψ₂.autCongr.symm.trans φ₂) hnc

/-- **A perfect group times an abelian group.**  A perfect group has no nontrivial abelian
quotient, so the two groups share no quotient and the compositum stays regular. -/
theorem IsRegularInverseGalois.prod_of_perfect {G₁ G₂ : Type*} [Group G₁] [CommGroup G₂]
    (h₁ : IsRegularInverseGalois G₁) (h₂ : IsRegularInverseGalois G₂)
    (hp : commutator G₁ = ⊤) :
    IsRegularInverseGalois (G₁ × G₂) :=
  h₁.prod_of_noCommonQuotient h₂
    (Rigidity.RET.noCommonQuotient_of_commutator_eq_top hp mul_comm)
