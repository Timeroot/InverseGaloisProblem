/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.PlaceInertia
import InverseGalois.Rigidity.RET.Genus.UnramifiedAbstract
import InverseGalois.Rigidity.RET.Genus.InftyChartRing

/-!
# Comparing the ramification of a cover in the two charts of the line

A cover of the line has an integral model over each of the two charts, and the ramification of the
cover is recorded twice, once in each model.  Over the overlap of the charts — the line with both
ends removed — the two records must agree, since a place of the cover lying over the overlap is
visible in both models and inertia is a property of the place.

The comparison is carried out here.  A place of the second model at which the coordinate is regular
contains the whole first model, because the first model is integral over the polynomials in the
coordinate; so it is the place of a prime of the first model, and the two primes have the same
inertia group.  Consequently a cover unramified over the whole affine line is automatically
unramified at every place of the second chart except possibly the one at the far end.

## Main results

* `Rigidity.RET.algebraMap_polynomial_mem` — a place containing the constants and the coordinate
  contains every polynomial in the coordinate.
* `Rigidity.RET.mem_placeSubring_of_notMem` — the coordinate is regular at a place of the second
  model at which its reciprocal does not vanish.
* `Rigidity.RET.exists_inertia_eq_chartOne` — such a place has the inertia group of a place of the
  first model.
* `Rigidity.RET.inertia_eq_one_of_chartOne` — a cover unramified over the whole affine line has no
  non-trivial inertia at any place of the second model away from the far end.
-/

open Polynomial IsDedekindDomain

noncomputable section


namespace Rigidity.RET

/-! ## The action on an integral model is the action on the field -/

section Model

open scoped Rigidity.RET

variable (A : Type*) {K F : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field F] [Algebra K F] [Algebra A F] [IsScalarTower A K F]
  [Algebra.IsAlgebraic K F]

omit [IsDedekindDomain A] in
/-- **The Galois action on an integral model is the restriction of the action on the field.** -/
theorem algebraMap_smul_integralClosure (σ : F ≃ₐ[K] F) (x : ↥(integralClosure A F)) :
    algebraMap ↥(integralClosure A F) F (σ • x) = σ • algebraMap ↥(integralClosure A F) F x :=
  algebraMap_galRestrict_apply A σ x

end Model

/-! ## A place containing the constants and the coordinate contains the first chart -/

section Coefficients

/-- **A place containing the constants and the coordinate contains every polynomial in the
coordinate**, the coefficients being read through the coordinate ring itself. -/
theorem algebraMap_polynomial_mem_of_C {k F : Type*} [Field k] [Field F] [Algebra k[X] F]
    (A : ValuationSubring F) (hc : ∀ c : k, algebraMap k[X] F (C c) ∈ A)
    (hX : algebraMap k[X] F X ∈ A) (p : k[X]) : algebraMap k[X] F p ∈ A := by
  induction p using Polynomial.induction_on with
  | C a => exact hc a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a ih => rw [pow_succ, ← mul_assoc, map_mul]; exact mul_mem ih hX

end Coefficients

section Charts

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra k[X] F]
  [Algebra (RatFunc k) F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F]

omit [Algebra k F] [IsScalarTower k k[X] F] in
/-- The coordinate of the first chart, read in the cover. -/
theorem algebraMap_X_eq : algebraMap k[X] F X = algebraMap (RatFunc k) F RatFunc.X := by
  rw [IsScalarTower.algebraMap_apply k[X] (RatFunc k) F, RatFunc.algebraMap_X]

/-- **A place containing the constants and the coordinate contains every polynomial in the
coordinate.** -/
theorem algebraMap_polynomial_mem (A : ValuationSubring F) (hc : ∀ c : k, algebraMap k F c ∈ A)
    (hX : algebraMap (RatFunc k) F RatFunc.X ∈ A) (p : k[X]) : algebraMap k[X] F p ∈ A := by
  refine algebraMap_polynomial_mem_of_C A (fun a => ?_) (by rw [algebraMap_X_eq]; exact hX) p
  rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  exact hc a

end Charts

/-! ## The two integral models of a cover of the line -/

section TwoModels

open scoped Rigidity.RET

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra k[X] F]
  [Algebra (RatFunc k) F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [IsGalois (RatFunc k) F]

instance : IsFractionRing ↥(integralClosure k[X] F) F :=
  IsIntegralClosure.isFractionRing_of_finite_extension k[X] (RatFunc k) F _

instance : IsDedekindDomain ↥(integralClosure k[X] F) :=
  integralClosure.isDedekindDomain k[X] (RatFunc k) F

set_option synthInstance.maxHeartbeats 200000 in
instance : IsFractionRing ↥(integralClosure ↥(inftyChart k) F) F :=
  IsIntegralClosure.isFractionRing_of_finite_extension ↥(inftyChart k) (RatFunc k) F _

instance : IsDedekindDomain ↥(integralClosure ↥(inftyChart k) F) :=
  integralClosure.isDedekindDomain ↥(inftyChart k) (RatFunc k) F

omit [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] in
/-- The constants are regular at every place of the second model. -/
theorem algebraMap_const_mem_placeSubring
    (v : HeightOneSpectrum ↥(integralClosure ↥(inftyChart k) F)) (c : k) :
    algebraMap k F c ∈ placeSubring F v := by
  have hmem : algebraMap k (RatFunc k) c ∈ inftyChart k := (inftyChart k).algebraMap_mem c
  have hb : IsIntegral ↥(inftyChart k) (algebraMap k F c) := by
    refine ⟨X - C ⟨algebraMap k (RatFunc k) c, hmem⟩, monic_X_sub_C _, ?_⟩
    rw [eval₂_sub, eval₂_X, eval₂_C]
    have : algebraMap ↥(inftyChart k) F ⟨algebraMap k (RatFunc k) c, hmem⟩ = algebraMap k F c := by
      rw [IsScalarTower.algebraMap_apply ↥(inftyChart k) (RatFunc k) F,
        IsScalarTower.algebraMap_apply k (RatFunc k) F]
      rfl
    rw [this, sub_self]
  refine mem_of_isIntegral_algebraMap (R := ↥(inftyChart k)) (fun r => ?_) hb
  have hr : algebraMap ↥(inftyChart k) F r
      = algebraMap ↥(integralClosure ↥(inftyChart k) F) F
        ⟨algebraMap ↥(inftyChart k) F r, isIntegral_algebraMap⟩ := rfl
  rw [hr]
  exact algebraMap_mem_placeSubring F v _

omit [Algebra k F] [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] in
/-- **The coordinate is regular at a place of the second model at which its reciprocal does not
vanish**: the reciprocal is then a unit of the place. -/
theorem mem_placeSubring_of_notMem (v : HeightOneSpectrum ↥(integralClosure ↥(inftyChart k) F))
    {y : ↥(integralClosure ↥(inftyChart k) F)}
    (hy : algebraMap ↥(integralClosure ↥(inftyChart k) F) F y
      = algebraMap (RatFunc k) F (RatFunc.X)⁻¹) (hv : y ∉ v.asIdeal) :
    algebraMap (RatFunc k) F RatFunc.X ∈ placeSubring F v := by
  set A := placeSubring F v with hA
  have hy0 : algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)⁻¹ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc k) F).injective).2 (inv_ne_zero RatFunc.X_ne_zero)
  have hyv : A.valuation (algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)⁻¹) = 1 := by
    rw [← hy]
    refine le_antisymm (A.valuation_le_one ⟨_, algebraMap_mem_placeSubring F v y⟩) ?_
    exact not_lt.mp fun hlt => hv ((valuation_lt_one_iff_mem (F := F) v y).mp hlt)
  have hinv : algebraMap (RatFunc k) F RatFunc.X
      = (algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)⁻¹)⁻¹ := by
    rw [map_inv₀, inv_inv]
  rw [hinv]
  refine A.mem_of_valuation_le_one _ (le_of_eq ?_)
  have hone : A.valuation (algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)⁻¹) *
      A.valuation (algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)⁻¹)⁻¹ = 1 := by
    rw [← Valuation.map_mul, mul_inv_cancel₀ hy0, Valuation.map_one]
  rwa [hyv, one_mul] at hone

/-- **A place of the second model at which the coordinate is regular is a place of the first
model**, and the two have the same inertia group. -/
theorem exists_inertia_eq_chartOne
    (v₂ : HeightOneSpectrum ↥(integralClosure ↥(inftyChart k) F))
    (hX : algebraMap (RatFunc k) F RatFunc.X ∈ placeSubring F v₂) :
    ∃ v₁ : HeightOneSpectrum ↥(integralClosure k[X] F),
      Ideal.inertia (F ≃ₐ[RatFunc k] F) v₁.asIdeal
        = Ideal.inertia (F ≃ₐ[RatFunc k] F) v₂.asIdeal := by
  refine exists_inertia_eq_of_mem_placeSubring (algebraMap_smul_integralClosure k[X])
    (algebraMap_smul_integralClosure ↥(inftyChart k)) v₂ fun b => ?_
  refine mem_of_isIntegral_algebraMap (R := k[X])
    (algebraMap_polynomial_mem _ (algebraMap_const_mem_placeSubring v₂) hX) ?_
  exact b.2

/-- **A cover unramified over the whole affine line has no non-trivial inertia at any place of the
second model away from the far end.** -/
theorem inertia_eq_one_of_chartOne
    (h₁ : ∀ Q : Ideal ↥(integralClosure k[X] F), Q.IsMaximal →
      ∀ σ : F ≃ₐ[RatFunc k] F, σ ∈ Ideal.inertia (F ≃ₐ[RatFunc k] F) Q → σ = 1)
    (v₂ : HeightOneSpectrum ↥(integralClosure ↥(inftyChart k) F))
    (hX : algebraMap (RatFunc k) F RatFunc.X ∈ placeSubring F v₂)
    (σ : F ≃ₐ[RatFunc k] F) (hσ : σ ∈ Ideal.inertia (F ≃ₐ[RatFunc k] F) v₂.asIdeal) : σ = 1 := by
  obtain ⟨v₁, hv⟩ := exists_inertia_eq_chartOne v₂ hX
  exact h₁ v₁.asIdeal (v₁.isPrime.isMaximal v₁.ne_bot) σ (hv ▸ hσ)

end TwoModels

end Rigidity.RET
