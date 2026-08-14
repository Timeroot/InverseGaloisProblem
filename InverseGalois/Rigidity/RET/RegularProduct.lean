/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Core.Product
import InverseGalois.Rigidity.RET.GeometricIrreducibility
import InverseGalois.Rigidity.RET.RegularBase
import InverseGalois.Rigidity.RET.RegularResolvent

/-!
# Regular inverse Galois groups are closed under coprime direct products

Over `ℚ` the compositum of two Galois extensions of coprime degree realizes the direct product of
their groups, and that is how `IsInverseGalois.prod_of_coprime` is proved.  Over `ℚ(T)` the group
theory is identical — the same compositum, the same restriction pair, the same counting argument —
but there is a second thing to check: the compositum must again be **regular**.

That is not automatic.  The two extensions `ℚ(T)(√T)` and `ℚ(T)(√(-T))` are regular and meet only
in `ℚ(T)`, yet their compositum contains the quotient of the two radicals, a square root of `-1`:
a compositum of regular extensions can acquire constants.  Coprimality is what rules this out, and
it does so through the degree of a constant.

A constant `x` of the compositum is algebraic over `ℚ`, and its minimal polynomial over `ℚ` stays
irreducible over each of the two factors, because a factorization would have coefficients algebraic
over `ℚ` — hence, by regularity of the factor, rational.  So the degree of `x` over `ℚ` is its
degree over `K₁`, which divides `[E : K₁] = [K₂ : ℚ(T)]`, and equally its degree over `K₂`, which
divides `[K₁ : ℚ(T)]`.  Coprime degrees leave only degree one: `x` is rational.

## Main results

* `Rigidity.RET.natDegree_minpoly_dvd_finrank` — over a regular base the degree of an algebraic
  element does not drop, so it divides the degree of any finite extension containing it.
* `Rigidity.RET.algebraicClosure_sup_eq_bot` — the compositum of two regular subextensions of
  coprime degree is regular.
* `Rigidity.RET.isRegularInverseGalois_of_coprime_intermediate_fields` — the compositum realizes
  the direct product regularly.
* `IsRegularInverseGalois.prod_of_coprime` — the direct product of two regular inverse Galois
  groups of coprime order is a regular inverse Galois group.
-/

open Polynomial Module

open scoped IntermediateField

noncomputable section

namespace Rigidity.RET

/-! ## The rational structure of a tower -/

/-- **A tower of characteristic-zero fields is a tower over the rationals.**  Both actions of a
rational number are multiplication by its image in the field at hand, and a ring homomorphism
preserves rational numbers. -/
theorem isScalarTower_rat (R E : Type*) [Field R] [Field E] [Algebra R E]
    [CharZero R] [CharZero E] : IsScalarTower ℚ R E := by
  refine ⟨fun x y z => ?_⟩
  rw [Rat.smul_def, Algebra.smul_def, map_mul, map_ratCast, Algebra.smul_def y z, Rat.smul_def,
    mul_assoc]

/-! ## The degree of a constant over a regular base -/

/-- **Over a regular base the degree of an algebraic element does not drop.**

If `ℚ` is relatively algebraically closed in `R`, then the `ℚ`-minimal polynomial of an element
`x` algebraic over `ℚ` stays irreducible over `R`, so it *is* the `R`-minimal polynomial of `x`.
The subfield it generates has that degree over `R`, and the degree of a subfield divides the
degree of the whole extension. -/
theorem natDegree_minpoly_dvd_finrank {R E : Type*} [Field R] [Field E] [Algebra R E]
    [FiniteDimensional R E] [CharZero R] [CharZero E]
    (hreg : algebraicClosure ℚ R = ⊥) {x : E} (hx : IsIntegral ℚ x) :
    (minpoly ℚ x).natDegree ∣ finrank R E := by
  haveI : IsScalarTower ℚ R E := isScalarTower_rat R E
  have hmonic : (minpoly ℚ x).Monic := minpoly.monic hx
  have hirrmap : Irreducible ((minpoly ℚ x).map (algebraMap ℚ R)) :=
    irreducible_map_of_algClosure_eq_bot hreg hmonic (minpoly.irreducible hx)
  have hroot : (aeval x) ((minpoly ℚ x).map (algebraMap ℚ R)) = 0 := by
    rw [aeval_map_algebraMap]
    exact minpoly.aeval ℚ x
  have hmin : minpoly R x = (minpoly ℚ x).map (algebraMap ℚ R) :=
    (minpoly.eq_of_irreducible_of_monic hirrmap hroot (hmonic.map _)).symm
  have hfr : finrank R ↥R⟮x⟯ = (minpoly ℚ x).natDegree := by
    rw [IntermediateField.adjoin.finrank hx.tower_top, hmin, hmonic.natDegree_map]
  exact ⟨finrank ↥R⟮x⟯ E, by rw [← hfr]; exact (Module.finrank_mul_finrank R ↥R⟮x⟯ E).symm⟩

/-! ## Regularity of a coprime compositum -/

/-- **The compositum of two regular subextensions of coprime degree is regular.**

A constant of the compositum has the same degree over `ℚ` as over either factor, because the
factors are regular; those degrees divide the two steps `[E : K₁]` and `[E : K₂]` of the tower,
which coprimality identifies with the degrees of the *other* factor.  So the degree of the
constant divides two coprime numbers, and is one. -/
theorem algebraicClosure_sup_eq_bot {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [CharZero Ω]
    (K₁ K₂ : IntermediateField F Ω) [FiniteDimensional F ↥K₁] [FiniteDimensional F ↥K₂]
    (h₁ : algebraicClosure ℚ ↥K₁ = ⊥) (h₂ : algebraicClosure ℚ ↥K₂ = ⊥)
    (hcop : Nat.Coprime (finrank F ↥K₁) (finrank F ↥K₂)) :
    algebraicClosure ℚ ↥(K₁ ⊔ K₂) = ⊥ := by
  haveI : FiniteDimensional F ↥(K₁ ⊔ K₂) := IntermediateField.finiteDimensional_sup K₁ K₂
  haveI : FiniteDimensional ↥K₁ ↥(K₁ ⊔ K₂) := FiniteDimensional.right F ↥K₁ ↥(K₁ ⊔ K₂)
  haveI : FiniteDimensional ↥K₂ ↥(K₁ ⊔ K₂) := FiniteDimensional.right F ↥K₂ ↥(K₁ ⊔ K₂)
  have hsup : finrank F ↥(K₁ ⊔ K₂) = finrank F ↥K₁ * finrank F ↥K₂ :=
    (IntermediateField.LinearDisjoint.of_finrank_coprime hcop).finrank_sup
  -- the two steps of the tower are the degrees of the opposite factors
  have hstep₁ : finrank ↥K₁ ↥(K₁ ⊔ K₂) = finrank F ↥K₂ := by
    have h := Module.finrank_mul_finrank F ↥K₁ ↥(K₁ ⊔ K₂)
    rw [hsup] at h
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h
  have hstep₂ : finrank ↥K₂ ↥(K₁ ⊔ K₂) = finrank F ↥K₁ := by
    have h := Module.finrank_mul_finrank F ↥K₂ ↥(K₁ ⊔ K₂)
    rw [hsup, mul_comm (finrank F ↥K₁)] at h
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h
  refine le_antisymm (fun x hx => ?_) bot_le
  have hint : IsIntegral ℚ x := mem_algebraicClosure_iff'.mp hx
  have hd₁ : (minpoly ℚ x).natDegree ∣ finrank F ↥K₂ :=
    hstep₁ ▸ natDegree_minpoly_dvd_finrank h₁ hint
  have hd₂ : (minpoly ℚ x).natDegree ∣ finrank F ↥K₁ :=
    hstep₂ ▸ natDegree_minpoly_dvd_finrank h₂ hint
  have hone : (minpoly ℚ x).natDegree = 1 :=
    Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hd₂ hd₁)
  have hbot : (ℚ⟮x⟯ : IntermediateField ℚ ↥(K₁ ⊔ K₂)) = ⊥ :=
    IntermediateField.finrank_eq_one_iff.mp (by rw [IntermediateField.adjoin.finrank hint, hone])
  exact hbot ▸ IntermediateField.mem_adjoin_simple_self ℚ x

/-! ## The product realization -/

/-- **The compositum of two regular Galois subextensions of `ℚ̄(T) / ℚ(T)` of coprime degree
realizes the direct product of their groups, regularly.** -/
theorem isRegularInverseGalois_of_coprime_intermediate_fields
    (K₁ K₂ : IntermediateField (RatFunc ℚ) (AlgebraicClosure (RatFunc ℚ)))
    [IsGalois (RatFunc ℚ) ↥K₁] [IsGalois (RatFunc ℚ) ↥K₂]
    [FiniteDimensional (RatFunc ℚ) ↥K₁] [FiniteDimensional (RatFunc ℚ) ↥K₂]
    (hreg₁ : algebraicClosure ℚ ↥K₁ = ⊥) (hreg₂ : algebraicClosure ℚ ↥K₂ = ⊥)
    (hcop : Nat.Coprime (finrank (RatFunc ℚ) ↥K₁) (finrank (RatFunc ℚ) ↥K₂))
    {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (e₁ : (↥K₁ ≃ₐ[RatFunc ℚ] ↥K₁) ≃* G₁) (e₂ : (↥K₂ ≃ₐ[RatFunc ℚ] ↥K₂) ≃* G₂) :
    IsRegularInverseGalois (G₁ × G₂) := by
  haveI : FiniteDimensional (RatFunc ℚ) ↥(K₁ ⊔ K₂) :=
    IntermediateField.finiteDimensional_sup K₁ K₂
  haveI : IsGalois (RatFunc ℚ) ↥(K₁ ⊔ K₂) :=
    FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateFieldMax K₁ K₂
  exact ⟨↥(K₁ ⊔ K₂), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    isScalarTower_rat_ratFunc _, algebraicClosure_sup_eq_bot K₁ K₂ hreg₁ hreg₂ hcop,
    ⟨(galSupProdEquiv K₁ K₂ hcop).trans (MulEquiv.prodCongr e₁ e₂)⟩⟩

end Rigidity.RET

/-- **The direct product of two regular inverse Galois groups of coprime order is a regular
inverse Galois group.**  Embed the two realizing extensions into an algebraic closure of `ℚ(T)`
and take their compositum: coprimality makes its Galois group the product, and it also makes the
compositum regular. -/
theorem IsRegularInverseGalois.prod_of_coprime {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (h₁ : IsRegularInverseGalois G₁) (h₂ : IsRegularInverseGalois G₂)
    (hcop : Nat.Coprime (Nat.card G₁) (Nat.card G₂)) :
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
  have hfr₁ : finrank (RatFunc ℚ) ↥i₁.fieldRange = Nat.card G₁ := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact Nat.card_congr (ψ₁.autCongr.symm.trans φ₁).toEquiv
  have hfr₂ : finrank (RatFunc ℚ) ↥i₂.fieldRange = Nat.card G₂ := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact Nat.card_congr (ψ₂.autCongr.symm.trans φ₂).toEquiv
  exact Rigidity.RET.isRegularInverseGalois_of_coprime_intermediate_fields
    i₁.fieldRange i₂.fieldRange hregK₁ hregK₂ (by rw [hfr₁, hfr₂]; exact hcop)
    (ψ₁.autCongr.symm.trans φ₁) (ψ₂.autCongr.symm.trans φ₂)

end
