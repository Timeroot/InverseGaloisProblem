/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts

/-!
# The two charts of the line

The projective line is covered by two copies of the affine line, glued along the inversion of the
coordinate: the functions regular on the first are the polynomials in the coordinate, and the
functions regular on the second are the polynomials in its inverse.  A function regular on both is
regular everywhere, hence constant, and that is the statement this file establishes in the form it
is used: an element of the field of rational functions integral over both charts is a constant.

For the first chart nothing is needed beyond the polynomials being integrally closed in their
fraction field.  For the second, integrality is turned into a bound on the valuation at infinity:
the elements of valuation at most one form a ring that is integrally closed in the ambient field,
so an element integral over a subring of it lies in it, and the valuation at infinity of a
polynomial records its degree.

The same comparison bounds the pole at infinity of an element integral over the first chart:
multiplying a polynomial by a large enough power of the inverse coordinate lands it in the second
chart, so scaling the roots of an integral equation by that power moves the whole equation into the
second chart.

## Main definitions

* `Rigidity.RET.inftyChart` — the functions regular at the far end of the line.

## Main results

* `Rigidity.RET.valuation_le_one_of_isIntegral_adjoin` — integrality over the polynomials in an
  element of valuation at most one bounds the valuation.
* `Rigidity.RET.natDegree_eq_zero_of_isIntegral_inftyChart` — a polynomial integral over the second
  chart has degree zero.
* `Rigidity.RET.exists_const_of_isIntegral_charts` — an element integral over both charts is a
  constant.
* `Rigidity.RET.inv_pow_mul_algebraMap_mem_inftyChart` — a polynomial divided by a large enough
  power of the coordinate is regular at the far end of the line.
* `Rigidity.RET.isIntegral_of_monic_of_coeff_mem` — a monic equation with coefficients in a
  subalgebra witnesses integrality over it.
* `Rigidity.RET.isIntegral_coeff_minpoly` — the coefficients of the minimal polynomial of an
  integral element are integral.
-/

open Polynomial IsDedekindDomain WithZero

noncomputable section


namespace Rigidity.RET

/-! ## Integrality over a chart bounds a valuation -/

section AdjoinValuation

variable {k K Γ : Type*} [Field k] [Field K] [Algebra k K] [LinearOrderedCommGroupWithZero Γ]

/-- **Integrality over the polynomials in an element of valuation at most one bounds the
valuation.**  The elements of valuation at most one form a ring integrally closed in the field, and
it contains the polynomials in question. -/
theorem valuation_le_one_of_isIntegral_adjoin (v : Valuation K Γ) {t : K} (ht : v t ≤ 1)
    (hconst : ∀ a : k, v (algebraMap k K a) ≤ 1) {c : K}
    (hc : IsIntegral ↥(Algebra.adjoin k {t}) c) : v c ≤ 1 := by
  have hsub : ∀ z ∈ Algebra.adjoin k {t}, v z ≤ 1 := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem w hw => exact (Set.mem_singleton_iff.1 hw) ▸ ht
    | algebraMap a => exact hconst a
    | add w₁ w₂ _ _ h₁ h₂ => exact le_trans (v.map_add w₁ w₂) (max_le h₁ h₂)
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_le_one' h₁ h₂
  let f : ↥(Algebra.adjoin k {t}) →+* ↥v.integer :=
    { toFun := fun z => ⟨(z : K), (Valuation.mem_integer_iff v _).2 (hsub z z.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hint : IsIntegral ↥v.integer ((RingHom.id K) c) :=
    hc.map_of_comp_eq f (RingHom.id K) (by ext z; rfl)
  exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.1 hint

end AdjoinValuation

/-! ## The far end of the line -/

section Charts

variable (k : Type*) [Field k]

/-- **The functions regular at the far end of the line**: the polynomials in the inverse
coordinate. -/
abbrev inftyChart : Subalgebra k (RatFunc k) := Algebra.adjoin k {(RatFunc.X : RatFunc k)⁻¹}

/-- **An element integral over the first chart is a polynomial**, the polynomials being integrally
closed in the rational functions. -/
theorem exists_polynomial_of_isIntegral {c : RatFunc k} (h : IsIntegral k[X] c) :
    ∃ p : k[X], algebraMap k[X] (RatFunc k) p = c :=
  IsIntegrallyClosed.isIntegral_iff.1 h

/-- **A polynomial integral over the second chart has degree zero.**  Its valuation at infinity is
at most one, and that valuation records the degree. -/
theorem natDegree_eq_zero_of_isIntegral_inftyChart {p : k[X]}
    (h : IsIntegral ↥(inftyChart k) (algebraMap k[X] (RatFunc k) p)) : p.natDegree = 0 := by
  classical
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have hle : FunctionField.inftyValuation k (algebraMap k[X] (RatFunc k) p) ≤ 1 := by
    refine valuation_le_one_of_isIntegral_adjoin (k := k) (FunctionField.inftyValuation k) ?_ ?_ h
    · have hX : FunctionField.inftyValuation k (1 / (RatFunc.X : RatFunc k)) = exp (-1) :=
        FunctionField.inftyValuation.X_inv k
      rw [one_div] at hX
      rw [hX, ← WithZero.exp_zero (M := ℤ), WithZero.exp_le_exp]
      norm_num
    · intro a
      rcases eq_or_ne a 0 with rfl | ha
      · simp
      · have hC : algebraMap k (RatFunc k) a = RatFunc.C a := rfl
        rw [hC, FunctionField.inftyValuation.C k ha]
  rw [FunctionField.inftyValuation_apply, FunctionField.inftyValuation.polynomial k hp,
    ← WithZero.exp_zero (M := ℤ), WithZero.exp_le_exp] at hle
  omega

/-- **An element integral over both charts is a constant.**  It is a polynomial by the first chart
and of degree zero by the second. -/
theorem exists_const_of_isIntegral_charts {c : RatFunc k} (h₁ : IsIntegral k[X] c)
    (h₂ : IsIntegral ↥(inftyChart k) c) : ∃ a : k, c = algebraMap k (RatFunc k) a := by
  obtain ⟨p, rfl⟩ := exists_polynomial_of_isIntegral k h₁
  obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.1 (natDegree_eq_zero_of_isIntegral_inftyChart k h₂)
  refine ⟨a, ?_⟩
  rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k), Polynomial.algebraMap_eq]

/-- **A polynomial divided by a large enough power of the coordinate is regular at the far end of
the line**: dividing reverses the coefficients, and no negative powers survive once the power
exceeds the degree. -/
theorem inv_pow_mul_algebraMap_mem_inftyChart {p : k[X]} {N : ℕ} (h : p.natDegree ≤ N) :
    (RatFunc.X : RatFunc k)⁻¹ ^ N * algebraMap k[X] (RatFunc k) p ∈ inftyChart k := by
  letI : Invertible (RatFunc.X : RatFunc k) := invertibleOfNonzero RatFunc.X_ne_zero
  have key := Polynomial.eval₂_reflect_mul_pow (algebraMap k (RatFunc k))
    (RatFunc.X : RatFunc k) N p h
  rw [invOf_eq_inv] at key
  have hXN : ((RatFunc.X : RatFunc k)⁻¹) ^ N * (RatFunc.X : RatFunc k) ^ N = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ RatFunc.X_ne_zero, one_pow]
  have hval : (RatFunc.X : RatFunc k)⁻¹ ^ N * algebraMap k[X] (RatFunc k) p
      = Polynomial.aeval (RatFunc.X : RatFunc k)⁻¹ (Polynomial.reflect N p) := by
    have hp : algebraMap k[X] (RatFunc k) p = Polynomial.eval₂ (algebraMap k (RatFunc k))
        (RatFunc.X : RatFunc k) p := by
      rw [← Polynomial.aeval_def]
      have halg : (Polynomial.aeval (RatFunc.X : RatFunc k) : k[X] →ₐ[k] RatFunc k)
          = IsScalarTower.toAlgHom k k[X] (RatFunc k) := by
        refine Polynomial.algHom_ext ?_
        simp [RatFunc.algebraMap_X]
      exact (congrArg (fun φ => φ p) halg).symm
    rw [hp, ← key, Polynomial.aeval_def]
    calc (RatFunc.X : RatFunc k)⁻¹ ^ N
          * (Polynomial.eval₂ (algebraMap k (RatFunc k)) (RatFunc.X : RatFunc k)⁻¹
              (Polynomial.reflect N p) * (RatFunc.X : RatFunc k) ^ N)
        = ((RatFunc.X : RatFunc k)⁻¹ ^ N * (RatFunc.X : RatFunc k) ^ N)
          * Polynomial.eval₂ (algebraMap k (RatFunc k)) (RatFunc.X : RatFunc k)⁻¹
              (Polynomial.reflect N p) := by ring
      _ = _ := by rw [hXN, one_mul]
  rw [hval]
  exact Polynomial.aeval_mem_adjoin_singleton k _

end Charts

/-! ## Recognising integrality -/

section Recognise

variable {k L F : Type*} [Field k] [Field L] [Field F] [Algebra k L] [Algebra L F]

/-- **A monic equation with coefficients in a subalgebra witnesses integrality over it.** -/
theorem isIntegral_of_monic_of_coeff_mem {A : Subalgebra k L} {z : F} {q : L[X]} (hq : q.Monic)
    (hmem : ∀ i, q.coeff i ∈ A) (hz : Polynomial.aeval z q = 0) : IsIntegral ↥A z := by
  have hlifts : q ∈ Polynomial.lifts (algebraMap ↥A L) :=
    (Polynomial.lifts_iff_coeff_lifts q).2 fun i => ⟨⟨q.coeff i, hmem i⟩, rfl⟩
  obtain ⟨q', hq'map, _, hq'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hq
  refine ⟨q', hq'm, ?_⟩
  have hmap : Polynomial.aeval z (q'.map (algebraMap ↥A L)) = Polynomial.aeval z q' :=
    Polynomial.aeval_map_algebraMap L z q'
  rw [← Polynomial.aeval_def, ← hmap, hq'map, hz]

end Recognise

/-! ## The coefficients of a minimal polynomial -/

section MinpolyCoeff

variable {A L F : Type*} [CommRing A] [Field L] [Field F] [Algebra A L] [Algebra L F] [Algebra A F]
  [IsScalarTower A L F]

/-- **The coefficients of the minimal polynomial of an integral element are integral.**  The
minimal polynomial divides any monic equation with integral coefficients, so its own coefficients
are polynomial expressions in the roots of such an equation. -/
theorem isIntegral_coeff_minpoly {y : F} (hy : IsIntegral A y) (i : ℕ) :
    IsIntegral A ((minpoly L y).coeff i) := by
  obtain ⟨p, hpm, hp⟩ := hy
  have hpa : Polynomial.aeval y (p.map (algebraMap A L)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, hp]
  have hyL : IsIntegral L y := ⟨p.map (algebraMap A L), hpm.map _, by
    rw [← Polynomial.aeval_def]; exact hpa⟩
  exact Polynomial.isIntegral_coeff_of_dvd p (minpoly L y) hpm (minpoly.monic hyL)
    (minpoly.dvd L y hpa) i

end MinpolyCoeff

end Rigidity.RET
